//===-- sanitizer_stoptheworld_linux_libcdep.cc ---------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// See sanitizer_stoptheworld.h for details.
// This implementation was inspired by Markus Gutschke's linuxthreads.cc.
//
//===----------------------------------------------------------------------===//

#include "sanitizer_platform.h"

#if SANITIZER_FREEBSD && (defined(__i386__) || defined(__x86_64__))

#include "sanitizer_stoptheworld.h"

#include "sanitizer_platform_limits_posix.h"
#include "sanitizer_atomic.h"

#include <errno.h>
#include <stddef.h>
#include <sys/types.h> // for pid_t
#include <sys/ptrace.h> // for PTRACE_* definitions
#include <sys/thr.h>
#include <sys/wait.h> // for signal-related stuff
#include <link.h>
#include <pthread.h>
#include <unistd.h> // for rfork

#ifdef sa_handler
# undef sa_handler
#endif

#ifdef sa_sigaction
# undef sa_sigaction
#endif

#include "sanitizer_common.h"
#include "sanitizer_flags.h"
#include "sanitizer_libc.h"
#include "sanitizer_linux.h"
#include "sanitizer_mutex.h"
#include "sanitizer_placement_new.h"

// This module works by forking a tracer process that shares the address space
// with the caller process, which subsequently attaches to the caller process
// with ptrace and suspends all threads within. PTRACE_GETREGS can then be used
// to obtain their register state. The callback supplied to StopTheWorld() is
// run in the tracer process while the threads are suspended.

namespace __sanitizer {

class SuspendedThreadsListFreeBSD : public SuspendedThreadsList {
 public:
  SuspendedThreadsListFreeBSD() : parent_pid_(-1) { lwp_ids_.reserve(1024); }
  ~SuspendedThreadsListFreeBSD();
  bool populate(pid_t pid);

  tid_t GetThreadID(uptr index) const;
  uptr ThreadCount() const;
  bool ContainsTid(tid_t thread_id) const;

  PtraceRegistersStatus GetRegistersAndSP(uptr index, uptr *buffer,
                                          uptr *sp) const;
  uptr RegisterCount() const;

 private:
  InternalMmapVector<lwpid_t> lwp_ids_;
  pid_t parent_pid_;
};

// Structure for passing arguments into the tracer thread.
struct TracerThreadArgument {
  StopTheWorldCallback callback;
  void *callback_argument;
  uptr parent_pid;
};

// Size of alternative stack for signal handlers in the tracer thread.
static const int kHandlerStackSize = 8192;

// This function will be run as a cloned task.
static int TracerThread(void* argument) {
  TracerThreadArgument *tracer_thread_argument =
      (TracerThreadArgument *)argument;

  SuspendedThreadsListFreeBSD suspended_threads_list;

  if (suspended_threads_list.populate(tracer_thread_argument->parent_pid))
    tracer_thread_argument->callback(suspended_threads_list,
                                     tracer_thread_argument->callback_argument);

  return 0;
}

class ScopedStackSpaceWithGuard {
 public:
  explicit ScopedStackSpaceWithGuard(uptr stack_size) {
    stack_size_ = stack_size;
    guard_size_ = GetPageSizeCached();
    // FIXME: Omitting MAP_STACK here works in current kernels but might break
    // in the future.
    guard_start_ = (uptr)MmapOrDie(stack_size_ + guard_size_,
                                   "ScopedStackWithGuard");
    CHECK(MprotectNoAccess((uptr)guard_start_, guard_size_));
  }
  ~ScopedStackSpaceWithGuard() {
    UnmapOrDie((void *)guard_start_, stack_size_ + guard_size_);
  }
  void *Bottom() const {
    return (void *)(guard_start_ + stack_size_ + guard_size_);
  }

 private:
  uptr stack_size_;
  uptr guard_size_;
  uptr guard_start_;
};

// When sanitizer output is being redirected to file (i.e. by using log_path),
// the tracer should write to the parent's log instead of trying to open a new
// file. Alert the logging code to the fact that we have a tracer.
struct ScopedSetTracerPID {
  explicit ScopedSetTracerPID(uptr tracer_pid) {
    stoptheworld_tracer_pid = tracer_pid;
    stoptheworld_tracer_ppid = internal_getpid();
  }
  ~ScopedSetTracerPID() {
    stoptheworld_tracer_pid = 0;
    stoptheworld_tracer_ppid = 0;
  }
};

void StopTheWorld(StopTheWorldCallback callback, void *argument) {
  // Prepare the arguments for TracerThread.
  struct TracerThreadArgument tracer_thread_argument;
  tracer_thread_argument.callback = callback;
  tracer_thread_argument.callback_argument = argument;
  tracer_thread_argument.parent_pid = internal_getpid();
  const uptr kTracerStackSize = 2 * 1024 * 1024;
  ScopedStackSpaceWithGuard tracer_stack(kTracerStackSize);

  uptr tracer_pid = rfork_thread(RFPROC | RFMEM, tracer_stack.Bottom(),
                                 TracerThread, &tracer_thread_argument);
  int local_errno = 0;
  if (internal_iserror(tracer_pid, &local_errno)) {
    VReport(1, "Failed spawning a tracer thread (errno %d).\n", local_errno);
  } else {
    //ScopedSetTracerPID scoped_set_tracer_pid(tracer_pid);
    for (;;) {
      int status;
      uptr waitpid_status = internal_waitpid(tracer_pid, &status, 0);
      if (internal_iserror(waitpid_status, &local_errno)) {
        if (local_errno == EINTR)
          continue;
        VReport(1, "Waiting on the tracer thread failed (errno %d).\n",
                local_errno);
        break;
      }
      if (WIFEXITED(status) && WEXITSTATUS(status) != 0)
        internal__exit(WEXITSTATUS(status));
      if (WIFEXITED(status))
        break;
    }
  }
}

// Platform-specific methods from SuspendedThreadsList.
#if defined(__i386__) || defined(__x86_64__)
typedef reg regs_struct;
#if defined(__i386__)
#define REG_SP r_esp
#else
#define REG_SP r_rsp
#endif
#else
#error "Unsupported architecture"
#endif

SuspendedThreadsListFreeBSD::~SuspendedThreadsListFreeBSD() {
  stoptheworld_tracer_pid = 0;
  stoptheworld_tracer_ppid = 0;

  if (parent_pid_ < 0)
    return;

  int local_errno = 0;
  if (internal_iserror(internal_ptrace(PT_DETACH, parent_pid_, 0, 0),
                       &local_errno)) {
    VReport(1, "Failed to detach the parent.\n");
  }
}

bool SuspendedThreadsListFreeBSD::populate(pid_t pid) {
  stoptheworld_tracer_pid = internal_getpid();
  stoptheworld_tracer_ppid = pid;

  int local_errno = 0;
  if (internal_iserror(internal_ptrace(PT_ATTACH, pid, 0, 0),
                       &local_errno)) {
    VReport(1, "Failed to attach the parent.\n");
    return false;
  }

  parent_pid_ = pid;

  // wait for the parent process to stop
  for (;;) {
    int status;
    if (internal_iserror(internal_waitpid(pid, &status, 0),
                         &local_errno)) {
      if (local_errno == EINTR)
        continue;
      VReport(1, "Failed to stop the parent (errno %d).\n", local_errno);
      return false;
    }
    if (WIFSTOPPED(status))
      break;
  }

  uptr lwp_count = internal_ptrace(PT_GETNUMLWPS, pid, 0, 0);
  if (internal_iserror(lwp_count, &local_errno)) {
      VReport(1, "Failed to get LWP count (errno %d).\n", local_errno);
      return false;
  }

  lwp_ids_.resize(lwp_count);
  if (internal_iserror(internal_ptrace(PT_GETLWPLIST, pid,
                       lwp_ids_.data(), (void*)lwp_ids_.size()),
                       &local_errno)) {
      lwp_ids_.clear();
      VReport(1, "Failed to get LWP list (errno %d).\n", local_errno);
      return false;
  }

  return true;
}

tid_t SuspendedThreadsListFreeBSD::GetThreadID(uptr index) const {
  CHECK_LT(index, lwp_ids_.size());
  return lwp_ids_[index];
}

uptr SuspendedThreadsListFreeBSD::ThreadCount() const {
  return lwp_ids_.size();
}

bool SuspendedThreadsListFreeBSD::ContainsTid(tid_t thread_id) const {
  lwpid_t lwp_id = (lwpid_t)thread_id;
  for (uptr i = 0; i < lwp_ids_.size(); i++) {
    if (lwp_ids_[i] == lwp_id) return true;
  }
  return false;
}

PtraceRegistersStatus SuspendedThreadsListFreeBSD::GetRegistersAndSP(
    uptr index, uptr *buffer, uptr *sp) const {
  int tid = GetThreadID(index);
  regs_struct regs;
  int pterrno;
  bool isErr = internal_iserror(internal_ptrace(PT_GETREGS, tid,
                                (caddr_t)&regs, 0), &pterrno);
  if (isErr) {
    VReport(1, "Could not get registers from thread %d (errno %d).\n", tid,
            pterrno);
    // ESRCH means that the given thread is not suspended or already dead.
    // Therefore it's unsafe to inspect its data (e.g. walk through stack) and
    // we should notify caller about this.
    return pterrno == ESRCH ? REGISTERS_UNAVAILABLE_FATAL
                            : REGISTERS_UNAVAILABLE;
  }

  *sp = regs.REG_SP;
  internal_memcpy(buffer, &regs, sizeof(regs));
  return REGISTERS_AVAILABLE;
}

uptr SuspendedThreadsListFreeBSD::RegisterCount() const {
  return sizeof(regs_struct) / sizeof(uptr);
}
} // namespace __sanitizer

#endif
