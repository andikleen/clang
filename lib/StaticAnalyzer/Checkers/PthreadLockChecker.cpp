//===--- PthreadLockChecker.cpp - Check for locking problems ---*- C++ -*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This defines PthreadLockChecker, a simple lock -> unlock checker.
// Also handles XNU locks, which behave similarly enough to share code.
// And Linux kernel locks too.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "llvm/ADT/ImmutableList.h"
#include "llvm/Support/Regex.h"

using namespace clang;
using namespace ento;

namespace {
class PthreadLockChecker : public Checker< check::PostStmt<CallExpr> > {
  mutable OwningPtr<BugType> BT_doublelock;
  mutable OwningPtr<BugType> BT_lor;
  enum LockingSemantics {
    NotApplicable = 0,
    PthreadSemantics,
    XNUSemantics,
    LinuxSemantics
  };
public:
  void checkPostStmt(const CallExpr *CE, CheckerContext &C) const;
    
  void AcquireLock(CheckerContext &C, const CallExpr *CE, SVal lock,
                   bool isTryLock, enum LockingSemantics semantics) const;
    
  void ReleaseLock(CheckerContext &C, const CallExpr *CE, SVal lock) const;
};

// should be inside the class, but the class is const and Regex.match()
// modifies the "error" member
llvm::Regex LinuxLock("^(_?raw_|bit_|rcu_)?(spin|read|write|mutex)_(try|nest_|seq)?lock(_(bh|irq|irqsave))?(_nested)?$");
llvm::Regex LinuxUnlock("^(raw_|bit_|rcu_)?(spin|read|write|mutex)_(seq)?unlock(_bh|_irq|_irqrestore)?$");
// Checked only after LinuxLock
// XXX how about semaphores with non lock semantics?
llvm::Regex LinuxLock_sem("^down(_(read|write))?$");
llvm::Regex LinuxUnlock_sem("^up(_(read|write))?$");
llvm::Regex TryLock("try_.*");
} // end anonymous namespace

// GDM Entry for tracking lock state.
REGISTER_LIST_WITH_PROGRAMSTATE(LockSet, const MemRegion *)

void PthreadLockChecker::checkPostStmt(const CallExpr *CE,
                                       CheckerContext &C) const {
  ProgramStateRef state = C.getState();
  const LocationContext *LCtx = C.getLocationContext();
  StringRef FName = C.getCalleeName(CE);
  if (FName.empty())
    return;

  if (CE->getNumArgs() != 1 && CE->getNumArgs() != 2)
    return;

  if (FName == "pthread_mutex_lock" ||
      FName == "pthread_rwlock_rdlock" ||
      FName == "pthread_rwlock_wrlock")
    AcquireLock(C, CE, state->getSVal(CE->getArg(0), LCtx),
                false, PthreadSemantics);
  else if (FName == "lck_mtx_lock" ||
           FName == "lck_rw_lock_exclusive" ||
           FName == "lck_rw_lock_shared") 
    AcquireLock(C, CE, state->getSVal(CE->getArg(0), LCtx),
                false, XNUSemantics);
  else if (FName == "pthread_mutex_trylock" ||
           FName == "pthread_rwlock_tryrdlock" ||
           FName == "pthread_rwlock_tryrwlock")
    AcquireLock(C, CE, state->getSVal(CE->getArg(0), LCtx),
                true, PthreadSemantics);
  else if (FName == "lck_mtx_try_lock" ||
           FName == "lck_rw_try_lock_exclusive" ||
           FName == "lck_rw_try_lock_shared")
    AcquireLock(C, CE, state->getSVal(CE->getArg(0), LCtx),
                true, XNUSemantics);
  else if (FName == "pthread_mutex_unlock" ||
           FName == "pthread_rwlock_unlock" ||
           FName == "lck_mtx_unlock" ||
           FName == "lck_rw_done")
    ReleaseLock(C, CE, state->getSVal(CE->getArg(0), LCtx));
  else if (LinuxLock.match(FName) || LinuxLock_sem.match(FName))
    AcquireLock(C, CE, state->getSVal(CE->getArg(0), LCtx),
		TryLock.match(FName), LinuxSemantics);
  else if (LinuxUnlock.match(FName) || LinuxUnlock_sem.match(FName))
    ReleaseLock(C, CE, state->getSVal(CE->getArg(0), LCtx));
}

void PthreadLockChecker::AcquireLock(CheckerContext &C, const CallExpr *CE,
                                     SVal lock, bool isTryLock,
                                     enum LockingSemantics semantics) const {
  
  const MemRegion *lockR = lock.getAsRegion();
  if (!lockR)
    return;
  
  ProgramStateRef state = C.getState();
  
  SVal X = state->getSVal(CE, C.getLocationContext());
  if (X.isUnknownOrUndef())
    return;
  
  DefinedSVal retVal = X.castAs<DefinedSVal>();

  if (state->contains<LockSet>(lockR)) {
    if (!BT_doublelock)
      BT_doublelock.reset(new BugType("Double locking", "Lock checker"));
    ExplodedNode *N = C.generateSink();
    if (!N)
      return;
    BugReport *report = new BugReport(*BT_doublelock,
                                                      "This lock has already "
                                                      "been acquired", N);
    report->addRange(CE->getArg(0)->getSourceRange());
    C.emitReport(report);
    return;
  }

  ProgramStateRef lockSucc = state;
  if (isTryLock) {
    // Bifurcate the state, and allow a mode where the lock acquisition fails.
    ProgramStateRef lockFail;
    switch (semantics) {
    case PthreadSemantics:
      llvm::tie(lockFail, lockSucc) = state->assume(retVal);    
      break;
    case LinuxSemantics:
      llvm::tie(lockSucc, lockFail) = state->assume(retVal);    
      break;
    case XNUSemantics:
      llvm::tie(lockSucc, lockFail) = state->assume(retVal);    
      break;
    default:
      llvm_unreachable("Unknown tryLock locking semantics");
    }
    assert(lockFail && lockSucc);
    C.addTransition(lockFail);

  } else if (semantics == PthreadSemantics) {
    // Assume that the return value was 0.
    lockSucc = state->assume(retVal, false);
    assert(lockSucc);

  } else {
    // XNU or Linux locking semantics return void on non-try locks
    assert((semantics == XNUSemantics || semantics == LinuxSemantics) && "Unknown locking semantics");
    lockSucc = state;
  }
  
  // Record that the lock was acquired.  
  lockSucc = lockSucc->add<LockSet>(lockR);
  C.addTransition(lockSucc);
}

void PthreadLockChecker::ReleaseLock(CheckerContext &C, const CallExpr *CE,
                                     SVal lock) const {

  const MemRegion *lockR = lock.getAsRegion();
  if (!lockR)
    return;
  
  ProgramStateRef state = C.getState();
  LockSetTy LS = state->get<LockSet>();

  // FIXME: Better analysis requires IPA for wrappers.
  // FIXME: check for double unlocks
  if (LS.isEmpty())
    return;
  
  const MemRegion *firstLockR = LS.getHead();
  if (firstLockR != lockR) {
    if (!BT_lor)
      BT_lor.reset(new BugType("Lock order reversal", "Lock checker"));
    ExplodedNode *N = C.generateSink();
    if (!N)
      return;
    BugReport *report = new BugReport(*BT_lor,
                                                      "This was not the most "
                                                      "recently acquired lock. "
                                                      "Possible lock order "
                                                      "reversal", N);
    report->addRange(CE->getArg(0)->getSourceRange());
    C.emitReport(report);
    return;
  }

  // Record that the lock was released. 
  state = state->set<LockSet>(LS.getTail());
  C.addTransition(state);
}


void ento::registerPthreadLockChecker(CheckerManager &mgr) {
  mgr.registerChecker<PthreadLockChecker>();
}
