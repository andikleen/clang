//===- CLog.h - Logging Interface -------------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIBCLANG_CLOG_H
#define LLVM_LIBCLANG_CLOG_H

#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/IntrusiveRefCntPtr.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

namespace llvm {
class format_object_base;
}

namespace clang {

namespace cxindex {

class Logger;
typedef IntrusiveRefCntPtr<Logger> LogRef;

/// \brief Collects logging output and writes it to stderr when it's destructed.
/// Common use case:
/// \code
///   if (LogRef Log = Logger::make(__func__)) {
///     *Log << "stuff";
///   }
/// \endcode
class Logger : public RefCountedBase<Logger> {
  std::string Name;
  bool Trace;
  llvm::SmallString<64> Msg;
  llvm::raw_svector_ostream LogOS;
public:
  static const char *getEnvVar() {
    static const char *sCachedVar = ::getenv("LIBCLANG_LOGGING");
    return sCachedVar;
  }
  static bool isLoggingEnabled() { return getEnvVar() != 0; }
  static bool isStackTracingEnabled() {
    if (const char *EnvOpt = Logger::getEnvVar())
      return llvm::StringRef(EnvOpt) =="2";
    return false;
  }
  static LogRef make(llvm::StringRef name,
                     bool trace = isStackTracingEnabled()) {
    if (isLoggingEnabled())
      return new Logger(name, trace);
    return 0;
  }

  explicit Logger(llvm::StringRef name, bool trace)
    : Name(name), Trace(trace), LogOS(Msg) { }
  ~Logger();

  Logger &operator<<(CXTranslationUnit);
  Logger &operator<<(CXSourceLocation);
  Logger &operator<<(CXSourceRange);
  Logger &operator<<(CXString);
  Logger &operator<<(llvm::StringRef Str) { LogOS << Str; return *this; }
  Logger &operator<<(const char *Str) {
    if (Str)
      LogOS << Str;
    return *this;
  }
  Logger &operator<<(unsigned long N) { LogOS << N; return *this; }
  Logger &operator<<(long N) { LogOS << N ; return *this; }
  Logger &operator<<(unsigned int N) { LogOS << N; return *this; }
  Logger &operator<<(int N) { LogOS << N; return *this; }
  Logger &operator<<(char C) { LogOS << C; return *this; }
  Logger &operator<<(unsigned char C) { LogOS << C; return *this; }
  Logger &operator<<(signed char C) { LogOS << C; return *this; }
  Logger &operator<<(const llvm::format_object_base &Fmt);
};

}
}

/// \brief Macros to automate common uses of Logger. Like this:
/// \code
///   LOG_FUNC_SECTION {
///     *Log << "blah";
///   }
#define LOG_SECTION(NAME) if (LogRef Log = clang::cxindex::Logger::make(NAME))
#define LOG_FUNC_SECTION LOG_SECTION(__func__)

#endif