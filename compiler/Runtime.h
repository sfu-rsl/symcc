// This file is part of SymCC.
//
// SymCC is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// SymCC is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// SymCC. If not, see <https://www.gnu.org/licenses/>.

#ifndef LLVM_TRANSFORMS_SYMBOLICCOMPILER_RUNTIME_H
#define LLVM_TRANSFORMS_SYMBOLICCOMPILER_RUNTIME_H

#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Module.h>

#if LLVM_VERSION_MAJOR >= 9 && LLVM_VERSION_MAJOR < 11
  using SymFnT = llvm::Value *;
#else
  using SymFnT = llvm::FunctionCallee;
#endif

namespace llvm {

/// Runtime functions
struct Runtime {
  Runtime(llvm::Module &M);

  SymFnT buildInteger{};
  SymFnT buildInteger128{};
  SymFnT buildValueFromMemory{};
  SymFnT buildFloat{};
  SymFnT buildNullPointer{};
  SymFnT buildTrue{};
  SymFnT buildFalse{};
  SymFnT buildBool{};
  SymFnT buildSExt{};
  SymFnT buildZExt{};
  SymFnT buildTrunc{};
  SymFnT buildBswap{};
  SymFnT buildIntToFloat{};
  SymFnT buildFloatToFloat{};
  SymFnT buildBitsToFloat{};
  SymFnT buildFloatToBits{};
  SymFnT buildFloatToSignedInt{};
  SymFnT buildFloatToUnsignedInt{};
  SymFnT buildFloatAbs{};
  SymFnT buildBoolAnd{};
  SymFnT buildBoolOr{};
  SymFnT buildBoolXor{};
  SymFnT buildBoolToBits{};
  SymFnT buildBoolToSignBits{};
  SymFnT buildInsert{};
  SymFnT buildExtract{};

  // branch queries
  SymFnT pushPathConstraint{};

  // symbolic hanlding of function calls / returns
  SymFnT getParameterExpression{};
  SymFnT getParameterExpressionWithTruncate{};
  SymFnT setParameterExpression{};
  SymFnT setParameterCount{};
  SymFnT setIntParameterExpression{};
  SymFnT setReturnExpression{};
  SymFnT isIntParameter{};
  SymFnT getReturnExpressionWithTruncate{};
  SymFnT getReturnExpression{};

  // models
  SymFnT memcpy{};
  SymFnT memset{};
  SymFnT memmove{};
  SymFnT LibcMemset{};
  SymFnT LibcMemcpy{};
  SymFnT LibcMemmove{};

  // memory
  SymFnT readMemory{};
  SymFnT writeMemory{};
  SymFnT concretizeMemory{};

  // events
  SymFnT notifyCall{};
  SymFnT notifyRet{};
  SymFnT notifyBasicBlock{};

  // handling of indirect calls
  SymFnT wrapIndirectCallArgCount{};
  SymFnT wrapIndirectCallArgInt{};
  SymFnT wrapIndirectCallInt1{};
  SymFnT wrapIndirectCallInt8{};
  SymFnT wrapIndirectCallInt16{};
  SymFnT wrapIndirectCallInt32{};
  SymFnT wrapIndirectCallInt64{};
  SymFnT wrapIndirectCallPtr{};
  SymFnT wrapIndirectCallVoid{};
  SymFnT checkIndirectCallTarget{};

  // variadic functions
  SymFnT vaListStart{};

  // debugging
  SymFnT checkConsistency{};

  SymFnT switchFsRegisterToNative{};
  SymFnT switchFsRegisterToEmulation{};

  /// Mapping from icmp predicates to the functions that build the corresponding
  /// symbolic expressions.
  std::array<SymFnT, llvm::CmpInst::BAD_ICMP_PREDICATE>
      comparisonHandlers{};

  /// Mapping from binary operators to the functions that build the
  /// corresponding symbolic expressions.
  std::array<SymFnT, llvm::Instruction::BinaryOpsEnd>
      binaryOperatorHandlers{};
};

bool isInterceptedFunction(const llvm::Function &f);

}

#endif
