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


#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/SymbolicCompilerPass.h"
#include "llvm/Transforms/Utils/SymbolicCompilerRuntime.h"
#include "llvm/Transforms/Utils/SymbolicCompilerSymbolizer.h"

using namespace llvm;

#ifndef NDEBUG
#define DEBUG(X)                                                               \
  do {                                                                         \
    X;                                                                         \
  } while (false)
#else
#define DEBUG(X) ((void)0)
#endif

namespace {

static constexpr char kSymCtorName[] = "__sym_ctor";

bool instrumentModule(Module &M) {
  DEBUG(errs() << "Symbolizer module instrumentation\n");

  // Redirect calls to external functions to the corresponding wrappers and
  // rename internal functions.
  for (auto &function : M.functions()) {
    auto name = function.getName();
    if (isInterceptedFunction(function))
      function.setName(name + "_symbolized");
  }

  // Insert a constructor that initializes the runtime and any globals.
  Function *ctor;
  std::tie(ctor, std::ignore) = createSanitizerCtorAndInitFunctions(
      M, kSymCtorName, "_sym_initialize", {}, {});
  appendToGlobalCtors(M, ctor, 0);

  return true;
}

bool instrumentFunction(Function &F) {
  auto functionName = F.getName();
  if (functionName == kSymCtorName)
    return false;

  DEBUG(errs() << "Symbolizing function ");
  DEBUG(errs().write_escaped(functionName) << '\n');

  SmallVector<Instruction *, 0> allInstructions;
  allInstructions.reserve(F.getInstructionCount());
  for (auto &I : instructions(F))
    allInstructions.push_back(&I);

  Symbolizer symbolizer(*F.getParent());
  symbolizer.symbolizeFunctionArguments(F);

  for (auto &basicBlock : F)
    symbolizer.insertBasicBlockNotification(basicBlock);

  for (auto *instPtr : allInstructions)
    symbolizer.visit(instPtr);

  symbolizer.finalizePHINodes();
  symbolizer.shortCircuitExpressionUses();

  // DEBUG(errs() << F << '\n');
  assert(!verifyFunction(F, &errs()) &&
         "SymbolizePass produced invalid bitcode");

  return true;
}

} // namespace

bool SymbolizeLegacyPass::doInitialization(Module &M) {
  return instrumentModule(M);
}

bool SymbolizeLegacyPass::runOnFunction(Function &F) {
  return instrumentFunction(F);
}

#if LLVM_VERSION_MAJOR >= 13

PreservedAnalyses SymbolizePass::run(Function &F, FunctionAnalysisManager &) {
  return instrumentFunction(F) ? PreservedAnalyses::none()
                               : PreservedAnalyses::all();
}

PreservedAnalyses SymbolizePass::run(Module &M, ModuleAnalysisManager &) {
  return instrumentModule(M) ? PreservedAnalyses::none()
                             : PreservedAnalyses::all();
}

#endif

char SymbolizeLegacyPass::ID = 0;

SymbolizeLegacyPass::SymbolizeLegacyPass() : FunctionPass(ID) {
    initializeSymbolizeLegacyPassPass(*PassRegistry::getPassRegistry());
}

INITIALIZE_PASS(SymbolizeLegacyPass, "symcc",
                "Efficient Compiler-Based Symbolic Execution", false, false)

FunctionPass *llvm::createSymbolizeLegacyPass() {
  return new SymbolizeLegacyPass();
}

void LLVMAddSymbolizePass(LLVMPassManagerRef PM) {
  unwrap(PM)->add(createSymbolizeLegacyPass());
}
