#include "llvm/Transforms/FunctionPointerAnalysis.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CallSite.h"

#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Constants.h"

#include <vector>
#include <algorithm>
#include <map>
#include <set>
#include <string>

#include "llvm/IR/Metadata.h"

#define DEBUG_TYPE "funcptr-analysis"

using namespace llvm;

static cl::opt<bool> PrintCFG("print-cfg", cl::init(false),
                                           cl::desc("Print CFG"));

namespace {

	struct FunctionPointerAnalysisPass : public ModulePass {
		static char ID;
        std::set<Function*> allFuncSet;
        std::set<Function*> ctorsSet;
        std::set<Function*> dtorsSet;

        // The worklists for the different threads
        std::map<Function*, SmallVector<Function*,10>*> threadFunctionStackMap;

        // Track the creation of new processes
        std::set<Function*> forkedPoints;

        std::map<std::string, std::set<int>> discriminatorMap;
		
		FunctionPointerAnalysisPass() : ModulePass(ID) {
			//initializeFunctionPointerAnalysisPassPass(*PassRegistry::getPassRegistry());

		}

		void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.setPreservesCFG();
		}

		bool contains(Value* V, std::vector<Value*>& L) {
			if (std::find(L.begin(), L.end(), V) != L.end()) {
				return true;
			} else {
				return false;
			}
		}

        void setup() {
            discriminatorMap["ngx_process"].insert(0);
            discriminatorMap["ngx_process"].insert(1);
            discriminatorMap["ngx_process"].insert(2);
            discriminatorMap["ngx_process"].insert(3);
            discriminatorMap["ngx_process"].insert(4);
        }

        void getFunctionOperandsIfAny(Value* operandValue, std::vector<Function*>& funcOperands) {
            if (Function* funcVal = dyn_cast<Function>(operandValue)) {
                funcOperands.push_back(funcVal);
            }

            if (ConstantExpr* consExpr = dyn_cast<ConstantExpr>(operandValue)) {
                for (int i = 0; i < consExpr->getNumOperands(); i++) {
                    Value* operandValue = consExpr->getOperand(i);
                    getFunctionOperandsIfAny(operandValue, funcOperands);
                }
            }
        }

        void internalFindEmbeddedFunctions(User* init, std::set<Function*>* funcSet, std::vector<User*>& visitedGlobals) {
            if (Function* funcOp = dyn_cast<Function>(init)) {
                funcSet->insert(funcOp);
            } else {
                for (int i = 0; i < init->getNumOperands(); i++) {
                    if (User* user = dyn_cast<User>(init->getOperand(i))) {
                        if (std::find(visitedGlobals.begin(), visitedGlobals.end(), user) == visitedGlobals.end()) {
                            visitedGlobals.push_back(user);
                            internalFindEmbeddedFunctions(user, funcSet, visitedGlobals);
                        }
                    }
                }
            }
        }

        std::set<User*> globals;

        void findEmbeddedFunctions(GlobalVariable* gvar, std::map<Function*, std::set<Function*>*>* funcMap, std::vector<User*>& visitedGlobals) {
            User* init = gvar->getInitializer();

            // First find all the functions embedded in the global variable's
            // constant initializer
            std::set<Function*>* setPtr = new std::set<Function*>();
            internalFindEmbeddedFunctions(init, setPtr, visitedGlobals);

            if (!setPtr->empty() && isAddressTaken(gvar)) {
                globals.insert(gvar);
            }

            // setPtr contains all the functions that are embedded in this
            // global variable

            // Now, find all users of this global variable, and if they're
            // instructions, then go to their functions.

            for(User* user: gvar->users()) {
                std::set<Function*> parentFuncList;

                if (Instruction* inst = dyn_cast<Instruction>(user)) {
                    Function* parentFunction = inst->getParent()->getParent();
                    parentFuncList.insert(parentFunction);
                } else if (ConstantExpr* expr = dyn_cast<ConstantExpr>(user)) {
                    for (User* user1: expr->users()) {
                        if (Instruction* inst = dyn_cast<Instruction>(user1)) {
                            Function* parentFunction = inst->getParent()->getParent();
                            parentFuncList.insert(parentFunction);
                        }
                    }
                }

                for (Function* parentFunction: parentFuncList) {
                    std::map<Function*, std::set<Function*>*>::iterator it = funcMap->find(parentFunction);
                    std::set<Function*>* targetSetPtr = nullptr;
                    if (it == funcMap->end()) {
                        targetSetPtr = new std::set<Function*>();
                    } else {
                        targetSetPtr = it->second;
                    }
                    targetSetPtr->insert(setPtr->begin(), setPtr->end());

                    funcMap->insert(std::make_pair(parentFunction, targetSetPtr));
                }
            }
        }


        bool isAddressTaken(User* value) {
            for (User* user: value->users()) {
                // If the address of this appears as the value operand in a
                // Store instruction
                if (StoreInst* storeInst = dyn_cast<StoreInst>(user)) {
                    if (storeInst->getValueOperand() == value) {
                        return true;
                    }
                }
                // If there are any geps taken from this then check those too
                if (GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(user)) {
                    if (gepInst->getType()->isFunctionTy()) {
                        return isAddressTaken(gepInst);
                    }
                } else if (ConstantExpr* consExpr = dyn_cast<ConstantExpr>(user)) {
                    if (consExpr->getType()->isFunctionTy()) {
                        return isAddressTaken(consExpr);
                    }
                }
            }
        }

        bool runOnModule(Module &M) override {
            setup();
			// Handle the ctors and dtors
			GlobalVariable *GVCtor = M.getGlobalVariable("llvm.global_ctors");
			if (GVCtor) {
                if (GVCtor->getInitializer() != nullptr) {
                    if (ConstantArray *CA = dyn_cast<ConstantArray>(GVCtor->getInitializer())) {
                        for (auto &V : CA->operands()) {
                            if (ConstantStruct *CS = dyn_cast<ConstantStruct>(V)) {
                                if (Function* F = dyn_cast<Function>(CS->getOperand(1))) {
                                    ctorsSet.insert(F);
                                }
                            }
                        }
                    }
                }
            }

            GlobalVariable *GVDtor = M.getGlobalVariable("llvm.global_dtors");
			if (GVDtor) {
                if (GVDtor->getInitializer() != nullptr) {
                    if (ConstantArray *CA = dyn_cast<ConstantArray>(GVDtor->getInitializer())) {
                        for (auto &V : CA->operands()) {
                            if (ConstantStruct *CS = dyn_cast<ConstantStruct>(V)) {
                                if (Function* F = dyn_cast<Function>(CS->getOperand(1))) {
                                    dtorsSet.insert(F);
                                }
                            }
                        }
                    }
                }
            }

            // Build list of all internal functions
            for (Module::iterator MIterator = M.begin(); MIterator != M.end(); MIterator++) {
                if (auto *F = dyn_cast<Function>(MIterator)) {
                    if (!F->isDeclaration()) {
                        allFuncSet.insert(F);
                    }
                }
            }
             
            /*
            for (Function* allFunc: allFuncSet) {
                errs() << "Internal function: " << allFunc->getName() << "\n";
            }
            */
            // Anything that's stored in a global structure can be accessed by
            // any of the threads
            std::map<Function*, std::set<Function*>*> embeddedFunctionMap;
            std::vector<User*> visitedGlobals;

            for (GlobalVariable& gvar: M.getGlobalList()) {
                //errs() << "Global variable: " << gvar << "\n";
                if (gvar.hasInitializer()) {
                    // If the global variable has no users, then skip!
                    int countUsers = 0;
                    for (User* user: gvar.users()) {
                        if (user == &gvar) {
                            continue;
                        }
                        countUsers++;
                    }
                    if (countUsers == 0) {
                        continue;
                    }
                    //Constant* init = gvar.getInitializer();
                    //errs() << *init << "\n";
                    findEmbeddedFunctions(&gvar, &embeddedFunctionMap, visitedGlobals);
                }
            }

            Function* mainFunction = M.getFunction("main");
            threadFunctionStackMap[mainFunction] = new SmallVector<Function*, 10>();
            
            threadFunctionStackMap[mainFunction]->push_back(mainFunction);

            std::map<std::string, std::set<std::string>> initPointToFnMap;

            embeddedFunctionMap.insert(std::make_pair(mainFunction, new std::set<Function*>()));

            for (Function* func: *(embeddedFunctionMap)[mainFunction]) {
                threadFunctionStackMap[mainFunction]->push_back(func);
            }

            // Go through the globals whose address was taken, and add them
            // too
            std::vector<User*> visitedGlobals2;
            std::set<Function*> undecidable;
            for (User* glvar: globals) {
                internalFindEmbeddedFunctions(glvar, &undecidable, visitedGlobals2);
            }

            for (Function* func: undecidable) {
                threadFunctionStackMap[mainFunction]->push_back(func);
            }

						int indexUndec = 0;
            bool newThreadFound = false;
            do {
                newThreadFound = false;
                for (std::map<Function*, SmallVector<Function*, 10>*>::iterator iter = threadFunctionStackMap.begin();
                        iter != threadFunctionStackMap.end(); ++iter) {
                    Function* initPoint = iter->first;
                    SmallVector<Function*, 10>* functionStack = iter->second;
                    std::vector<Function*> visitedFuncs;
                    while (!functionStack->empty()) {
                        Function* caller = functionStack->back();
                        functionStack->pop_back();
                        // Iterate over all functions called in this function
                        for (BasicBlock& BB : *caller) {
                            for (Instruction &I: BB) {
                                for (int i = 0; i < I.getNumOperands(); i++) {
                                    Value* operandValue = I.getOperand(i);
                                    // Track direct calls, and function
                                    // pointer loads
                                    std::vector<Function*> funcOperands;
                                    getFunctionOperandsIfAny(operandValue, funcOperands);
                                    // Check if any of the functions is
                                    // annotated as init-points
                                    for (Function* funcOp: funcOperands) {
                                        if (funcOp->getName() == "ngx_worker_process_cycle" || funcOp->getName() == "ngx_cache_manager_process_cycle" 
                                                || funcOp->getName() == "child_main" || funcOp->getName() == "uv__process_child_init") {
                                            newThreadFound = true;
                                            SmallVector<Function*, 10>* newFunctionStack = new SmallVector<Function*, 10>();
                                            newFunctionStack->push_back(funcOp);
                                            // everything that's in a global,
                                            // and has it's address taken
                                            for (Function* func: undecidable) {
                                                //errs() << "New func pushing: " << func->getName() << "\n";
                                                newFunctionStack->push_back(func);
                                            }

                                            threadFunctionStackMap.insert(iter, std::pair<Function*, SmallVector<Function*, 10>*>(funcOp, newFunctionStack));
                                        } else {
                                            if (funcOp->getName() == "llvm.dbg.declare") {
                                                continue;
                                            } else if (funcOp->getName().startswith("llvm.memcpy")) {
                                                initPointToFnMap[initPoint->getName()].insert("memcpy");
                                            } else if (funcOp->getName().startswith("llvm.memmove")) {
                                                initPointToFnMap[initPoint->getName()].insert("memmove");
                                            } else if (funcOp->getName().startswith("llvm.memset")) {
                                                initPointToFnMap[initPoint->getName()].insert("memset");
                                            } else {
                                                if (PrintCFG) {
                                                    errs() << initPoint->getName() << " : " << caller->getName() << " ... called " << funcOp->getName() << "\n";
                                                }
                                                if (std::find(allFuncSet.begin(), allFuncSet.end(), funcOp) == allFuncSet.end()) {
                                                    initPointToFnMap[initPoint->getName()].insert(funcOp->getName());
                                                }
                                            }
                                            if (std::find(visitedFuncs.begin(), visitedFuncs.end(), funcOp) == visitedFuncs.end()) {
                                                visitedFuncs.push_back(funcOp);
                                                functionStack->push_back(funcOp);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        // If it accesses any functions embedded in global
                        // variables, add them here too
                        if (embeddedFunctionMap[caller] != nullptr) {
                            for (Function* func: *(embeddedFunctionMap[caller])) {
                                if (PrintCFG) {
                                    errs() << initPoint->getName() << " : " << caller->getName() << " ... called " << func->getName() << "\n";
                                }
                                if (std::find(visitedFuncs.begin(), visitedFuncs.end(), func) == visitedFuncs.end()) {
                                    visitedFuncs.push_back(func);

                                    functionStack->push_back(func);
                                }
                            }
                        }
                    }
                }
            } while (newThreadFound);

            std::map<std::string, std::set<std::string>>::iterator it;
            for (it = initPointToFnMap.begin(); it != initPointToFnMap.end(); it++) {
                std::string initpoint = it->first;
                std::set<std::string> funcSet = it->second;
                for (std::string func: funcSet) {
                    errs() << initpoint << " : " << func << "\n";
                }
            }

            /*
            for(std::map<Function*, SmallVector<Function*, 10>*>::iterator iter = threadFunctionStackMap.begin(); iter != threadFunctionStackMap.end(); ++iter) {
                Function* initpoint =  iter->first;
                errs() << "For function initpoint: " << initpoint->getName() << "\n";
                SmallVector<Function*, 10>* functionStack = iter->second;
                for (Function* func: *functionStack) {
                    errs() << "Called function: " << func->getName() << "\n";
                }
            }
            */

//            M.dump();
                        /*
            std::map<Value*, std::set<Value*>>::iterator callGraphIt;
            for (callGraphIt = callGraph.begin(); callGraphIt != callGraph.end(); callGraphIt++) {
                Value* function = callGraphIt->first;
                std::set<Value*> calledFunctions = callGraphIt->second;
                errs() << "Caller function: \n";
                for (Value* calledFunction: calledFunctions) {
                    if (std::find(allFuncSet.begin(), allFuncSet.end(), calledFunction) != allFuncSet.end()) {
                        dumpCallGraphFunction(M, calledFunction);
                        errs() << "Callee function: \n";
                    }
                }
            }
            */
            return true;
		}

        /*
		bool runOnModule1(Module &M) {
            M.dump();
            setup();
			// Handle the ctors and dtors
			GlobalVariable *GVCtor = M.getGlobalVariable("llvm.global_ctors");
			if (GVCtor) {
                if (GVCtor->getInitializer() != nullptr) {
                    if (ConstantArray *CA = dyn_cast<ConstantArray>(GVCtor->getInitializer())) {
                        for (auto &V : CA->operands()) {
                            if (ConstantStruct *CS = dyn_cast<ConstantStruct>(V)) {
                                if (Function* F = dyn_cast<Function>(CS->getOperand(1))) {
                                    ctorsSet.insert(F);
                                }
                            }
                        }
                    }
                }
            }

            GlobalVariable *GVDtor = M.getGlobalVariable("llvm.global_dtors");
			if (GVDtor) {
                if (GVDtor->getInitializer() != nullptr) {
                    if (ConstantArray *CA = dyn_cast<ConstantArray>(GVDtor->getInitializer())) {
                        for (auto &V : CA->operands()) {
                            if (ConstantStruct *CS = dyn_cast<ConstantStruct>(V)) {
                                if (Function* F = dyn_cast<Function>(CS->getOperand(1))) {
                                    dtorsSet.insert(F);
                                }
                            }
                        }
                    }
                }
            }

            // Build list of all internal functions
            for (Module::iterator MIterator = M.begin(); MIterator != M.end(); MIterator++) {
                if (auto *F = dyn_cast<Function>(MIterator)) {
                    if (!F->isDeclaration()) {
                        allFuncSet.insert(F);
                    }
                }
            }
             
            Function* mainFunction = M.getFunction("main");
            threadFunctionStackMap[mainFunction] = new SmallVector<Function*, 10>();
            threadFunctionStackMap[mainFunction]->push_back(mainFunction);

            bool newThreadFound = false;
            do {
                for (std::map<Function*, SmallVector<Function*, 10>*>::iterator iter = threadFunctionStackMap.begin();
                        iter != threadFunctionStackMap.end(); ++iter) {
                    Function* initPoint = iter->first;
                    SmallVector<Function*, 10>* functionStack = iter->second;
                    newThreadFound = false;
                    while (!functionStack->empty()) {
                        Function* caller = functionStack->back();
                        functionStack->pop_back();
                        // Iterate over all functions called in this function
                        for (BasicBlock& BB : *caller) {
                            for (Instruction &I: BB) {
                                for (int i = 0; i < I.getNumOperands(); i++) {
                                    Value* operandValue = I.getOperand(i);
                                    // Track direct calls, and function
                                    // pointer loads
                                    std::vector<Function*> funcOperands;
                                    getFunctionOperandsIfAny(operandValue, funcOperands);
                                    // Check if any of the functions is
                                    // annotated as init-points
                                    for (Function* funcOp: funcOperands) {
                                        if (funcOp->getName() == "ngx_worker_process_cycle" || funcOp->getName() == "ngx_cache_manager_process_cycle") {
                                            newThreadFound = true;
                                            SmallVector<Function*, 10>* newFunctionStack = new SmallVector<Function*, 10>();
                                            newFunctionStack->push_back(funcOp);
                                            threadFunctionStackMap.insert(iter, std::pair<Function*, SmallVector<Function*, 10>*>(funcOp, newFunctionStack));
                                        } else {
                                            // Simple call
                                            functionStack->push_back(funcOp);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            } while (newThreadFound);

            for(std::map<Function*, SmallVector<Function*, 10>*>::iterator iter = threadFunctionStackMap.begin(); iter != threadFunctionStackMap.end(); ++iter) {
                Function* initpoint =  iter->first;
                //errs() << "For function initpoint: " << initpoint->getName() << "\n";
                SmallVector<Function*, 10>* functionStack = iter->second;
                for (Function* func: *functionStack) {
                    //errs() << "Called function: " << func->getName() << "\n";
                }
            }

//            M.dump();
            std::map<Value*, std::set<Value*>>::iterator callGraphIt;
            for (callGraphIt = callGraph.begin(); callGraphIt != callGraph.end(); callGraphIt++) {
                Value* function = callGraphIt->first;
                std::set<Value*> calledFunctions = callGraphIt->second;
                errs() << "Caller function: \n";
                for (Value* calledFunction: calledFunctions) {
                    if (std::find(allFuncSet.begin(), allFuncSet.end(), calledFunction) != allFuncSet.end()) {
                        dumpCallGraphFunction(M, calledFunction);
                        errs() << "Callee function: \n";
                    }
                }
            }
            return true;
		}
*/
	};
}  // end of anonymous namespace

char FunctionPointerAnalysisPass::ID = 0;

static RegisterPass<FunctionPointerAnalysisPass> X("function-analysis", "Function Analysis Pass",
        false /* Only looks at CFG */,
        false /* Analysis Pass */);

/*
ModulePass* llvm::createFunctionPointerAnalysisPass() { return new FunctionPointerAnalysisPass(); } 

INITIALIZE_PASS_BEGIN(FunctionPointerAnalysisPass, "function-ptr-analysis", "Function Pointer Analysis", false, true)
INITIALIZE_PASS_END(FunctionPointerAnalysisPass, "function-ptr-analysis", "Function Pointer Analysis", false, true)

*/

