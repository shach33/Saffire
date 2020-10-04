#define DEBUG_TYPE "opCounterBackTrace"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/TypeFinder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/Allocator.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#define RECURSION_LEVEL 200
#define STEPS_LEVEL 5000
#define KEY 31
using namespace llvm;
using namespace std;
namespace {
	struct CountOpBackTrace : public FunctionPass {
 	std::map<std::string, int> opCounter;
 	static char ID;
	int argCount = 0;
	mutable BumpPtrAllocator ExpressionAllocator;
	int hop0=0,hop1=0, hop25=0, hop610=0,hopm10=0;
	int numCall = 0;
	int curHop =0;
 	CountOpBackTrace() : FunctionPass(ID) {}
	const std::vector<string> listOfLibs {"fwrite" };
  const std::vector<string> listOfLibs2 {"mmap64" , "mmap" , //"mprotect" , 
      "open",
      "open64", "access", "write", "execve" , "fstat", "read", "pread" , "read64",
      "clone", "pread64", "fopen", "fwrite" , "fread", "fseek" };
  const std::vector<string> listOfLibs3 {"mmap", "mmap64", "open64", "write","execve", "read", "pread64" };

  bool isInTestedLibs( StringRef name ){
    return std::find(listOfLibs.begin(), listOfLibs.end(), name) != listOfLibs.end();
  }

	int findxRefs(int rec, Function &func, int argNum, int isGEPRef, vector<int> indexVec){
		int num = 0;
		for (Value::use_iterator i = func.use_begin(), e = func.use_end(); i != e; ++i){
			if (Instruction *inst = dyn_cast<Instruction>(i->getUser())) {
			  errs() << "\n[" << rec << "]~~~~~~~~~\n" << func.getName() << "() is used in function: " << inst->getFunction()->getName() << "()\n";
				//errs() << "Inst: " << *inst << "\n";
				readxRefs(rec, inst, argNum, indexVec);
				num++;
			}
  	}
		return num;
	}
	void setHopStats(int i){
		switch(i){
			case 0: hop0++; break;
			case 1: hop1++; break;
			case 2 ... 5: hop25++; break;
			case 6 ... 10: hop610++; break;
			default: hopm10++; break;
		}
	}
	void readxRefs(int rec, Instruction *inst, int argNum, vector<int> indexVec){
		//errs() << "Are we here!\n";
		for (unsigned i=0; i<indexVec.size() ; i++){
			//errs()  << indexVec[i] << "-";
		}
		/*Function *F = ins->getFunction();
		BasicBlock* bb = ins->getParent();
		vector<Value*> valVect;
		valVect.push_back(dyn_cast<Value>(inst));
		int rt = findValue(valVect, 1, arg, *F, bbIter, iPrev)
		*/	
		if (CallInst * CI = dyn_cast<CallInst>(dyn_cast<Value>(inst))){
			errs() << "Call Inst to test\n" ;
			int n = getCallFunctionXRef(rec+1, CI, argNum, indexVec);
		}
	}

	/*void readxRefs(Instruction *inst, int argNum){
		errs() << "From function: " << inst->getFunction()->getName() << "\n";
		Value *v1 = dyn_cast<Value>(inst);
		if (CallInst * CI = dyn_cast<CallInst>(v1)){
			errs() << "Call Inst\n" ;
			int n = getCallFunction(1, CI, argNum);
		}
	}*/

	/*int getCallFunction(int rec, CallInst *ins, int argNum, vector<int> indexVec) {
		Function *F = ins->getFunction();
		Value *arg = ins->getArgOperand(argNum);
		BasicBlock* bb = ins->getParent();
		Function::iterator bbIter;
		BasicBlock::iterator iPrev;
		vector<Value*> valVect;
		for (Function::iterator bb1 = F->begin(), e = F->end(); bb1 != e; ++bb1) {
			if(&*bb1 == bb){
				bbIter = bb1;
			}
		}
		for (BasicBlock::iterator i1 = bbIter->begin(), e = bbIter->end(); i1 != e; ++i1) {
			if(&*i1 == ins){
				iPrev = i1;
			}
		}
		valVect.push_back(arg);
		errs() << "getCallFindVal\n";
		int rt = findValue(valVect, rec+1, arg, *F, bbIter, iPrev, indexVec);
		valVect.pop_back();

	}*/
	int getCallFunctionXRef(int rec, CallInst *ins, int argNum, vector<int> indexVec) {
		if (rec > RECURSION_LEVEL){
			return -1;
		}

		errs() <<"{" << rec << "}" <<  argNum << " xRef Call insn" << *ins << "(" << ins->getNumOperands() << ")\n";
		Function *F = ins->getFunction();
		Value *arg = ins->getArgOperand(argNum);
		errs() << "Args here: " << *arg << "\n";
		BasicBlock* bb = ins->getParent();
		Function::iterator bbIter;
		BasicBlock::iterator iPrev;
		vector<Value*> valVect;
		for (Function::iterator bb1 = F->begin(), e = F->end(); bb1 != e; ++bb1) {
			if(&*bb1 == bb){
				bbIter = bb1;
			}
		}
		for (BasicBlock::iterator i1 = bbIter->begin(), e = bbIter->end(); i1 != e; ++i1) {
			if(&*i1 == ins){
				iPrev = i1;
			}
		}

      	if(auto* cin = dyn_cast<ConstantInt>(arg)){     
        	errs() << " Const Arg: " << cin->getValue() << "\n";
				}                                               
        else if(auto *ci = dyn_cast<ConstantPointerNull>(arg)){
        	errs() <<   " [null]\n";	          
        }                                              
        else if(auto *ci = dyn_cast<ConstantDataArray>(arg)){
        	errs() <<  " Const Data Array\n";
        }                                               
        else { //if(auto *ptrTy = dyn_cast<PointerType>(arg)){
        	errs() << F->getName() <<  " [NAN]\n";           
        	Value *v = arg;                            
            if(isa<ConstantExpr>(v)){                   
            	errs() << "Constant Expr Found\n" ;
            }                                           
            std::vector<Value*> valVect;                
            valVect.push_back(v);                       
            vector<int> indexVec;                       
            errs() << "Finding value";                  
			int rt = findValue(valVect, rec, arg, *F, bbIter, iPrev, indexVec);
			valVect.pop_back();
			}
		return -1;
	}
	int getCallFunction(int rec, CallInst *ins, int argNum, vector<int> indexVec) {
		if (rec > RECURSION_LEVEL){
			return -1;
		}
		//errs() <<"{" << rec << "}" <<  argNum << " New Call insn" << *ins << "(" << ins->getNumOperands() << ")\n";
		Function *F = ins->getFunction();
		Value *arg = ins->getArgOperand(argNum);
		//errs() << "1111111...Args here: " << *arg << "\n";
		BasicBlock* bb = ins->getParent();
		Function::iterator bbIter;
		BasicBlock::iterator iPrev;
		vector<Value*> valVect;
		for (Function::iterator bb1 = F->begin(), e = F->end(); bb1 != e; ++bb1) {
			if(&*bb1 == bb){
				bbIter = bb1;
			}
		}
		for (BasicBlock::iterator i1 = bbIter->begin(), e = bbIter->end(); i1 != e; ++i1) {
			if(&*i1 == ins){
				iPrev = i1;
			}
		}
		valVect.push_back(arg);
		//errs() << "getCallFindVal\n";
		//int rt = findValue(valVect, rec+1, arg, *F, bbIter, iPrev, indexVec);
		valVect.pop_back();
	}
	int findValueForward(vector<Value*> valVect, int rec, Value *v, Function &F, Function::iterator &bb, BasicBlock::iterator &i){
		//errs() << "Find values forward" << *v << "\n";
		BasicBlock::iterator iNext = i;
		Function::iterator bbNext = bb;
		vector<int> indexVec;
		iNext++;
		int in = 0;
		while(1){
			//errs() << "Checking here" << *iNext << "\n";
			//BasicBlock::reverse_iterator bbEnd = bbNext->rbegin();
			BasicBlock::iterator bbEnd = bbNext->end();
			bbEnd--;
			//errs() << "BB End" << *(bbEnd) << "\n";

			//errs() << "1iNext : " << *iNext << "\n";	
			
			Value *v1 = dyn_cast<Value>(iNext);
			if(isa<StoreInst>(v1)){
				StoreInst *si = dyn_cast<StoreInst>(v1);
				if(si->getPointerOperand()==v){
					errs() << "Found Value being set\n" << *v1;
					//Find Value of this instruction backwards
					valVect.push_back(v1);
					errs() << rec << "\n";
					iNext--;
					int rt = findValue(valVect, rec+1, si->getValueOperand(), F, bb, iNext, indexVec);
					valVect.pop_back();
					break;
				}
			}
			auto fEnd = F.end();
			fEnd--;
			if(iNext == bbEnd){
				if(bbNext == fEnd){
					return -1;
				}
				//errs() << "Changing BBs\n";
				bbNext++;
				iNext = bbNext->begin();
			}
			else{
				iNext++;
			}
		}
		errs() << "Break\n";
		return 1;
	}
	int findValue(vector<Value*> valVect, int rec, Value *v, Function &F, Function::iterator &bb, BasicBlock::iterator &i, vector<int> indexVec ){
		//Read instruction arguments to check if arg(and indexes)  is used as destination.
		//Further check later in the part if the value is set later.
		if (rec > RECURSION_LEVEL){
			return -1;
		}
		errs() << "Finding Value: " << *v <<"\n";
		Instruction *ins = dyn_cast<Instruction>(i);
		//errs() << "1.2" << *v <<"\n";
		BasicBlock* bSrc = ins->getParent();
		//errs() << "1.3" << *v <<"\n";
		Function::iterator bbIter;
		for (Function::iterator bb1 = F.begin(), e = F.end(); bb1 != e; ++bb1) {
			if(&*bb1 == bSrc){
				bbIter = bb1;
			}
		}
			//if(v->getType()->isIntegerTy() ){ //Integer Type
			//errs() << "1" << *v <<"\n";
			//errs() << "2" <<  *i <<"\n";
			bool v_name = v->hasName();
			//errs() << "Var Name: " << v->getName() << "\n";
			//errs() << "Index Vec Size: " << indexVec.size() << "\n";
			BasicBlock::iterator iPrev = i;
			//Function::iterator bbPrev = bbIter;
			Function::iterator bbPrev = bb;
			int pIn = 0;
			//errs() << "Cur inst: (" << pIn <<  ") " <<  *i << "\n";
			//Backwards Slicing
			while(1){
				if (iPrev == bbPrev->begin()){
					if (bbPrev == F.begin()){
						int argNum = 0;
						for (Function::arg_iterator ai = F.arg_begin(), ae = F.arg_end(); ai!=ae ; ++ai){
							Value *vArg = ai;
							if ( v == vArg){
								errs() << "Found in Input Args\n";
								vector<int> v;
								curHop++;
								int numCallSites = findxRefs(rec, F, argNum, 0, v);
							}
							argNum++;
						}
						break;
					}
					bbPrev--;
					iPrev = bbPrev->end();
				}
				iPrev--;
				pIn++;
				Value *v1 = dyn_cast<Value>(iPrev);
				if(isa<StoreInst>(v1)){
					StoreInst *si = dyn_cast<StoreInst>(v1);
					if(si->getPointerOperand()==v){
						//errs() << "Store in Pointer\n";
						int rt = findValue( valVect, rec+1, si->getValueOperand(), F, bbPrev, iPrev, indexVec );
						return -1;
					}
					if(si->getValueOperand()==v){
						//errs() << "Store in Value\n";
						setHopStats(curHop);
						return 1;
					}
				}
				if(v->getType()->isPointerTy()){
					if(isa<CallInst>(v1)){
						//Read through all the arguments to ensure 'v' is not passed to it. 
						CallInst * CI = dyn_cast<CallInst>(v1);
						for(auto argCI = CI->arg_begin(); argCI != CI->arg_end(); ++argCI) {
							if(argCI->get() == v){
								errs() << "Passed to another function." << *v1 << " Exiting!\n";
								return NULL;
							}
						}
					}
				}
//				errs() <<  "v:: " << *v <<"\n";
//				errs() <<  "\nv1::" << *iPrev <<"\n";

				if (v == v1){
					//errs() << "Prev inst: " << *iPrev << "\n";
					//Found local reference variable.
					if ((iPrev->getOpcode() == Instruction::Add) ||
						(iPrev->getOpcode() == Instruction::Sub)  ||
						(iPrev->getOpcode() == Instruction::Mul)  ||
						(iPrev->getOpcode() == Instruction::UDiv) ||
						(iPrev->getOpcode() == Instruction::SDiv) ||
						(iPrev->getOpcode() == Instruction::SRem)){
							//errs() << "Arithmetic Inst\n" ;
							Value *o1 = iPrev->getOperand(0);
							Value *o2 = iPrev->getOperand(1);
							int n = arithFunction(valVect, 1, F, bbPrev, iPrev, v1, iPrev->getOpcode(), o1, o2, indexVec);
					}
					else if (isa<LoadInst>(v1)){
						//errs() << "Load Inst\n" ;
						Function::iterator bbH = bbPrev;
						int n = loadFunction(valVect, 1, F, bbPrev, iPrev, v1, indexVec);
						bbPrev = bbH;
					}
					else if (isa<StoreInst>(v1)){
						//errs() << "Store Insrt\n";
					}
					else if (isa<GetElementPtrInst>(v1)){
						//errs() << "GetElementPtr Inst\n" ;
						int n = getElemPtrFunction(valVect, 1, F, bbPrev, iPrev, v1, indexVec);
					}
					else if (isa<CallInst>(v1)){
						//errs() << "Call Inst\n" ;
						errs() << "Return From Call Inst\n" ;
						//int n = getCallFunction(1, dyn_cast<CallInst>(v1), 1, indexVec);
					}
					else if (isa<PHINode>(v1)){
						Value *o1 = iPrev->getOperand(0);
						Value *o2 = iPrev->getOperand(1);
						//errs() << "Phi Node\n";
						int n = phiNode(valVect, rec+1, F, bbPrev, iPrev, v1, o1, o2, indexVec);
					}
					else if (isa<SelectInst>(v1)){
						//errs() << "Select Inst\n" ;
						SelectInst *si = cast<SelectInst>(v1);
						Value *cond = si->getCondition();
						Value *trueVal = si->getTrueValue();
						Value *falseVal = si->getFalseValue();
						
						int n = selectFunction(valVect, rec+1, F, bbPrev, iPrev, v1,  cond, trueVal, falseVal, indexVec);
					}
					else if (isa<BitCastInst>(v1)){
						Value *o1 = iPrev->getOperand(0);
						int n = findValue(valVect, rec+1, o1, F, bbPrev, iPrev, indexVec);
					}
					else if (isa<SExtInst>(v1)){
						Value *o1 = iPrev->getOperand(0);
						int n = findValue(valVect, rec+1, o1, F, bbPrev, iPrev, indexVec);
					}
					iPrev = i;
					break;
				}
				else if(isa<GetElementPtrInst>(v1)){
					GetElementPtrInst *gepIns = dyn_cast<GetElementPtrInst>(v1);
					Instruction *inst = dyn_cast<Instruction>(v1);
					Value *opr = gepIns->getPointerOperand();
					if(v == opr){
						if (indexVec.size() != (gepIns->getNumOperands()-1))
							continue;
						unsigned int in = 1, matchFound =  1;
						for (unsigned IE = gepIns->getNumOperands(); in != IE; ++in) {
       						Value *V = gepIns->getOperand(in);
							if (const ConstantInt *CI = dyn_cast<ConstantInt>(V)){
								if(CI->getZExtValue() != indexVec[in-1]){
									matchFound = 0;
									break;
								}
							}
						}
						if(matchFound){
							errs() << "GEP Indexes matched\n";
							//The current Value is used later in the IR, and set by some value.
							//This needs forward slicing to find when set.
							int rt = findValueForward(valVect, rec+1, v1, F, bbPrev, iPrev);
						}

		//if (oprType->isIntegerTy()){
						int argNum = 0;
						for (Function::arg_iterator ai = F.arg_begin(), ae = F.arg_end(); ai!=ae ; ++ai){
							Value *vArg = ai;
							if ( opr == vArg){
								//errs() << "[GEP] Found in Input Args\n";
								// Need to send indices as well.
								int numCallSites = findxRefs(rec, F, argNum, 1, indexVec);
							}
							argNum++;
						}
					}
				}
			}
	/*	}
		else{
			errs() << "Non Integer Arg\n";
		}*/
		return 1;
	}
	int loadFunction( vector<Value*> valVect, int rec, Function &F, Function::iterator &bb, BasicBlock::iterator &iPrev, Value *ins, vector<int> indexVec){
		errs() << "new load insn" << *ins << "\n";
		LoadInst * CI = dyn_cast<LoadInst>(ins);
		Value *src = CI->getPointerOperand();
		Type *typeSrc = CI->getPointerOperandType();
		Function::iterator bbPrev = bb;

		// Add checks for volatile and alignment.
		//Backwards Slicing

		while(1){
			//errs() << *(bbPrev->begin()) << "\n";
			if(iPrev == bbPrev->begin()){
				if(bbPrev == F.begin()){
					break;
				}
				bbPrev--;
				iPrev = bbPrev->end();
			}
			iPrev--;
			Value *v1 = dyn_cast<Value>(iPrev);
			if(isa<StoreInst>(v1)){
				StoreInst *si = dyn_cast<StoreInst>(v1);
				if(si->getPointerOperand()==src){
					errs() << "[Load] Store in Pointer" << *si << "\n" ;
					if (dyn_cast<ConstantInt>(si->getValueOperand())){
						errs() << "Constant Found: " << dyn_cast<ConstantInt>(si->getValueOperand())->getZExtValue();
						return dyn_cast<ConstantInt>(si->getValueOperand())->getZExtValue();
					}
					else if(dyn_cast<ConstantPointerNull>(si->getValueOperand())){
						errs() << "NULL Value\n";
						return NULL;
					}
					else{
						int rt = findValue( valVect, rec+1, si->getValueOperand(), F, bbPrev, iPrev, indexVec);
					}
					return -1;
				}
				if(si->getValueOperand()==src){
					errs() << "[Load] Store in Value\n";
				}

			}
			if (src == v1){
				errs() << "[Load" << rec << "] Prev inst: " << *iPrev << "\n";
				//Found local reference variable.
				if (iPrev->getOpcode() == Instruction::SRem){
					errs() << "[Load"<< rec << "] Remainder Inst\n" ;
				}
				else if (isa<LoadInst>(v1)){
					errs() << "[Load" << rec << "] Load Inst\n" ;
					int n = loadFunction(valVect, rec+1, F, bbPrev, iPrev, v1, indexVec);
				}
				else if (isa<GetElementPtrInst>(v1)){
					errs() << "[Load" << rec << "] GetElementPtr Inst\n" ;
					int n = getElemPtrFunction(valVect, rec+1, F, bbPrev, iPrev, v1, indexVec);
				}
				else if (isa<BitCastInst>(v1)){
					errs() << "[Load" << rec << "] BitCast Inst\n";
//					int n = FindValue( 
				}
				errs() << "Ret[" << rec << "]\n";
				setHopStats(curHop);
				return 1;
				break;
			}
		}
		return 1;
	}
	int storeFunction(vector<Value*> valVect, int rec, Function::iterator &bb, BasicBlock::iterator &iPrev, Value *Ins){
	}
	int arithFunction(vector<Value*> valVect, int rec, Function &F, Function::iterator &bb, BasicBlock::iterator &iPrev, Value *ins, unsigned int opcode, Value *o1, Value *o2, vector<int> indexVec){
		errs() << "new arith insn" << *ins << "\n";
  		//Testing Arg1
		if(auto* cin = dyn_cast<ConstantInt>(o1)){
    		errs() << "Opcode:" << opcode << " Const Arg: " << cin->getValue() << "\n";
		}else if(auto *ci = dyn_cast<ConstantPointerNull>(o2)){
			errs() << "Opcode:"  << opcode <<  " [null]\n";
		}
		else { //if(auto *ptrTy = dyn_cast<PointerType>(arg)){
			errs() << "Opcode:"  << opcode <<  " [NAN]\n";
			if(std::find(valVect.begin(), valVect.end(), o1) != valVect.end()) {
 				return -1;
			}
			valVect.push_back(o1);
			int rt = findValue(	valVect, rec+1, o1, F, bb, iPrev, indexVec );
			valVect.pop_back();
		}

		//Testing Arg2
		if(auto* cin = dyn_cast<ConstantInt>(o2)){
    		errs() << "Opcode:"  << opcode << " Const Arg: " << cin->getValue() << "\n";
		}else if(auto *ci = dyn_cast<ConstantPointerNull>(o2)){
			errs() << "Opcode:"  << opcode <<  " [null]\n";
		}
		else { //if(auto *ptrTy = dyn_cast<PointerType>(arg)){
			errs() << "Opcode:"  << opcode <<  " [NAN]\n";
			if(std::find(valVect.begin(), valVect.end(), o2) != valVect.end()) {
 				return -1;
			}
			valVect.push_back(o2);
			int rt = findValue(valVect, rec+1, o2, F, bb, iPrev, indexVec);
			valVect.pop_back();
		}

		setHopStats(curHop);
		return 1;

	}
	int phiNode(vector<Value*> valVect, int rec, Function &F, Function::iterator &bb, BasicBlock::iterator &iPrev, Value *ins, Value *o1, Value *o2, vector<int> indexVec){
		PHINode *phi = cast<PHINode>(ins);
		errs() << "Phi Inst(" << phi->getNumIncomingValues() << ")\n" ;
		int n = phi->getNumIncomingValues(), index =0;
		while(index < n){
			Value *v = phi->getIncomingValue(index);
			if(auto* cin = dyn_cast<ConstantInt>(v)){
				errs() << "[Phi] Const Arg\n" ;
			}
			else{
				BasicBlock* bSrc = phi->getIncomingBlock(index);
				Function::iterator bbIter;
				for (Function::iterator bb1 = F.begin(), e = F.end(); bb1 != e; ++bb1) {
					if(&*bb1 == bSrc){
						bbIter = bb1;
					}
				}
				//Exception handler when BB not found
				BasicBlock::iterator iPrevH = bbIter->end();
				iPrevH--;
				if(std::find(valVect.begin(), valVect.end(), v) != valVect.end()) {
 					return -1;
				}
				valVect.push_back(v);
				int rt = findValue(valVect, rec+1, v, F, bbIter, iPrevH, indexVec);
				valVect.pop_back();
				if (rt == -1){
					return -1;
				}
			}
			index++;
		}
		errs() << "Phi Node insn" << *ins << "\n";
	}
	int getElemPtrFindValue(int rec, Function::iterator &bb, BasicBlock::iterator &iPrev, Value *ins){
	}
	int getElemPtrFunction(vector<Value*> valVect, int rec, Function &F, Function::iterator &bb, BasicBlock::iterator &iPrev, Value *ins, vector<int> indexVec){
		GetElementPtrInst *gepIns = dyn_cast<GetElementPtrInst>(ins);
		Instruction *inst = dyn_cast<Instruction>(ins);
		errs() << "new getelementptr insn" << *ins <<  "(" << gepIns->getNumIndices() << "\n";
		errs() << "has all zero indices:: " << gepIns->hasAllZeroIndices() << "\n";
		Value *opr = gepIns->getPointerOperand();
		Type *oprType = gepIns->getPointerOperandType();
		Function::iterator bbPrev = bb;

		unsigned in = 1;
/*		for (unsigned IE = gepIns->getNumOperands(); in != IE; ++in) {
       		Value *V = gepIns->getOperand(in);
			if (const ConstantInt *CI = dyn_cast<ConstantInt>(V)){
				indexVec.push_back(CI->getZExtValue());
				errs() << "GEP Index:: " << *CI << "\n";
			}
		}*/
/*		while(1){
			if(iPrev == bbPrev->begin()){
				if(bbPrev == F.begin()){
					break;
				}
				bbPrev--;
				iPrev = bbPrev->end();
			}
			iPrev--;
			Value *v1 = dyn_cast<Value>(iPrev);
			if(isa<StoreInst>(v1)){
				StoreInst *si = dyn_cast<StoreInst>(v1);
				if(si->getPointerOperand()==opr){
					errs() << "[Load] Store in Pointer\n";
					int rt = findValue( valVect, rec+1, si->getValueOperand(), F, bbPrev, iPrev, indexVec);
					return -1;
				}
				if(si->getValueOperand()==opr){
					errs() << "[Load] Store in Value\n";
				}

			}
			if (opr == v1){
				errs() << "[GEP" << rec << "] Prev inst: " << *iPrev << "\n";
				errs() << *v1 <<"\n";
				int rt = findValue(valVect, rec+1, opr, F, bbPrev, iPrev, indexVec);
				//Found local reference variable.
				break;
			}
		}
*/		//if (oprType->isIntegerTy()){
        valVect.push_back(opr);                                    
        int rt = findValue(valVect, rec+1, opr, F, bb, iPrev, indexVec);
        valVect.pop_back();
		
/*			int argNum = 0;
			for (Function::arg_iterator ai = F.arg_begin(), ae = F.arg_end(); ai!=ae ; ++ai){
				Value *vArg = ai;
				if ( opr == vArg){
					errs() << "[GEP] Found in Input Args\n";
					// Need to send indices as well.
					int numCallSites = findxRefs(rec, F, argNum, 1, indexVec);
				}
				argNum++;
			}
*/		//}

	}
	int selectFunction(vector<Value*> valVect, int rec, Function &F, Function::iterator &bb, BasicBlock::iterator &iPrev, Value *ins, Value *cond, Value *trueVal, Value *falseVal, vector<int> indexVec){
		errs() << "new select insn" << *ins << "\n";
		errs() << "Checking Condition\n";
		
		if( cond->getType()->isIntegerTy() ){
			if(std::find(valVect.begin(), valVect.end(), cond) != valVect.end()) {
 				return -1;
			}
			valVect.push_back(cond);
			int rt = findValue(valVect, rec+1, cond, F, bb, iPrev, indexVec);
			valVect.pop_back();
		}
		errs() << "Checking True Condition\n";
		if( trueVal->getType()->isIntegerTy()){
			if(isa<ConstantInt>(trueVal)){
				errs() << "Constant Found: " << *trueVal << "\n"; 
			}
			else {
				if(std::find(valVect.begin(), valVect.end(), trueVal) != valVect.end()) {
 					return -1;
				}
			
				valVect.push_back(trueVal);
				int rt = findValue(valVect, rec+1, trueVal, F, bb, iPrev, indexVec);
				valVect.pop_back();
			}
		}
		errs() << "Checking False Condition\n";
		if( falseVal->getType()->isIntegerTy()){
			if(isa<ConstantInt>(falseVal)){
				errs() << "Constant Found: " << *falseVal << "\n"; 
			}
			else{
				if(std::find(valVect.begin(), valVect.end(), falseVal) != valVect.end()) {
 					return -1;
				}
			
				valVect.push_back(falseVal);
				int rt = findValue(valVect, rec+1, falseVal, F, bb, iPrev, indexVec);
				valVect.pop_back();
			}
		}
	}
	virtual bool runOnFunction(Function &F) {
 		//	errs() << "\nFunction " << F.getName() << "::";
		const DataLayout DL = F.getParent()->getDataLayout();

		for (Function::arg_iterator ai = F.arg_begin(), ae = F.arg_end(); ai!=ae ; ++ai){
			argCount++;
			Type *argType =  ai->getType();
			Type::TypeID argTypeID =  argType->getTypeID();
			unsigned allocSize = DL.getTypeAllocSize(argType);
			//errs() << argCount << "(" << allocSize << "-" << argTypeID << ") " ;
			/////errs() << argCount << "(" << allocSize  << ") " ;
		}
		//errs() << "NumFunctions(" << argCount << "): " << '\n'  ;
 		for(BasicBlock &BB : F){
			int num_pred=0, num_succ = 0;
			BasicBlock *B = &BB;
			//errs() << "\nBasic block has " << BB.size() << " instructions. ";
			for (BasicBlock *Pred: predecessors(B)){
				num_pred++;
			}
			for (BasicBlock *Pred: successors(B)){
				num_succ++;
			}
			//errs() << "Num Preds: " << num_pred << " NumSuccs: " << num_succ ;
		}
		//int numCall = 0;
		for (auto bb = F.begin(), e = F.end(); bb != e; ++bb) {
 			for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i) {
 				if(opCounter.find(i->getOpcodeName()) == opCounter.end()) {
 					opCounter[i->getOpcodeName()] = 1;
 				} else {
	 				opCounter[i->getOpcodeName()] += 1;
 				}
				//Instruction *I = i;
				BasicBlock* bbThis = i->getParent();
				if (CallInst * CI = dyn_cast<CallInst>(i)) {

					Type* t = IntegerType::get(i->getModule()->getContext(), 32);
					BasicBlock* bbThis = i->getParent();
					Instruction* p=&( bbThis->back());
					AllocaInst* ptr_input_addr = new AllocaInst(t,NULL, "inputadd", p);
					ptr_input_addr->setAlignment(4);
					LoadInst* int32_16 = new LoadInst(ptr_input_addr, "", false, p);

					int inOper = 0 ,in1 = 0;
					if(CI->getCalledFunction()!=NULL){
						Function* fn = CI->getCalledFunction();
						StringRef fn_name = fn->getName();
            if (fn_name == "fwrite"){
							errs() << "\nCalled" << fn_name << " NumArgs: " << i->getNumOperands() << "\n";
						}
						if (isInTestedLibs(fn_name)){
							numCall++;
							errs() <<"\n"<< numCall << "-- " << *i <<  "\n";
							errs() << "Args::" << i->getNumOperands() << " \n" ;
							curHop=1;	
							for(auto arg = CI->arg_begin(); arg != CI->arg_end(); ++arg) {
  								if(auto* cin = dyn_cast<ConstantInt>(arg)){
    								errs() << fn_name << " Const Arg: " << cin->getValue() << "\n";
								}
								else if(auto *ci = dyn_cast<ConstantPointerNull>(arg)){
									errs() << fn_name <<  " [null]\n";
								}
								else if(auto *ci = dyn_cast<ConstantDataArray>(arg)){
									errs() << fn_name <<  " Const Data Array\n";
								}
								else if(auto *ci = dyn_cast<ConstantExpr>(arg)){
									errs() << fn_name <<  " Const Expression\n";
								}
								else { //if(auto *ptrTy = dyn_cast<PointerType>(arg)){
									errs() << fn_name <<  " [Unknown]\n";
									Value *v = *arg;
									//if(v->getType()->isIntegerTy()){ // || v->getType()->isPointerTy()){ //Integer or Pointer Type
									if(v->getType()->isIntegerTy() || v->getType()->isPointerTy()){ //Integer or Pointer Type
										if(isa<ConstantExpr>(v)){
											errs() << "Constant Expr Found\n" ;
											continue;
										}
										std::vector<Value*> valVect;
										valVect.push_back(v);
										vector<int> indexVec;
										/*if(v->getType()->isIntegerTy() ){ //Integer Type
												for (BasicBlock::iterator ih = bbThis->begin(), eh = bbThis->end(); ih != eh; ++ih) {
												Instruction* iih = &*ih;
												errs() << *iih << "\n";
											}
											//Decryption - Division
											//TODOs - Encrypt
											LLVMContext &context = F.getContext();
											//IRBuilder<NoFolder> builder(&Instruction);
											//Value *lefArg = v;// ConstantInt::get(Type::getInt32Ty(context), 4);
											Value *rightArg = ConstantInt::get(Type::getInt64Ty(context), KEY);
											BinaryOperator* ins_add = BinaryOperator::Create(Instruction::SDiv, v, rightArg, "insadd", dyn_cast<Instruction>(i));
											//auto* op   = dyn_cast<BinaryOperator>(i);
											//IRBuilder<> builder(op);
											//Value *Result = builder.CreateAdd(lefArg, rightArg);
											errs() << "-----------------------------\n" ;
											for (BasicBlock::iterator ih = bbThis->begin(), eh = bbThis->end(); ih != eh; ++ih) {
												Instruction* iih = &*ih;
												errs() << *iih << "\n";
											}	//
										}*/
										errs() << "Finding value";
										int rt = findValue(valVect, 1, v, F, bb, i, indexVec);
										valVect.pop_back();
										/*if(v->getType()->isIntegerTy() ){ //Integer Type
											//StringRef
											bool v_name = v->hasName();
											errs() << "Var Name: " << v->getName() << "\n";
	
											BasicBlock::iterator iPrev = i;
											Function::iterator bbPrev = bb;
											int pIn = 0;
											errs() << "Cur inst: (" << pIn <<  ") " <<  *i << "\n";
											//Backwards Slicing
											while(1){
												if(iPrev == bbPrev->begin()){
													if (bbPrev == F.begin()){
														errs() << "Reached Beginning of Function\n";
														for (Function::arg_iterator ai = F.arg_begin(), ae = F.arg_end(); ai!=ae ; ++ai){
																Value *vArg = ai;
																if ( v == vArg){
																errs() << "Found in Input Args\n";
															}
														}
														break;
													}
													bbPrev--;
													iPrev = bbPrev->end();
												}
												iPrev--;
												pIn++;
												Value *v1 = dyn_cast<Value>(iPrev);
												if (v == v1){
													errs() << "Prev inst: " << *iPrev << "\n";
													//Found local reference variable.
													if ((iPrev->getOpcode() == Instruction::Add) ||
													(iPrev->getOpcode() == Instruction::Sub)  ||
													(iPrev->getOpcode() == Instruction::Mul)  ||
													(iPrev->getOpcode() == Instruction::UDiv) ||
													(iPrev->getOpcode() == Instruction::SDiv) ||
													(iPrev->getOpcode() == Instruction::SRem)){
														errs() << "Arithmetic Inst\n" ;
														Value *o1 = iPrev->getOperand(0);
														Value *o2 = iPrev->getOperand(1);
														int n = arithFunction(1,F, bbPrev, iPrev, v1, iPrev->getOpcode(), o1, o2);
													}
													else if (isa<LoadInst>(v1)){
														errs() << "Load Inst\n" ;
														Function::iterator bbH = bbPrev;
														int n = loadFunction(1, F, bbPrev, iPrev, v1);
														bbPrev = bbH;
													}
													else if (isa<GetElementPtrInst>(v1)){
														errs() << "GetElementPtr Inst\n" ;
														int n = getElemPtrFunction(1, bbPrev, iPrev, v1);
													}
													else if (isa<CallInst>(v1)){
														errs() << "Call Inst\n" ;
														int n = getCallFunction(1, bbPrev, iPrev, v1);
													}
													else if (isa<PHINode>(v1)){
														Value *o1 = iPrev->getOperand(0);
														Value *o2 = iPrev->getOperand(1);
														errs() << "Phi Inst\n" ;
														int n = phiNode(1,F, bbPrev, iPrev, v1, iPrev->getOpcode(), o1, o2);
													}
													else if (isa<SelectInst>(v1)){
														errs() << "Select Inst\n" ;
														SelectInst *si = cast<SelectInst>(v1);
														Value *cond = si->getCondition();
														Value *trueVal = si->getTrueValue();
														Value *falseVal = si->getFalseValue();
														int n = selectFunction(1, bbPrev, iPrev, v1,  cond, trueVal, falseVal);
													}
													iPrev = i;
													break;
												}//
											}
										}*/
						
									}
									else{
										errs() << "Pointer Argument\n";
									}
								}
							in1++;
						}
					}
					// Indirect calls through function Ptrs
					else{
						//errs() << "Function Ptr: " << CI->getCalledValue() << "\n" ;
						Value* v = CI->getCalledValue();
						Function *f = dyn_cast<Function>(v->stripPointerCasts());
					}
				}
			}
		}
	}
 		opCounter.clear();
 		return false;
}
};
}
char CountOpBackTrace::ID = 0;
static RegisterPass<CountOpBackTrace> X("opCounterBackTrace", "Find Args of functions By BackTrace");
