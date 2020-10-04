#define DEBUG_TYPE "ArgumentExtractionPass"
#include "llvm/Pass.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/TypeFinder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/Allocator.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Verifier.h"
//#include "llvm/IR/InlineAsm.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <map>
#define RECURSION_LEVEL 6
#define STEPS_LEVEL 30
#define KEY 31
#define GLOB(NAME,X) NAME##X
#define MODE 1 /* 1- Test 2- All 3-Special Cases*/
using namespace llvm;
using namespace std;
namespace {
	struct ArgumentExtractionPass : public ModulePass {
	IRBuilder<> Builder();
 	std::map<std::string, int> opCounter;
 	static char ID;
	int argCount = 0;
	mutable BumpPtrAllocator ExpressionAllocator;
	int numCall = 0;
	int anchorInd = 1;
 	ArgumentExtractionPass() : ModulePass(ID) {}
	void readxRefs(int rec, Instruction *inst, int argNum, vector<int> indexVec){}
	Function *hook;
	int globIndex = 1;
	bool getPageSizeAdded = false;	
	int indexForLibCall = 0;
	const std::vector<string> listOfLibs {"fwrite" };
	const std::vector<string> listOfLibs2 {"mmap64" , "mmap" , //"mprotect" , 
			"open", 
			"open64", "access", "write", "execve" , "fstat", "read", "pread" , "read64", 
			"clone", "pread64", "fopen", "fwrite" , "fread", "fseek" };
	const std::vector<string> listOfLibs3 {"mmap", "mmap64", "open64", "write","execve", "read", "pread64" };

	bool isInTestedLibs( StringRef name ){
		return std::find(listOfLibs.begin(), listOfLibs.end(), name) != listOfLibs.end();
	}
	virtual bool runOnModule(Module &M) {
		errs() << "Did it begin? \n" ;
		Module::FunctionListType &functions = M.getFunctionList();
		vector<Function*> funcsToAdd;
		int i = 1;
		int customFuncIndex = 1;
		Function *customFunc = NULL;
		Function *hashFunc = NULL;
		Function *hashPtrFunc = NULL;
		std::vector<BasicBlock::iterator> toBeDeleted;
		Module::FunctionListType::iterator itBegin = functions.begin();
		Function *syscallFunc = NULL;
		Function *exitFunc = NULL;
		Function *getPageSizeFunc = NULL;
		bool foundSysCallFn=false;
		bool foundGetPageSizeFn=false;
		bool foundExitFn=false;
		llvm::DataLayout* dl = new llvm::DataLayout(&M); 
		for(Module::FunctionListType::iterator it = functions.begin(), it_end=functions.end(); it!=it_end; ++it){
			i++;
		}
		errs() << "Num Functions: " << i << "\n";
		
		for(Module::FunctionListType::iterator it = functions.begin(), it_end=functions.end(); it!=it_end; ++it){
			if((*it).getName()=="syscall"){
				foundSysCallFn=true;
				syscallFunc = &*it;
			}
			if((*it).getName()=="getpagesize"){
				foundGetPageSizeFn=true;
				getPageSizeFunc= &*it;
			}
			if((*it).getName()=="exit"){
				foundExitFn=true;
				exitFunc = &*it;
			}
		}
		i=1;
		//Types To be used
		llvm::Type *i8_type = llvm::IntegerType::getInt8Ty(M.getContext());
		llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(M.getContext());
		llvm::Type *i64_type = llvm::IntegerType::getInt64Ty(M.getContext());		
		llvm::Type *void_type = llvm::IntegerType::getVoidTy(M.getContext());		
		llvm::Type *i8p_type = llvm::PointerType::getUnqual(i8_type);

		//Declare Syscall with VarArgs
		if(!foundSysCallFn){
			std::vector<llvm::Type *> putsArgs;
			putsArgs.push_back(i64_type);	
			llvm::ArrayRef<llvm::Type*>  argsRef(putsArgs);
			FunctionType *syscallType = FunctionType::get(i64_type, argsRef,  true); 
									
			syscallFunc = Function::Create(syscallType, Function::ExternalLinkage, "syscall" , &M);
		}							
		//Exit Function
		if(!exitFunc){
			std::vector<llvm::Type *> putsArgsExit;
			putsArgsExit.push_back(i32_type);	
			llvm::ArrayRef<llvm::Type*>  argsRefExit(putsArgsExit);
			FunctionType *exitType = FunctionType::get( void_type, argsRefExit,  false); 
								
			exitFunc = Function::Create(exitType, Function::ExternalLinkage, "exit" , &M);
		}
		//GetPageSize Function
		if(!foundGetPageSizeFn){
			llvm::ArrayRef<llvm::Type*>  argsRefgetPageSize();
			FunctionType *getPageSizeType = FunctionType::get( i32_type,  false); 
								
			getPageSizeFunc = Function::Create(getPageSizeType, Function::ExternalLinkage, "getpagesize" , &M);
		}

		for(Module::FunctionListType::iterator it = functions.begin(), it_end=functions.end(); it!=it_end; ++it){

			Function &F = *it;
			if((F.getName()).find("custom")!=std::string::npos){
				continue;
			}
			//errs() << (*it).getName() << "\n";
 			getPageSizeAdded = false;
			Value *gpSextIns; 
			//Insert Hashing Function
			Type *hashRetType = i64_type;
			std::vector<Type*> hashArgsType;
			hashArgsType.push_back(i32_type);
			FunctionType* hashFuncType = FunctionType::get(hashRetType, hashArgsType, false);
			
			std::vector<Type*> hashPtrArgsType;
			hashPtrArgsType.push_back(i8p_type);
			hashPtrArgsType.push_back(i64_type);
			FunctionType* hashPtrFuncType = FunctionType::get(hashRetType, hashPtrArgsType, false);

			std::string hashFuncName = std::string("hashFunc");
			Constant *hashC = M.getOrInsertFunction(hashFuncName  , hashFuncType);
			hashFunc = cast<Function>(hashC);
			
			std::string hashPtrFuncName = std::string("hashPtrFunc");
			Constant *hashPC = M.getOrInsertFunction(hashPtrFuncName  , hashPtrFuncType);
			hashPtrFunc = cast<Function>(hashPC);
								
			for (auto bb = F.begin(), e = F.end(); bb != e; ++bb) {
				for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i) {
					//BasicBlock* bbThis = i->getParent();
					if (CallInst * CI = dyn_cast<CallInst>(i)) {

						Type* t = IntegerType::get(i->getModule()->getContext(), 32);
						BasicBlock* bbThis = i->getParent();
						Instruction* p=&( bbThis->back());

            if(CI->getCalledFunction()!=NULL){
							Function* fn = CI->getCalledFunction();
							StringRef fn_name = fn->getName();
							if (isInTestedLibs(fn_name)){
								errs() <<  "Called from: "  << (*it).getName() <<"\n";
								
								FunctionType *ft = fn->getFunctionType();
								//set Return Type of Custom Function
								Type *typ = ft->getReturnType();
								CallSite CS(CI);
								
								std::vector<Type*> custFuncArgsType;

								//Replacing current callSite
								SmallVector<Value*, 16> newArgs;
								SmallVector<Value*, 16> knownArgs;
								SmallVector<Constant*, 16> knownConstArgs;
							
								SmallVector<GlobalVariable*, 16> globArr;	
								//auto arg=fn->arg_begin();
								int inn =0;
								auto argFn = fn->arg_begin();
								for(auto argCI = CI->arg_begin(); argCI != CI->arg_end(); ++argCI) {
									//llvm::ConstantInt::get(t, in+1);
									//Constant Value
									if(auto* cin = dyn_cast<ConstantInt>(argCI)){
										errs() << "Inserting to knownArgs ["  << inn+1 <<"]\n";
										knownArgs.push_back(llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), inn+1));
										knownArgs.push_back(llvm::ConstantInt::get(argCI->get()->getType() , cin->getValue()));
										
									}
									//NULL Value
									//else if(auto* cin = dyn_cast<ConstantPointerNull>(argCI)){
									else if(dyn_cast<ConstantPointerNull>(argCI)){
										errs() << "[Null]Inserting to knownArgs ["  << inn+1 <<"]\n";
										errs() << "Type:: " << argCI->get()->getType() << "\n" ;
										knownArgs.push_back(llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), inn+1));
										knownArgs.push_back(Constant::getNullValue(argCI->get()->getType()) );
								  }
									//Constant Expression
									else if(auto* cin = dyn_cast<ConstantExpr>(argCI)){
										errs() << "[Null][Expr]Inserting to knownArgs ["  << inn+1 <<"]\n";
										errs() << "Type:: " << argCI->get()->getType() << "\n" ;
										knownConstArgs.push_back(llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), inn+1));
										knownConstArgs.push_back(cin);
									}
									//Unknown - Need to trace backwards
									else{
										errs() << argCI << "\n";	
										//auto in = findPrevUseInstruction(argCI);	
										//Insert Arg to custom function
										errs() << "Inserting to newArgs ["  << inn+1 <<"]\n";
										errs() << "IntWidth: " <<  argCI->get()->getType()->getTypeID() << "\n";
										custFuncArgsType.push_back( IntegerType::get(M.getContext(), 64));
										custFuncArgsType.push_back(argCI->get()->getType());
										newArgs.push_back(llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), inn+1));
										newArgs.push_back(CI->getArgOperand(inn));
										if(CI->getArgOperand(inn)->getType()->isPointerTy()){	

											if(CI->getArgOperand(inn)->getType() != i8p_type){
											}
											else{
											}
										
											errs() << "Size:: " << dl->getTypeAllocSize(((CI->getArgOperand(inn))->getType())->getPointerElementType());	
											// If Size == 1 -> Basic Char/Void Type - Need String Length
											if(dl->getTypeAllocSize(((CI->getArgOperand(inn))->getType())->getPointerElementType()) ==1){
												//Get String Length 
											}
											//Else: Structure type - Get Size of Structure Object
											else{
											}
										}
										else{	
											//Input to Hash is 32 bit, need to truncate 64bit to 32bit
											if(CI->getArgOperand(inn)->getType()->isIntegerTy(32)){	
											}
											if(CI->getArgOperand(inn)->getType()->isIntegerTy(64)){	
											}
										}
								 }
								}
								
								//Create New Function
								FunctionType* custFuncType = FunctionType::get(typ, custFuncArgsType, fn->isVarArg());

								customFunc = Function::Create(custFuncType, fn->getLinkage());

								customFunc->copyAttributesFrom(*&fn);
								std::string newFuncName = std::string("custom") + std::string(fn_name) + std::to_string(customFuncIndex++);
								Constant *C = M.getOrInsertFunction(newFuncName  , custFuncType);
								customFunc = cast<Function>(C);
								customFunc->setCallingConv(CallingConv::C);

								//Create Basic Blocks
								int globArrSize = globArr.size();
								int globIndex=0;
								auto argsFromThisFn =customFunc->arg_begin();
								argsFromThisFn++;
								BasicBlock *entry;
							
								if(newArgs.size()){	
									entry = BasicBlock::Create(M.getContext(), "verify", customFunc);
								}
								globIndex=0;
								BasicBlock* finalT = BasicBlock::Create(M.getContext(), "finalT", customFunc); 
								BasicBlock* finalF = BasicBlock::Create(M.getContext(), "finalF", customFunc);
								errs() << "***" << globArr.size() << "***\n";
								while(globIndex < globArr.size()){
								
/*									IRBuilder<> builder(entry);
									builder.SetInsertPoint(entry);
									
									//Load from the location 
									LoadInst *loadGv = builder.CreateLoad(globArr[globIndex]);
									
									//Create Arguments
									SmallVector<Value*, 16> hashArgs;
									Value *hashCallInst;
									Value *castIntInst;
									Value *bitCastInst;
									errs() << "Really Here\n";
									if(argsFromThisFn->getType()->isPointerTy()){
										//Value *IntToPtrInst = builder.CreatePtrToInt(argsFromThisFn, i64_type, "inpInt");
										//hashArgs.push_back(IntToPtrInst);
										if(argsFromThisFn->getType() != i8p_type){
											bitCastInst = builder.CreateBitCast(argsFromThisFn, i8p_type, "int8Ptr");
											hashArgs.push_back(bitCastInst);
										}
										else{
											hashArgs.push_back(argsFromThisFn);
										}

										if(dl->getTypeAllocSize((argsFromThisFn->getType())->getPointerElementType())==1){			
											//Get String Length 
											Function *funcStrlen = cast<Function>(M.getFunction("strlen"));
											SmallVector<Value*, 1> strlenArgs;
											strlenArgs.push_back(argsFromThisFn);
											Value *strlenCall = builder.CreateCall(funcStrlen, strlenArgs, Twine("len"));
											hashArgs.push_back(strlenCall);
										}
										else{
												hashArgs.push_back(llvm::ConstantInt::get(i64_type, dl->getTypeAllocSize((argsFromThisFn->getType())->getPointerElementType()) , true) );
										}
										hashCallInst = builder.CreateCall(hashPtrFunc, hashArgs, Twine("hash"));
									}
									else{
											//Input to Hash is 32 bit, need to truncate 64bit to 32bit
											if(argsFromThisFn->getType()->isIntegerTy(32)){	
												hashArgs.push_back(argsFromThisFn);
											}
											if(argsFromThisFn->getType()->isIntegerTy(64)){	
												castIntInst = builder.CreateCast(Instruction::Trunc,argsFromThisFn, i32_type, "t64" );
												hashArgs.push_back(castIntInst);
											}
										hashCallInst = builder.CreateCall(hashFunc, hashArgs, Twine("hash"));
									}
									
									Value *savedH = builder.CreatePtrToInt(loadGv, i64_type, "savedH");
									Value* xEqualsY = builder.CreateICmpEQ(hashCallInst, savedH, "tmp");

									argsFromThisFn++;
									if((globIndex+1)==globArr.size()){
										BranchInst *end = builder.CreateCondBr(xEqualsY, finalT, finalF );
									}
									else{
									  entry =  BasicBlock::Create(M.getContext(), "verify", customFunc);
									  BranchInst *end = builder.CreateCondBr(xEqualsY, entry, finalF );
									}
									argsFromThisFn++;
	*/								
									globIndex++;	
								}									
								//Insert Call to Original function in custom Func
								Constant *syscallConstant = M.getFunction(fn_name);//getOrInsertFunction(fn_name  , fn->getFunctionType());
								Function* libcallToInsert = cast<Function>(M.getFunction(fn_name));
								auto argsFromFn = newArgs.begin();
								auto argsFromConst = knownArgs.begin();
								auto argsFromConstExpr = knownConstArgs.begin();
	
								SmallVector<Value*, 8> newArgsForLibCall;
								int in=1;
								inn = 1;
								argsFromThisFn =customFunc->arg_begin();

								//while(argsFromFn!=newArgs.end() && argsFromConst!=knownArgs.end() && argsFromConstExpr!=knownConstArgs.end()){
								while(argsFromFn!=newArgs.end() || argsFromConst!=knownArgs.end() || argsFromConstExpr!=knownConstArgs.end()){
									if((argsFromFn!=newArgs.end()) && *argsFromFn == llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), in)){
									//		errs() << "[" << inn+1 <<  "] newArgs Writing for: " << *argsFromThisFn << "\n";
										argsFromFn++;				
										argsFromThisFn++;						
										errs() << "[Fn" << inn+1 <<  "] newArgs for real libcall: " << *argsFromThisFn << "\n";
										newArgsForLibCall.push_back(argsFromThisFn);//customFunc->getArgOperand(in++));
										argsFromFn++;
										argsFromThisFn++;
									}
									//else if(*argsFromFn == llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), in)){
											
									//}
									else if((argsFromConstExpr!=knownConstArgs.end() ) && (*argsFromConstExpr == llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), in))){
										argsFromConstExpr++;
										errs() << "[Expr" << inn+1 <<  "] newArgs for real libcall: " << *argsFromConstExpr << "\n";
										newArgsForLibCall.push_back(*argsFromConstExpr);
										argsFromConstExpr++;
									}
									else if ((argsFromConst!=knownArgs.end() ) && (*argsFromConst == llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64),in))){
										argsFromConst++;
										errs() << "[Const" << inn+1 <<  "] newArgs for real libcall: " << *argsFromConst << "\n";
										newArgsForLibCall.push_back(*argsFromConst);
										argsFromConst++;
									}
									in++;
								}

								//BasicBlock* block = BasicBlock::Create(M.getContext(), "final", customFunc); 
								//BasicBlock* ret = BasicBlock::Create(M.getContext(), "cTrue", customFunc); 
								//BasicBlock* cFalse = BasicBlock::Create(M.getContext(), "cFalse", customFunc); 
								//finalT = BasicBlock::Create(M.getContext(), "finalT", customFunc); 
								//finalF = BasicBlock::Create(M.getContext(), "finalF", customFunc); 
									
								IRBuilder<> builder(finalT);
	
								Value* callSCInst = builder.CreateCall(libcallToInsert,newArgsForLibCall, Twine("tmp2"));
								builder.CreateRet(callSCInst);
								
								IRBuilder<> builderF(finalF);
								Value *retNull = nullptr;
								//builderF.CreateRet(ConstantPointerNull::get(PointerType::get( typ, 0)));
								
								if( PointerType *pt = dyn_cast<PointerType>(typ)){
									builderF.CreateRet(ConstantPointerNull::get(cast<PointerType>(typ)));
								}
								else{
									builderF.CreateRet(llvm::ConstantInt::get(typ, -1, true));
								}
								//builderF.CreateRet(ConstantPointerNull::get());
								//builderF.CreateRet(PointerType::get( typ, 0));
								//builderF.CreateRet(LLVMConstPointerNull(typ));


								//Verify Newly created function
								verifyFunction(*customFunc);
								numCall++;
							
								//Insert MPK TESTS	
							
								//Insert At the Beginning of Function
								if(!getPageSizeAdded){
									Instruction *gps = CallInst::Create( getPageSizeFunc);
									(F.begin())->getInstList().insert(F.begin()->begin(), gps);
	
									IRBuilder<> builderBegin(F.begin()->begin()->getParent());
									auto instPos = F.begin()->begin();
									instPos++;
									builderBegin.SetInsertPoint(F.begin()->begin()->getParent(), instPos )	;
									gpSextIns = builderBegin.CreateSExt(gps, i64_type, "gpsExt");
									getPageSizeAdded = true;	
								}

								globIndex=0;
								while(globIndex < globArr.size()){
									globIndex++;
								}
								Instruction *newCI = CallInst::Create(customFunc, newArgs);
								i->getParent()->getInstList().insert(i, newCI);
								if (!CI->use_empty())
		  							CI->replaceAllUsesWith(newCI);
							
								toBeDeleted.push_back(i);
							}
						}
					}
 	      }
      }
		}//*/
		for(int n = 0; n < toBeDeleted.size() ; n++){
			toBeDeleted[n]->eraseFromParent();
		}
	//	M.print(errs(), nullptr);
		errs() << toBeDeleted.size() ;
		errs() << " \n~~~~~~~~~~~~~~~New Func List~~~~~~~~~~~~~~~\n";
		for(Module::FunctionListType::iterator it = functions.begin(), it_end=functions.end(); it!=it_end; ++it){
			Function &F = *it;
			int numBBs = 0;
			for (auto bb = F.begin(), e = F.end(); bb != e; ++bb) {
				numBBs++;
			}
			//if(F.getName()=="decode_file"){
			//if((F.getName()).find("custom")!=std::string::npos){//=="decode_file"){
			if((F.getName()=="maini1") || ((F.getName()).find("custom")!=std::string::npos)){//=="decode_file"){
				errs() << "\n~~~~~~~~~~\n";
				F.print(errs(), nullptr);
			}

		} // */
 		return false;
  }
	};
}

char ArgumentExtractionPass::ID = 0;
static RegisterPass<ArgumentExtractionPass> X("argExtract","Extract Arguments from syscalls", true, true);
/*
static llvm::RegisterStandardPasses Y(
    llvm::PassManagerBuilder::EP_FullLinkTimeOptimizationLast,
    [](const llvm::PassManagerBuilder &Builder,
       llvm::legacy::PassManagerBase &PM) { PM.add(new CallSiteTransformWithHash()); });
*/
