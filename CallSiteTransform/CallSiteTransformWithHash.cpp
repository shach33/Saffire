#define DEBUG_TYPE "callsiteTransformWithHash"
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
using namespace llvm;
using namespace std;
namespace {
	struct CallSiteTransformWithHash : public ModulePass {
	IRBuilder<> Builder();
 	std::map<std::string, int> opCounter;
 	static char ID;
	int argCount = 0;
	mutable BumpPtrAllocator ExpressionAllocator;
	int numCall = 0;
	int anchorInd = 1;
 	CallSiteTransformWithHash() : ModulePass(ID) {}
	void readxRefs(int rec, Instruction *inst, int argNum, vector<int> indexVec){
	}
	Function *hook;
	int globIndex = 1;
	bool getPageSizeAdded = false;	
	int indexForLibCall = 0;
	const std::vector<string> listOfLibs {"mmap64" , "mmap" , //"mprotect" , 
			"open", 
			"open64", "access", "write", "execve" , "fstat", "read", "pread" , "read64", 
			"clone", "pread64", "fopen", "fwrite" , "fread", "fseek" };
	
//	const std::vector<string> listOfLibs {"mmap", "mmap64", "open64", "write","execve", "read", "pread64" };
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

						//int inOper = 0 ,in1 = 0; //New Comment
            if(CI->getCalledFunction()!=NULL){
							Function* fn = CI->getCalledFunction();
							StringRef fn_name = fn->getName();
							if (isInTestedLibs(fn_name)){;// ==  "fwrite"){
								errs() <<  "Called from: "  << (*it).getName() <<"\n";
								
								
								FunctionType *ft = fn->getFunctionType();
								//set Return Type
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
									if(auto* cin = dyn_cast<ConstantInt>(argCI)){
										errs() << "Inserting to knownArgs ["  << inn+1 <<"]\n";
										knownArgs.push_back(llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), inn+1));
										knownArgs.push_back(llvm::ConstantInt::get(argCI->get()->getType() , cin->getValue()));
										
									}
									//else if(auto* cin = dyn_cast<ConstantPointerNull>(argCI)){
									else if(dyn_cast<ConstantPointerNull>(argCI)){
										errs() << "[Null]Inserting to knownArgs ["  << inn+1 <<"]\n";
										errs() << "Type:: " << argCI->get()->getType() << "\n" ;
										knownArgs.push_back(llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), inn+1));
										
										//knownArgs.push_back(llvm::ConstantPointerNull::get(PointerType::get(argCI->get()->getType(),NULL)));//, NULL));
										knownArgs.push_back(Constant::getNullValue(argCI->get()->getType()) );
								  }
									else if(auto* cin = dyn_cast<ConstantExpr>(argCI)){
										errs() << "[Null][Expr]Inserting to knownArgs ["  << inn+1 <<"]\n";
										errs() << "Type:: " << argCI->get()->getType() << "\n" ;
										knownConstArgs.push_back(llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), inn+1));
										knownConstArgs.push_back(cin);
									}
									else{
										errs() << "Inserting to newArgs ["  << inn+1 <<"]\n";
										errs() << "IntWidth: " <<  argCI->get()->getType()->getTypeID() << "\n";
										custFuncArgsType.push_back( IntegerType::get(M.getContext(), 64));
										custFuncArgsType.push_back(argCI->get()->getType());
										newArgs.push_back(llvm::ConstantInt::get(IntegerType::get(M.getContext(), 64), inn+1));
										newArgs.push_back(CI->getArgOperand(inn));
										//Create Shadow Var Here  of 64 bit Int type
										GlobalVariable* anchor = new GlobalVariable(
											/*Module=*/     M, 
											/*Type*/        i64_type,
							        /*isConstant=*/ false,
							        /*Linkage=*/    GlobalValue::PrivateLinkage,
							        /*Initializer=*/0, // has initializer, specified below
							        /*Name=*/       "cst_anchor", NULL,
   										                GlobalVariable::GeneralDynamicTLSModel,
   										0, false );
										anchor->setAlignment(4);
										
										anchor->setInitializer(llvm::ConstantInt::get(i64_type, -1, true) );
										globArr.push_back(anchor);

										//Create Hash(CI->getArgOperand(inn)) --> Save to its location 
										SmallVector<Value*, 1> hashArgs;
										BitCastInst *bitCastInst;
										Function *funcStrlen;
										SmallVector<Value*, 1> strlenArgs;
										Instruction *strlenCall;
										Instruction *castIntInst;
										if(CI->getArgOperand(inn)->getType()->isPointerTy()){	

											if(CI->getArgOperand(inn)->getType() != i8p_type){
												bitCastInst = new BitCastInst(CI->getArgOperand(inn), i8p_type, "bitCast");
												i->getParent()->getInstList().insert(i,bitCastInst);
												hashArgs.push_back(bitCastInst);
											}
											else{
												hashArgs.push_back(CI->getArgOperand(inn) );
											}
										
											errs() << "Size:: " << dl->getTypeAllocSize(((CI->getArgOperand(inn))->getType())->getPointerElementType());	
											// If Size == 1 -> Basic Char/Void Type - Need String Length
											if(dl->getTypeAllocSize(((CI->getArgOperand(inn))->getType())->getPointerElementType()) ==1){
												//Get String Length 
												funcStrlen = cast<Function>(M.getFunction("strlen"));
												strlenArgs.push_back(CI->getArgOperand(inn));
												strlenCall = CallInst::Create(funcStrlen, strlenArgs);
												hashArgs.push_back(strlenCall);
												i->getParent()->getInstList().insert(i, strlenCall);
											}
											//Else: Structure type - Get Size of Structure Object
											else{
												hashArgs.push_back(llvm::ConstantInt::get(i64_type, dl->getTypeAllocSize(((CI->getArgOperand(inn))->getType())->getPointerElementType()) , true) );
											}
										}
										else{	
											//Input to Hash is 32 bit, need to truncate 64bit to 32bit
											if(CI->getArgOperand(inn)->getType()->isIntegerTy(32)){	
												hashArgs.push_back(CI->getArgOperand(inn));
											}
											if(CI->getArgOperand(inn)->getType()->isIntegerTy(64)){	
												castIntInst = CastInst::Create(Instruction::Trunc,CI->getArgOperand(inn), i32_type, "t64" );
												i->getParent()->getInstList().insert(i, castIntInst);
												hashArgs.push_back(castIntInst);
											}
										}
										Instruction *hashCallInst; 
										if(CI->getArgOperand(inn)->getType()->isPointerTy() ){
											hashCallInst = CallInst::Create(hashPtrFunc, hashArgs);
										}
										else{
											hashCallInst = CallInst::Create(hashFunc, hashArgs);
										}
										i->getParent()->getInstList().insert(i, hashCallInst);
										StoreInst *storeI = new StoreInst(hashCallInst, anchor);
										i->getParent()->getInstList().insert(i, storeI);
									}
									inn++;
									argFn++;
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
								
									IRBuilder<> builder(entry);
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
									//*/

									/*
									Value* gepIndexList[1] ={ConstantInt::get(i32_type, 1)};
									//Value *nullValue = ConstantPointerNull::get(cast<PointerType>(globArr[globIndex]->getType()));
									Value *nullValue = ConstantPointerNull::get(globArr[globIndex]->getType());

									//GetElementPtrInst *gep = builder.CreateGEP(globArr[globIndex]->getType(), nullptr,
									Value *gep = builder.CreateGEP(0, nullValue,
										gepIndexList, "gepSize");
									LoadInst *loadGEP = builder.CreateLoad(gep, "ldGep");

									Value *typPtr = builder.CreatePtrToInt(loadGEP, i32_type, "sizeStruct");
									//errs() << "Size of Struct:  " << globArr[globIndex]->getType()->getTypeAllocSize() << "\n"; 
									
									*/
									argsFromThisFn++;
									if((globIndex+1)==globArr.size()){
										BranchInst *end = builder.CreateCondBr(xEqualsY, finalT, finalF );
									}
									else{
									  entry =  BasicBlock::Create(M.getContext(), "verify", customFunc);
									  BranchInst *end = builder.CreateCondBr(xEqualsY, entry, finalF );
									}
									argsFromThisFn++;
									
									globIndex++;	
								}									
								//Insert Call to Original function in custom Func
								Constant *syscallConstant = M.getFunction(fn_name);//getOrInsertFunction(fn_name  , fn->getFunctionType());
								Function* libcallToInsert = cast<Function>(M.getFunction(fn_name));
								//Function::arg_iterator argsFromFn = customFunc->arg_begin();
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
									//Allocate Pkey
/*									SmallVector<Value*, 16> pkeyAllocArgs;
									llvm::Constant *sysCallNumAlloc = llvm::ConstantInt::get(i64_type, 330, true);
									llvm::Constant *sysCallFlagsAlloc = llvm::ConstantInt::get(i32_type, 0, true);
									llvm::Constant *sysCallAccessAlloc = llvm::ConstantInt::get(i32_type,0, true);
									pkeyAllocArgs.push_back(sysCallNumAlloc);
									pkeyAllocArgs.push_back(sysCallFlagsAlloc);
									pkeyAllocArgs.push_back(sysCallAccessAlloc);
									
									Function *allocPkey = NULL;
						
									//SysCall(330,0,0)	
									Instruction *pkeyAlloc = CallInst::Create( syscallFunc, pkeyAllocArgs);
									i->getParent()->getInstList().insert(i, pkeyAlloc);
									
									IRBuilder<> builderHere(i->getParent());
									builderHere.SetInsertPoint(i->getParent(), i)	;
									
									//%14 = trunc i64 %13 to i32
									Value *truncAlloc = builderHere.CreateTrunc(pkeyAlloc, i32_type);// "allocKey");

									//%shlBy1 = shl i64 %77, 1 
									Value *shlBy1 = builderHere.CreateShl(pkeyAlloc, llvm::ConstantInt::get(i64_type, 1, true), "shlBy1", false, false);
									//%andLarge = and i64 %shlBy1, 4294967294
									Value *andLarge = builderHere.CreateAnd(shlBy1, llvm::ConstantInt::get(i64_type, 4294967294, true), "andLarge");
									//%shlInst2 = shl i64 2, %andLarge
									Value *shlInst2 = builderHere.CreateShl(llvm::ConstantInt::get(i64_type, 2, true), andLarge, "shlInst2", false, false);
									//%truncToPerm = trunc i64 %shlInst2 to i32 
									Value *truncToAsm = builderHere.CreateTrunc(shlInst2, i32_type);// "truncToAsm");

									//Asm Call 
									SmallVector<Value*, 16>  asmArgs;
									std::vector<Type*> asmArgTypes;
									asmArgTypes.push_back(i32_type);
									asmArgTypes.push_back(i32_type);
									asmArgTypes.push_back(i32_type);
	   							llvm::FunctionType *asmFty = llvm::FunctionType::get(Type::getVoidTy(M.getContext()), asmArgTypes, false);
									llvm::Constant *asmArg23 = llvm::ConstantInt::get(i32_type, 0, true);
									asmArgs.push_back(truncToAsm);
									asmArgs.push_back(asmArg23);
									asmArgs.push_back(asmArg23);

                  //call void asm sideeffect ".byte 0x0f,0x01,0xef", "{ax},{cx},{dx},~{dirflag},~{fpsr},~{flags}"(i32 %truncToAsm, i32 0, i32 0)
									InlineAsm *IA = InlineAsm::get(asmFty, ".byte 0x0f,0x01,0xef\0A\09",
																		"{ax},{cx},{dx},~{dirflag},~{fpsr},~{flags}", 
																		true, false);//,
									Instruction *asmPkey = CallInst::Create(IA, asmArgs);//, i->getParent());
									i->getParent()->getInstList().insert(i, asmPkey);
									
*/
									//Asm Call 
/*									SmallVector<Value*, 16>  asmArgs1111;
									std::vector<Type*> asmArgTypes1111;
									//asmArgTypes11.push_back(i64_type);
									//asmArgTypes1.push_back(i64_type);
	   							llvm::FunctionType *asmFty1111 = llvm::FunctionType::get(Type::getVoidTy(M.getContext()), asmArgTypes1111, false);
									llvm::Constant *asmArg2311111 = llvm::ConstantInt::get(i64_type, 4660, true);
									//asmArgs11.push_back(asmArg23111);
									//asmArgs1.push_back(andLarge);
									
									InlineAsm *IA1111 = InlineAsm::get(asmFty1111, "xor %rax, %rax",
									//InlineAsm *IA1 = InlineAsm::get(asmFty1, "mov %eax, %ecx",
									//									"{ax}",	
																		"",	
																		true, false);//,
									Instruction *asmPkey1111 = CallInst::Create(IA1111, asmArgs1111);//, i->getParent());
									i->getParent()->getInstList().insert(i, asmPkey1111);
*/
//////////////////////////////////////


////////////////////////////////////////
									//Asm Call 
/*									SmallVector<Value*, 16>  asmArgs2;
									std::vector<Type*> asmArgTypes2;
									asmArgTypes2.push_back(i64_type);
									//asmArgTypes1.push_back(i64_type);
	   							llvm::FunctionType *asmFty2 = llvm::FunctionType::get(Type::getVoidTy(M.getContext()), asmArgTypes2, false);
									llvm::Constant *asmArg2 = llvm::ConstantInt::get(i64_type, 2, true);
									asmArgs2.push_back(asmArg2);
									//asmArgs1.push_back(andLarge);
									
									InlineAsm *IA2 = InlineAsm::get(asmFty2, "push %rax",
									//InlineAsm *IA1 = InlineAsm::get(asmFty1, "mov %eax, %ecx",
																		"{rax}",	
																		true, false);//,
									Instruction *asmPkey2 = CallInst::Create(IA2, asmArgs2);//, i->getParent());
									i->getParent()->getInstList().insert(i, asmPkey2);
*/									
///////////////////////////////////////////////////
	/*								SmallVector<Value*, 16>  asmArgs111;
									std::vector<Type*> asmArgTypes111;
									//asmArgTypes11.push_back(i64_type);
									//asmArgTypes1.push_back(i64_type);
	   							llvm::FunctionType *asmFty111 = llvm::FunctionType::get(Type::getVoidTy(M.getContext()), asmArgTypes111, false);
									llvm::Constant *asmArg231111 = llvm::ConstantInt::get(i64_type, 4660, true);
									//asmArgs11.push_back(asmArg23111);
									//asmArgs1.push_back(andLarge);
									
									InlineAsm *IA111 = InlineAsm::get(asmFty111, "pop %gs",
									//InlineAsm *IA1 = InlineAsm::get(asmFty1, "mov %eax, %ecx",
									//									"{ax}",	
																		"",	
																		true, false);//,
									Instruction *asmPkey111 = CallInst::Create(IA111, asmArgs111);//, i->getParent());
									i->getParent()->getInstList().insert(i, asmPkey111);
*/
////////////////////////////////////////////////////
/*									SmallVector<Value*, 16>  asmArgs5;
									std::vector<Type*> asmArgTypes5;
									//asmArgTypes5.push_back(i64_type);
									//asmArgTypes1.push_back(i64_type);
	   							llvm::FunctionType *asmFty5 = llvm::FunctionType::get(Type::getVoidTy(M.getContext()), asmArgTypes5, false);
									llvm::Constant *asmArg5 = llvm::ConstantInt::get(i64_type, 2, true);
									//asmArgs5.push_back(asmArg5);
									//asmArgs1.push_back(andLarge);
									
								  InlineAsm *IA5 = InlineAsm::get(asmFty5, "movq %fs:0xfffffffffffffffc, %rax",
								  //InlineAsm *IA5 = InlineAsm::get(asmFty5, "movq %r14, %rax",
									//InlineAsm *IA1 = InlineAsm::get(asmFty1, "mov %eax, %ecx",
									//									"{rax}",	
																		"",	
																		true, false);//,
									Instruction *asmPkey5 = CallInst::Create(IA5, asmArgs5);//, i->getParent());
									i->getParent()->getInstList().insert(i, asmPkey5);
*/
////////////////////////////////////////////////////
/*									SmallVector<Value*, 16>  asmArgs7;
									std::vector<Type*> asmArgTypes7;
									asmArgTypes7.push_back(i64_type);
									//asmArgTypes1.push_back(i64_type);
	   							llvm::FunctionType *asmFty7 = llvm::FunctionType::get(Type::getVoidTy(M.getContext()), asmArgTypes7, false);
									llvm::Constant *asmArg7 = llvm::ConstantInt::get(i64_type, 2, true);
									asmArgs7.push_back(asmArg7);
									//asmArgs1.push_back(andLarge);
									
								  InlineAsm *IA7 = InlineAsm::get(asmFty7, "mov %rbx, %gs:0xfffffffffffffff8",
									//InlineAsm *IA1 = InlineAsm::get(asmFty1, "mov %eax, %ecx",
								  								"{rbx}",	
									//									"",	
																		true, false);//,
									Instruction *asmPkey7 = CallInst::Create(IA7, asmArgs7);//, i->getParent());
									i->getParent()->getInstList().insert(i, asmPkey7);
*/
////////////////////////////////////////////////////
////////////////////////////////////////////////////
/*									SmallVector<Value*, 16>  asmArgs6;
									std::vector<Type*> asmArgTypes6;
									//asmArgTypes6.push_back(i64_type);
									//asmArgTypes6.push_back(i64_type);
	   							llvm::FunctionType *asmFty6 = llvm::FunctionType::get(Type::getVoidTy(M.getContext()), asmArgTypes6, false);
									llvm::Constant *asmArg6 = llvm::ConstantInt::get(i64_type, 3, true);
									//asmArgs6.push_back(asmArg6);
									//asmArgs6.push_back(andLarge);
									
									//InlineAsm *IA6 = InlineAsm::get(asmFty6, "movq %fs:0xfffffffffffffffc, %rax",
									InlineAsm *IA6 = InlineAsm::get(asmFty6, "movq %gs, %rax",
									//InlineAsm *IA1 = InlineAsm::get(asmFty1, "mov %eax, %ecx",
									//									"{ax}",	
																		"",	
																		true, false);//,
									Instruction *asmPkey6 = CallInst::Create(IA6, asmArgs6);//, i->getParent());
								//	i->getParent()->getInstList().insert(i, asmPkey6);
*/
///////////////////////////////////////////////////////
									SmallVector<Value*, 16>  asmArgs1;
									std::vector<Type*> asmArgTypes1;
									//asmArgTypes1.push_back(i64_type);
									//asmArgTypes1.push_back(i64_type);
	   							llvm::FunctionType *asmFty1 = llvm::FunctionType::get(Type::getVoidTy(M.getContext()), asmArgTypes1, false);
									llvm::Constant *asmArg231 = llvm::ConstantInt::get(i64_type, 40960, true);
									llvm::Constant *asmArg2311 = llvm::ConstantInt::get(i32_type, 77, true);
									//asmArgs1.push_back(asmArg231);
									//asmArgs1.push_back(andLarge);

                  //call void asm sideeffect ".byte 0x0f,0x01,0xef", "{ax},{cx},{dx},~{dirflag},~{fpsr},~{flags}"(i32 %truncToAsm, i32 0, i32 0)
									//InlineAsm *IA1 = InlineAsm::get(asmFty1, ".byte 0x48,0x01,0xef\0A\09",
	/*								char str[25];
									//strcpy(str, "mov %eax, %es:0x");
									//strcpy(str, "mov %gs:0x2, %eax");
									strcpy(str, "mov %rax, %gs:0x0");
									//anchorInd++;
									char anchorNum[5];
									//sprintf(anchorNum,"%d", anchorInd);
									//InlineAsm *IA1 = InlineAsm::get(asmFty1, strcat(str,anchorNum),
									InlineAsm *IA1 = InlineAsm::get(asmFty1, str,
									//InlineAsm *IA1 = InlineAsm::get(asmFty1, "mov %eax, %ecx",
								//										"{ax}",	
																		"",	
																		true, false);//,
									Instruction *asmPkey1 = CallInst::Create(IA1, asmArgs1);//, i->getParent());
									i->getParent()->getInstList().insert(i, asmPkey1);
*/
/*									//%78 = load i8*, i8** @cst_anchor
									LoadInst *loadGv = builderHere.CreateLoad(globArr[globIndex]);
									//%shlBy32 = shl i64 %77, 32
									Value *shlBy32 = builderHere.CreateShl(pkeyAlloc, llvm::ConstantInt::get(i64_type, 32, true), "shlBy32", false, false);
									//%ashr = shl nuw i64 %shlBy32, 32
									Value *ashr = builderHere.CreateShl(shlBy32, llvm::ConstantInt::get(i64_type, 32, true), "ashr", true);
	
									SmallVector<Value*, 16> pkeyMProtectArgs;
									llvm::Constant *sysCallMProtect1 = llvm::ConstantInt::get(i64_type, 329, true);
									llvm::Constant *sysCallMProtect4 = llvm::ConstantInt::get(i64_type, 3, true); //READ|WRITE
									pkeyMProtectArgs.push_back(sysCallMProtect1);
									pkeyMProtectArgs.push_back(loadGv);
									pkeyMProtectArgs.push_back(gpSextIns);
									pkeyMProtectArgs.push_back(sysCallMProtect4);
									pkeyMProtectArgs.push_back(ashr);
									
									//%79 = call i64 (i64, ...) @syscall(i64 329, i8* %78, i64 %gpsExt, i64 3, i64 %ashr)
									Instruction *pkeyMProtect = CallInst::Create( syscallFunc, pkeyMProtectArgs);
									i->getParent()->getInstList().insert(i, pkeyMProtect);

									//%truncToMProtect = trunc i64 %79 to i32
									Instruction *truncMProtect = new TruncInst(pkeyMProtect, i32_type);//, "truncToMProtect");
									i->getParent()->getInstList().insert(i, truncMProtect);
									
									//%82 = call i64 (i64, ...) @syscall(i64 331, i64 %ashr)
									SmallVector<Value*, 16> pkeyFreeArgs;
									llvm::Constant *sysCallFree1 = llvm::ConstantInt::get(i64_type, 331, true);
									pkeyFreeArgs.push_back(sysCallFree1);
									pkeyFreeArgs.push_back(ashr);
									Instruction *pkeyFree = CallInst::Create( syscallFunc, pkeyFreeArgs);
									auto nextI = i;
									nextI++;
									i->getParent()->getInstList().insert(nextI, pkeyFree);
	
									*/
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
		}
		for(int n = 0; n < toBeDeleted.size() ; n++){
			toBeDeleted[n]->eraseFromParent();
		}
	//	M.print(errs(), nullptr);
		errs() << toBeDeleted.size() ;
		errs() << " \n~~~~~~~~~~~~~~~New Func List~~~~~~~~~~~~~~~\n";
	//	/*
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
char CallSiteTransformWithHash::ID = 0;
static RegisterPass<CallSiteTransformWithHash> X("callsiteTransformWithHash","Transform Sy Sites with hash", true, true);
/*
static llvm::RegisterStandardPasses Y(
    llvm::PassManagerBuilder::EP_FullLinkTimeOptimizationLast,
    [](const llvm::PassManagerBuilder &Builder,
       llvm::legacy::PassManagerBase &PM) { PM.add(new CallSiteTransformWithHash()); });
*/
