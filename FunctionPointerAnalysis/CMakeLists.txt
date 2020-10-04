add_llvm_library(LLVMFunctionPointerAnalysis MODULE
    FunctionPointerAnalysis.cpp
    PLUGIN_TOOL
    opt
    )

