#if( NOT LLVM_REQUIRES_RTTI )                                                   
#endif()                                                                        
                                                                                
#if(WIN32 OR CYGWIN)                                                            
#  set(LLVM_LINK_COMPONENTS Core Support)                                       
#endif()                                                                        
                                                                                
add_llvm_library( LLVMCallSiteTransformWithHash MODULE                          
  CallSiteTransformWithHash.cpp                                                 
                                                                                
  PLUGIN_TOOL                                                                   
  opt                                                                           
  )                                                                             
