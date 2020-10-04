"""
Extract the syscalls for each process

"""
import logging
import os
import sys
#sys.path.insert(0, '/home/hamed/container-debloating')

import graph
import syscall as sycall
import re
import optparse

processInitLibMap = {}
processInitSyscallMap = {}

def isValidOpts(opts):
    """
    Check if the required options are sane to be accepted
        - Check if the provided files exist
        - Check if two sections (additional data) exist
        - Read all target libraries to be debloated from the provided list
    :param opts:
    :return:
    """
    if not options.cfginput or not options.targetcfg:
        parser.error("Both options -c and -f should be provided.")
        return False

    return True

def setLogPath(logPath):
    """
    Set the property of the logger: path, config, and format
    :param logPath:
    :return:
    """
    if os.path.exists(logPath):
        os.remove(logPath)

    rootLogger = logging.getLogger("coverage")
    rootLogger.setLevel(logging.DEBUG)

#    ch = logging.StreamHandler(sys.stdout)
    consoleHandler = logging.StreamHandler()
    rootLogger.addHandler(consoleHandler)
    return rootLogger
#    rootLogger.addHandler(ch)

def processSeparatedCalls(procsepfile, callgraphfile, sep):
    f = open(procsepfile)
    for line in f:
        words = line.split(":")
        initPoint = words[0].strip()
        calledFunc = words[1].strip()
        if initPoint not in processInitLibMap:
            processInitLibMap[initPoint] = []
        processInitLibMap[initPoint].append(calledFunc)

    # Create the graph
    rootLogger = setLogPath("graph.log")
    myGraph = graph.Graph(rootLogger)
    myGraph.createGraphFromInput(callgraphfile, sep)

    syscallList = list()

    i = 0
    while i < 400:
        syscallList.append("syscall(" + str(i) + ")")
        syscallList.append("syscall(" + str(i) + ")")
        syscallList.append("syscall ( " + str(i) + " )")
        syscallList.append("syscall( " + str(i) + " )")
        i += 1

    for initPoint in processInitLibMap:
        for func in processInitLibMap[initPoint]:
            leaves = myGraph.getLeavesFromStartNode(func, syscallList, list())
            for leaf in leaves:
                leaf = "".join(leaf.split())
                words = re.split('[()]', leaf)
                syscallno = words[1]
                if initPoint not in processInitSyscallMap:
                    processInitSyscallMap[initPoint] = set()
                processInitSyscallMap[initPoint].add(int(syscallno))


    translator = sycall.Syscall(rootLogger)
    syscallmap = translator.createMap()
    for initPoint in processInitSyscallMap:
        syscallset = processInitSyscallMap[initPoint]
        syscalllist = sorted(syscallset)
        print ("------- " + initPoint + " --------")
        for syscall in syscalllist:
            print (str(syscall))


if __name__ == "__main__":

    """
    Find system calls for function
    """
    usage = "Usage: %prog -f <Target program cfg> -c <glibc callgraph file>"

    parser = optparse.OptionParser(usage=usage, version="1")

    parser.add_option("-f", "--targetcfg", dest="targetcfg", default=None, nargs=1,
                      help="Function name")

    parser.add_option("-c", "--cfginput", dest="cfginput", default=None, nargs=1,
                      help="CFG input for creating graph from CFG")

    parser.add_option("-d", "--debug", dest="debug", action="store_true", default=False,
                      help="Debug enabled/disabled")

    (options, args) = parser.parse_args()
    if isValidOpts(options):
        processSeparatedCalls(options.targetcfg,
            options.cfginput,
            ":");

        # In case of nginx
        """
        mainset = processInitSyscallMap['main']
        cachemgrset = processInitSyscallMap['ngx_cache_manager_process_cycle']
        workerset = processInitSyscallMap['ngx_worker_process_cycle']
        """

        # In case of httpd
        mainset = processInitSyscallMap['main']
        workerset = processInitSyscallMap['uv__process_child_init']

        """
        for syscall in mainset:
            print (syscall)

        for syscall in workerset:
            print (syscall)

        """
        mminusw = sorted(mainset.difference(workerset))
        wminusm = sorted(workerset.difference(mainset))

        #mminusc = sorted(mainset.difference(cachemgrset))
        #cminusm = sorted(cachemgrset.difference(mainset))

        rootLogger = setLogPath("graph.log")

        translator = sycall.Syscall(rootLogger)
        syscallmap = translator.createMap()

        print ("------- main minus worker -------")
        for syscall in mminusw:
            print (syscallmap[syscall])
        print ("------- worker minus main -------")
        for syscall in wminusm:
            print (syscallmap[syscall])

