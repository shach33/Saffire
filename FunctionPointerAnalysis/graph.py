import os, sys, subprocess, signal

class Graph():
    """
    This class can be used to create a graph and run DFS and BFS on it
    """
    def __init__(self, logger):
        self.logger = logger
        self.adjGraph = dict()

    def addNode(self, nodeName):
        if ( not self.adjGraph.get(nodeName, None) ):
            self.adjGraph[nodeName] = list()

    def addEdge(self, nodeName, dstNode):
        currentList = self.adjGraph.get(nodeName, list())
        currentList.append(dstNode)
        self.adjGraph[nodeName] = currentList

    def dfs(self):
        #TODO
        return list()

    def bfs(self):
        #TODO
        return list()

    def getLeavesFromStartNode(self, nodeName, filterList, exceptList):
        results = set()
        visitedNodes = set()
        myStack = list()
        myStack.append(nodeName)

        if ( len(self.adjGraph.get(nodeName, list())) == 0 ):
            return results

        while ( len(myStack) != 0 ):
            currentNode = myStack.pop()
            if ( currentNode not in visitedNodes):
#                self.logger.debug("Visiting node: " + currentNode)
                visitedNodes.add(currentNode)
                if ( len(self.adjGraph.get(currentNode, list())) != 0 ):
                    for node in self.adjGraph.get(currentNode, list()):
                        myStack.append(node)
                else:
                    if ( ( len(filterList) == 0 and len(exceptList) == 0 ) or ( len(filterList) > 0 and currentNode in filterList) or ( len(exceptList) > 0 and currentNode not in exceptList ) ):
                        results.add(currentNode)

        return results

    def getSyscallFromStartNode(self, nodeName):
        results = set()
        visitedNodes = set()
        myStack = list()
        myStack.append(nodeName)

        if ( len(self.adjGraph.get(nodeName, list())) == 0 ):
            return results

        while ( len(myStack) != 0 ):
            currentNode = myStack.pop()
            if ( currentNode not in visitedNodes):
#                self.logger.debug("Visiting node: " + currentNode)
                visitedNodes.add(currentNode)
                if ( len(self.adjGraph.get(currentNode, list())) != 0 ):
                    for node in self.adjGraph.get(currentNode, list()):
                        myStack.append(node)
                else:
                    if ( currentNode.strip().startswith("syscall") ):
                        #self.logger.debug("getSyscallFromStartNode: currentNode: %s", currentNode)
                        currentNode = currentNode.replace("syscall","")
                        currentNode = currentNode.replace("(","")
                        currentNode = currentNode.replace(")","")
                        currentNode = currentNode.strip()
                        if ( not currentNode.startswith("%") ):
                            results.add(int(currentNode))

        return results


    def createGraphFromInput(self, inputFilePath, separator):
        inputFile = open(inputFilePath, 'r')
        inputLine = inputFile.readline()
        while ( inputLine ):
            splittedInput = inputLine.split(separator)
            if ( len(splittedInput) == 2 ):
                func1 = splittedInput[0].strip()
                func2 = splittedInput[1].strip()
                if ( func2.startswith("@") ):
                    func2 = func2[1:]
                #self.logger.debug("Adding %s->%s", func1, func2)
                self.addEdge(func1, func2)
            inputLine = inputFile.readline()
        inputFile.close()
