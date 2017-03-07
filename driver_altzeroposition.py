from math import sqrt
import time
import resource
import sys
from heapq import heappush, heappop

class puzzle_state:
    
    def __init__(self, state, parent=None, operation=None, depth=0, cost=0):
        self._state = state
        self._sideofpuzzle = int(sqrt(len(self._state)))
        self._parent = parent
        self._operation = operation
        self._children = []
        self._depth = depth
        self._cost = cost
        self._goal_state = range(1,len(state))
        self._goal_state.append(0)
    
    def _is_goal(self):
        return(self._state == self._goal_state)
        
    def _find_zero(self):
        return(self._state.index(0)+1)
    
    def _make_child(self,new_state,operation):
        return puzzle_state(new_state, self, operation, self._depth+1, self._cost+1)

    def _find_moves(self):
        if self._find_zero()>self._sideofpuzzle:
            operation = 'Up'
            new_state = self._swap_tiles(self._find_zero() - self._sideofpuzzle)
            self._children.append(self._make_child(new_state,operation))
            
        if self._find_zero()<=(self._sideofpuzzle**2-self._sideofpuzzle):
            operation = 'Down'
            new_state = self._swap_tiles(self._find_zero() + self._sideofpuzzle)
            self._children.append(self._make_child(new_state,operation))
            
        if (self._find_zero()-1)%self._sideofpuzzle>0:
            operation = 'Left'
            new_state = self._swap_tiles(self._find_zero() - 1)
            self._children.append(self._make_child(new_state,operation))
            
        if self._find_zero()%self._sideofpuzzle>0:
            operation =  'Right'
            new_state = self._swap_tiles(self._find_zero() + 1)
            self._children.append(self._make_child(new_state,operation))
            
    def _swap_tiles(self, tile_index):
        _new_state = list(self._state)
        _new_state[self._find_zero()-1] = _new_state[tile_index-1]
        _new_state[tile_index-1] = 0
        return _new_state

    def _manhattanHeur(self):
        manhattandist = 0
        for i in range(1,len(self._state)):
            current_col = self._state.index(i)%self._sideofpuzzle
            current_row = self._state.index(i)/self._sideofpuzzle
            ideal_col = (i-1)%self._sideofpuzzle
            ideal_row = (i-1)/self._sideofpuzzle
            manhattandist += abs(current_col-ideal_col)+abs(current_row-ideal_row)
        return manhattandist
        
class Solver(object):
    def __init__(self, startstate):
        self._startnode = puzzle_state(startstate)
        self._frontier = {tuple(self._startnode._state) : self._startnode}
        self._explored = dict()
        self._moves = 0
        self._queue = [self._startnode]
        self._stack = [self._startnode]
        self._heap = []
        self._nodes_expanded = 0
        self._max_fringe_size = 0
        self._max_search_depth = 0

    def _generate_solution_path(self, end_node):
        move_path = []
        node = end_node
        while True:
            if node._parent == None:
                return move_path
            else:
                move_path.insert(0,node._operation)
                node = node._parent
                    
    def _bfs(self):
        while not self._queue == []:
            node = self._queue.pop(0)
            if self._max_fringe_size < len(self._frontier) : self._max_fringe_size = len(self._frontier)
            del self._frontier[tuple(node._state)]
            
            if node._is_goal():
                return self._Success(node)
            else:
                self._explored.update({tuple(node._state) : node})
                node._find_moves()
                self._nodes_expanded += 1
                for x in node._children:
                    if (tuple(x._state) not in self._frontier) and (tuple(x._state) not in self._explored):
                        if self._max_search_depth < x._depth : self._max_search_depth = x._depth
                        self._frontier.update({tuple(x._state) : x})
                        self._queue.append(self._frontier.get(tuple(x._state)))

    def _dfs(self):
        while not self._stack == []:
            if self._max_fringe_size < len(self._frontier) : self._max_fringe_size = len(self._frontier)
            node = self._stack.pop()
            del self._frontier[tuple(node._state)]
            
            if node._is_goal():
                return self._Success(node)
            else:
                self._explored.update({tuple(node._state) : node})
                node._find_moves()
                self._nodes_expanded += 1
                for x in node._children[::-1]:
                    if (tuple(x._state) not in self._frontier) and (tuple(x._state) not in self._explored):
                        if self._max_search_depth < x._depth : self._max_search_depth = x._depth
                        self._frontier.update({tuple(x._state) : x})
                        self._stack.append(self._frontier.get(tuple(x._state)))
                        
    def _ast(self):
        heappush(self._heap, (0, self._startnode))
        while not self._heap == []:
            if self._max_fringe_size < len(self._frontier) : self._max_fringe_size = len(self._frontier)
            node = heappop(self._heap)[1]
            if (tuple(node._state) in self._frontier): del self._frontier[tuple(node._state)]
            
            if node._is_goal():
                return self._Success(node)
            else:
                self._explored.update({tuple(node._state) : node})
                node._find_moves()
                self._nodes_expanded += 1
                for x in node._children:
                    f_node = x._cost+x._manhattanHeur()
                    if (tuple(x._state) not in self._frontier) and (tuple(x._state) not in self._explored):
                        if self._max_search_depth < x._depth : self._max_search_depth = x._depth
                        self._frontier.update({tuple(x._state) : x})
                        heappush(self._heap, (f_node, x))
                    elif (tuple(x._state) in self._frontier):
                        if self._frontier.get(tuple(x._state))._cost > x._cost:
                            heappush(self._heap, (f_node, x))

    def _ida(self):
        f_nextlimit = self._startnode._cost + self._startnode._manhattanHeur()
        while True:
            f_limit = f_nextlimit
            self._startnode = puzzle_state(self._startnode._state)
            self._frontier = {tuple(self._startnode._state) : self._startnode}
            self._explored = dict()
            heappush(self._heap, (0, self._startnode))

            while not len(self._heap) == 0:
                if self._max_fringe_size < len(self._frontier) : self._max_fringe_size = len(self._frontier)
                node = heappop(self._heap)[1]
                if (tuple(node._state) in self._frontier): del self._frontier[tuple(node._state)]

                if node._is_goal():
                    return self._Success(node)

                else:
                    self._explored.update({tuple(node._state) : node})
                    node._find_moves()
                    self._nodes_expanded += 1
                    for x in node._children:
                        f_node = x._cost+x._manhattanHeur()
                        if f_node <= f_limit:
                            if (tuple(x._state) not in self._frontier) and (tuple(x._state) not in self._explored):
                                if self._max_search_depth < x._depth : self._max_search_depth = x._depth
                                self._frontier.update({tuple(x._state) : x})
                                heappush(self._heap, (f_node, x))
                            elif (tuple(x._state) in self._frontier):
                                if self._frontier.get(tuple(x._state))._cost > x._cost:
                                    heappush(self._heap, (f_node, x))
                        else:
                            if f_node > f_nextlimit: 
                                f_nextlimit = f_node

    def _Success(self, node):
        path_to_goal = self._generate_solution_path(node)
        return [path_to_goal, node._cost, self._nodes_expanded, len(self._frontier), self._max_fringe_size, node._depth, self._max_search_depth]
    
def main():
    
    strategy = sys.argv[1]
    start_state = map(int, sys.argv[2].split(","))
    t1 = time.time()

    solution = Solver(start_state)

    if strategy == "bfs":
        results = solution._bfs()
    elif strategy == "dfs":
        results = solution._dfs()
    elif strategy == "ast":
        results = solution._ast()
    elif strategy == "ida":
        results = solution._ida()

    t2 = time.time()
    results.extend([str("%.8f" % (t2 - t1)),str("%.8f" % (resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/float(10**6)))])

    print ("path_to_goal: {0}\n".format(results[0]))
    print ("cost_of_path: {0}\n".format(results[1]))
    print ("nodes_expanded: {0}\n".format(results[2]))
    print ("fringe_size: {0}\n".format(results[3]))
    print ("max_fringe_size: {0}\n".format(results[4]))
    print ("search_depth: {0}\n".format(results[5]))
    print ("max_search_depth: {0}\n".format(results[6]))
    print ("running_time: {0}\n".format(results[7]))
    print ("max_ram_usage: {0}\n".format(results[8]))
    
    text_file = open("output.txt", "w")
    text_file.write( "path_to_goal: {0}\n".format(results[0]))
    text_file.write( "cost_of_path: {0}\n".format(results[1]))
    text_file.write( "nodes_expanded: {0}\n".format(results[2]))
    text_file.write( "fringe_size: {0}\n".format(results[3]))
    text_file.write( "max_fringe_size: {0}\n".format(results[4]))
    text_file.write( "search_depth: {0}\n".format(results[5]))
    text_file.write( "max_search_depth: {0}\n".format(results[6]))
    text_file.write( "running_time: {0}\n".format(results[7]))
    text_file.write( "max_ram_usage: {0}\n".format(results[8]))
    text_file.close()
    
if __name__ == "__main__":
    main()