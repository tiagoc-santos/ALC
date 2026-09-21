import sys
from pysat.formula import IDPool

def read_instance():
    instance = {"n": 0, "B": 0, "dist": [], "w": [0], "a": [0], "b": [0], "precedences": []}
    instance["n"], instance["B"] = map(int, sys.stdin.readline().split())
    
    n = instance["n"]
    for _ in range(n + 1):
        row = list(map(int, sys.stdin.readline().split()))
        instance["dist"].append(row)
    
    for _ in range(n):
        w, a, b = map(int, sys.stdin.readline().split())
        instance["w"].append(w)
        instance["a"].append(a)
        instance["b"].append(b)
        
    P = int(sys.stdin.readline())
    
    for _ in range(P):
        before, after = map(int, sys.stdin.readline().split())
        instance["precedences"].append((before, after))
    
    return instance

def solve(instance):
    n = instance["n"]
    dist_matrix = instance["dist"]
    vpool = IDPool()
    
    # allowed flights
    flight = {}

    #locations served
    served = {}
    
    for i in range(n + 1):
        if i > 0:
            # location i is served if it is visited
            served[i] = vpool.id(("served", i))
        for j in range(n + 1):
            # cannot fly to itself and cannot be a forbidden flight
            if i != j and dist_matrix[i][j] >= 0:
                flight[(i, j)] = vpool.id(f"flight_{i}_{j}") #vpool.id(("flight", i, j))
    print(flight)
    print(served)
    return

def main():
    instance = read_instance()
    solve(instance) 
    
if __name__ == "__main__":
    main()