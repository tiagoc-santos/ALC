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
    x = {}
    
    for i in range(n + 1):
        for j in range(n + 1):
            # cannot fly to itself and cannot be a forbidden flight
            if i != j and dist_matrix[i][j] > 0:
                x[(i, j)] = vpool.id(f"x_{i}_{j}")
    return

def main():
    instance = read_instance()
    
    
if __name__ == "__main__":
    main()