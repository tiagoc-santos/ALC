import sys
from pysat.formula import IDPool, CNF
from pysat.card import CardEnc, EncType
from pysat.pb import PBEnc

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

def at_most_one(formula, literals, vpool):
    if len(literals) <= 1:
        return
    encoding = CardEnc.atmost(lits=literals, bound=1, vpool=vpool, encoding=EncType.seqcounter)
    formula.extend(encoding.clauses)

def solve(instance):
    n = instance["n"]
    dist_matrix = instance["dist"]
    vpool = IDPool()
    formula = CNF()
    
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

    for c in range(1, n + 1):
        incoming = [flight[(i, c)] for i in range(n + 1) if (i, c) in flight]
        outgoing = [flight[(c, j)] for j in range(n + 1) if (c, j) in flight]

        # at most one incoming and outgoing flight
        at_most_one(formula, incoming, vpool)
        at_most_one(formula, outgoing, vpool)

        # if edge is selected -> c is served
        for edge in incoming:
            formula.append([-edge, served[c]])

        for edge in outgoing:
            formula.append([-edge, served[c]])

        # if c is served -> needs outgoing and incoming flights
        formula.append([-served[c], *incoming])
        formula.append([-served[c], *outgoing])

    flight_lits = []
    flight_weights = []

    for (i, j), edge in flight.items():
        energy = dist_matrix[i][j]

        # count only positive weight flights
        if energy > 0:
            flight_lits.append(edge)
            flight_weights.append(energy)

    if flight_lits:
        battery = PBEnc.leq(lits=flight_lits, weights=flight_weights, 
                            bound=instance["B"], vpool=vpool)

        formula.extend(battery.clauses)

    print(flight)
    print(served)
    print(formula.clauses)
    return

def main():
    instance = read_instance()
    solve(instance) 
    
if __name__ == "__main__":
    main()