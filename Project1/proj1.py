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

def check_windows(instance, i, j):
    a_i = instance["a"][i]
    b_i = instance["b"][i]
    
    a_j = instance["a"][j]
    b_j = instance["b"][j]
    
    if i == 0:
        return a_j == 1
    
    if j == 0:
        return True
    
    first_position = max(instance["a"][i], instance["a"][j] - 1, 1)
    last_position = min(instance["b"][i], instance["b"][j] - 1, instance["n"] - 1)
    
    return first_position <= last_position

def solve(instance):
    n = instance["n"]
    dist_matrix = instance["dist"]
    vpool = IDPool()
    formula = CNF()
    
    # allowed flights
    flight = {}

    # locations served
    served = {}
    
    for i in range(n + 1):
        if i > 0:
            # location i is served if it is visited
            served[i] = vpool.id(("served", i))
        for j in range(n + 1):
            # cannot fly to itself, cannot be a forbidden flight and cannot be an impossible flight
            if i != j and 0 <= dist_matrix[i][j] <= instance["B"] and check_windows(instance, i, j):
                flight[(i, j)] = vpool.id(f"flight_{i}_{j}") # vpool.id(("flight", i, j))

    for c in range(0, n + 1):
        incoming = [flight[(i, c)] for i in range(n + 1) if (i, c) in flight]
        outgoing = [flight[(c, j)] for j in range(n + 1) if (c, j) in flight]

        # at most one incoming and outgoing flight
        at_most_one(formula, incoming, vpool)
        at_most_one(formula, outgoing, vpool)

        # special depot flights
        if c == 0:
            depot_incoming = incoming
            depot_outgoing = outgoing
            continue

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

    visit = {}

    for c in range(1, n + 1):
        positions = []
        # enforce delievery windows
        for p in range(max(1, instance["a"][c]), min(n, instance["b"][c]) + 1):
            visit[(c, p)] = vpool.id(("visit", c, p))
            positions.append(visit[(c, p)])

        # can only be at one position
        at_most_one(formula, positions, vpool)

        # being assigned a position means c is served
        for position_var in positions:
            formula.append([-position_var, served[c]])

        # a served destination must have a valid position
        formula.append([-served[c], *positions])
    
    occupied = {p: vpool.id(("occupied", p)) for p in range(1, n + 1)}

    for p in range(1, n + 1): 
        destinations_at_p = [visit[(c, p)] for c in range(1, n + 1) if (c, p) in visit]

        # at most one destination at position p
        at_most_one(formula, destinations_at_p, vpool)

        # a destination at p -> p is occupied
        for visit_var in destinations_at_p:
            formula.append([-visit_var, occupied[p]])

        # an occupied position must contain a destination
        formula.append([-occupied[p], *destinations_at_p])
        
        # if destination p + 1 is occupied -> p has to be occupied 
        if p < n:
            formula.append([-occupied[p + 1], occupied[p]])
        
    # if the route is nonempty -> flight leaves the depot
    formula.append([-occupied[1], *depot_outgoing])

    # if the route is nonempty -> flight returns to the depot
    formula.append([-occupied[1], *depot_incoming])
    
    print(flight)
    print(served)
    print(formula.clauses)
    return

def main():
    instance = read_instance()
    solve(instance) 
    
if __name__ == "__main__":
    main()