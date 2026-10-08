import sys
from pysat.formula import IDPool, WCNF
from pysat.card import CardEnc, EncType, ITotalizer
from pysat.pb import PBEnc
from z3 import Bool, Implies, Int, Not, Optimize, Or, is_true, sat

def read_instance():
    instance = {"n": 0, "B": 0, "dist": [], "w": [0], "a": [0], "b": [0], "precedences": [], "deadlines": {}}
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

    T = int(sys.stdin.readline())
    for _ in range(T):
        c, deadline = map(int, sys.stdin.readline().split())
        instance["deadlines"][c] = deadline
    
    return instance

def at_most_one(formula, literals, vpool):
    if len(literals) <= 1:
        return
    encoding = CardEnc.atmost(lits=literals, bound=1, vpool=vpool, encoding=EncType.seqcounter)
    formula.extend(encoding.clauses)

def check_windows(instance, i, j):
    if i == 0:
        return instance["a"][j] == 1
    
    if j == 0:
        return True
    
    first_position = max(instance["a"][i], instance["a"][j] - 1, 1)
    last_position = min(instance["b"][i], instance["b"][j] - 1, instance["n"] - 1)
    
    return first_position <= last_position

def solve(instance):
    n = instance["n"]
    dist_matrix = instance["dist"]
    vpool = IDPool()
    formula = WCNF()
    
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
                flight[(i, j)] = vpool.id(f"flight_{i}_{j}")

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

    for before, after in set(instance["precedences"]):
        
        # a destination cannot strictly precede itself
        if before == after:
            formula.append([-served[before]])
            continue

        first_before = instance["a"][before]
        last_before = instance["b"][before]

        first_after = instance["a"][after]
        last_after = instance["b"][after]

        # every possible position already respects the precedence
        if last_before < first_after:
            continue

        # no possible positions can satisfy before < after
        if first_before >= last_after:
            formula.append([-served[before], -served[after]])
            continue

        # forbid reversed positions.
        for p in range(first_before, last_before + 1):
            for q in range(first_after, min(last_after, p - 1) + 1):
                formula.append([-visit[(before, p)], -visit[(after, q)]])
    
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
    
    # assign flights to positions
    for (i, j), edge in flight.items():
        # flight depot -> j: j must be first
        if i == 0:
            formula.append([-edge, visit[(j, 1)]])

        # flight i -> depot: i must be last
        elif j == 0:
            for p in range(max(1, instance["a"][i]), min(n, instance["b"][i]) + 1):
                if p < n:
                    formula.append([-edge, -visit[(i, p)], -occupied[p + 1]])

        # flight i -> j: j must immediately follow i
        else:
            for p in range(max(1, instance["a"][i]), min(n, instance["b"][i]) + 1):
                next_visit = visit.get((j, p + 1))
                
                if next_visit is None:
                    formula.append([-edge, -visit[(i, p)]])
                else:
                    # if this flight is selected and i occupies p -> j occupies p+1
                    formula.append([-edge, -visit[(i, p)], next_visit])

    # selecting a flight costs energy
    for edge, energy in zip(flight_lits, flight_weights):
        formula.append([-edge], weight=energy)

    # skipping a destination costs its penalty
    for c in range(1, n + 1):
        penalty = instance["w"][c]

        if penalty > 0:
            formula.append([served[c]], weight=penalty)

    # if k destinations are served, position k is used.
    with ITotalizer(lits=list(served.values()), ubound=n,
                    top_id=vpool.top) as totalizer:
        formula.extend(totalizer.cnf.clauses)
        for p in range(1, n + 1):
            threshold = totalizer.rhs[p - 1]
            formula.append([-threshold, occupied[p]])
            formula.append([-occupied[p], threshold])
        if totalizer.top_id > vpool.top:
            vpool.occupy(vpool.top + 1, totalizer.top_id)
    
    # Keep the existing Boolean encoding, but solve it with an SMT optimizer.
    optimizer = Optimize()
    optimizer.set(maxsat_engine="wmax")
    variables = {i: Bool(f"v_{i}") for i in range(1, formula.nv + 1)}

    def smt_clause(clause):
        return Or([variables[lit] if lit > 0 else Not(variables[-lit])
                   for lit in clause])

    for clause in formula.hard:
        optimizer.add(smt_clause(clause))
    for clause, weight in zip(formula.soft, formula.wght):
        optimizer.add_soft(smt_clause(clause), weight=weight)

    # Arrival distance counts the route prefix, excluding the return to depot.
    arrival = {c: Int(f"arrival_{c}") for c in range(n + 1)}
    optimizer.add(arrival[0] == 0)
    for c in range(1, n + 1):
        optimizer.add(arrival[c] >= 0, arrival[c] <= instance["B"])
    for (i, j), edge in flight.items():
        if j != 0:
            optimizer.add(Implies(variables[edge],
                                  arrival[j] == arrival[i] + dist_matrix[i][j]))
    for c, deadline in instance["deadlines"].items():
        optimizer.add(Implies(variables[served[c]], arrival[c] <= deadline))

    if optimizer.check() != sat:
        raise RuntimeError("SMT optimizer could not find an optimal route")
    model = optimizer.model()
    best_cost = sum(weight for clause, weight in zip(formula.soft, formula.wght)
                    if not is_true(model.eval(smt_clause(clause))))
    true_vars = {i for i, variable in variables.items() if is_true(model.eval(variable))}

    ordered_visits = sorted((p, c) for (c, p), variable in visit.items()
                            if variable in true_vars)
    route = [c for p, c in ordered_visits]

    return best_cost, route

def decode_out(best_cost, route):
    print(best_cost, len(route))
    print(*route)

def main():
    instance = read_instance()
    best_cost, route = solve(instance)
    decode_out(best_cost, route)
    
if __name__ == "__main__":
    main()
