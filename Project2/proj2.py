#!/usr/bin/python3
# alc26 - 4 - project2 
# DO NOT remove or edit the lines above. Thank you.
import sys
from pysat.formula import IDPool, WCNF
from pysat.card import CardEnc, EncType, ITotalizer
from pysat.pb import PBEnc
from z3 import And, AtMost, Bool, If, Implies, Int, IntVal, Not, Optimize, Or, PbLe, Sum, is_true, sat, set_param

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


def at_most_one(solver, literals):
    if len(literals) > 1:
        solver.add(AtMost(*literals, 1))

def at_most_one_bool(formula, literals, vpool):
    if len(literals) <= 1:
        return
    encoding = CardEnc.atmost(lits=literals, bound=1, vpool=vpool, encoding=EncType.seqcounter)
    formula.extend(encoding.clauses)

def check_windows(instance, i, j):
    if i == 0:
        return instance["a"][j] <= 1 <= instance["b"][j]

    if j == 0:
        return True

    first_position = max(instance["a"][i], instance["a"][j] - 1, 1)
    last_position = min(instance["b"][i], instance["b"][j] - 1, instance["n"] - 1)

    return first_position <= last_position

def smt_clause(clause, variables):
        return Or([variables[lit] if lit > 0 else Not(variables[-lit])
                   for lit in clause])

def solve_bool(instance):
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
        at_most_one_bool(formula, incoming, vpool)
        at_most_one_bool(formula, outgoing, vpool)

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
        at_most_one_bool(formula, positions, vpool)

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
        at_most_one_bool(formula, destinations_at_p, vpool)

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
    
    arrival = {}
    limits = {}

    for c in range(1, n + 1):
        limits[c] = min(instance["B"], instance["deadlines"].get(c, instance["B"]))

        distances = []
        for d in range(limits[c] + 1):
            arrival[(c, d)] = vpool.id(("arrival", c, d))
            distances.append(arrival[(c, d)])

        # destination can have at most one arrival distance.
        at_most_one_bool(formula, distances, vpool)

        # arrival_distance -> served
        for variable in distances:
            formula.append([-variable, served[c]])

        # served -> arrival distance
        formula.append([-served[c], *distances])

    # assign arrivals to flights
    for (i, j), edge in flight.items():
        # skip return flight
        if j == 0:
            continue

        energy = dist_matrix[i][j]

        # depot -> j: arrival distance must equal flight cost
        if i == 0:
            
            first_arrival = arrival.get((j, energy))

            # deadline < flight cost
            if first_arrival is None:
                formula.append([-edge])
            else:
                formula.append([-edge, first_arrival])

        else:
            # i -> j: arrival at j must equal arrival at i + flight cost.
            for d in range(limits[i] + 1):
                current_arrival = arrival[(i, d)]
                next_arrival = arrival.get((j, d + energy))
                
                # i + flight cost > deadline j
                if next_arrival is None:
                    formula.append([-edge, -current_arrival])
                else:
                    formula.append([-edge, -current_arrival, next_arrival])
    
    # use SMT
    optimizer = Optimize()
    optimizer.set(maxsat_engine="wmax")
    
    # creates Z3 boolean variable for every variable ID
    variables = {i: Bool(f"v_{i}") for i in range(1, formula.nv + 1)}

    for clause in formula.hard:
        optimizer.add(smt_clause(clause, variables))
        
    for clause, weight in zip(formula.soft, formula.wght):
        optimizer.add_soft(smt_clause(clause, variables), weight=weight)

    if optimizer.check() != sat:
        raise RuntimeError("SMT optimizer could not find an optimal route")
    
    
    model = optimizer.model()
    
    best_cost = sum(weight for clause, weight in zip(formula.soft, formula.wght) 
                    if not is_true(model.eval(smt_clause(clause, variables))))
    
    true_vars = {i for i, variable in variables.items() if is_true(model.eval(variable))}

    ordered_visits = sorted((p, c) for (c, p), variable in visit.items()
                            if variable in true_vars)
    route = [c for p, c in ordered_visits]

    return best_cost, route

def position_bounds(instance, allowed):
    n, B = instance["n"], instance["B"]
    a, b = instance["a"], instance["b"]
    deadlines = instance["deadlines"]

    # arrivals can't be > B
    # start at unreachable (B + 1)
    # tracks the minimum energy needed to reach i at position p
    forward = [[B + 1] * (n + 1) for _ in range(n + 1)]
    forward[0][0] = 0
    
    for p in range(1, n + 1):
        for (i, j), energy in allowed.items():
            # if j isn't the depot and p is a valid position for j
            if j and a[j] <= p <= b[j]:
                # calculate arrival for j : arrival in i at position p-1 + flight cost
                value = forward[p - 1][i] + energy
                # arrival must respect the deadline of j (or if j has no deadline the battery constraint)
                if value <= min(B, deadlines.get(j, B)):
                    # saves the minimum value possible
                    forward[p][j] = min(forward[p][j], value)

    # arrival energy can't be < 0
    # start at no feasible continuation (-1)
    # tracks the max arrival energy at a c in position p that allows a feasible route
    backward = [[-1] * (n + 1) for _ in range(n + 1)]
    # start from last to first position
    for p in range(n, 0, -1):
        for (i, j), energy in allowed.items():
            # if i isn't the depot and p is a valid position for i
            if i and a[i] <= p <= b[i]:
                # if its the last flight the maximum energy possible for it to be valid is: B - flight cost
                if j == 0:
                    value = B - energy
                # if p is not the last position
                elif p < n:
                    # the maximum energy one can reach i in p is the maximum energy for j in p + 1 minus the flight cost
                    value = backward[p + 1][j] - energy
                # if p is the last no other destiation can appear next
                else:
                    value = -1
                
                # min ensures the deadline (or B constraint) is respected
                # max between the previous value and the new one
                backward[p][i] = max(backward[p][i], min(deadlines.get(i, B), value))

    positions = {}

    for c in range(1, n + 1):
        valid_p = []
        for p in range(1, n + 1):
            # checks if minimum arrival values <= maximum valid arrival
            if forward[p][c] <= backward[p][c]:
                valid_p.append(p)
                
        positions[c] = valid_p
        
    return forward, backward, positions

def solve_int(instance):
    n, B = instance["n"], instance["B"]
    dist = instance["dist"]
    
    allowed = {}
    for i in range(n + 1):
        for j in range(n + 1):
            cost = dist[i][j]
            # cannot fly to itself, cannot be a forbidden flight and cannot be an impossible flight
            if i != j and 0 <= cost <= B and check_windows(instance, i, j):
                allowed[(i, j)] = cost
                
    # remove flights impossible at every position
    forward, backward, feasible_positions = position_bounds(instance, allowed)
    while True:
        remaining = {}
        for (i, j), energy in allowed.items():
            possible = False
            # leaving the depot
            if i == 0:
                # j must be in the first position and flight energy <= deadline_j
                if 1 in feasible_positions[j] and energy <= backward[1][j]:
                    possible = True
            
            # going to the depot
            elif j == 0:
                # for each possible position checks: minimum arrival energy at i + return energy <= battery
                for p in feasible_positions[i]:
                    if forward[p][i] + energy <= B:
                        possible = True
                        break
            # flight i -> j
            else:
                # for all possible positions p of i check: if j can be at p + 1 and 
                # minimum arrival energy at j + flight energy <= maximum arrival at j
                for p in feasible_positions[i]:
                    if (p < n and p + 1 in feasible_positions[j] 
                            and forward[p][i] + energy <= backward[p + 1][j]):
                                possible = True
                                break
            
            if possible:
                remaining[i, j] = energy
        
        if len(remaining) == len(allowed):
            break
        
        allowed = remaining
        forward, backward, feasible_positions = position_bounds(instance, allowed)

    set_param("smt.arith.solver", 1)
    solver = Optimize()

    flights = {(i, j): Bool(f"flight_{i}_{j}") for i, j in allowed}
    served = {c: Bool(f"served_{c}") for c in range(1, n + 1)}

    for c in range(n + 1):
        incoming = [edge for (i, j), edge in flights.items() if j == c]
        outgoing = [edge for (i, j), edge in flights.items() if i == c]
        
        at_most_one(solver, incoming)
        at_most_one(solver, outgoing)

        if c == 0:
            solver.add(Or(incoming) == Or(list(served.values())))
            solver.add(Or(outgoing) == Or(list(served.values())))
        else:
            # a served destination has exactly one incoming and outgoing flight.
            solver.add(served[c] == Or(incoming), served[c] == Or(outgoing))

    position = {c: Int(f"position_{c}") for c in served}
    arrival = {c: Int(f"arrival_{c}") for c in range(n + 1)}
    solver.add(arrival[0] == 0)

    for c in served:
        # constraint to respect delivery windows and deadlines
        solver.add(Implies(served[c], And(position[c] >= max(1, instance["a"][c]),
            position[c] <= min(n, instance["b"][c]), arrival[c] >= 0,
            arrival[c] <= min(B, instance["deadlines"].get(c, B)))))

        possible = feasible_positions[c]
        # c does not have any feasable postions
        if not possible:
            solver.add(Not(served[c]))
        else:
            solver.add(Implies(served[c], And(
                position[c] >= min(possible), position[c] <= max(possible),
                arrival[c] >= min(forward[p][c] for p in possible),
                arrival[c] <= max(backward[p][c] for p in possible))))

    for (i, j), edge in flights.items():
        if j != 0:
            solver.add(Implies(edge, position[j] == (1 if i == 0 else position[i] + 1)))
            solver.add(Implies(edge, arrival[j] == arrival[i] + allowed[(i, j)]))
    
    for before, after in instance["precedences"]:
        solver.add(Implies(And(served[before], served[after]), position[before] < position[after]))

    energy_terms = []

    for flight, variable in flights.items():
        if allowed[flight] > 0:
            energy_terms.append((variable, allowed[flight]))
    
    if energy_terms:
        solver.add(PbLe(energy_terms, B))
    
    objective_terms = [If(Not(served[c]), instance["w"][c], 0) for c in served if instance["w"][c] > 0]
    
    for i in range(n + 1):
        incoming = []
        for flight, edge in flights.items():
            if flight[1] == i:
                incoming.append((edge, allowed[flight]))
        
        previous = 0
        for level in sorted({weight for edge, weight in incoming if weight > 0}):
            expensive = Or([edge for edge, weight in incoming if weight >= level])
            objective_terms.append(If(expensive, level - previous, 0))
            previous = level
    
    total_cost = Sum([IntVal(0)] + objective_terms)
    solver.minimize(total_cost)

    if solver.check() != sat:
        raise RuntimeError("Z3 could not determine an optimal route")

    best_model = solver.model()
    best_cost = best_model.eval(total_cost).as_long()
    
    ordered_visits = sorted((best_model.eval(position[c]).as_long(), c)
                            for c in served if is_true(best_model.eval(served[c])))
    
    return best_cost, [c for p, c in ordered_visits]

def decode_out(best_cost, route):
    print(best_cost, len(route))
    print(*route)

def main():
    instance = read_instance()
    best_cost, route = solve_int(instance)
    decode_out(best_cost, route)

if __name__ == "__main__":
    main()