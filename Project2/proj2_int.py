import sys
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


def check_windows(instance, i, j):
    if i == 0:
        return instance["a"][j] <= 1 <= instance["b"][j]

    if j == 0:
        return True

    first_position = max(instance["a"][i], instance["a"][j] - 1, 1)
    last_position = min(instance["b"][i], instance["b"][j] - 1, instance["n"] - 1)

    return first_position <= last_position


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