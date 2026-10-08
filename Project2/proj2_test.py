import sys
from z3 import And, AtMost, Bool, If, Implies, Int, Not, Or, PbLe, SolverFor, Sum, is_true, sat, unsat


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
        return instance["a"][j] == 1

    if j == 0:
        return True

    first_position = max(instance["a"][i], instance["a"][j] - 1, 1)
    last_position = min(instance["b"][i], instance["b"][j] - 1, instance["n"] - 1)

    return first_position <= last_position


def solve(instance):
    n, B = instance["n"], instance["B"]
    dist = instance["dist"]

    # --- FIXED OPTIMIZATION 3: True Lower Bounds via Lightweight Dijkstra ---
    # Calculates the guaranteed minimum arrival time at every node from the depot
    shortest_from_0 = {i: float('inf') for i in range(n + 1)}
    shortest_from_0[0] = 0
    unvisited = set(range(n + 1))
    
    while unvisited:
        u = min(unvisited, key=lambda x: shortest_from_0[x])
        if shortest_from_0[u] == float('inf'):
            break
        unvisited.remove(u)
        
        for v in unvisited:
            if check_windows(instance, u, v) and dist[u][v] >= 0:
                alt = shortest_from_0[u] + dist[u][v]
                if alt < shortest_from_0[v]:
                    shortest_from_0[v] = alt

    # Safely reject edges using true lower bounds
    allowed = {}
    for i in range(n + 1):
        for j in range(n + 1):
            if i != j and 0 <= dist[i][j] <= B and check_windows(instance, i, j):
                # Guaranteed minimum time to reach i + flight time to j
                min_arrival_at_j = shortest_from_0[i] + dist[i][j]
                deadline_j = instance["deadlines"].get(j, B)
                
                if min_arrival_at_j <= deadline_j and min_arrival_at_j <= B:
                    allowed[(i, j)] = dist[i][j]

    # --- PRE-CALCULATIONS FOR OPTIMIZATIONS 1 & 2 ---
    all_weights = sorted([allowed[e] for e in allowed if allowed[e] > 0])
    min_flight = min(all_weights, default=0) if all_weights else 0
    min_energy_for_steps = [0] + [sum(all_weights[:k]) if k <= len(all_weights) else sum(all_weights) for k in range(1, n + 1)]

    # Provide safe bounds for variables
    lower = {c: 0 for c in range(1, n + 1)}
    upper = {c: instance["deadlines"].get(c, B) for c in range(1, n + 1)}

    native_pb = max(B, sum(instance["w"])) <= 2**31 - 1
    solver = SolverFor("QF_IDL" if native_pb else "QF_LIA")
    if native_pb:
        solver.set("arith.solver", 1)

    def weighted_bound(terms, bound):
        if native_pb:
            return PbLe(terms, bound)
        return Sum([If(literal, weight, 0) for literal, weight in terms]) <= bound

    flight = {(i, j): Bool(f"flight_{i}_{j}") for i, j in allowed}
    served = {c: Bool(f"served_{c}") for c in range(1, n + 1)}

    for c in range(n + 1):
        incoming = [edge for (i, j), edge in flight.items() if j == c]
        outgoing = [edge for (i, j), edge in flight.items() if i == c]
        at_most_one(solver, incoming)
        at_most_one(solver, outgoing)

        if c == 0:
            solver.add(Or(incoming) == Or(list(served.values())))
            solver.add(Or(outgoing) == Or(list(served.values())))
        else:
            solver.add(served[c] == Or(incoming), served[c] == Or(outgoing))

    position = {c: Int(f"position_{c}") for c in served}
    arrival = {c: Int(f"arrival_{c}") for c in range(n + 1)}
    solver.add(arrival[0] == 0)

    for c in served:
        solver.add(Implies(Not(served[c]), And(position[c] == 0, arrival[c] == 0)))
        solver.add(Implies(served[c], And(
            position[c] >= max(1, instance["a"][c]),
            position[c] <= min(n, instance["b"][c]),
            arrival[c] >= lower[c],
            arrival[c] <= upper[c],
        )))

        # --- OPTIMIZATION 1: Position-to-Energy Lower Bounds ---
        for k in range(1, n + 1):
            solver.add(Implies(position[c] == k, arrival[c] >= min_energy_for_steps[k]))

    for (i, j), edge in flight.items():
        if j != 0:
            solver.add(Implies(edge, position[j] == (1 if i == 0 else position[i] + 1)))
            solver.add(Implies(edge, arrival[j] == arrival[i] + allowed[(i, j)]))

    for before, after in instance["precedences"]:
        # Standard sequence precedence
        solver.add(Implies(And(served[before], served[after]),
                           position[before] < position[after]))
        
        # --- OPTIMIZATION 2: Time-Based Precedence Tightening ---
        solver.add(Implies(And(served[before], served[after]),
                           arrival[after] >= arrival[before] + min_flight))

    energy_terms = [(edge, allowed[key]) for key, edge in flight.items() if allowed[key] > 0]
    if energy_terms:
        solver.add(weighted_bound(energy_terms, B))
    costs = energy_terms + [(Not(served[c]), instance["w"][c])
                            for c in served if instance["w"][c] > 0]

    # Matrix offset reduction (Massive head start for the solver)
    choices = {key: (edge, allowed[key]) for key, edge in flight.items()}
    choices.update({(c, c): (Not(served[c]), instance["w"][c]) for c in served})
    choices[(0, 0)] = (Not(Or(list(served.values()))), 0)
    
    row_min = {i: min(weight for (a, b), (literal, weight) in choices.items() if a == i)
               for i in range(n + 1)}
    col_min = {j: min(weight - row_min[a] for (a, b), (literal, weight) in choices.items() if b == j)
               for j in range(n + 1)}
    offset = sum(row_min.values()) + sum(col_min.values())
    reduced_costs = [(literal, weight - row_min[i] - col_min[j])
                     for (i, j), (literal, weight) in choices.items()
                     if weight > row_min[i] + col_min[j]]

    # Incremental binary search
    low, high = offset, sum(instance["w"])
    best_cost, best_model = high, None
    while low <= high:
        bound = (low + high) // 2
        solver.push()
        if reduced_costs:
            solver.add(weighted_bound(reduced_costs, bound - offset))
        result = solver.check()
        if result == sat:
            best_model = solver.model()
            best_cost = sum(weight for literal, weight in costs
                            if is_true(best_model.eval(literal, model_completion=True)))
            high = best_cost - 1
        elif result == unsat:
            low = bound + 1
        else:
            raise RuntimeError(f"SMT solver could not prove the optimum: {solver.reason_unknown()}")
        solver.pop()

    if best_model is None:
        return best_cost, []
    ordered_visits = sorted((best_model.eval(position[c]).as_long(), c)
                            for c in served if is_true(best_model.eval(served[c])))
    return best_cost, [c for p, c in ordered_visits]


def decode_out(best_cost, route):
    print(best_cost, len(route))
    print(*route)


def main():
    instance = read_instance()
    best_cost, route = solve(instance)
    decode_out(best_cost, route)


if __name__ == "__main__":
    main()