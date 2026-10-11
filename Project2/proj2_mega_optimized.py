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


def prune_flights(instance):
    n, B = instance["n"], instance["B"]
    dist = instance["dist"]
    allowed = {(i, j): dist[i][j] for i in range(n + 1) for j in range(n + 1)
               if i != j and 0 <= dist[i][j] <= B and check_windows(instance, i, j)}

    # Shortest paths are optimistic: they ignore whole-route windows/precedences.
    # Removing an impossible flight can strengthen these bounds, so repeat.
    while True:
        shortest = [[0 if i == j else allowed.get((i, j), float("inf"))
                     for j in range(n + 1)] for i in range(n + 1)]
        for k in range(n + 1):
            for i in range(n + 1):
                for j in range(n + 1):
                    shortest[i][j] = min(shortest[i][j], shortest[i][k] + shortest[k][j])

        upper = {c: min(B - shortest[c][0], instance["deadlines"].get(c, B))
                 for c in range(1, n + 1)}
        remaining = {(i, j): energy for (i, j), energy in allowed.items()
                     if shortest[0][i] + energy + shortest[j][0] <= B
                     and (i == 0 or shortest[0][i] <= upper[i])
                     and (j == 0 or shortest[0][i] + energy <= upper[j])}
        if remaining == allowed:
            return allowed, shortest[0], upper
        allowed = remaining


def solve(instance):
    n, B = instance["n"], instance["B"]
    allowed, lower, upper = prune_flights(instance)

    # Native pseudo-Boolean bounds leave only integer difference constraints:
    # position[j] - position[i] == 1 and arrival[j] - arrival[i] == distance.
    # Z3's PbLe API takes 32-bit coefficients/bounds; retain exact arithmetic
    # for larger inputs by falling back to general linear integer arithmetic.
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
            # A served destination has exactly one incoming and outgoing flight.
            solver.add(served[c] == Or(incoming), served[c] == Or(outgoing))

    position = {c: Int(f"position_{c}") for c in served}
    arrival = {c: Int(f"arrival_{c}") for c in range(n + 1)}
    solver.add(arrival[0] == 0)

    for c in served:
        solver.add(Implies(Not(served[c]), And(position[c] == 0, arrival[c] == 0)))
        if lower[c] > upper[c]:
            solver.add(Not(served[c]))
            continue
        solver.add(Implies(served[c], And(
            position[c] >= max(1, instance["a"][c]),
            position[c] <= min(n, instance["b"][c]),
            arrival[c] >= int(lower[c]),
            arrival[c] <= int(upper[c]),
        )))

    for (i, j), edge in flight.items():
        if j != 0:
            solver.add(Implies(edge, position[j] == (1 if i == 0 else position[i] + 1)))
            solver.add(Implies(edge, arrival[j] == arrival[i] + allowed[(i, j)]))

    # The degree constraints form cycles; increasing positions forbid every
    # cycle that excludes the depot. Thus all visits belong to one route with
    # distinct consecutive positions, without extra pairwise/count constraints.
    for before, after in instance["precedences"]:
        solver.add(Implies(And(served[before], served[after]),
                           position[before] < position[after]))

    energy_terms = [(edge, allowed[key]) for key, edge in flight.items() if allowed[key] > 0]
    if energy_terms:
        solver.add(weighted_bound(energy_terms, B))
    costs = energy_terms + [(Not(served[c]), instance["w"][c])
                            for c in served if instance["w"][c] > 0]

    # Treat skipping c as the self-edge c -> c. Every vertex then has exactly
    # one incoming and outgoing choice (the empty route skips the depot too).
    # Subtract row/column minima: every route loses the same constant offset,
    # so the optimum is unchanged, but the weighted bounds are much tighter.
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

    # The empty route gives an initial upper bound. Incremental binary search
    # proves the optimum, keeping learned information between cost-bound checks.
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
