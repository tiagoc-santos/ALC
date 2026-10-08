#!/usr/bin/env python3
"""
Validate a Drone Delivery P2 route (P1 + delivery deadlines) against an instance, and
optionally render it. Standalone: a copy of the P1 validator (validate.py) with the deadlines
added; it does not import it.

A P2 instance ends, after the precedences, with an optional deadline list:

    D
    c d_c        (D lines)

meaning that, if destination c is served, the distance flown from the depot until reaching c
must be at most d_c. Without the list (or with D = 0) it is exactly the P1 problem.

By default it prints a plain-text verdict with the recomputed cost and whether
the six constraints hold (restricted legs, windows, precedence, battery, deadlines,
valid IDs), exiting non-zero on any violation. Optionally, with --save FILE, it instead
writes a Mermaid diagram (flowchart) plus a Markdown summary to a .mmd/.md file.

Usage examples:
  python3 validateP2.py instance.drn
  python3 validateP2.py instance.drn --solution solution.out
  python3 validateP2.py instance.drn --route "2 1 3" --mermaid-view ordered
  python3 validateP2.py instance.drn --route "2 1 3" --save view.md
"""

import argparse
from typing import Dict, List, Sequence, Tuple


def read_instance(path: str):
    with open(path, "r", encoding="utf-8") as f:
        lines = [ln.strip() for ln in f if ln.strip()]

    it = iter(lines)
    n, B = map(int, next(it).split())

    dist = []
    for _ in range(n + 1):
        dist.append(list(map(int, next(it).split())))

    penalty: Dict[int, int] = {}
    windows: Dict[int, Tuple[int, int]] = {}
    for i in range(1, n + 1):
        w, a, b = map(int, next(it).split())
        penalty[i] = w
        windows[i] = (a, b)

    # Restricted (forbidden) legs are encoded as NEGATIVE entries in the matrix
    # (any negative means the direct flight i -> j is forbidden).
    nofly = [(i, j) for i in range(n + 1) for j in range(n + 1)
             if i != j and dist[i][j] < 0]

    P = int(next(it))
    precedence = []
    for _ in range(P):
        a, b = map(int, next(it).split())
        precedence.append((a, b))

    # Deadlines (P2): optional list "D" then D lines "c d_c"; absent means D = 0.
    deadline: Dict[int, int] = {}
    D_line = next(it, None)
    for _ in range(int(D_line) if D_line is not None else 0):
        c, d = map(int, next(it).split())
        deadline[c] = d

    return n, B, dist, penalty, windows, nofly, precedence, deadline


def parse_solution(path: str) -> Tuple[int, int, List[int]]:
    with open(path, "r", encoding="utf-8") as f:
        lines = [ln.rstrip("\n") for ln in f]

    if not lines:
        raise ValueError("Empty solution file.")

    head = lines[0].split()
    if len(head) < 2:
        raise ValueError("Invalid first line in solution. Expected: <cost> <K>")

    cost, k = map(int, head[:2])

    route: List[int] = []
    if len(lines) > 1 and lines[1].strip():
        route = list(map(int, lines[1].split()))

    if len(route) != k:
        raise ValueError(
            f"Solution route length mismatch: K={k}, but found {len(route)} nodes"
        )

    return cost, k, route


def parse_route_text(route_text: str) -> List[int]:
    route_text = route_text.strip()
    if not route_text:
        return []
    return [int(x) for x in route_text.split()]


def route_legs(route: Sequence[int]) -> List[Tuple[int, int]]:
    if not route:
        return []
    full = [0] + list(route) + [0]
    return list(zip(full, full[1:]))


def leg_dist(dist: Sequence[Sequence[int]], i: int, j: int):
    """dist[i][j] when both endpoints are valid locations, else None.

    Keeps the checker from crashing on routes with out-of-range destination
    IDs; the bad IDs are reported as a violation in validate_route.
    """
    n = len(dist) - 1
    if 0 <= i <= n and 0 <= j <= n:
        return dist[i][j]
    return None


def build_mermaid(
    n: int,
    dist: Sequence[Sequence[int]],
    penalty: Dict[int, int],
    windows: Dict[int, Tuple[int, int]],
    nofly: Sequence[Tuple[int, int]],
    precedence: Sequence[Tuple[int, int]],
    route: Sequence[int],
    mermaid_view: str,
) -> str:
    if mermaid_view == "ordered":
        return build_mermaid_ordered(dist, route)

    return build_mermaid_full(n, dist, penalty, windows, nofly, precedence, route)


def build_mermaid_ordered(
    dist: Sequence[Sequence[int]],
    route: Sequence[int],
) -> str:
    lines: List[str] = []
    lines.append("%%{init: {'theme':'base'}}%%")
    lines.append("flowchart LR")

    if not route:
        lines.append('  N0["0 Depot"]')
        lines.append("  class N0 depot;")
        lines.append('  I["No served destinations in route"]')
        lines.append("  N0 --> I")
        lines.append("  classDef depot fill:#0EA5E9,stroke:#0C4A6E,stroke-width:2px;")
        return "\n".join(lines) + "\n"

    full = [0] + list(route)

    for node in full:
        if node == 0:
            lines.append('  N0["0 Depot"]')
        else:
            lines.append(f'  N{node}["{node}"]')

    for a, b in zip(full, full[1:]):
        d = leg_dist(dist, a, b)
        lines.append(f"  N{a} -->|{d if d is not None else '?'}| N{b}")

    last = route[-1]
    dret = leg_dist(dist, last, 0)
    lines.append(f"  N{last} -. return {dret if dret is not None else '?'} .-> N0")

    dest_nodes = ",".join([f"N{i}" for i in route])
    lines.append("  class N0 depot;")
    if dest_nodes:
        lines.append(f"  class {dest_nodes} destination;")

    lines.append("  classDef depot fill:#0EA5E9,stroke:#0C4A6E,stroke-width:2px;")
    lines.append("  classDef destination fill:#1F2937,stroke:#334155,stroke-width:1.5px;")

    seq_count = max(len(full) - 1, 0)
    if seq_count > 0:
        lines.append(
            "  linkStyle "
            + ",".join(str(i) for i in range(seq_count))
            + " stroke:#22D3EE,stroke-width:3px;"
        )
        lines.append(
            f"  linkStyle {seq_count} stroke:#A78BFA,stroke-width:2px,stroke-dasharray:6,3;"
        )

    return "\n".join(lines) + "\n"


def build_mermaid_full(
    n: int,
    dist: Sequence[Sequence[int]],
    penalty: Dict[int, int],
    windows: Dict[int, Tuple[int, int]],
    nofly: Sequence[Tuple[int, int]],
    precedence: Sequence[Tuple[int, int]],
    route: Sequence[int],
) -> str:
    route_set = set(route_legs(route))
    nofly_set = set(nofly)
    route_links: List[int] = []
    nofly_links: List[int] = []
    precedence_links: List[int] = []
    link_idx = 0

    lines: List[str] = []
    lines.append("%%{init: {'theme':'base'}}%%")
    lines.append("flowchart LR")

    lines.append('  N0["0 Depot"]')
    for i in range(1, n + 1):
        a, b = windows[i]
        lines.append(f'  N{i}["{i} | w={penalty[i]} | [{a},{b}]"]')

    dest_nodes = ",".join([f"N{i}" for i in range(1, n + 1)])
    lines.append("  class N0 depot;")
    if dest_nodes:
        lines.append(f"  class {dest_nodes} destination;")

    for i in range(0, n + 1):
        for j in range(0, n + 1):
            if i == j or (i, j) in nofly_set:
                continue
            lines.append(f"  N{i} -->|{dist[i][j]}| N{j}")
            if (i, j) in route_set:
                route_links.append(link_idx)
            link_idx += 1

    for i, j in nofly:
        lines.append(f"  N{i} -. X .-> N{j}")
        nofly_links.append(link_idx)
        link_idx += 1

    for a, b in precedence:
        lines.append(f"  N{a} -. before .-> N{b}")
        precedence_links.append(link_idx)
        link_idx += 1

    lines.append("  classDef depot fill:#0EA5E9,stroke:#0C4A6E,stroke-width:2px;")
    lines.append("  classDef destination fill:#1F2937,stroke:#334155,stroke-width:1.5px;")
    if route_links:
        lines.append(
            "  linkStyle "
            + ",".join(map(str, route_links))
            + " stroke:#22D3EE,stroke-width:3px;"
        )
    if nofly_links:
        lines.append(
            "  linkStyle "
            + ",".join(map(str, nofly_links))
            + " stroke:#F43F5E,stroke-width:2px;"
        )
    if precedence_links:
        lines.append(
            "  linkStyle "
            + ",".join(map(str, precedence_links))
            + " stroke:#A78BFA,stroke-width:2px,stroke-dasharray:6,3;"
        )

    return "\n".join(lines) + "\n"


def sanitize_ascii(text: str) -> str:
    return "".join(ch for ch in text if ord(ch) < 128)


def arrivals(dist: Sequence[Sequence[int]], route: Sequence[int]) -> Dict[int, int]:
    """Distance flown from the depot when the route reaches each destination."""
    acc, prev, arr = 0, 0, {}
    for c in route:
        d = leg_dist(dist, prev, c)
        acc += d if d is not None and d >= 0 else 0
        arr[c] = acc
        prev = c
    return arr


def compute_cost(
    n: int,
    dist: Sequence[Sequence[int]],
    penalty: Dict[int, int],
    route: Sequence[int],
) -> Tuple[int, int, int]:
    served = set(route)
    skip_pen = sum(penalty[i] for i in range(1, n + 1) if i not in served)
    # Forbidden legs (negative dist) never count as energy; using one is caught
    # as a violation in validate_route. Out-of-range legs are skipped (None).
    energy = sum(d for i, j in route_legs(route)
                 if (d := leg_dist(dist, i, j)) is not None and d >= 0)
    return energy + skip_pen, energy, skip_pen


def validate_route(
    n: int,
    B: int,
    dist: Sequence[Sequence[int]],
    windows: Dict[int, Tuple[int, int]],
    nofly: Sequence[Tuple[int, int]],
    precedence: Sequence[Tuple[int, int]],
    deadline: Dict[int, int],
    route: Sequence[int],
) -> List[str]:
    warnings: List[str] = []

    if len(set(route)) != len(route):
        warnings.append("Route repeats destinations")

    out_of_range = [x for x in route if x < 1 or x > n]
    if out_of_range:
        warnings.append(f"Invalid destination IDs in route: {out_of_range}")

    nofly_set = set(nofly)
    used_nofly = [leg for leg in route_legs(route) if leg in nofly_set]
    if used_nofly:
        legs_txt = ", ".join(f"{i}->{j}" for i, j in used_nofly)
        warnings.append(f"Restricted leg(s): {legs_txt}")

    for pos, c in enumerate(route, start=1):
        if c in windows:
            a, b = windows[c]
            if not (a <= pos <= b):
                warnings.append(
                    f"Window at destination {c}: position {pos} not in [{a}, {b}]"
                )

    pos_map = {c: i for i, c in enumerate(route)}
    bad_prec = [(a, b) for a, b in precedence
                if a in pos_map and b in pos_map and pos_map[a] >= pos_map[b]]
    if bad_prec:
        prec_txt = ", ".join(f"{a}<<{b}" for a, b in bad_prec)
        warnings.append(f"Precedence: {prec_txt}")

    energy = sum(d for i, j in route_legs(route)
                 if (d := leg_dist(dist, i, j)) is not None and d >= 0)
    if energy > B:
        warnings.append(f"Battery: {energy} (max {B})")

    arr = arrivals(dist, route)
    late = [(c, arr[c], d) for c, d in sorted(deadline.items()) if c in arr and arr[c] > d]
    if late:
        late_txt = ", ".join(f"destination {c} reached after {a} (max {d})" for c, a, d in late)
        warnings.append(f"Deadline: {late_txt}")

    return warnings


def build_summary_markdown(
    n: int,
    B: int,
    dist: Sequence[Sequence[int]],
    penalty: Dict[int, int],
    windows: Dict[int, Tuple[int, int]],
    nofly: Sequence[Tuple[int, int]],
    precedence: Sequence[Tuple[int, int]],
    deadline: Dict[int, int],
    route: Sequence[int],
    reported_cost: int = None,
) -> str:
    total, energy, skip_pen = compute_cost(n, dist, penalty, route)
    violations = validate_route(n, B, dist, windows, nofly, precedence, deadline, route)
    energy_ok = energy <= B

    if energy_ok:
        energy_text = (
            f"<span style=\"color:#2E7D32\"><strong>{energy}</strong>({B})</span>"
        )
    else:
        energy_text = (
            f"<span style=\"color:#C62828\"><strong>{energy}</strong>({B})</span>"
        )

    lines: List[str] = []
    lines.append("")
    lines.append("### Route Summary")
    lines.append(f"- Route: {' '.join(map(str, route)) if route else '(empty)'}")
    lines.append(
        "- Cost | Energy(B) | Penalties: "
        f"<strong>{total}</strong> | {energy_text} | {skip_pen}"
    )
    if reported_cost is not None:
        lines.append(f"- Total cost (solution file): {reported_cost}")
        if reported_cost != total:
            lines.append("- Cost mismatch: computed total differs from solution file total")

    if deadline:
        arr = arrivals(dist, route)
        lines.append("- Deadlines (flown / max): " + ", ".join(
            f"{c}: {arr[c]}/{d}" if c in arr else f"{c}: not served"
            for c, d in sorted(deadline.items())))
    if violations:
        lines.append('- Constraints: <span style="color:#C62828"><strong>VIOLATIONS</strong></span>')
        for v in violations:
            lines.append(f"  - {v}")
    else:
        lines.append('- Constraints: <span style="color:#2E7D32"><strong>OK</strong></span> (no violations detected)')

    lines.append("")
    return "\n".join(lines)


def build_checker_report(
    n: int,
    B: int,
    dist: Sequence[Sequence[int]],
    penalty: Dict[int, int],
    windows: Dict[int, Tuple[int, int]],
    nofly: Sequence[Tuple[int, int]],
    precedence: Sequence[Tuple[int, int]],
    deadline: Dict[int, int],
    route: Sequence[int],
    reported_cost: int = None,
) -> Tuple[str, bool]:
    """Plain-text verdict for use as a checker. Returns (text, ok)."""
    total, energy, skip_pen = compute_cost(n, dist, penalty, route)
    violations = validate_route(n, B, dist, windows, nofly, precedence, deadline, route)
    if reported_cost is not None and reported_cost != total:
        violations.append(
            f"Cost mismatch: solution reports {reported_cost}, recomputed {total}."
        )

    # P2: the verdict comes first (OK or INVALID); the list of violations, if any, at the end.
    lines: List[str] = ["INVALID" if violations else "OK"]
    lines.append(f"Route: {' '.join(map(str, route)) if route else '(empty)'}")
    lines.append(f"Cost: {total}  (energy {energy}/{B}, penalties {skip_pen})")
    if deadline:
        arr = arrivals(dist, route)
        lines.append("Deadlines: " + ", ".join(
            f"{c}: {arr[c]}/{d}" if c in arr else f"{c}: not served"
            for c, d in sorted(deadline.items())))
    if violations:
        lines.append("Violations:")
        for v in violations:
            lines.append(f"  - {v}")

    return "\n".join(lines) + "\n", not violations


def main():
    parser = argparse.ArgumentParser(
        description="Validate a P2 route (P1 + deadlines) against an instance, and optionally render it."
    )
    parser.add_argument("instance", help="Path to instance file (.drn)")
    parser.add_argument("--solution", help="Path to solution file (<cost> <K> + route line)")
    parser.add_argument("--route", help="Route as space-separated destination IDs, e.g., '2 1 3'")
    parser.add_argument("--save", help="Save Mermaid output to a file (.mmd/.md)")
    parser.add_argument(
        "--mermaid-view",
        choices=["full", "ordered"],
        default="full",
        help="Mermaid view: full graph or ordered route sequence",
    )
    args = parser.parse_args()

    n, B, dist, penalty, windows, nofly, precedence, deadline = read_instance(args.instance)

    route: List[int] = []
    reported_cost = None

    if args.solution:
        try:
            reported_cost, _, route = parse_solution(args.solution)
        except (ValueError, OSError) as err:
            # A malformed .out is a failed check, not a crash: clean verdict + exit 1.
            print("INVALID")
            print("Violations:")
            print(f"  - Malformed solution file: {err}")
            raise SystemExit(1)

    if args.route is not None:
        route = parse_route_text(args.route)

    if args.save:
        # Full visual report (Mermaid + Markdown summary) to the given .md/.mmd file.
        mermaid = sanitize_ascii(
            build_mermaid(
                n=n,
                dist=dist,
                penalty=penalty,
                windows=windows,
                nofly=nofly,
                precedence=precedence,
                route=route,
                mermaid_view=args.mermaid_view,
            )
        )
        summary_md = build_summary_markdown(
            n=n,
            B=B,
            dist=dist,
            penalty=penalty,
            windows=windows,
            nofly=nofly,
            precedence=precedence,
            deadline=deadline,
            route=route,
            reported_cost=reported_cost,
        )
        with open(args.save, "w", encoding="utf-8") as f:
            f.write("```mermaid\n")
            f.write(mermaid)
            f.write("```\n")
            f.write(summary_md)
    else:
        # Checker mode: plain-text verdict, non-zero exit on any violation.
        report, ok = build_checker_report(
            n=n,
            B=B,
            dist=dist,
            penalty=penalty,
            windows=windows,
            nofly=nofly,
            precedence=precedence,
            deadline=deadline,
            route=route,
            reported_cost=reported_cost,
        )
        print(report, end="")
        raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
