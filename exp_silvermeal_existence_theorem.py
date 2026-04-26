# exp_silvermeal_existence_theorem.py

"""
Experimental validation of the Silver-Meal existence theorem.

This script generates random lot-sizing instances and checks the following property:
if there exists a non-decrease point (A(k+1) >= A(k)), then the first such point
is a valid Silver-Meal stopping index.

The check is performed over large-scale randomized data (up to 500,000 instances),
with results summarized and optionally exported to CSV.
"""

import csv
import random
from dataclasses import dataclass
from typing import List, Optional


@dataclass
class Problem:
    setup_cost: float
    holding_cost: float
    demands: List[float]


def valid(p: Problem) -> bool:
    return (
        p.setup_cost >= 0
        and p.holding_cost >= 0
        and all(d >= 0 for d in p.demands)
    )


def horizon(p: Problem) -> int:
    return len(p.demands)


def holding_prefix(p: Problem, k: int) -> float:
    """
    Σ_{j=0}^{k-1} j * D_j
    """
    return sum(j * p.demands[j] for j in range(min(k, len(p.demands))))


def avg_cost(p: Problem, k: int) -> float:
    if k <= 0:
        raise ValueError("k must be positive")
    return (p.setup_cost + p.holding_cost * holding_prefix(p, k)) / k


def avg_profile(p: Problem) -> List[float]:
    return [avg_cost(p, k) for k in range(1, horizon(p) + 1)]


def is_nondecrease_point(p: Problem, k: int, eps: float = 1e-12) -> bool:
    """
    Lean-style:
      1 <= k < horizon
      A(k+1) >= A(k)
    """
    n = horizon(p)
    if not (1 <= k < n):
        return False
    return avg_cost(p, k + 1) >= avg_cost(p, k) - eps


def all_nondecrease_points(p: Problem, eps: float = 1e-12) -> List[int]:
    n = horizon(p)
    return [k for k in range(1, n) if is_nondecrease_point(p, k, eps)]


def first_nondecrease_point(p: Problem, eps: float = 1e-12) -> Optional[int]:
    pts = all_nondecrease_points(p, eps)
    return pts[0] if pts else None


def is_silver_meal_stop(p: Problem, K: int, eps: float = 1e-12) -> bool:
    """
    Lean-style:
      1 <= K < horizon
      for all j < K: A(j+1) < A(j)
      and A(K+1) >= A(K)
    """
    n = horizon(p)
    if not (1 <= K < n):
        return False

    for j in range(1, K):
        if not (avg_cost(p, j + 1) < avg_cost(p, j) - eps):
            return False

    return avg_cost(p, K + 1) >= avg_cost(p, K) - eps


def theorem_holds_for_problem(p: Problem, eps: float = 1e-12) -> bool:
    """
    Experimental form of the Lean theorem:

    If there exists any nondecrease point, then the first such point
    is a Silver-Meal stopping point.

    If there is no nondecrease point, the implication is vacuously true.
    """
    nd_points = all_nondecrease_points(p, eps)

    if not nd_points:
        return True

    first_k = nd_points[0]
    return is_silver_meal_stop(p, first_k, eps)


def generate_problem(
    min_horizon: int = 3,
    max_horizon: int = 12,
    max_setup: int = 1000,
    max_holding: int = 20,
    max_demand: int = 500,
) -> Problem:
    n = random.randint(min_horizon, max_horizon)
    return Problem(
        setup_cost=float(random.randint(1, max_setup)),
        holding_cost=float(random.randint(1, max_holding)),
        demands=[float(random.randint(1, max_demand)) for _ in range(n)],
    )


def serialize_list(xs: List[float]) -> str:
    return ";".join(str(x) for x in xs)


def run_experiments(
    num_examples: int,
    seed: int = 12345,
    csv_path: Optional[str] = None,
    print_first_n: int = 10,
) -> None:
    random.seed(seed)

    total_valid = 0
    with_nondecrease = 0
    without_nondecrease = 0
    theorem_pass = 0
    theorem_fail = 0
    first_fail = None

    writer = None
    csv_file = None

    if csv_path is not None:
        csv_file = open(csv_path, "w", newline="", encoding="utf-8")
        writer = csv.writer(csv_file)
        writer.writerow([
            "example_id",
            "setup_cost",
            "holding_cost",
            "horizon",
            "demands",
            "avg_profile",
            "nondecrease_points",
            "first_nondecrease_point",
            "theorem_holds",
            "is_valid",
        ])

    try:
        for i in range(1, num_examples + 1):
            p = generate_problem()

            if not valid(p):
                continue

            total_valid += 1

            profile = avg_profile(p)
            nd_points = all_nondecrease_points(p)
            first_nd = nd_points[0] if nd_points else None
            holds = theorem_holds_for_problem(p)

            if nd_points:
                with_nondecrease += 1
            else:
                without_nondecrease += 1

            if holds:
                theorem_pass += 1
            else:
                theorem_fail += 1
                if first_fail is None:
                    first_fail = {
                        "example_id": i,
                        "setup_cost": p.setup_cost,
                        "holding_cost": p.holding_cost,
                        "demands": p.demands,
                        "avg_profile": profile,
                        "nondecrease_points": nd_points,
                        "first_nondecrease_point": first_nd,
                    }

            if i <= print_first_n:
                print("--------------------------------------------------")
                print(f"Example {i}")
                print(f"setup_cost         = {p.setup_cost}")
                print(f"holding_cost       = {p.holding_cost}")
                print(f"demands            = {p.demands}")
                print(f"avg_profile        = {profile}")
                print(f"nondecrease_points = {nd_points}")
                print(f"first_nondecrease  = {first_nd}")
                print(f"theorem_holds      = {holds}")

            if writer is not None:
                writer.writerow([
                    i,
                    p.setup_cost,
                    p.holding_cost,
                    horizon(p),
                    serialize_list(p.demands),
                    serialize_list(profile),
                    serialize_list([float(k) for k in nd_points]),
                    first_nd if first_nd is not None else "",
                    holds,
                    True,
                ])

        print("\n==================================================")
        print("FINAL SUMMARY")
        print("==================================================")
        print(f"Generated examples:              {num_examples}")
        print(f"Valid examples:                  {total_valid}")
        print(f"With some nondecrease point:     {with_nondecrease}")
        print(f"With no nondecrease point:       {without_nondecrease}")
        print(f"Theorem check passed:            {theorem_pass}")
        print(f"Theorem check failed:            {theorem_fail}")
        print(f"Random seed:                     {seed}")

        print("\nThe theorem being tested experimentally is:")
        print("  If there exists any nondecrease point K with A(K+1) >= A(K),")
        print("  then the first such point is a Silver-Meal stopping point.")

        if theorem_fail == 0:
            print("\nExpected result? YES.")
            print("All generated valid instances satisfied the theorem.")
            print("When no nondecrease point existed, the implication was vacuously true.")
        else:
            print("\nExpected result? NO.")
            print("At least one generated instance violated the intended theorem.")
            print("\nFirst failing example:")
            for k, v in first_fail.items():
                print(f"{k}: {v}")

        if csv_path is not None:
            print(f"\nCSV written to: {csv_path}")

    finally:
        if csv_file is not None:
            csv_file.close()


if __name__ == "__main__":
    print("=== SMALL READABLE RUN: 10 EXAMPLES ===")
    run_experiments(
        num_examples=10,
        seed=12345,
        csv_path="silver_meal_existence_10.csv",
        print_first_n=10,
    )

    #print("\n\n=== LARGE RUN: 100,000 EXAMPLES ===")
    #run_experiments(
    #    num_examples=100_000,
    #    seed=12345,
    #    csv_path="silver_meal_existence_100k.csv",
    #    print_first_n=0,
    #)

    #print("\n\n=== VERY LARGE RUN: 500,000 EXAMPLES ===")
    #run_experiments(
    #    num_examples=500_000,
    #    seed=12345,
    #    csv_path="silver_meal_existence_500k.csv",
    #    print_first_n=0,
    #)
'''
=== VERY LARGE RUN: 500,000 EXAMPLES ===

==================================================
FINAL SUMMARY
==================================================
Generated examples:              500000
Valid examples:                  500000
With some nondecrease point:     498147
With no nondecrease point:       1853
Theorem check passed:            500000
Theorem check failed:            0
Random seed:                     12345

The theorem being tested experimentally is:
  If there exists any nondecrease point K with A(K+1) >= A(K),
  then the first such point is a Silver-Meal stopping point.

Expected result? YES.
All generated valid instances satisfied the theorem.
When no nondecrease point existed, the implication was vacuously true.

CSV written to: silver_meal_existence_500k.csv
'''
