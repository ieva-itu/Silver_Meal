# exp_silvermeal.py

'''
This file defines the core components of the Silver-Meal heuristic for
dynamic lot-sizing within the Wagner–Whitin setting.

It introduces:
- the problem structure (setup cost, holding cost, demand sequence),
- the planning horizon,
- the weighted prefix sum capturing holding costs,
- the average cost per period A(k), used by the Silver-Meal rule.

These definitions form the basis for subsequent formalization of the
stopping condition, structural properties, and verification-oriented
results developed in later files.
'''


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
    # Σ_{j=0}^{k-1} j * D_j
    return sum(j * p.demands[j] for j in range(min(k, len(p.demands))))


def avg_cost(p: Problem, k: int) -> float:
    if k <= 0:
        raise ValueError("k must be positive")
    return (p.setup_cost + p.holding_cost * holding_prefix(p, k)) / k


def avg_profile(p: Problem) -> List[float]:
    return [avg_cost(p, k) for k in range(1, horizon(p) + 1)]


def first_nondecrease_stop(p: Problem, eps: float = 1e-12) -> Optional[int]:
    """
    Return the first K such that A(K+1) >= A(K), if it exists.
    Otherwise return None.
    """
    n = horizon(p)
    if n < 2:
        return None

    for k in range(1, n):
        if avg_cost(p, k + 1) >= avg_cost(p, k) - eps:
            return k
    return None


def is_silver_meal_stop(p: Problem, K: int, eps: float = 1e-12) -> bool:
    """
    Lean-style predicate:
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


def serialize_demands(demands: List[float]) -> str:
    return ";".join(str(x) for x in demands)


def run_experiments(
    num_examples: int,
    seed: int = 12345,
    csv_path: Optional[str] = None,
    print_first_n: int = 10,
) -> None:
    random.seed(seed)

    total_valid = 0
    stop_found = 0
    no_stop_found = 0
    theorem_holds = 0
    theorem_fails = 0
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
            "first_stop_K",
            "is_valid",
            "theorem_holds",
        ])

    try:
        for i in range(1, num_examples + 1):
            p = generate_problem()

            is_valid = valid(p)
            if not is_valid:
                continue

            total_valid += 1
            profile = avg_profile(p)
            K = first_nondecrease_stop(p)

            if K is None:
                no_stop_found += 1
                holds = True
            else:
                stop_found += 1
                holds = is_silver_meal_stop(p, K)

            if holds:
                theorem_holds += 1
            else:
                theorem_fails += 1
                if first_fail is None:
                    first_fail = (i, p, profile, K)

            if i <= print_first_n:
                print("--------------------------------------------------")
                print(f"Example {i}")
                print(f"setup_cost   = {p.setup_cost}")
                print(f"holding_cost = {p.holding_cost}")
                print(f"demands      = {p.demands}")
                print(f"avg_profile  = {profile}")
                print(f"first_stop_K = {K}")
                print(f"theorem_holds = {holds}")

            if writer is not None:
                writer.writerow([
                    i,
                    p.setup_cost,
                    p.holding_cost,
                    horizon(p),
                    serialize_demands(p.demands),
                    serialize_demands(profile),
                    K if K is not None else "",
                    is_valid,
                    holds,
                ])

        print("\n==================================================")
        print("FINAL SUMMARY")
        print("==================================================")
        print(f"Generated examples:         {num_examples}")
        print(f"Valid examples:             {total_valid}")
        print(f"Examples with stop K:       {stop_found}")
        print(f"Examples with no stop:      {no_stop_found}")
        print(f"Theorem check passed:       {theorem_holds}")
        print(f"Theorem check failed:       {theorem_fails}")
        print(f"Random seed:                {seed}")

        if theorem_fails == 0:
            print("\nExpected result? YES.")
            print("For all generated valid instances, the first non-decrease point")
            print("satisfied the Silver-Meal stopping condition.")
        else:
            print("\nExpected result? NO.")
            print("At least one instance failed the intended theorem-style check.")
            fail_id, p, profile, K = first_fail
            print("\nFirst failing example:")
            print(f"example_id    = {fail_id}")
            print(f"setup_cost    = {p.setup_cost}")
            print(f"holding_cost  = {p.holding_cost}")
            print(f"demands       = {p.demands}")
            print(f"avg_profile   = {profile}")
            print(f"first_stop_K  = {K}")

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
        csv_path="silver_meal_10.csv",
        print_first_n=10,
    )

    #print("\n\n=== LARGE RUN: 100,000 EXAMPLES ===")
    #run_experiments(
    #    num_examples=100_000,
    #    seed=12345,
    #    csv_path="silver_meal_100k.csv",
    #    print_first_n=0,
    #)

    # Large option:
    # print("\n\n=== VERY LARGE RUN: 500,000 EXAMPLES ===")
    # run_experiments(
    #     num_examples=500_000,
    #     seed=12345,
    #     csv_path="silver_meal_500k.csv",
    #     print_first_n=0,
    # )
'''
=== VERY LARGE RUN: 500,000 EXAMPLES ===

==================================================
FINAL SUMMARY
==================================================
Generated examples:         500000
Valid examples:             500000
Examples with stop K:       498147
Examples with no stop:      1853
Theorem check passed:       500000
Theorem check failed:       0
Random seed:                12345

Expected result? YES.
For all generated valid instances, the first non-decrease point
satisfied the Silver-Meal stopping condition.

CSV written to: silver_meal_500k.csv

'''
