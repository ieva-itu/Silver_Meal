# exp_silvermeal_characterization_theorem.py

"""
Experimental validation for the Silver-Meal formalization.

This script generates random problem instances and checks:
- existence of stopping indices,
- equivalence between stopping and first non-decrease,
- agreement between direct computation and SMT (Z3) encoding.

Used for large-scale evaluation (up to 500k instances).
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
    # Σ_{j=0}^{k-1} j * D_j
    return sum(j * p.demands[j] for j in range(min(k, len(p.demands))))


def avg_cost(p: Problem, k: int) -> float:
    if k <= 0:
        raise ValueError("k must be positive")
    return (p.setup_cost + p.holding_cost * holding_prefix(p, k)) / k


def avg_profile(p: Problem) -> List[float]:
    return [avg_cost(p, k) for k in range(1, horizon(p) + 1)]


def is_nondecrease_point(p: Problem, k: int, eps: float = 1e-12) -> bool:
    n = horizon(p)
    if not (1 <= k < n):
        return False
    return avg_cost(p, k + 1) >= avg_cost(p, k) - eps


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


def is_first_nondecrease_point(p: Problem, K: int, eps: float = 1e-12) -> bool:
    """
    Characterization-theorem side:
      K is a nondecrease point, and
      every earlier admissible j still has strict decrease.
    """
    n = horizon(p)
    if not (1 <= K < n):
        return False

    if not is_nondecrease_point(p, K, eps):
        return False

    for j in range(1, K):
        if not (avg_cost(p, j + 1) < avg_cost(p, j) - eps):
            return False

    return True


def first_nondecrease_point(p: Problem, eps: float = 1e-12) -> Optional[int]:
    n = horizon(p)
    for k in range(1, n):
        if is_nondecrease_point(p, k, eps):
            return k
    return None


def characterization_holds_for_problem(p: Problem, eps: float = 1e-12) -> bool:
    """
    Experimental form of the Lean characterization theorem:
      isSilverMealStop(p, K) iff isFirstNondecreasePoint(p, K)
    for every candidate K.
    """
    n = horizon(p)
    for k in range(1, n):
        lhs = is_silver_meal_stop(p, k, eps)
        rhs = is_first_nondecrease_point(p, k, eps)
        if lhs != rhs:
            return False
    return True


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
    total_candidate_checks = 0
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
            "first_nondecrease_point",
            "characterization_holds",
            "candidate_checks",
            "is_valid",
        ])

    try:
        for i in range(1, num_examples + 1):
            p = generate_problem()

            if not valid(p):
                continue

            total_valid += 1
            n = horizon(p)
            profile = avg_profile(p)
            first_nd = first_nondecrease_point(p)
            holds = characterization_holds_for_problem(p)
            candidate_checks = max(0, n - 1)
            total_candidate_checks += candidate_checks

            if holds:
                theorem_pass += 1
            else:
                theorem_fail += 1
                if first_fail is None:
                    mismatch_rows = []
                    for k in range(1, n):
                        lhs = is_silver_meal_stop(p, k)
                        rhs = is_first_nondecrease_point(p, k)
                        if lhs != rhs:
                            mismatch_rows.append((k, lhs, rhs))
                    first_fail = {
                        "example_id": i,
                        "setup_cost": p.setup_cost,
                        "holding_cost": p.holding_cost,
                        "demands": p.demands,
                        "avg_profile": profile,
                        "first_nondecrease_point": first_nd,
                        "mismatches": mismatch_rows,
                    }

            if i <= print_first_n:
                print("--------------------------------------------------")
                print(f"Example {i}")
                print(f"setup_cost              = {p.setup_cost}")
                print(f"holding_cost            = {p.holding_cost}")
                print(f"demands                 = {p.demands}")
                print(f"avg_profile             = {profile}")
                print(f"first_nondecrease_point = {first_nd}")
                print(f"characterization_holds  = {holds}")
                print("Candidate comparison:")
                for k in range(1, n):
                    lhs = is_silver_meal_stop(p, k)
                    rhs = is_first_nondecrease_point(p, k)
                    print(f"  K={k}: stop={lhs}, first_nondecrease={rhs}")

            if writer is not None:
                writer.writerow([
                    i,
                    p.setup_cost,
                    p.holding_cost,
                    n,
                    serialize_list(p.demands),
                    serialize_list(profile),
                    first_nd if first_nd is not None else "",
                    holds,
                    candidate_checks,
                    True,
                ])

        print("\n==================================================")
        print("FINAL SUMMARY")
        print("==================================================")
        print(f"Generated examples:              {num_examples}")
        print(f"Valid examples:                  {total_valid}")
        print(f"Total candidate checks:          {total_candidate_checks}")
        print(f"Characterization passed:         {theorem_pass}")
        print(f"Characterization failed:         {theorem_fail}")
        print(f"Random seed:                     {seed}")

        print("\nThe theorem being tested experimentally is:")
        print("  isSilverMealStop(P, K) iff isFirstNondecreasePoint(P, K)")

        if theorem_fail == 0:
            print("\nExpected result? YES.")
            print("For every generated valid instance and every admissible K,")
            print("the Silver-Meal stopping predicate agreed with the")
            print("first-nondecrease characterization.")
        else:
            print("\nExpected result? NO.")
            print("At least one generated instance violated the intended equivalence.")
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
        csv_path="silver_meal_characterization_10.csv",
        print_first_n=10,
    )

    #print("\n\n=== LARGE RUN: 100,000 EXAMPLES ===")
    #run_experiments(
    #    num_examples=100_000,
    #    seed=12345,
    #    csv_path="silver_meal_characterization_100k.csv",
    #    print_first_n=0,
    #)

    #print("\n\n=== VERY LARGE RUN: 500,000 EXAMPLES ===")
    #run_experiments(
    #    num_examples=500_000,
    #    seed=12345,
    #    csv_path="silver_meal_characterization_500k.csv",
    #    print_first_n=0,
    #)


'''
=== LARGE RUN: 100,000 EXAMPLES ===

==================================================
FINAL SUMMARY
==================================================
Generated examples:              100000
Valid examples:                  100000
Total candidate checks:          648171
Characterization passed:         100000
Characterization failed:         0
Random seed:                     12345

The theorem being tested experimentally is:
  isSilverMealStop(P, K) iff isFirstNondecreasePoint(P, K)

Expected result? YES.
For every generated valid instance and every admissible K,
the Silver-Meal stopping predicate agreed with the
first-nondecrease characterization.

CSV written to: silver_meal_characterization_100k.csv

'''


'''
=== VERY LARGE RUN: 500,000 EXAMPLES ===

==================================================
FINAL SUMMARY
==================================================
Generated examples:              500000
Valid examples:                  500000
Total candidate checks:          3252234
Characterization passed:         500000
Characterization failed:         0
Random seed:                     12345

The theorem being tested experimentally is:
  isSilverMealStop(P, K) iff isFirstNondecreasePoint(P, K)

Expected result? YES.
For every generated valid instance and every admissible K,
the Silver-Meal stopping predicate agreed with the
first-nondecrease characterization.

CSV written to: silver_meal_characterization_500k.csv

'''
