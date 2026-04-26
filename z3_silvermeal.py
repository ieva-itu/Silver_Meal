'''
# z3_silvermeal.py
#
# Verification-oriented encoding of the Silver-Meal stopping rule.
#
# This mirrors the Lean development:
#
#   inequalityCondition(P, k) :=
#       h * (k^2 * D_k - H(k)) >= C
#
# where
#   H(k) = sum_{j=0}^{k-1} j * D_j
#
# and the theorem states:
#
#   avgCost(k+1) >= avgCost(k)  <->  inequalityCondition(P, k)
#
# This file supports:
#   (1) toy example
#   (2) batch experiments: 10k / 100k / 500k
#
# 
###
Installation:
pip install z3-solver

we used Python 3.8 version and installed:
python3 -m pip uninstall -y Solver z3-solver z3
python3 -m pip install --upgrade pip setuptools wheel
python3 -m pip install "z3-solver==4.9.1.0"

test it (should output "[]"):
python3 -c "from z3 import Solver, RealVal; s = Solver(); print(s)"
###

'''



import csv
import random
import time
from dataclasses import dataclass
from typing import List, Optional
from z3 import Solver, RealVal, Int, And, Or, Not, sat


@dataclass
class Problem:
    setup_cost: float
    holding_cost: float
    demands: List[float]


def horizon(p: Problem) -> int:
    return len(p.demands)


def valid(p: Problem) -> bool:
    return (
        p.setup_cost >= 0
        and p.holding_cost >= 0
        and all(d >= 0 for d in p.demands)
    )


def holding_prefix_py(p: Problem, k: int) -> float:
    """H(k) = sum_{j=0}^{k-1} j * D_j"""
    return sum(j * p.demands[j] for j in range(min(k, len(p.demands))))


def avg_cost_py(p: Problem, k: int) -> float:
    if k <= 0:
        raise ValueError("k must be positive")
    return (p.setup_cost + p.holding_cost * holding_prefix_py(p, k)) / k


def inequality_condition_py(p: Problem, k: int) -> bool:
    """
    Solver-friendly algebraic condition:
        h * (k^2 * D_k - H(k)) >= C
    """
    if not (1 <= k < horizon(p)):
        return False
    hk = holding_prefix_py(p, k)
    lhs = p.holding_cost * (k * k * p.demands[k] - hk)
    return lhs >= p.setup_cost


def is_silver_meal_stop_py(p: Problem, K: int) -> bool:
    """
    Direct Silver-Meal stop predicate:
      1 <= K < n
      for all j < K: A(j+1) < A(j)
      and A(K+1) >= A(K)
    """
    n = horizon(p)
    if not (1 <= K < n):
        return False

    for j in range(1, K):
        if not (avg_cost_py(p, j + 1) < avg_cost_py(p, j)):
            return False

    return avg_cost_py(p, K + 1) >= avg_cost_py(p, K)


def first_nondecrease_py(p: Problem) -> Optional[int]:
    """
    First k such that A(k+1) >= A(k).
    """
    n = horizon(p)
    for k in range(1, n):
        if avg_cost_py(p, k + 1) >= avg_cost_py(p, k):
            return k
    return None


def rational(x: float):
    """
    Z3-friendly exact rational literal from a decimal string.
    """
    return RealVal(str(x))


def inequality_condition_z3_expr(p: Problem, k: int):
    """
    Concrete Z3 Boolean expression for:
        h * (k^2 * D_k - H(k)) >= C
    """
    if not (1 <= k < horizon(p)):
        raise ValueError(f"k must satisfy 1 <= k < horizon, got k={k}")

    C = rational(p.setup_cost)
    h = rational(p.holding_cost)
    Dk = rational(p.demands[k])
    Hk = rational(holding_prefix_py(p, k))
    kk = rational(float(k * k))

    return h * (kk * Dk - Hk) >= C


def strict_decrease_z3_expr(p: Problem, j: int):
    """
    Using the equivalent inequality form:
      A(j+1) < A(j) iff h * (j^2 * D_j - H(j)) < C
    """
    if not (1 <= j < horizon(p)):
        raise ValueError(f"j must satisfy 1 <= j < horizon, got j={j}")

    C = rational(p.setup_cost)
    h = rational(p.holding_cost)
    Dj = rational(p.demands[j])
    Hj = rational(holding_prefix_py(p, j))
    jj = rational(float(j * j))

    return h * (jj * Dj - Hj) < C


def verify_claimed_stop_with_z3(p: Problem, K: int, verbose: bool = True) -> bool:
    """
    Verify that K is a Silver-Meal stop using the solver-friendly condition:
      - for all j < K: strict decrease
      - at K: nondecrease
    """
    n = horizon(p)
    if not (1 <= K < n):
        raise ValueError(f"K must satisfy 1 <= K < {n}, got {K}")

    s = Solver()

    for j in range(1, K):
        s.add(strict_decrease_z3_expr(p, j))

    s.add(inequality_condition_z3_expr(p, K))
    result = s.check()

    if verbose:
        print("=== Z3 verification of claimed stop index ===")
        print(f"K = {K}")
        print(f"Solver result: {result}")
        print(f"Expected from direct computation: {is_silver_meal_stop_py(p, K)}")
        if result == sat:
            print("Interpretation: the finite verification conditions are satisfiable.")
        else:
            print("Interpretation: the claimed stop index does not satisfy the conditions.")

    return result == sat


def refute_claimed_stop_with_z3(p: Problem, K: int, verbose: bool = True) -> bool:
    """
    Check the negation of 'K is a valid stop':
      exists some earlier j with nondecrease
      OR K itself fails nondecrease.
    """
    n = horizon(p)
    if not (1 <= K < n):
        raise ValueError(f"K must satisfy 1 <= K < {n}, got {K}")

    s = Solver()
    bad_clauses = []

    for j in range(1, K):
        bad_clauses.append(Not(strict_decrease_z3_expr(p, j)))

    bad_clauses.append(Not(inequality_condition_z3_expr(p, K)))
    s.add(Or(*bad_clauses))
    result = s.check()

    if verbose:
        print("\n=== Z3 check of negation ===")
        print(f"K = {K}")
        print(f"Solver result: {result}")
        if result == sat:
            print("Interpretation: there is a violation of the Silver-Meal stop conditions.")
        else:
            print("Interpretation: no violation exists for this claimed stop index.")

    return result == sat


def search_stop_index_with_z3(p: Problem, verbose: bool = True) -> Optional[int]:
    """
    Search for some K satisfying the Silver-Meal stop conditions.
    Since horizon is finite, we encode a finite disjunction over candidate K.
    """
    n = horizon(p)
    if n < 2:
        return None

    K = Int("K")
    s = Solver()
    s.add(K >= 1, K < n)

    clauses = []
    for k in range(1, n):
        local_constraints = []
        for j in range(1, k):
            local_constraints.append(strict_decrease_z3_expr(p, j))
        local_constraints.append(inequality_condition_z3_expr(p, k))
        clauses.append(And(K == k, *local_constraints))

    s.add(Or(*clauses))
    result = s.check()

    if verbose:
        print("\n=== Z3 search for a stop index ===")
        print(f"Solver result: {result}")

    if result != sat:
        if verbose:
            print("No stop index exists before the horizon ends.")
        return None

    model = s.model()
    found = model[K].as_long()

    if verbose:
        print(f"Found stop index K = {found}")
        print(f"Direct first nondecrease = {first_nondecrease_py(p)}")
        print(f"Direct stop predicate    = {is_silver_meal_stop_py(p, found)}")

    return found


def print_problem_summary(p: Problem):
    print("=== Problem summary ===")
    print(f"setup_cost   = {p.setup_cost}")
    print(f"holding_cost = {p.holding_cost}")
    print(f"demands      = {p.demands}")
    print("Average-cost profile:")
    for k in range(1, horizon(p) + 1):
        print(f"  A({k}) = {avg_cost_py(p, k)}")
    print("Inequality condition by index:")
    for k in range(1, horizon(p)):
        print(f"  k={k}: {inequality_condition_py(p, k)}")


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


def batch_run(
    num_examples: int,
    seed: int = 12345,
    csv_path: Optional[str] = None,
    print_first_n: int = 0,
) -> None:
    """
    Batch experiment:
      - generate random valid instances
      - compute direct first nondecrease point
      - ask Z3 to search for a stop index
      - compare direct and solver results
      - verify the found/direct K using the solver
    """
    random.seed(seed)

    total = 0
    valid_count = 0
    direct_has_stop = 0
    direct_no_stop = 0
    z3_found_stop = 0
    z3_no_stop = 0
    exact_match = 0
    mismatch = 0
    verification_pass = 0
    verification_fail = 0
    first_mismatch = None

    csv_file = None
    writer = None
    if csv_path is not None:
        csv_file = open(csv_path, "w", newline="", encoding="utf-8")
        writer = csv.writer(csv_file)
        writer.writerow([
            "example_id",
            "setup_cost",
            "holding_cost",
            "horizon",
            "demands",
            "direct_first_nondecrease",
            "z3_found_stop",
            "exact_match",
            "verification_pass",
            "avg_profile",
        ])

    start = time.time()

    try:
        for i in range(1, num_examples + 1):
            total += 1
            p = generate_problem()

            if not valid(p):
                continue

            valid_count += 1
            direct_k = first_nondecrease_py(p)
            z3_k = search_stop_index_with_z3(p, verbose=False)

            if direct_k is None:
                direct_no_stop += 1
            else:
                direct_has_stop += 1

            if z3_k is None:
                z3_no_stop += 1
            else:
                z3_found_stop += 1

            match = (direct_k == z3_k)
            if match:
                exact_match += 1
            else:
                mismatch += 1
                if first_mismatch is None:
                    first_mismatch = {
                        "example_id": i,
                        "problem": p,
                        "direct_first_nondecrease": direct_k,
                        "z3_found_stop": z3_k,
                        "avg_profile": [avg_cost_py(p, k) for k in range(1, horizon(p) + 1)],
                    }

            verified_ok = True
            if direct_k is not None:
                verified_ok = verify_claimed_stop_with_z3(p, direct_k, verbose=False)
            else:
                # If no direct stop exists, Z3 should also fail to find one
                verified_ok = (z3_k is None)

            if verified_ok:
                verification_pass += 1
            else:
                verification_fail += 1

            if i <= print_first_n:
                print("--------------------------------------------------")
                print(f"Example {i}")
                print(f"setup_cost   = {p.setup_cost}")
                print(f"holding_cost = {p.holding_cost}")
                print(f"demands      = {p.demands}")
                print(f"avg_profile  = {[avg_cost_py(p, k) for k in range(1, horizon(p) + 1)]}")
                print(f"direct_first_nondecrease = {direct_k}")
                print(f"z3_found_stop            = {z3_k}")
                print(f"exact_match              = {match}")
                print(f"verification_pass        = {verified_ok}")

            if writer is not None:
                writer.writerow([
                    i,
                    p.setup_cost,
                    p.holding_cost,
                    horizon(p),
                    serialize_list(p.demands),
                    "" if direct_k is None else direct_k,
                    "" if z3_k is None else z3_k,
                    match,
                    verified_ok,
                    serialize_list([avg_cost_py(p, k) for k in range(1, horizon(p) + 1)]),
                ])

    finally:
        if csv_file is not None:
            csv_file.close()

    elapsed = time.time() - start

    print("\n==================================================")
    print("BATCH SUMMARY")
    print("==================================================")
    print(f"Generated examples:         {total}")
    print(f"Valid examples:             {valid_count}")
    print(f"Direct has stop:            {direct_has_stop}")
    print(f"Direct no stop:             {direct_no_stop}")
    print(f"Z3 found stop:              {z3_found_stop}")
    print(f"Z3 no stop:                 {z3_no_stop}")
    print(f"Exact direct/Z3 match:      {exact_match}")
    print(f"Mismatch count:             {mismatch}")
    print(f"Verification pass:          {verification_pass}")
    print(f"Verification fail:          {verification_fail}")
    print(f"Elapsed seconds:            {elapsed:.2f}")
    print(f"Seed:                       {seed}")

    if mismatch == 0 and verification_fail == 0:
        print("\nExpected result? YES.")
        print("The solver-oriented encoding agrees with the direct Silver–Meal computation")
        print("on all tested instances.")
    else:
        print("\nExpected result? NO.")
        print("At least one mismatch or verification failure occurred.")
        if first_mismatch is not None:
            print("\nFirst mismatch:")
            print(f"example_id              = {first_mismatch['example_id']}")
            p = first_mismatch["problem"]
            print(f"setup_cost              = {p.setup_cost}")
            print(f"holding_cost            = {p.holding_cost}")
            print(f"demands                 = {p.demands}")
            print(f"avg_profile             = {first_mismatch['avg_profile']}")
            print(f"direct_first_nondecrease= {first_mismatch['direct_first_nondecrease']}")
            print(f"z3_found_stop           = {first_mismatch['z3_found_stop']}")

    if csv_path is not None:
        print(f"\nCSV written to: {csv_path}")


def toy_example_run():
    p = Problem(
        setup_cost=500.0,
        holding_cost=2.0,
        demands=[100.0, 200.0, 150.0, 250.0],
    )

    if not valid(p):
        raise ValueError("Problem is not valid")

    print_problem_summary(p)

    expected_k = first_nondecrease_py(p)
    print(f"\nDirect first nondecrease point: {expected_k}")

    verify_claimed_stop_with_z3(p, 2, verbose=True)
    refute_claimed_stop_with_z3(p, 2, verbose=True)
    search_stop_index_with_z3(p, verbose=True)


if __name__ == "__main__":
    MODE = "toy"
    # MODE = "10k"
    # MODE = "100k"
    # MODE = "500k"

    if MODE == "toy":
        toy_example_run()

    elif MODE == "10k":
        batch_run(
            num_examples=10_000,
            seed=12345,
            csv_path="silver_meal_z3_10k.csv",
            print_first_n=5,
        )

    elif MODE == "100k":
        batch_run(
            num_examples=100_000,
            seed=12345,
            csv_path="silver_meal_z3_100k.csv",
            print_first_n=0,
        )

    elif MODE == "500k":
        batch_run(
            num_examples=500_000,
            seed=12345,
            csv_path="silver_meal_z3_500k.csv",
            print_first_n=0,
        )

    else:
        raise ValueError(f"Unknown MODE: {MODE}")

'''
TOY EXAMPLE
Output:

=== Problem summary ===
setup_cost   = 500.0
holding_cost = 2.0
demands      = [100.0, 200.0, 150.0, 250.0]
Average-cost profile:
  A(1) = 500.0
  A(2) = 450.0
  A(3) = 500.0
  A(4) = 750.0
Inequality condition by index:
  k=1: False
  k=2: True
  k=3: True

Direct first nondecrease point: 2
=== Z3 verification of claimed stop index ===
K = 2
Solver result: sat
Expected from direct computation: True
Interpretation: the finite verification conditions are satisfiable.

=== Z3 check of negation ===
K = 2
Solver result: unsat
Interpretation: no violation exists for this claimed stop index.

=== Z3 search for a stop index ===
Solver result: sat
Found stop index K = 2
Direct first nondecrease = 2
Direct stop predicate    = True
'''



'''
500k EXAMPLE 
OUTPUT:
$ python3 z3_silvermeal.py 

================================================== 
BATCH SUMMARY
================================================== 
Generated examples:         500000
Valid examples:             500000
Direct has stop:            498147
Direct no stop:             1853
Z3 found stop:              498147
Z3 no stop:                 1853
Exact direct/Z3 match:      500000
Mismatch count:             0
Verification pass:          500000
Verification fail:          0
Elapsed seconds:            64861.28
Seed:                       12345

Expected result? YES.
The solver-oriented encoding agrees with the direct Silver–Meal computation
on all tested instances.

CSV written to: silver_meal_z3_500k.csv

'''


