/-
SilverMeal.lean

A self-contained Lean 4 formalization of the Silver-Meal stopping rule.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace WagnerWhitin
namespace SilverMeal

noncomputable section

/-- Parameters of a Silver-Meal instance. -/
structure Problem where
  setupCost : ℝ
  holdingCost : ℝ
  demands     : List ℝ

/-- Planning horizon. -/
def horizon (P : Problem) : ℕ :=
  P.demands.length

/--
Auxiliary recursive weighted prefix sum.

`holdingPrefixAux ds k i` means:
take the first `k` demands from `ds`, starting with time-index `i`,
and compute Σ (time-index) * demand.
-/
def holdingPrefixAux : List ℝ → ℕ → ℕ → ℝ
  | _, 0, _ => 0
  | [], _ + 1, _ => 0
  | d :: ds, k + 1, i => (i : ℝ) * d + holdingPrefixAux ds k (i + 1)

/-- Prefix holding term Σ_{j=0}^{k-1} j * D_j. -/
def holdingPrefix (P : Problem) (k : ℕ) : ℝ :=
  holdingPrefixAux P.demands k 0

/-- Average cost per covered period:
    A(k) = (C + h * holdingPrefix(k)) / k. -/
def avgCost (P : Problem) (k : ℕ) : ℝ :=
  (P.setupCost + P.holdingCost * holdingPrefix P k) / (k : ℝ)

/--
Optional well-formedness predicate.
This is not needed to make the example compute, but it expresses the usual
inventory-theoretic assumptions: nonnegative costs and nonnegative demands.
-/
def Valid (P : Problem) : Prop :=
  0 ≤ P.setupCost ∧
  0 ≤ P.holdingCost ∧
  ∀ d ∈ P.demands, 0 ≤ d

/-- `K` is a Silver-Meal stopping index if:
    - `1 ≤ K < horizon`
    - for every earlier `j < K`, average cost strictly decreases
    - at `K`, extending one more period does not decrease average cost. -/
def isSilverMealStop (P : Problem) (K : ℕ) : Prop :=
  1 ≤ K ∧
  K < horizon P ∧
  (∀ j : ℕ, 1 ≤ j → j < K → avgCost P (j + 1) < avgCost P j) ∧
  avgCost P (K + 1) ≥ avgCost P K

/-- Generic constructor theorem:
    if the defining Silver-Meal inequalities hold, then `K` is a stop. -/
theorem first_nondecrease_is_stop
    (P : Problem) (K : ℕ)
    (hK1 : 1 ≤ K)
    (hKh : K < horizon P)
    (hdec : ∀ j : ℕ, 1 ≤ j → j < K → avgCost P (j + 1) < avgCost P j)
    (hstop : avgCost P (K + 1) ≥ avgCost P K) :
    isSilverMealStop P K := by
  exact ⟨hK1, hKh, hdec, hstop⟩

/-- Example instance:
    C = 500, h = 2, demands = [100, 200, 150, 250]. -/
def exampleProblem : Problem :=
  { setupCost := 500
    holdingCost := 2
    demands := [100, 200, 150, 250] }

example : horizon exampleProblem = 4 := by
  rfl

example : Valid exampleProblem := by
  constructor
  · norm_num [exampleProblem]
  · constructor
    · norm_num [exampleProblem]
    · intro d hd
      simp [exampleProblem] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> norm_num

/-- Concrete prefix values:
    holdingPrefix 1 = 0
    holdingPrefix 2 = 200
    holdingPrefix 3 = 500
    holdingPrefix 4 = 1250 -/
example : holdingPrefix exampleProblem 1 = 0 := by
  norm_num [holdingPrefix, holdingPrefixAux, exampleProblem]

example : holdingPrefix exampleProblem 2 = 200 := by
  norm_num [holdingPrefix, holdingPrefixAux, exampleProblem]

example : holdingPrefix exampleProblem 3 = 500 := by
  norm_num [holdingPrefix, holdingPrefixAux, exampleProblem]

example : holdingPrefix exampleProblem 4 = 1250 := by
  norm_num [holdingPrefix, holdingPrefixAux, exampleProblem]

/-- Average-cost values:
    A(1)=500, A(2)=450, A(3)=500, A(4)=750. -/
example : avgCost exampleProblem 1 = 500 := by
  norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

example : avgCost exampleProblem 2 = 450 := by
  norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

example : avgCost exampleProblem 3 = 500 := by
  norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

example : avgCost exampleProblem 4 = 750 := by
  norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

/-- Main theorem for the example:
    Silver-Meal stops at K = 2. -/
theorem example_stop_at_two : isSilverMealStop exampleProblem 2 := by
  apply first_nondecrease_is_stop
  · norm_num
  · norm_num [horizon, exampleProblem]
  · intro j hj1 hjlt
    have hj : j = 1 := by omega
    subst hj
    norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]
  · norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

/-- It does not stop at K = 1. -/
theorem example_not_stop_at_one : ¬ isSilverMealStop exampleProblem 1 := by
  intro h
  rcases h with ⟨h1k, hhorizon, hdec, hstop⟩
  norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem] at hstop


/-
####### Existence theorem 
1) in finite-horizon form
2) Existence theorem for Silver-Meal stopping points.
-/

/-- A candidate index where the average cost no longer decreases. -/
def isNondecreasePoint (P : Problem) (K : ℕ) : Prop :=
  1 ≤ K ∧
  K < horizon P ∧
  avgCost P (K + 1) ≥ avgCost P K

/--
If there exists any index `K` at which the average cost stops decreasing,
then the first such index is a Silver-Meal stopping point.
-/
theorem exists_stop_of_exists_nondecrease
    (P : Problem)
    (hex : ∃ K, isNondecreasePoint P K) :
    ∃ K, isSilverMealStop P K := by
  classical
  let K := Nat.find hex
  have hK : isNondecreasePoint P K := Nat.find_spec hex
  rcases hK with ⟨hK1, hKh, hstop⟩
  refine ⟨K, ?_⟩
  refine ⟨hK1, hKh, ?_, hstop⟩
  intro j hj1 hjlt
  have hnot : ¬ avgCost P (j + 1) ≥ avgCost P j := by
    intro hge
    have hle : K ≤ j := by
      apply Nat.find_min' hex
      exact ⟨hj1, lt_trans hjlt hKh, hge⟩
    exact (not_le_of_gt hjlt) hle
  linarith

/--
A corollary with the usual inventory-style validity assumptions.
-/
theorem exists_stop_of_exists_nondecrease_valid
    (P : Problem)
    --(hV : Valid P)
    (hex : ∃ K, isNondecreasePoint P K) :
    ∃ K, isSilverMealStop P K := by
  exact exists_stop_of_exists_nondecrease P hex

/-- In the example, `K = 2` is a nondecrease point. -/
example : isNondecreasePoint exampleProblem 2 := by
  constructor
  · norm_num
  constructor
  · norm_num [horizon, exampleProblem]
  · norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

/-- Therefore the example has a Silver-Meal stopping point. -/
example : ∃ K, isSilverMealStop exampleProblem K := by
  apply exists_stop_of_exists_nondecrease
  refine ⟨2, ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num [horizon, exampleProblem]
  · norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

lemma example_nondecrease_at_two : isNondecreasePoint exampleProblem 2 := by
  constructor
  · norm_num
  constructor
  · norm_num [horizon, exampleProblem]
  · norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

lemma exampleProblem_valid : Valid exampleProblem := by
  constructor
  · norm_num [exampleProblem]
  constructor
  · norm_num [exampleProblem]
  · intro d hd
    simp [exampleProblem] at hd
    rcases hd with rfl | rfl | rfl | rfl
    all_goals norm_num

/-- The existence theorem can also be invoked through `Valid`. -/
example : ∃ K, isSilverMealStop exampleProblem K := by
  apply exists_stop_of_exists_nondecrease
  exact ⟨2, example_nondecrease_at_two⟩

/-
####### End of Existence theorem in finite-horizon form
-/



/-
#######
####### Start of Characterization theorem.
A Silver-Meal stopping index is exactly the first nondecrease point.
-/

/-- `K` is the first nondecrease point if:
    - `K` is a nondecrease point
    - every earlier admissible index still has strict decrease. -/
def isFirstNondecreasePoint (P : Problem) (K : ℕ) : Prop :=
  isNondecreasePoint P K ∧
  (∀ j : ℕ, 1 ≤ j → j < K → avgCost P (j + 1) < avgCost P j)

/--
Characterization theorem:
`K` is a Silver-Meal stopping index if and only if `K` is the first
nondecrease point of the average-cost sequence.
-/
theorem silverMealStop_iff_firstNondecreasePoint
    (P : Problem) (K : ℕ) :
    isSilverMealStop P K ↔ isFirstNondecreasePoint P K := by
  constructor
  · intro h
    rcases h with ⟨hK1, hKh, hdec, hstop⟩
    refine ⟨?_, hdec⟩
    exact ⟨hK1, hKh, hstop⟩
  · intro h
    rcases h with ⟨hnd, hdec⟩
    rcases hnd with ⟨hK1, hKh, hstop⟩
    exact ⟨hK1, hKh, hdec, hstop⟩

/-- A direct constructor from "first nondecrease point" to Silver-Meal stop. -/
theorem firstNondecreasePoint_is_stop
    (P : Problem) (K : ℕ)
    (h : isFirstNondecreasePoint P K) :
    isSilverMealStop P K := by
  exact (silverMealStop_iff_firstNondecreasePoint P K).2 h

/-- A direct constructor from Silver-Meal stop to "first nondecrease point". -/
theorem stop_is_firstNondecreasePoint
    (P : Problem) (K : ℕ)
    (h : isSilverMealStop P K) :
    isFirstNondecreasePoint P K := by
  exact (silverMealStop_iff_firstNondecreasePoint P K).1 h

/-- In the example, `K = 2` is the first nondecrease point. -/
lemma example_first_nondecrease_at_two : isFirstNondecreasePoint exampleProblem 2 := by
  apply (silverMealStop_iff_firstNondecreasePoint exampleProblem 2).1
  exact example_stop_at_two

/-- Conversely, the characterization theorem recovers the Silver-Meal stop. -/
example : isSilverMealStop exampleProblem 2 := by
  apply (silverMealStop_iff_firstNondecreasePoint exampleProblem 2).2
  exact example_first_nondecrease_at_two

/-- So the example identifies `K = 2` exactly as the first nondecrease point. -/
example : isFirstNondecreasePoint exampleProblem 2 ∧ isSilverMealStop exampleProblem 2 := by
  constructor
  · exact example_first_nondecrease_at_two
  · exact example_stop_at_two

/-
#######
####### End of Characterization theorem
-/

/-
#######
#######
####### Start of Silver-Meal as a verification tool.
Verification-oriented encoding of the Silver-Meal nondecrease test.
-/

/-- One-step weighted-prefix recursion:
    H(k+1) = H(k) + k * D_k. -/
lemma holdingPrefixAux_succ (ds : List ℝ) (k i : ℕ) :
    holdingPrefixAux ds (k + 1) i
      = holdingPrefixAux ds k i + ((i + k : ℕ) : ℝ) * ds.getD k 0 := by
  induction ds generalizing k i with
  | nil =>
      cases k <;> simp [holdingPrefixAux]
  | cons d ds ih =>
      cases k with
      | zero =>
          simp [holdingPrefixAux]
      | succ k =>
          simp [holdingPrefixAux, ih,
            add_assoc, add_comm, add_left_comm]

/-- Specialization of the weighted-prefix recursion at index 0:
    holdingPrefix P (k+1) = holdingPrefix P k + k * D_k. -/
lemma holdingPrefix_succ (P : Problem) (k : ℕ) :
    holdingPrefix P (k + 1)
      = holdingPrefix P k + (k : ℝ) * P.demands.getD k 0 := by
  simpa [holdingPrefix] using holdingPrefixAux_succ P.demands k 0

/--
Verification-oriented algebraic encoding of the nondecrease test.

This is the denominator-free inequality corresponding to
`avgCost P (k+1) ≥ avgCost P k`.
-/
def inequalityCondition (P : Problem) (k : ℕ) : Prop :=
  P.holdingCost *
      ((k : ℝ) * ((k : ℝ) * P.demands.getD k 0) - holdingPrefix P k)
    ≥ P.setupCost

/--
Nondecrease is equivalent to the algebraic inequality condition.

For admissible indices `k ≥ 1`:
  avgCost P (k+1) ≥ avgCost P k
iff
  holdingCost * (k^2 * D_k - holdingPrefix P k) ≥ setupCost.
-/
theorem nondecrease_iff_inequality
    (P : Problem) {k : ℕ} (hk : 1 ≤ k) :
    avgCost P (k + 1) ≥ avgCost P k ↔ inequalityCondition P k := by
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  rw [avgCost, avgCost, holdingPrefix_succ]
  unfold inequalityCondition
  constructor
  · intro h
    field_simp [hk_ne, hk1_ne] at h
    norm_num at h ⊢
    ring_nf at h ⊢
    linarith
  · intro h
    field_simp [hk_ne, hk1_ne]
    norm_num at h ⊢
    ring_nf at h ⊢
    linarith

/-- The verification-oriented inequality holds at `k = 2` in the worked example. -/
example : inequalityCondition exampleProblem 2 := by
  norm_num [inequalityCondition, holdingPrefix, holdingPrefixAux, exampleProblem]

/-- In the example, the algebraic inequality exactly matches nondecrease. -/
example : avgCost exampleProblem 3 ≥ avgCost exampleProblem 2
    ↔ inequalityCondition exampleProblem 2 := by
  apply nondecrease_iff_inequality
  norm_num

/--
A solver-friendly restatement of the Silver-Meal stop predicate:
strict decrease before `K`, and the algebraic inequality at `K`.
-/
theorem silverMealStop_iff_verificationCondition
    (P : Problem) {K : ℕ} (hK : 1 ≤ K) :
    isSilverMealStop P K ↔
      (1 ≤ K ∧
       K < horizon P ∧
       (∀ j : ℕ, 1 ≤ j → j < K → avgCost P (j + 1) < avgCost P j) ∧
       inequalityCondition P K) := by
  constructor
  · intro h
    rcases h with ⟨hK1, hKh, hdec, hnd⟩
    refine ⟨hK1, hKh, hdec, ?_⟩
    exact (nondecrease_iff_inequality P hK).1 hnd
  · intro h
    rcases h with ⟨hK1, hKh, hdec, hineq⟩
    refine ⟨hK1, hKh, hdec, ?_⟩
    exact (nondecrease_iff_inequality P hK).2 hineq

/-
#######
#######
####### End of Silver-Meal as a verification tool.
-/

end
end SilverMeal
end WagnerWhitin
