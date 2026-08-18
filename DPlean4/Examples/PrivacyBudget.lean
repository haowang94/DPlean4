/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Mechanism.Gaussian
import DPlean4.Privacy.Composition
import DPlean4.Privacy.ZCDP
import DPlean4.Basic.Adjacency

/-!
# Privacy Budget Management

This file demonstrates two approaches to answering multiple queries within
a fixed privacy budget:

## Approach 1: Basic Composition (Budget Splitting)

Split the privacy budget ε equally among k queries: each gets ε/k.
By composition, the total is (ε/k)·k = ε. The noise scale per query is k/ε.

## Approach 2: zCDP Accounting

Use Gaussian noise and account via zCDP composition. For k queries with
Gaussian noise variance v, each step is ρ-zCDP with ρ = 1/(2v).
After k steps: k·ρ-zCDP. Convert to (ε,δ)-DP with tight bounds.

The zCDP conversion is `kρ + 2√(kρ log(1/δ))`; both terms must be retained
when selecting the Gaussian variance.

## References

* Dwork & Roth (2014), §3.5: "Composition Theorems"
* Bun & Dwork (2016): "Concentrated Differential Privacy"
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*}

-- ============================================================================
-- Approach 1: Basic composition with Laplace noise
-- ============================================================================

/-- Two counting queries with split budget: each gets ε/2, total is ε. -/
theorem two_queries_split_budget {ε : ℝ≥0} (hε : ε ≠ 0) :
    IsPureDP ListHeadAddRemove
      ((laplaceMech (D := List α) (fun l => (l.length : ℝ)) 1 (ε / 2)).prod
       (laplaceMech (D := List α) (fun l => (l.length : ℝ)) 1 (ε / 2)))
      (ε / 2 + ε / 2) := by
  apply isPureDP_prod <;> {
    apply laplaceMech_isPureDP
    · exact div_ne_zero hε two_ne_zero
    · intro l₁ l₂ hadj; simp only [NNReal.coe_one]
      obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
      · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
      · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  }

/-- Budget splitting gives back the original budget. -/
theorem split_budget_total {ε : ℝ≥0} : ε / 2 + ε / 2 = ε := by
  ext; push_cast; ring

/-- Three counting queries: each gets ε/3, total is ε.
    Demonstrates nested product composition. -/
theorem three_queries_budget {ε : ℝ≥0} (hε : ε ≠ 0) :
    let q := laplaceMech (D := List α) (fun l => (l.length : ℝ)) 1 (ε / 3)
    IsPureDP ListHeadAddRemove (q.prod (q.prod q)) (ε / 3 + (ε / 3 + ε / 3)) := by
  intro q
  have hε3 : ε / 3 ≠ 0 := div_ne_zero hε (by norm_num)
  have hq : IsPureDP ListHeadAddRemove q (ε / 3) := by
    apply laplaceMech_isPureDP hε3
    intro l₁ l₂ hadj; simp only [NNReal.coe_one]
    obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
    · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
    · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  exact isPureDP_prod hq (isPureDP_prod hq hq)

-- ============================================================================
-- Approach 2: zCDP accounting with Gaussian noise
-- ============================================================================

private def countQuery (l : List α) : ℝ := (l.length : ℝ)

private theorem countQuery_sensitivity :
    HasL1Sensitivity ListHeadAddRemove (countQuery (α := α)) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj; simp only [countQuery, NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]

/-- **zCDP accounting for two Gaussian queries**: total is 2ρ where ρ = 1/(2v).

    This demonstrates the key advantage of zCDP: the privacy parameters
    compose *linearly* in ρ, and the final (ε,δ)-DP conversion gives
    much tighter bounds than basic composition for small ε. -/
theorem two_gaussian_queries_zCDP {v : ℝ≥0} (hv : v ≠ 0) :
    IsZCDP ListHeadAddRemove
      ((gaussianMech (countQuery (α := α)) v).prod
       (gaussianMech (countQuery (α := α)) v))
      ((1 : ℝ≥0) ^ 2 / (2 * v) + (1 : ℝ≥0) ^ 2 / (2 * v)) :=
  isZCDP_prod
    (gaussianMech_isZCDP hv countQuery_sensitivity.toL2)
    (gaussianMech_isZCDP hv countQuery_sensitivity.toL2)

/-- Concrete comparison: with v=2, each Gaussian query is (1/4)-zCDP.
    Two queries compose to (1/2)-zCDP.

    Compare with basic Laplace composition for the same accuracy:
    - Laplace with σ = 2 → each query is (1/2)-DP → total 1-DP
    - Gaussian with v = 2 → each query is (1/4)-zCDP → total (1/2)-zCDP
      → for any ε > 1/2, ∃ δ: (ε,δ)-DP

    The Gaussian+zCDP approach gives (ε,δ)-DP for any ε > 1/2 with
    exponentially small δ, while basic Laplace gives 1-DP (no δ needed,
    but ε is fixed at 1 rather than adjustable). -/
theorem comparison_laplace_vs_gaussian :
    IsPureDP ListHeadAddRemove
      ((laplaceMech (D := List α) (fun l => (l.length : ℝ)) 1 (1/2 : ℝ≥0)).prod
       (laplaceMech (D := List α) (fun l => (l.length : ℝ)) 1 (1/2 : ℝ≥0)))
      ((1/2 : ℝ≥0) + (1/2 : ℝ≥0)) ∧
    IsZCDP ListHeadAddRemove
      ((gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0)).prod
       (gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0)))
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0)) + (1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0))) := by
  constructor
  · apply isPureDP_prod <;> {
      apply laplaceMech_isPureDP (by norm_num : (1/2 : ℝ≥0) ≠ 0)
      intro l₁ l₂ hadj; simp only [NNReal.coe_one]
      obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
      · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
      · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
    }
  · exact two_gaussian_queries_zCDP (by norm_num)

end DPlean4.Examples

end -- noncomputable section
