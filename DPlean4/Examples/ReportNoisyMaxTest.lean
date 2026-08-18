/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.ReportNoisyMax
import DPlean4.Basic.Adjacency

/-!
# Report Noisy Max: Paper Examples

This file demonstrates the Report Noisy Max mechanism from
Dwork & Roth (2014), Section 3.3.

## Examples

* `histogram_bin_select`: Privately select the largest bin in a histogram
* `best_query_select_3`: Select the best of 3 queries with ε-DP
* `reportNoisyMax_monotone`: DP monotonicity for Report Noisy Max
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open scoped NNReal

variable {α : Type*}

-- ============================================================================
-- Sensitivity proofs for query collections
-- ============================================================================

/-- Each coordinate of a counting histogram has sensitivity 1 under add/remove.
    A histogram counts elements matching each predicate, so adding/removing
    one element changes each bin by at most 1. -/
private theorem histogramBin_sens (ps : Fin n → α → Bool) (i : Fin n) :
    HasL1Sensitivity ListHeadAddRemove
      (fun (l : List α) => (l.countP (ps i) : ℝ)) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj
  simp only [NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]
    simp only [List.countP_cons]
    split <;> simp [Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]
    simp only [List.countP_cons]
    split <;> simp [Nat.cast_add, Nat.cast_one]

-- ============================================================================
-- Example 1: Private histogram bin selection
-- ============================================================================

/-- **Privately select the most popular histogram bin.**

    Given n predicates defining histogram bins, this mechanism privately
    selects which bin has the highest count. Since each bin count has
    sensitivity 1, Report Noisy Max gives ε-DP — much better than the
    nε bound from computing all counts and postprocessing.

    Application: survey analysis, demographic selection, feature selection. -/
theorem histogram_bin_select (ps : Fin n → α → Bool) [Nonempty (Fin n)]
    (ε : NNReal) :
    IsPureDP ListHeadAddRemove
      (reportNoisyMax (fun i (l : List α) => (l.countP (ps i) : ℝ)) ε 1)
      ε :=
  reportNoisyMax_isPureDP (by norm_num : (0 : ℝ) < 1) (histogramBin_sens ps)

-- ============================================================================
-- Example 2: Best of 3 queries
-- ============================================================================

/-- Three fixed counting queries (length, doubled length, tripled length)
    each with sensitivity 1 under add/remove. -/
private def threeQueries : Fin 3 → List α → ℝ :=
  ![fun l => (l.length : ℝ),
    fun l => (l.length : ℝ) + 1,
    fun l => (l.length : ℝ) - 1]

private theorem threeQueries_sens (i : Fin 3) :
    HasL1Sensitivity ListHeadAddRemove (threeQueries (α := α) i) (↑(1 : ℝ≥0)) := by
  fin_cases i <;> {
    intro l₁ l₂ hadj
    simp only [threeQueries, NNReal.coe_one, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.head_cons]
    obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj <;>
      rw [h.1, h.2] <;>
      simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  }

/-- **Select the best of 3 queries, ε-DP.**

    Demonstrates Report Noisy Max with a small, concrete query set. -/
theorem best_query_select_3 (ε : NNReal) :
    IsPureDP ListHeadAddRemove
      (reportNoisyMax (threeQueries (α := α)) ε 1)
      ε :=
  reportNoisyMax_isPureDP (by norm_num : (0 : ℝ) < 1) threeQueries_sens

-- ============================================================================
-- Example 3: DP monotonicity
-- ============================================================================

/-- ε-DP Report Noisy Max implies ε'-DP for ε' ≥ ε. -/
theorem reportNoisyMax_monotone (ps : Fin n → α → Bool) [Nonempty (Fin n)]
    {ε₁ ε₂ : NNReal} (hle : ε₁ ≤ ε₂) :
    IsPureDP ListHeadAddRemove
      (reportNoisyMax (fun i (l : List α) => (l.countP (ps i) : ℝ)) ε₁ 1)
      ε₂ :=
  isPureDP_mono (histogram_bin_select ps ε₁) hle

end DPlean4.Examples

end -- noncomputable section
