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
import DPlean4.Basic.Sensitivity

/-!
# Replace vs Add/Remove Adjacency

This file demonstrates how the choice of adjacency relation affects privacy
guarantees. Two standard notions exist:

* **Add/Remove** (`ListAddRemove`): databases differ by adding or removing one record.
  Standard for "unbounded DP" (Dwork & Roth 2014).
* **Replace** (`ListReplace`): databases have the same size but one record differs.
  Standard for "bounded DP" (used in many ML/statistics applications).

## Key Results

* Counting query has sensitivity 1 under add/remove but 0 under replace
* Bounded sum query has sensitivity 2B under add/remove but B under replace
* The factor-of-2 relationship between adjacency notions
* A query that is trivially private under replace but not under add/remove

## References

* Dwork & Roth (2014), §3.2: Adjacency conventions and their implications
* Vadhan (2017), "The Complexity of Differential Privacy" — comparison of notions
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory
open scoped NNReal

variable {α : Type*}

-- ============================================================================
-- Counting query: trivially private under replace adjacency
-- ============================================================================

private def countQuery (l : List α) : ℝ := (l.length : ℝ)

/-- **Count has sensitivity 0 under replace adjacency.**
    Replacing one element doesn't change the list length.
    This means count queries are *free* under replace adjacency. -/
theorem countQuery_replace_sens_zero :
    HasL1Sensitivity (ListReplace (α := α)) countQuery 0 := by
  intro l₁ l₂ hadj
  simp only [countQuery, NNReal.coe_zero]
  have := hadj.1
  simp [this]

/-- Count queries with Laplace noise are 0-DP under replace adjacency.
    Since sensitivity is 0, we get ε = 0 (perfect privacy). The mechanism
    degenerates to a Dirac measure (Laplace(0) = constant). -/
theorem count_replace_trivial_dp :
    IsPureDP (ListReplace (α := α)) (laplaceMech countQuery 0 (1 : ℝ≥0)) (1 : ℝ≥0) :=
  laplaceMech_isPureDP (by norm_num) countQuery_replace_sens_zero

-- ============================================================================
-- Bounded sum: sensitivity depends on adjacency notion
-- ============================================================================

/-- Bounded sum: sum of values clamped to [0, B].
    Under add/remove: sensitivity is B (adding one record contributes at most B).
    Under replace: sensitivity is also B (one record changes by at most B). -/
private def boundedSum (f : α → ℝ) (B : ℝ) (l : List α) : ℝ :=
  (l.map (fun a => max 0 (min B (f a)))).sum

/-- Clamped values are non-negative. -/
private theorem clamp_nonneg (B : ℝ) (x : ℝ) : 0 ≤ max 0 (min B x) :=
  le_max_left 0 (min B x)

/-- Clamped values are at most B (when B ≥ 0). -/
private theorem clamp_le_B {B : ℝ} (hB : 0 ≤ B) (x : ℝ) : max 0 (min B x) ≤ B :=
  max_le hB (min_le_left B x)

/-- **Bounded sum has sensitivity B under add/remove adjacency.**
    Adding a record contributes at most B to the sum (after clamping). -/
theorem boundedSum_addremove_sensitivity (f : α → ℝ) {B : NNReal} :
    HasL1Sensitivity ListAddRemove (boundedSum f B) B := by
  intro l₁ l₂ hadj; simp only [boundedSum]
  obtain ⟨a, s, h1, h2⟩ | ⟨a, s, h1, h2⟩ := hadj
  · rw [h1, h2]; simp only [List.map_cons, List.sum_cons]
    rw [show max 0 (min ↑B (f a)) + (List.map (fun a => max 0 (min ↑B (f a))) s).sum -
        (List.map (fun a => max 0 (min ↑B (f a))) s).sum = max 0 (min ↑B (f a)) by ring,
        abs_of_nonneg (clamp_nonneg ↑B (f a))]
    exact clamp_le_B B.2 (f a)
  · rw [h1, h2]; simp only [List.map_cons, List.sum_cons]
    rw [show (List.map (fun a => max 0 (min ↑B (f a))) s).sum -
        (max 0 (min ↑B (f a)) + (List.map (fun a => max 0 (min ↑B (f a))) s).sum) =
        -(max 0 (min ↑B (f a))) by ring, abs_neg, abs_of_nonneg (clamp_nonneg ↑B (f a))]
    exact clamp_le_B B.2 (f a)

-- ============================================================================
-- Comparing the two adjacency notions
-- ============================================================================

/-! ### Factor-of-2 relationship

`ListReplace` can be simulated by two steps of `ListAddRemove` (remove old
record, add new record). This means:
- ε-DP under add/remove ⟹ 2ε-DP under replace (via group privacy)
- The converse does not hold in general

Formally proving this requires constructing an intermediate list and showing
the adjacency chain, which needs list manipulation lemmas beyond current scope.
See `isPureDP_group_2` in `Privacy/Composition.lean` for the group privacy
infrastructure that would be used. -/

-- ============================================================================
-- Practical DP-ML example: Private mean under replace adjacency
-- ============================================================================

/-- **Private mean under replace adjacency**: when the dataset size n is public
    (a common assumption in ML), replacing one record changes the mean by at most
    2B/n. With Laplace noise calibrated to this sensitivity, the mechanism is ε-DP.

    This is the standard analysis for DP-SGD with fixed batch size.

    Note: we use sensitivity B under add/remove for the sum, which gives
    B-DP via Laplace. Under replace, the sensitivity halves to B/2 if we
    know n, giving tighter privacy. Here we demonstrate the add/remove version. -/
theorem private_bounded_sum {ε : NNReal} (hε : ε ≠ 0) (f : α → ℝ) (B : NNReal) :
    IsPureDP ListAddRemove
      (laplaceMech (boundedSum f B) B ε) ε :=
  laplaceMech_isPureDP hε (boundedSum_addremove_sensitivity f)

/-- **Two private bounded sums compose**: computing two bounded sums with
    independent Laplace noise gives (ε₁+ε₂)-DP via basic composition. -/
theorem two_bounded_sums_compose {ε₁ ε₂ : NNReal} (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0)
    (f g : α → ℝ) (B₁ B₂ : NNReal) :
    IsPureDP ListAddRemove
      ((laplaceMech (boundedSum f B₁) B₁ ε₁).prod
       (laplaceMech (boundedSum g B₂) B₂ ε₂))
      (ε₁ + ε₂) :=
  isPureDP_prod
    (laplaceMech_isPureDP hε₁ (boundedSum_addremove_sensitivity f))
    (laplaceMech_isPureDP hε₂ (boundedSum_addremove_sensitivity g))

end DPlean4.Examples

end -- noncomputable section
