/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Privacy.Postprocessing
import DPlean4.Basic.Adjacency

/-!
# Private Mean Estimation

This file demonstrates private mean estimation using the Laplace mechanism
and postprocessing. This is a fundamental DP algorithm appearing in nearly
every DP textbook.

## Two settings

**Private sum (add/remove adjacency).** For variable-length databases under
add/remove adjacency we can privately release a *sum* (sensitivity 1 for
[0,1]-clamped values). We do *not* divide by a size here: under add/remove the
number of records is itself sensitive, so there is no fixed public denominator.

**Private mean (fixed-size / bounded DP).** The textbook mean estimator divides
by the *public* number of records `n`. To model this honestly, the database is a
fixed-size vector `Fin n → α` under **replace-one-record** adjacency (bounded
DP): every admissible input has exactly `n` records, so `n` is a genuine public
constant and dividing the noisy sum by `n` is data-independent postprocessing.
(Dividing a variable-length add/remove sum by a fixed `n` unrelated to the input
length would *not* be a mean — that is exactly the setting we avoid here.)

## Algorithm (Dwork & Roth 2014, Section 3.5.2), fixed-size case

Given `n` records with values clamped to `[0, 1]`:
1. Sum the clamped values (sensitivity 1 under replace-one adjacency)
2. Add Laplace(1/ε) noise to the sum
3. Divide by the public size `n` (measurable postprocessing)

## Main Results

* `private_sum_pureDP`: Summing [0,1]-clamped values + Laplace noise is ε-DP
  (add/remove adjacency)
* `private_fixedSize_sum_pureDP`: Fixed-size clamped sum + Laplace noise is ε-DP
  (replace-one adjacency)
* `private_mean_pureDP`: Dividing the fixed-size sum by `n` is ε-DP (postprocessing)

## References

* Dwork & Roth, "The Algorithmic Foundations of Differential Privacy" (2014),
  Section 3.5.2
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open scoped NNReal

-- ============================================================================
-- Clamped sum sensitivity
-- ============================================================================

/-- Clamp a real number to the interval [lo, hi]. -/
def clamp (lo hi : ℝ) (x : ℝ) : ℝ := max lo (min hi x)

/-- The clamped sum of a list of values. -/
def clampedSum (f : α → ℝ) (lo hi : ℝ) (l : List α) : ℝ :=
  (l.map (fun a => clamp lo hi (f a))).sum

/-- Clamped values lie in [lo, hi]. -/
private theorem clamp_le_hi {lo hi x : ℝ} (hle : lo ≤ hi) : clamp lo hi x ≤ hi := by
  simp only [clamp]; exact max_le hle (min_le_left hi x)

private theorem lo_le_clamp {lo hi x : ℝ} : lo ≤ clamp lo hi x := by
  simp only [clamp]; exact le_max_left lo _

/-- The clamped sum over [0, B] has sensitivity B under add/remove adjacency.
    Adding one element changes the sum by at most B (the element's clamped value). -/
theorem clampedSum_sensitivity (B : ℝ≥0) (f : α → ℝ) :
    HasL1Sensitivity ListHeadAddRemove (clampedSum f 0 (↑B)) B := by
  intro l₁ l₂ hadj
  simp only [clampedSum]
  have hB : (0 : ℝ) ≤ ↑B := B.coe_nonneg
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]
    simp only [List.map_cons, List.sum_cons]
    have hclamp_nn : 0 ≤ clamp 0 (↑B) (f a) := lo_le_clamp
    have hclamp_le : clamp 0 (↑B) (f a) ≤ ↑B := clamp_le_hi hB
    rw [show clamp 0 (↑B) (f a) + (List.map (fun a => clamp 0 (↑B) (f a)) s).sum -
        (List.map (fun a => clamp 0 (↑B) (f a)) s).sum = clamp 0 (↑B) (f a) by ring]
    rw [abs_of_nonneg hclamp_nn]
    exact hclamp_le
  · rw [h.1, h.2]
    simp only [List.map_cons, List.sum_cons]
    have hclamp_nn : 0 ≤ clamp 0 (↑B) (f a) := lo_le_clamp
    have hclamp_le : clamp 0 (↑B) (f a) ≤ ↑B := clamp_le_hi hB
    rw [show (List.map (fun a => clamp 0 (↑B) (f a)) s).sum -
        (clamp 0 (↑B) (f a) + (List.map (fun a => clamp 0 (↑B) (f a)) s).sum) =
        -(clamp 0 (↑B) (f a)) by ring]
    rw [abs_neg, abs_of_nonneg hclamp_nn]
    exact hclamp_le

-- ============================================================================
-- Special case: sum of [0, 1]-bounded values (sensitivity 1)
-- ============================================================================

/-- Sum of [0,1]-clamped values has sensitivity 1. -/
theorem clampedSum01_sensitivity (f : α → ℝ) :
    HasL1Sensitivity ListHeadAddRemove (clampedSum f 0 1) 1 := by
  have h := clampedSum_sensitivity (1 : ℝ≥0) f
  simp only [NNReal.coe_one] at h
  exact h

-- ============================================================================
-- Example 1: Private sum via Laplace mechanism
-- ============================================================================

/-- **Private sum of bounded values is ε-DP.**

    Given a value function f : α → ℝ, clamp to [0, 1] and add Laplace(1/ε) noise.
    The result is ε-DP by the Laplace mechanism theorem.

    This is the first step of private mean estimation. -/
theorem private_sum_pureDP (f : α → ℝ) {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP ListHeadAddRemove
      (laplaceMech (clampedSum f 0 1) (1 : ℝ≥0) ε) ε :=
  laplaceMech_isPureDP hε (clampedSum01_sensitivity f)

-- ============================================================================
-- Example 2: Genuine private mean over a fixed-size database (bounded DP)
-- ============================================================================

/-- **Replace-one adjacency on fixed-size databases.** Two length-`n` databases
    are adjacent if they differ in at most one record. The size `n` is fixed by
    the type, so it is a genuine public constant. -/
def VectorReplace {n : ℕ} : (Fin n → α) → (Fin n → α) → Prop :=
  fun v₁ v₂ => ∃ i, ∀ j, j ≠ i → v₁ j = v₂ j

/-- Clamped sum over a fixed-size database: `∑ᵢ clamp[0,1] (f (v i))`. -/
def vecClampedSum (f : α → ℝ) {n : ℕ} (v : Fin n → α) : ℝ :=
  ∑ i, clamp 0 1 (f (v i))

/-- The fixed-size clamped sum has sensitivity 1 under replace-one adjacency:
    changing a single record moves one clamped summand within `[0, 1]`. -/
theorem vecClampedSum_sensitivity (f : α → ℝ) {n : ℕ} :
    HasL1Sensitivity (VectorReplace (α := α) (n := n)) (vecClampedSum f) 1 := by
  intro v₁ v₂ hadj
  obtain ⟨i, hji⟩ := hadj
  simp only [NNReal.coe_one]
  have key : vecClampedSum f v₁ - vecClampedSum f v₂
      = clamp 0 1 (f (v₁ i)) - clamp 0 1 (f (v₂ i)) := by
    simp only [vecClampedSum]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · intro j _ hj; rw [hji j hj]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [key]
  have h1a : (0 : ℝ) ≤ clamp 0 1 (f (v₁ i)) := lo_le_clamp
  have h1b : clamp 0 1 (f (v₁ i)) ≤ 1 := clamp_le_hi (by norm_num)
  have h2a : (0 : ℝ) ≤ clamp 0 1 (f (v₂ i)) := lo_le_clamp
  have h2b : clamp 0 1 (f (v₂ i)) ≤ 1 := clamp_le_hi (by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-- **Fixed-size private sum is ε-DP** under replace-one adjacency. -/
theorem private_fixedSize_sum_pureDP (f : α → ℝ) {n : ℕ} {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP (VectorReplace (α := α) (n := n))
      (laplaceMech (vecClampedSum f) (1 : ℝ≥0) ε) ε :=
  laplaceMech_isPureDP hε (vecClampedSum_sensitivity f)

/-- **Private mean estimation is ε-DP.**

    Pipeline over a fixed-size database (`n` records, replace-one adjacency):
    clamp values to [0,1] → sum → add Laplace(1/ε) → divide by the public size `n`.
    Since every input has exactly `n` records, dividing by `n` is data-independent
    measurable postprocessing, so privacy is preserved and the result is a genuine
    mean. (For `n ≥ 1`; `n = 0` is the degenerate empty database.)

    This is the canonical private mean estimation algorithm from
    Dwork & Roth (2014), Section 3.5.2. -/
theorem private_mean_pureDP (f : α → ℝ) (n : ℕ) {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP (VectorReplace (α := α) (n := n))
      (fun (v : Fin n → α) =>
        (laplaceMech (vecClampedSum f) (1 : ℝ≥0) ε v).map
          (measurable_const_mul (n : ℝ)⁻¹).aemeasurable)
      ε :=
  isPureDP_postprocess (private_fixedSize_sum_pureDP f hε) (measurable_const_mul (n : ℝ)⁻¹)

-- ============================================================================
-- Example 3: Private sum with larger bound
-- ============================================================================

/-- **Private sum with clamp [0, B] and sensitivity B.**

    Generalizes to arbitrary upper bound B > 0. The Laplace noise scale
    is B/ε, giving ε-DP. -/
theorem private_sum_general {B : NNReal} (_hB : B ≠ 0) (f : α → ℝ)
    {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP ListHeadAddRemove
      (laplaceMech (clampedSum f 0 (↑B)) B ε) ε := by
  apply laplaceMech_isPureDP hε
  exact clampedSum_sensitivity B f

end DPlean4.Examples

end -- noncomputable section
