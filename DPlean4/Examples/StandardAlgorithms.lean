/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Mechanism.Gaussian
import DPlean4.Privacy.Composition
import DPlean4.Privacy.Postprocessing

/-!
# Standard DP Algorithms and Failure Cases

This file exercises the public library interface on textbook mechanisms under
arbitrary-position add/remove adjacency.

Positive examples:
* the Laplace mechanism for database size (Dwork et al., 2006),
* the Gaussian mechanism for database size,
* two independent Laplace releases via product composition, and
* data-independent scaling via postprocessing.

Negative examples:
* releasing the exact database size, and
* deterministically releasing whether a distinguished record occurs.
-/

noncomputable section

namespace DPlean4.Examples.StandardAlgorithms

open DPlean4 MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*}

/-- The database-size query. -/
def databaseSize (xs : List α) : ℝ := xs.length

/-- Database size has sensitivity one even when insertion/removal occurs in
    the middle or at the tail. -/
theorem databaseSize_sensitivity :
    HasL1Sensitivity ListAddRemove (databaseSize : List α → ℝ) 1 := by
  intro xs ys hadj
  rcases listAddRemove_length_diff xs ys hadj with h | h
  · simp only [databaseSize, h, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, abs_one]
    norm_num
  · simp only [databaseSize, h, Nat.cast_add, Nat.cast_one]
    rw [sub_add_cancel_left, abs_neg, abs_one]; norm_num

/-- Textbook Laplace release of database size: `ε`-DP. -/
def noisySizeLaplace (ε : ℝ≥0) : Mechanism (List α) ℝ :=
  laplaceMech databaseSize 1 ε

theorem noisySizeLaplace_isPureDP {ε : ℝ≥0} (hε : ε ≠ 0) :
    IsPureDP ListAddRemove (noisySizeLaplace (α := α) ε) ε :=
  laplaceMech_isPureDP hε databaseSize_sensitivity

/-- Gaussian release of database size with variance `v`. -/
def noisySizeGaussian (v : ℝ≥0) : Mechanism (List α) ℝ :=
  gaussianMech databaseSize v

theorem noisySizeGaussian_isZCDP {v : ℝ≥0} (hv : v ≠ 0) :
    IsZCDP ListAddRemove (noisySizeGaussian (α := α) v)
      ((1 : ℝ≥0) ^ 2 / (2 * v)) :=
  gaussianMech_isZCDP hv databaseSize_sensitivity.toL2

/-- Two independently randomized size releases obey additive composition. -/
theorem two_noisy_sizes_are_private {ε : ℝ≥0} (hε : ε ≠ 0) :
    IsPureDP ListAddRemove
      ((noisySizeLaplace (α := α) ε).prod (noisySizeLaplace (α := α) ε))
      (ε + ε) :=
  isPureDP_prod (noisySizeLaplace_isPureDP hε) (noisySizeLaplace_isPureDP hε)

/-- Scaling a private output is harmless data-independent postprocessing. -/
theorem scaled_noisy_size_is_private {ε : ℝ≥0} (hε : ε ≠ 0) (c : ℝ) :
    IsPureDP ListAddRemove
      (fun xs => (noisySizeLaplace (α := α) ε xs).map
        (measurable_const_mul c).aemeasurable) ε :=
  isPureDP_postprocess (noisySizeLaplace_isPureDP hε) (measurable_const_mul c)

/-! ## Algorithms that are not differentially private -/

/-- An unnoised release of database size. -/
def exactSize : Mechanism (List Bool) ℕ :=
  fun xs => ⟨Measure.dirac xs.length, inferInstance⟩

/-- Exact size is not pure DP for any finite `ε`: the singleton event `{1}`
    distinguishes `[true]` from `[]` with probability one. -/
theorem exactSize_not_pureDP (ε : ℝ≥0) :
    ¬ IsPureDP ListAddRemove exactSize ε := by
  intro h
  have hadj : ListAddRemove [true] ([] : List Bool) :=
    Or.inl ⟨[], [], true, by simp, by simp⟩
  have hdp := h [true] [] hadj {1} (measurableSet_singleton 1)
  simp [exactSize] at hdp

/-- Deterministically reveal whether `true` occurs in the database. -/
def revealsMembership : Mechanism (List Bool) Bool :=
  fun xs => ⟨Measure.dirac (true ∈ xs), inferInstance⟩

/-- Deterministic membership disclosure is not `(ε,δ)`-DP for any `δ < 1`. -/
theorem revealsMembership_not_approxDP (ε δ : ℝ≥0) (hδ : (δ : ℝ) < 1) :
    ¬ IsApproxDP ListAddRemove revealsMembership ε δ := by
  intro h
  have hadj : ListAddRemove [true] ([] : List Bool) :=
    Or.inl ⟨[], [], true, by simp, by simp⟩
  have hdp := h [true] [] hadj {true} (measurableSet_singleton true)
  have hdp' : (1 : ENNReal) ≤ (δ : ENNReal) := by
    simpa [revealsMembership] using hdp
  exact (not_le_of_gt hδ) (by exact_mod_cast hdp')

end DPlean4.Examples.StandardAlgorithms

end
