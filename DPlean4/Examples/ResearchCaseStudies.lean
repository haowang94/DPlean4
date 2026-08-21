/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Examples.StandardAlgorithms
import DPlean4.Mechanism.ReportNoisyMax
import DPlean4.Privacy.Subsampling

/-!
# Research-Oriented Library Validation

These examples exercise interactions that are easy to get wrong in a DP
formalization: selection among many data-dependent scores, heterogeneous
composition, conversion from zCDP, and a bounded-support noise counterexample.

The positive selection result is the report-noisy-max/exponential-mechanism
analysis from McSherry--Talwar and Dwork--Roth. Its privacy cost is `ε`, not
three times `ε`, despite comparing three private counts.

The negative example shows why merely adding nonzero random noise is not enough:
two-point bounded noise leaves database-dependent support endpoints and fails
pure DP for every finite parameter.
-/

noncomputable section

namespace DPlean4.Examples.ResearchCaseStudies

open DPlean4 MeasureTheory
open scoped ENNReal NNReal

/-! ## Private selection among three categories -/

/-- Score category `i` by its frequency in the private database. -/
def categoryScore (i : Fin 3) (xs : List (Fin 3)) : ℝ := xs.count i

/-- A category count has sensitivity one for insertion/removal at any position. -/
theorem categoryScore_sensitivity (i : Fin 3) :
    HasL1Sensitivity ListAddRemove (categoryScore i) 1 := by
  intro xs ys hadj
  rcases hadj with ⟨pre, suffix, a, rfl, rfl⟩ | ⟨pre, suffix, a, rfl, rfl⟩
  · simp only [categoryScore, List.count_append, List.count_cons]
    split_ifs <;> simp
  · simp only [categoryScore, List.count_append, List.count_cons]
    split_ifs <;> simp

/-- Report noisy max privately chooses the most frequent of three categories.
    The bound is independent of the number of candidates. -/
def privateMostFrequent (ε : ℝ≥0) : Mechanism (List (Fin 3)) (Fin 3) :=
  exponentialArgmax (fun i => categoryScore i) ε 1

theorem privateMostFrequent_isPureDP (ε : ℝ≥0) :
    IsPureDP ListAddRemove (privateMostFrequent ε) ε :=
  exponentialArgmax_isPureDP (by norm_num) categoryScore_sensitivity

/-! ## Heterogeneous release and concentrated-DP conversion -/

/-- Jointly release a private selected category and an independently noised
    database size. This validates composition across discrete and continuous
    output spaces. -/
def selectionAndNoisySize (εselect εsize : ℝ≥0) :
    Mechanism (List (Fin 3)) (Fin 3 × ℝ) :=
  (privateMostFrequent εselect).prod
    (StandardAlgorithms.noisySizeLaplace εsize)

theorem selectionAndNoisySize_isPureDP {εselect εsize : ℝ≥0}
    (hsize : εsize ≠ 0) :
    IsPureDP ListAddRemove (selectionAndNoisySize εselect εsize)
      (εselect + εsize) :=
  isPureDP_prod (privateMostFrequent_isPureDP εselect)
    (StandardAlgorithms.noisySizeLaplace_isPureDP hsize)

/-- At every target failure probability `δ ∈ (0,1)`, the Gaussian size release
    admits a finite approximate-DP parameter via its zCDP guarantee. -/
theorem gaussianSize_hasApproxDP {v δ : ℝ≥0} (hv : v ≠ 0)
    (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) :
    ∃ ε : ℝ≥0, IsApproxDP ListAddRemove
      (StandardAlgorithms.noisySizeGaussian (α := Fin 3) v) ε δ :=
  isApproxDP_of_isZCDP'
    (StandardAlgorithms.noisySizeGaussian_isZCDP hv) (by positivity) hδ hδ1

/-! ## Counterexample: bounded-support additive noise -/

/-- A probability measure equally supported on `n` and `n+1`. -/
def twoPointNoise (n : ℕ) : ProbabilityMeasure ℕ :=
  mixtureMeasure (1 / 2) (by norm_num)
    ⟨Measure.dirac n, inferInstance⟩ ⟨Measure.dirac (n + 1), inferInstance⟩

/-- Release database size with a random noise bit in `{0,1}`. This is genuinely
    randomized, but its support still reveals boundary information. -/
def boundedNoiseSize : Mechanism (List Bool) ℕ :=
  fun xs => twoPointNoise xs.length

private theorem boundedNoise_empty_at_zero :
    (boundedNoiseSize []).toMeasure {0} = (1 / 2 : ENNReal) := by
  simp only [boundedNoiseSize, twoPointNoise, mixtureMeasure]
  simp [Measure.add_apply, Measure.smul_apply]

private theorem boundedNoise_singleton_at_zero :
    (boundedNoiseSize [true]).toMeasure {0} = 0 := by
  simp only [boundedNoiseSize, twoPointNoise, mixtureMeasure]
  simp [Measure.add_apply, Measure.smul_apply]

/-- Bounded two-point noise fails pure DP for every finite `ε`. -/
theorem boundedNoiseSize_not_pureDP (ε : ℝ≥0) :
    ¬ IsPureDP ListAddRemove boundedNoiseSize ε := by
  intro h
  have hadj : ListAddRemove ([] : List Bool) [true] :=
    Or.inr ⟨[], [], true, by simp, by simp⟩
  have hdp := h [] [true] hadj {0} (measurableSet_singleton 0)
  rw [boundedNoise_empty_at_zero, boundedNoise_singleton_at_zero] at hdp
  norm_num at hdp

/-- More sharply, the same mechanism cannot be `(ε,δ)`-DP when `δ < 1/2`. -/
theorem boundedNoiseSize_not_approxDP (ε δ : ℝ≥0)
    (hδ : (δ : ℝ) < 1 / 2) :
    ¬ IsApproxDP ListAddRemove boundedNoiseSize ε δ := by
  intro h
  have hadj : ListAddRemove ([] : List Bool) [true] :=
    Or.inr ⟨[], [], true, by simp, by simp⟩
  have hdp := h [] [true] hadj {0} (measurableSet_singleton 0)
  rw [boundedNoise_empty_at_zero, boundedNoise_singleton_at_zero, mul_zero, zero_add] at hdp
  have hcoe : (1 / 2 : ENNReal) = ((1 / 2 : NNReal) : ENNReal) := by norm_num
  rw [hcoe] at hdp
  have hdp_nn : (1 / 2 : NNReal) ≤ δ := ENNReal.coe_le_coe.mp hdp
  have hdp' : (1 / 2 : ℝ) ≤ δ := by exact_mod_cast hdp_nn
  linarith

end DPlean4.Examples.ResearchCaseStudies

end
