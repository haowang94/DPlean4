/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.MeasureClose
import DPlean4.Privacy.Pure
import DPlean4.Privacy.Approximate
import DPlean4.Probability.Mechanism

/-!
# Privacy Amplification by Subsampling

This file proves the core measure-level inequalities underlying privacy
amplification by subsampling (Balle et al., 2018; Kasiviswanathan et al., 2011).

## Main Results

* `subsample_pure_bound`: If μ ≤[ε] ν, then
  q · μ(S) + (1-q) · ν(S) ≤ (q · exp(ε) + (1-q)) · ν(S)

* `subsample_approx_bound`: If μ ≤[ε,δ] ν, then
  q · μ(S) + (1-q) · ν(S) ≤ (q · exp(ε) + (1-q)) · ν(S) + q · δ

* `mixtureMeasure`: q-mixture of two probability measures as a ProbabilityMeasure

* `pureMeasureClose_subsample`: PureMeasureClose version connecting to the library

## Privacy Interpretation

In the Poisson subsampling model with rate q and add/remove adjacency:
- Database d₁ has one extra record x compared to d₂
- Subsampled output on d₁ = q · M(with x included) + (1-q) · M(without x)
- Subsampled output on d₂ = M(without x)

The measure-level bound gives:
  Subsampled(d₁)(S) ≤ (1 + q·(exp(ε)-1)) · Subsampled(d₂)(S)

so the subsampled mechanism is ln(1 + q·(exp(ε)-1))-DP.

For small ε, ln(1 + q·(exp(ε)-1)) ≈ q·ε, giving the standard subsampling
amplification: privacy cost scales as q·ε instead of ε.

## References

* Kasiviswanathan et al. (2011), "What can we learn privately?"
* Balle, Barthe, Gavin (2018), "Privacy Amplification by Subsampling"
-/

noncomputable section

namespace DPlean4

open MeasureTheory ENNReal Real

variable {D O : Type*} [MeasurableSpace O]

-- ============================================================================
-- Amplified Privacy Parameter
-- ============================================================================

private theorem subsample_factor_nonneg (q : NNReal) (ε : NNReal) :
    (0 : ℝ) ≤ ↑q * (Real.exp ↑ε - 1) :=
  mul_nonneg (NNReal.coe_nonneg _) (sub_nonneg.mpr (Real.one_le_exp (NNReal.coe_nonneg _)))

private theorem subsample_factor_pos (q : NNReal) (ε : NNReal) :
    (0 : ℝ) < 1 + ↑q * (Real.exp ↑ε - 1) := by
  linarith [subsample_factor_nonneg q ε]

/-- The amplified privacy parameter for subsampling at rate q with base ε:
    ε' = ln(1 + q · (exp(ε) - 1)).

    For small ε: ε' ≈ q · ε (linear scaling).
    Always: ε' ≤ ε (subsampling can only help). -/
noncomputable def subsampleEpsilon (q : NNReal) (ε : NNReal) : NNReal :=
  ⟨Real.log (1 + ↑q * (Real.exp ↑ε - 1)),
   Real.log_nonneg (by linarith [subsample_factor_nonneg q ε])⟩

-- ============================================================================
-- Core Measure-Level Inequalities
-- ============================================================================

/-- Core subsampling amplification bound (pure DP, measure level).
    If μ(S) ≤ exp(ε) · ν(S) for all measurable S, then the mixture
    q · μ(S) + (1-q) · ν(S) is at most (q · exp(ε) + (1-q)) · ν(S). -/
theorem subsample_pure_bound
    {ε : NNReal} {μ ν : ProbabilityMeasure O}
    (h : PureMeasureClose ε μ ν) {q : NNReal} (_hq : q ≤ 1)
    (s : Set O) (hs : MeasurableSet s) :
    (q : ℝ≥0∞) * μ.toMeasure s + (1 - (q : ℝ≥0∞)) * ν.toMeasure s ≤
      ((q : ℝ≥0∞) * ENNReal.ofReal (Real.exp ↑ε) +
        (1 - (q : ℝ≥0∞))) * ν.toMeasure s := by
  have h_dp := h s hs
  simp only [ENNReal.coe_zero, add_zero] at h_dp
  calc (q : ℝ≥0∞) * μ.toMeasure s + (1 - (q : ℝ≥0∞)) * ν.toMeasure s
      ≤ (q : ℝ≥0∞) * (ENNReal.ofReal (Real.exp ↑ε) * ν.toMeasure s) +
        (1 - (q : ℝ≥0∞)) * ν.toMeasure s := by gcongr
    _ = ((q : ℝ≥0∞) * ENNReal.ofReal (Real.exp ↑ε) +
        (1 - (q : ℝ≥0∞))) * ν.toMeasure s := by rw [← mul_assoc, ← add_mul]

/-- Core subsampling amplification bound (approximate DP, measure level).
    If μ(S) ≤ exp(ε) · ν(S) + δ, then the mixture
    q · μ(S) + (1-q) · ν(S) ≤ (q · exp(ε) + (1-q)) · ν(S) + q · δ.

    Both privacy parameters are amplified: ε shrinks and δ scales by q. -/
theorem subsample_approx_bound
    {ε δ : NNReal} {μ ν : ProbabilityMeasure O}
    (h : MeasureClose ε δ μ ν) {q : NNReal} (_hq : q ≤ 1)
    (s : Set O) (hs : MeasurableSet s) :
    (q : ℝ≥0∞) * μ.toMeasure s + (1 - (q : ℝ≥0∞)) * ν.toMeasure s ≤
      ((q : ℝ≥0∞) * ENNReal.ofReal (Real.exp ↑ε) +
        (1 - (q : ℝ≥0∞))) * ν.toMeasure s + (q : ℝ≥0∞) * (δ : ℝ≥0∞) := by
  have h_dp := h s hs
  calc (q : ℝ≥0∞) * μ.toMeasure s + (1 - (q : ℝ≥0∞)) * ν.toMeasure s
      ≤ (q : ℝ≥0∞) * (ENNReal.ofReal (Real.exp ↑ε) * ν.toMeasure s + (δ : ℝ≥0∞)) +
        (1 - (q : ℝ≥0∞)) * ν.toMeasure s := by gcongr
    _ = ((q : ℝ≥0∞) * ENNReal.ofReal (Real.exp ↑ε) +
        (1 - (q : ℝ≥0∞))) * ν.toMeasure s + (q : ℝ≥0∞) * (δ : ℝ≥0∞) := by
        rw [mul_add, ← mul_assoc, add_right_comm, ← add_mul]

-- ============================================================================
-- Mixture of Probability Measures
-- ============================================================================

/-- A q-mixture of two probability measures is a probability measure. -/
theorem mixture_isProbabilityMeasure {μ ν : ProbabilityMeasure O}
    {q : NNReal} (hq : q ≤ 1) :
    IsProbabilityMeasure
      ((q : ℝ≥0∞) • μ.toMeasure + (1 - (q : ℝ≥0∞)) • ν.toMeasure) := by
  constructor
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      smul_eq_mul, smul_eq_mul, measure_univ, measure_univ, mul_one, mul_one,
      add_comm]
  exact tsub_add_cancel_of_le (ENNReal.coe_le_coe.mpr hq)

/-- Convex combination of two probability measures. -/
noncomputable def mixtureMeasure (q : NNReal) (hq : q ≤ 1)
    (μ ν : ProbabilityMeasure O) : ProbabilityMeasure O :=
  ⟨(q : ℝ≥0∞) • μ.toMeasure + (1 - (q : ℝ≥0∞)) • ν.toMeasure,
   mixture_isProbabilityMeasure hq⟩

@[simp]
theorem mixtureMeasure_toMeasure (q : NNReal) (hq : q ≤ 1)
    (μ ν : ProbabilityMeasure O) :
    (mixtureMeasure q hq μ ν).toMeasure =
      (q : ℝ≥0∞) • μ.toMeasure + (1 - (q : ℝ≥0∞)) • ν.toMeasure :=
  rfl

-- ============================================================================
-- Coefficient Conversion
-- ============================================================================

/-- q · exp(ε) + (1-q) = exp(subsampleEpsilon q ε) in ℝ. -/
theorem subsample_factor_eq_real (q : NNReal) (ε : NNReal) :
    (↑q : ℝ) * Real.exp ↑ε + (1 - ↑q) = Real.exp ↑(subsampleEpsilon q ε) := by
  have : (subsampleEpsilon q ε : ℝ) = Real.log (1 + ↑q * (Real.exp ↑ε - 1)) := by
    unfold subsampleEpsilon; rfl
  rw [this, Real.exp_log (subsample_factor_pos q ε)]
  ring

/-- q · ofReal(exp ε) + (1-q) = ofReal(exp(subsampleEpsilon q ε)) in ENNReal. -/
theorem subsample_factor_eq_ennreal (q : NNReal) (hq : q ≤ 1) (ε : NNReal) :
    (q : ℝ≥0∞) * ENNReal.ofReal (Real.exp ↑ε) + (1 - (q : ℝ≥0∞)) =
      ENNReal.ofReal (Real.exp ↑(subsampleEpsilon q ε)) := by
  rw [← subsample_factor_eq_real q ε]
  have hq_real : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  have h_1mq : (1 : ℝ) - (↑q : ℝ) = ((1 - q : NNReal) : ℝ) := by
    simp [NNReal.coe_sub hq]
  rw [ENNReal.ofReal_add
        (mul_nonneg (NNReal.coe_nonneg _) (Real.exp_pos _).le)
        (by linarith),
      ENNReal.ofReal_mul (NNReal.coe_nonneg _),
      ENNReal.ofReal_coe_nnreal, h_1mq, ENNReal.ofReal_coe_nnreal]
  simp [ENNReal.coe_sub, ENNReal.coe_one]

-- ============================================================================
-- PureMeasureClose Result
-- ============================================================================

/-- **Privacy amplification by subsampling (pure DP)**:
    If μ ≤[ε] ν, then the mixture q·μ + (1-q)·ν is
    ln(1 + q·(exp(ε) - 1))-close to ν. -/
theorem pureMeasureClose_subsample
    {ε : NNReal} {μ ν : ProbabilityMeasure O}
    (h : PureMeasureClose ε μ ν) {q : NNReal} (hq : q ≤ 1) :
    PureMeasureClose (subsampleEpsilon q ε) (mixtureMeasure q hq μ ν) ν := by
  intro s hs
  simp only [ENNReal.coe_zero, add_zero,
             mixtureMeasure_toMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  conv_rhs => rw [← subsample_factor_eq_ennreal q hq ε]
  exact subsample_pure_bound h hq s hs

-- ============================================================================
-- Properties of subsampleEpsilon
-- ============================================================================

/-- subsampleEpsilon at q=0 is 0 (no subsampling = perfect privacy). -/
theorem subsampleEpsilon_zero (ε : NNReal) :
    subsampleEpsilon 0 ε = 0 := by
  simp only [subsampleEpsilon, NNReal.coe_zero, zero_mul, add_zero, Real.log_one]
  rfl

/-- subsampleEpsilon at q=1 is ε (full sampling = no amplification). -/
theorem subsampleEpsilon_one (ε : NNReal) :
    subsampleEpsilon 1 ε = ε := by
  apply NNReal.coe_injective
  simp only [subsampleEpsilon, NNReal.coe_one, one_mul]
  ring_nf
  exact Real.log_exp _

/-- subsampleEpsilon is monotone in q. -/
theorem subsampleEpsilon_mono_q {q₁ q₂ : NNReal} (hq : q₁ ≤ q₂) (ε : NNReal) :
    subsampleEpsilon q₁ ε ≤ subsampleEpsilon q₂ ε := by
  change (subsampleEpsilon q₁ ε : ℝ) ≤ (subsampleEpsilon q₂ ε : ℝ)
  simp only [subsampleEpsilon]
  have hexp : (0 : ℝ) ≤ Real.exp ↑ε - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (NNReal.coe_nonneg _))
  apply Real.log_le_log
  · linarith [subsample_factor_nonneg q₁ ε]
  · have hq' : (↑q₁ : ℝ) ≤ ↑q₂ := by exact_mod_cast hq
    have := mul_le_mul_of_nonneg_right hq' hexp; linarith

/-- subsampleEpsilon is monotone in ε. -/
theorem subsampleEpsilon_mono_eps {ε₁ ε₂ : NNReal} (hε : ε₁ ≤ ε₂) (q : NNReal) :
    subsampleEpsilon q ε₁ ≤ subsampleEpsilon q ε₂ := by
  change (subsampleEpsilon q ε₁ : ℝ) ≤ (subsampleEpsilon q ε₂ : ℝ)
  simp only [subsampleEpsilon]
  have hexp_le : Real.exp ↑ε₁ ≤ Real.exp ↑ε₂ :=
    Real.exp_le_exp_of_le (by exact_mod_cast hε)
  apply Real.log_le_log
  · linarith [subsample_factor_nonneg q ε₁]
  · have h1 : Real.exp ↑ε₁ - 1 ≤ Real.exp ↑ε₂ - 1 := by linarith
    have := mul_le_mul_of_nonneg_left h1 (NNReal.coe_nonneg q); linarith

/-- **Subsampling always helps**: subsampleEpsilon q ε ≤ ε for any q ≤ 1. -/
theorem subsampleEpsilon_le (q : NNReal) (hq : q ≤ 1) (ε : NNReal) :
    subsampleEpsilon q ε ≤ ε := by
  calc subsampleEpsilon q ε ≤ subsampleEpsilon 1 ε := subsampleEpsilon_mono_q hq ε
    _ = ε := subsampleEpsilon_one ε

end DPlean4

end -- noncomputable section
