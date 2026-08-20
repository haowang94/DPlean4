/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.ZCDP
import DPlean4.Privacy.Pure
import DPlean4.Privacy.RenyiDP
import DPlean4.Probability.Mechanism
import Mathlib.Probability.Moments.SubGaussian

/-!
# Tight Pure-DP to zCDP Conversion

This file proves the tight conversion from ε-pure DP to (ε²/2)-zCDP,
improving over the loose ε-zCDP conversion in `RenyiDP.lean`.

## Main Results

* `isZCDP_tight_of_isPureDP`: symmetric ε-pure DP implies (ε²/2)-zCDP

## Proof Strategy (Bun, Dwork, Rothblum, Vadhan 2018)

For mechanisms with symmetric adjacency (adj d₁ d₂ ↔ adj d₂ d₁), pure ε-DP
gives a two-sided bound on the log-likelihood ratio: log(dP/dQ) ∈ [-ε, ε] a.e.

The proof has three steps:

1. **Change of measure**: E_Q[(dP/dQ)^α] = E_P[(dP/dQ)^{α-1}]
   Uses `lintegral_rnDeriv_mul` from Mathlib.

2. **KL bound via Hoeffding**: KL(P‖Q) ≤ ε²/2
   Apply Hoeffding's lemma to -log(dP/dQ) at t=1 under P.
   Since E_P[dQ/dP] = 1, we get 1 ≤ exp(-KL + ε²/2).

3. **Rényi bound via Hoeffding**: D_α(P‖Q) ≤ αε²/2
   Apply Hoeffding to log(dP/dQ) at t=α-1 under P:
   E_P[(dP/dQ)^{α-1}] ≤ exp((α-1)·KL + (α-1)²ε²/2)
                        ≤ exp((α-1)ε²/2 + (α-1)²ε²/2)
                        = exp((α-1)αε²/2)

   So D_α = log(E_P[(dP/dQ)^{α-1}])/(α-1) ≤ αε²/2.

## References

* Bun, Dwork, Rothblum, Vadhan (2018), "Pure Differential Privacy from
  Secure Intermediaries"
* Bun & Dwork (2016), "Concentrated Differential Privacy"
-/

noncomputable section

namespace DPlean4

open MeasureTheory ENNReal Real

variable {D O : Type*} [MeasurableSpace O]

-- ============================================================================
-- Helper: rnDeriv upper bound from PureMeasureClose
-- ============================================================================

private lemma rnDeriv_le_of_pureMeasureClose {ε : NNReal}
    {μ ν : ProbabilityMeasure O}
    (h : PureMeasureClose ε μ ν) :
    μ.toMeasure.rnDeriv ν.toMeasure ≤ᵐ[ν.toMeasure]
      fun _ => ENNReal.ofReal (Real.exp ε) := by
  set c := ENNReal.ofReal (Real.exp ε)
  have hc_ne : c ≠ 0 := ENNReal.ofReal_pos.mpr (Real.exp_pos _) |>.ne'
  have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_le : μ.toMeasure ≤ c • ν.toMeasure := by
    rw [Measure.le_iff]; intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    have := h s hs; simp only [ENNReal.coe_zero, add_zero] at this; exact this
  haveI : SigmaFinite (c • ν.toMeasure) := by
    haveI := ν.toMeasure.smul_finite hc_ne_top (c := c)
    exact IsFiniteMeasure.toSigmaFinite _
  have h_scaled := Measure.rnDeriv_le_one_of_le h_le
  have h_smul := Measure.rnDeriv_smul_right_of_ne_top μ.toMeasure ν.toMeasure hc_ne hc_ne_top
  filter_upwards [h_scaled.filter_mono (Measure.absolutelyContinuous_smul hc_ne).ae_le,
                  h_smul] with x h1 h2
  simp only [Pi.one_apply] at h1; simp only [Pi.smul_apply, smul_eq_mul] at h2
  rw [h2] at h1; rw [ENNReal.inv_mul_le_iff hc_ne hc_ne_top] at h1
  simpa [mul_one] using h1

-- ============================================================================
-- Helper: Change of measure for Rényi moment
-- ============================================================================

private lemma renyiMoment_eq_lintegral_rpow_sub_one
    {μ ν : Measure O} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hac' : ν ≪ μ) {α : ℝ} (hα : 1 < α) :
    renyiMoment α μ ν = ∫⁻ x, (μ.rnDeriv ν x) ^ (α - 1) ∂μ := by
  set r := μ.rnDeriv ν
  simp only [renyiMoment]
  have h_split : ∀ᵐ x ∂ν, r x ^ α = r x ^ (α - 1) * r x := by
    filter_upwards [Measure.rnDeriv_ne_top μ ν,
                    hac'.ae_le (Measure.rnDeriv_pos hac)] with x hx_ne_top hx_pos
    conv_lhs => rw [show α = (α - 1) + 1 from by ring]
    rw [ENNReal.rpow_add _ _ hx_pos.ne' hx_ne_top, ENNReal.rpow_one]
  calc ∫⁻ x, r x ^ α ∂ν
      = ∫⁻ x, r x ^ (α - 1) * r x ∂ν := lintegral_congr_ae h_split
    _ = ∫⁻ x, r x * (r x ^ (α - 1)) ∂ν := by
        apply lintegral_congr; intro x; ring
    _ = ∫⁻ x, r x ^ (α - 1) ∂μ :=
        lintegral_rnDeriv_mul hac
          ((Measure.measurable_rnDeriv μ ν).pow_const (α - 1) |>.aemeasurable)

-- ============================================================================
-- Helper: ∫ exp(-log(rnDeriv)) dμ = 1
-- ============================================================================

private lemma integral_exp_neg_log_rnDeriv_eq_one
    {μ ν : Measure O} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hac' : ν ≪ μ) :
    ∫ x, Real.exp (-Real.log (μ.rnDeriv ν x).toReal) ∂μ = 1 := by
  set r := μ.rnDeriv ν
  have h_eq : (fun x => Real.exp (-Real.log (r x).toReal)) =ᵐ[μ]
      fun x => (ν.rnDeriv μ x).toReal := by
    filter_upwards [Measure.rnDeriv_pos hac,
                    hac.ae_le (Measure.rnDeriv_ne_top μ ν),
                    Measure.inv_rnDeriv hac] with x hx_pos hx_ne_top h_inv
    have hr : 0 < (r x).toReal := ENNReal.toReal_pos hx_pos.ne' hx_ne_top
    rw [Real.exp_neg, Real.exp_log hr, ← ENNReal.toReal_inv]
    congr 1
  rw [integral_congr_ae h_eq,
      MeasureTheory.integral_toReal (Measure.measurable_rnDeriv ν μ).aemeasurable
        (Measure.rnDeriv_lt_top ν μ),
      Measure.lintegral_rnDeriv hac', measure_univ, ENNReal.toReal_one]

-- ============================================================================
-- Core bound: Hoeffding + change of measure → tight Rényi bound
-- ============================================================================

open ProbabilityTheory in
private lemma lintegral_rpow_rnDeriv_le_of_log_bounded
    {μ ν : Measure O} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hac' : ν ≪ μ)
    {ε : ℝ} (hε : 0 ≤ ε) {α : ℝ} (hα : 1 < α)
    (h_bounded : ∀ᵐ x ∂μ, Real.log (μ.rnDeriv ν x).toReal ∈ Set.Icc (-ε) ε) :
    ∫⁻ x, (μ.rnDeriv ν x) ^ (α - 1) ∂μ ≤
      ENNReal.ofReal (Real.exp (α * (α - 1) * ε ^ 2 / 2)) := by
  set r := μ.rnDeriv ν
  set L : O → ℝ := fun x => Real.log (r x).toReal
  set m := ∫ x, L x ∂μ
  have hα_sub : (0 : ℝ) < α - 1 := sub_pos.mpr hα
  have hL_meas : Measurable L := (Measure.measurable_rnDeriv μ ν).ennreal_toReal.log
  have hL_ae : AEMeasurable L μ := hL_meas.aemeasurable
  have h_pos : ∀ᵐ x ∂μ, 0 < r x := Measure.rnDeriv_pos hac
  have h_ne_top : ∀ᵐ x ∂μ, r x ≠ ⊤ := hac.ae_le (Measure.rnDeriv_ne_top μ ν)
  -- Sub-Gaussian: (L - m) has sub-Gaussian MGF with parameter c = (‖2ε‖₊/2)²
  have hsub := hasSubgaussianMGF_of_mem_Icc hL_ae h_bounded
  set c := (‖ε - (-ε)‖₊ / 2) ^ 2 with hc_def
  have hc_val : (c : ℝ) = ε ^ 2 := by
    simp only [c, sub_neg_eq_add, ← two_mul, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
               coe_nnnorm, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * ε)]
    ring
  -- ENNReal rpow = ofReal(exp((α-1)*L)) a.e.
  have h_eq : ∀ᵐ x ∂μ,
      (r x) ^ (α - 1) = ENNReal.ofReal (Real.exp ((α - 1) * L x)) := by
    filter_upwards [h_pos, h_ne_top] with x hx_pos hx_ne_top
    have hr : 0 < (r x).toReal := ENNReal.toReal_pos hx_pos.ne' hx_ne_top
    have hfin : (r x) ^ (α - 1) ≠ ⊤ := rpow_ne_top_of_nonneg hα_sub.le hx_ne_top
    rw [← ENNReal.ofReal_toReal hfin]; congr 1
    rw [show ((r x) ^ (α - 1)).toReal = (r x).toReal ^ (α - 1) from
      (ENNReal.toReal_rpow (r x) (α - 1)).symm, Real.rpow_def_of_pos hr]
    congr 1; simp only [L]; ring
  -- Integrability and nonnegativity
  have h_int : Integrable (fun x => Real.exp ((α - 1) * L x)) μ :=
    integrable_exp_mul_of_mem_Icc hL_ae h_bounded
  have h_nn : ∀ᵐ x ∂μ, (0 : ℝ) ≤ Real.exp ((α - 1) * L x) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  -- KL bound: m ≤ ε²/2
  have h_inv_one := integral_exp_neg_log_rnDeriv_eq_one hac hac'
  have hm : m ≤ ε ^ 2 / 2 := by
    have h_le := hsub.mgf_le (-1 : ℝ)
    simp only [mgf] at h_le
    have h_rw : (fun ω => Real.exp ((-1 : ℝ) * (L ω - m))) =
        fun ω => Real.exp m * Real.exp (-L ω) := by
      ext ω; rw [← Real.exp_add]; congr 1; ring
    rw [h_rw, integral_const_mul, h_inv_one, mul_one] at h_le
    have hc_simp : ↑c * (-1 : ℝ) ^ 2 / 2 = ε ^ 2 / 2 := by rw [hc_val]; ring
    rw [hc_simp] at h_le
    exact exp_le_exp.1 h_le
  -- Main bound via sub-Gaussian at t = α-1
  have h_mgf_main := hsub.mgf_le (α - 1)
  have h_split : ∫ x, Real.exp ((α - 1) * L x) ∂μ =
      Real.exp ((α - 1) * m) * mgf (fun ω => L ω - m) μ (α - 1) := by
    simp only [mgf]
    have : (fun ω => Real.exp ((α - 1) * L ω)) =
        fun ω => Real.exp ((α - 1) * m) * Real.exp ((α - 1) * (L ω - m)) := by
      ext ω; rw [← Real.exp_add]; congr 1; ring
    rw [this, integral_const_mul]
  have h_bound : ∫ x, Real.exp ((α - 1) * L x) ∂μ ≤
      Real.exp (α * (α - 1) * ε ^ 2 / 2) := by
    rw [h_split]
    calc Real.exp ((α - 1) * m) * mgf (fun ω => L ω - m) μ (α - 1)
        ≤ Real.exp ((α - 1) * m) * Real.exp (↑c * (α - 1) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h_mgf_main (Real.exp_pos _).le
      _ ≤ Real.exp ((α - 1) * (ε ^ 2 / 2)) * Real.exp (↑c * (α - 1) ^ 2 / 2) := by
          gcongr
      _ = Real.exp ((α - 1) * (ε ^ 2 / 2)) * Real.exp (ε ^ 2 * (α - 1) ^ 2 / 2) := by
          rw [hc_val]
      _ = Real.exp (α * (α - 1) * ε ^ 2 / 2) := by
          rw [← Real.exp_add]; congr 1; ring
  -- Bridge: ENNReal lintegral → ℝ integral → bound
  calc ∫⁻ x, (r x) ^ (α - 1) ∂μ
      = ∫⁻ x, ENNReal.ofReal (Real.exp ((α - 1) * L x)) ∂μ := lintegral_congr_ae h_eq
    _ = ENNReal.ofReal (∫ x, Real.exp ((α - 1) * L x) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal h_int h_nn).symm
    _ ≤ ENNReal.ofReal (Real.exp (α * (α - 1) * ε ^ 2 / 2)) :=
        ENNReal.ofReal_le_ofReal h_bound

-- ============================================================================
-- Log-likelihood ratio bounds from symmetric PureMeasureClose
-- ============================================================================

private lemma log_rnDeriv_mem_Icc_of_symmetric_pureMeasureClose {ε : NNReal}
    {μ ν : ProbabilityMeasure O}
    (h_fwd : PureMeasureClose ε μ ν)
    (h_rev : PureMeasureClose ε ν μ)
    (hac : μ.toMeasure ≪ ν.toMeasure)
    (hac' : ν.toMeasure ≪ μ.toMeasure) :
    ∀ᵐ x ∂μ.toMeasure,
      Real.log (μ.toMeasure.rnDeriv ν.toMeasure x).toReal ∈ Set.Icc (-(ε : ℝ)) ε := by
  set r := μ.toMeasure.rnDeriv ν.toMeasure
  have h_upper := rnDeriv_le_of_pureMeasureClose h_fwd
  have h_upper_rev := rnDeriv_le_of_pureMeasureClose h_rev
  filter_upwards [hac.ae_le h_upper,
                  Measure.rnDeriv_pos hac,
                  hac.ae_le (Measure.rnDeriv_ne_top μ.toMeasure ν.toMeasure),
                  Measure.inv_rnDeriv hac,
                  h_upper_rev] with x h_le h_pos h_ne_top h_inv h_rev_le
  have hr_pos_real : (0 : ℝ) < (r x).toReal := ENNReal.toReal_pos h_pos.ne' h_ne_top
  have h_toReal_le : (r x).toReal ≤ Real.exp ε := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_le
    rwa [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))] at this
  have h_inv_eq : (r x)⁻¹ = ν.toMeasure.rnDeriv μ.toMeasure x := by
    rw [Pi.inv_apply] at h_inv; exact h_inv
  have h_inv_le_c : (r x)⁻¹ ≤ ENNReal.ofReal (Real.exp ε) := h_inv_eq ▸ h_rev_le
  have h_inv_toReal_le : (r x).toReal⁻¹ ≤ Real.exp ε := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_inv_le_c
    rwa [ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))] at this
  constructor
  · -- Lower bound: log(r x) ≥ -ε
    rw [neg_le, ← Real.log_inv, ← Real.log_exp (↑ε)]
    exact Real.log_le_log (by positivity) h_inv_toReal_le
  · -- Upper bound: log(r x) ≤ ε
    rw [← Real.log_exp (↑ε)]
    exact Real.log_le_log hr_pos_real h_toReal_le

-- ============================================================================
-- Main tight Rényi moment bound
-- ============================================================================

/-- **Tight Rényi moment bound for symmetric pure DP.**

    If P ≤[ε] Q and Q ≤[ε] P (symmetric pure DP, giving log(dP/dQ) ∈ [-ε, ε]),
    then the Rényi moment satisfies the quadratic bound:

    E_Q[(dP/dQ)^α] ≤ exp(α(α-1)ε²/2)

    This is tighter than the linear bound exp((α-1)ε) from `renyiMoment_le_of_pureMeasureClose'`
    whenever ε > 0 and α < 2/ε + 1.

    The proof uses:
    1. Change of measure: E_Q[(dP/dQ)^α] = E_P[(dP/dQ)^{α-1}]
    2. Log-likelihood bounds: log(dP/dQ) ∈ [-ε, ε] a.e. under P
    3. Sub-Gaussian/Hoeffding bound on the integral -/
theorem renyiMoment_le_of_symmetric_pureMeasureClose {ε : NNReal}
    {μ ν : ProbabilityMeasure O}
    (h_fwd : PureMeasureClose ε μ ν)
    (h_rev : PureMeasureClose ε ν μ)
    {α : ℝ} (hα : 1 < α)
    (hac : μ.toMeasure ≪ ν.toMeasure)
    (hac' : ν.toMeasure ≪ μ.toMeasure) :
    renyiMoment α μ.toMeasure ν.toMeasure ≤
      ENNReal.ofReal (Real.exp (α * (α - 1) * (ε : ℝ) ^ 2 / 2)) := by
  have h_log_bounded := log_rnDeriv_mem_Icc_of_symmetric_pureMeasureClose
    h_fwd h_rev hac hac'
  calc renyiMoment α μ.toMeasure ν.toMeasure
      = ∫⁻ x, (μ.toMeasure.rnDeriv ν.toMeasure x) ^ (α - 1) ∂μ.toMeasure :=
        renyiMoment_eq_lintegral_rpow_sub_one hac hac' hα
    _ ≤ ENNReal.ofReal (Real.exp (α * (α - 1) * (ε : ℝ) ^ 2 / 2)) :=
        lintegral_rpow_rnDeriv_le_of_log_bounded hac hac' (NNReal.coe_nonneg ε) hα h_log_bounded

-- ============================================================================
-- Tight zCDP conversion
-- ============================================================================

/-- **Tight ε-pure-DP to (ε²/2)-zCDP conversion.**

    For mechanisms with symmetric adjacency, ε-pure DP implies (ε²/2)-zCDP.
    This is a 2/ε improvement over the naive ε-zCDP conversion for small ε.

    Requires:
    - Symmetric adjacency: adj d₁ d₂ → adj d₂ d₁
    - Absolute continuity: M(d₁) ≪ M(d₂) for adjacent d₁, d₂
    - Rényi moment finiteness (follows from pure DP + absolute continuity)

    Example improvement for ε = 0.1:
    - Loose:  0.1-zCDP
    - Tight:  0.005-zCDP (20× tighter)

    Reference: Bun, Dwork, Rothblum, Vadhan (2018), Theorem 3.5. -/
theorem isZCDP_tight_of_isPureDP {adj : D → D → Prop} {M : Mechanism D O} {ε : NNReal}
    (h_symm : ∀ d₁ d₂, adj d₁ d₂ → adj d₂ d₁)
    (h : IsPureDP adj M ε)
    (hac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure)
    (hfin : ∀ d₁ d₂, adj d₁ d₂ → ∀ α : ℝ, 1 < α →
      renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤) :
    IsZCDP adj M (ε ^ 2 / 2) where
  ac := hac
  fin := hfin
  bound d₁ d₂ hadj α hα := by
    have hac_fwd := hac d₁ d₂ hadj
    have hac_rev := hac d₂ d₁ (h_symm d₁ d₂ hadj)
    have hfin' := hfin d₁ d₂ hadj α hα
    have h_moment := renyiMoment_le_of_symmetric_pureMeasureClose
      (h d₁ d₂ hadj) (h d₂ d₁ (h_symm d₁ d₂ hadj)) hα hac_fwd hac_rev
    set ρ : NNReal := ε ^ 2 / 2
    have hρ_val : (ρ : ℝ) = (ε : ℝ) ^ 2 / 2 := by
      simp only [ρ, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
    have hρα_nn : (0 : ℝ) ≤ (ρ : ℝ) * α := by positivity
    rw [renyiDivergence_le_iff hα hρα_nn hfin']
    calc renyiMoment α (M d₁).toMeasure (M d₂).toMeasure
        ≤ ENNReal.ofReal (Real.exp (α * (α - 1) * (ε : ℝ) ^ 2 / 2)) := h_moment
      _ = ENNReal.ofReal (Real.exp ((α - 1) * ((ρ : ℝ) * α))) := by
          congr 1; congr 1; rw [hρ_val]; ring

end DPlean4

end -- noncomputable section
