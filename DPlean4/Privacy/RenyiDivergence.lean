/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Rényi Divergence

This file defines the Rényi divergence of order α between two measures.

## Main Definitions

* `renyiMoment α μ ν`: The α-th moment of the likelihood ratio dμ/dν under ν,
  i.e., `∫⁻ x, (dμ/dν)^α dν`. This equals `exp((α-1) · D_α(μ‖ν))`.
* `renyiDivergence α μ ν`: The Rényi divergence `D_α(μ‖ν) = 1/(α-1) · log(renyiMoment α μ ν)`.

## Design Notes

We define the Rényi moment as the primary object since it avoids logarithms
and works directly in `ℝ≥0∞`. The Rényi divergence is derived from it.

For the zCDP definition, we use Rényi divergence (the standard formulation).
For proofs, working with the moment form is often more convenient.
-/

namespace DPlean4

open MeasureTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Rényi moment of order α: `∫⁻ x, (dμ/dν x)^α dν`.
    This equals `exp((α-1) · D_α(μ‖ν))` when the integral is finite and α > 1. -/
noncomputable def renyiMoment (α : ℝ) (μ ν : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ x, (μ.rnDeriv ν x) ^ α ∂ν

/-- Real-valued Rényi-divergence formula. This projection is mathematically
    meaningful only with `1 < α`, `μ ≪ ν`, and a finite Rényi moment.
    Privacy predicates bundle those obligations; callers handling arbitrary
    measures should use `renyiMoment` in `ℝ≥0∞` instead. -/
noncomputable def renyiDivergence (α : ℝ) (μ ν : Measure Ω) : ℝ :=
  (α - 1)⁻¹ * Real.log (renyiMoment α μ ν).toReal

/-- The Rényi moment of order 1 equals 1 for probability measures when μ ≪ ν. -/
theorem renyiMoment_one {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) :
    renyiMoment 1 μ ν = 1 := by
  simp only [renyiMoment, rpow_one]
  rw [Measure.lintegral_rnDeriv hac]
  exact measure_univ

/-- Rényi moment is 1 for identical measures (order α > 0). -/
theorem renyiMoment_self {μ : Measure Ω} [IsProbabilityMeasure μ] {α : ℝ} (_hα : 0 < α) :
    renyiMoment α μ μ = 1 := by
  simp only [renyiMoment]
  have : μ.rnDeriv μ =ᵐ[μ] 1 := Measure.rnDeriv_self μ
  calc ∫⁻ x, (μ.rnDeriv μ x) ^ α ∂μ
      = ∫⁻ x, (1 : ℝ≥0∞) ^ α ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [this] with x hx
        rw [hx, Pi.one_apply]
    _ = ∫⁻ _, 1 ∂μ := by simp [one_rpow]
    _ = μ Set.univ := by simp
    _ = 1 := measure_univ

/-- Rényi divergence of a measure with itself is 0. -/
theorem renyiDivergence_self {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : ℝ} (hα : 1 < α) :
    renyiDivergence α μ μ = 0 := by
  simp only [renyiDivergence, renyiMoment_self (by linarith : 0 < α)]
  simp [Real.log_one]

/-- The Rényi moment is at least 1 for probability measures when α > 1 and μ ≪ ν.
    Proved via the power mean inequality (Hölder variant). -/
theorem renyiMoment_ge_one {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {α : ℝ} (hα : 1 < α) (hac : μ ≪ ν) :
    1 ≤ renyiMoment α μ ν := by
  have hα_pos : (0 : ℝ) < α := by linarith
  have hα_ne : (α : ℝ) ≠ 0 := ne_of_gt hα_pos
  have hα_inv_pos : (0 : ℝ) < 1 / α := div_pos one_pos hα_pos
  have hq_nn : (0 : ℝ) ≤ 1 - 1 / α := by
    rw [sub_nonneg, div_le_one hα_pos]; linarith
  have hpq : 1 / α + (1 - 1 / α) = 1 := by ring
  have hf_ae : AEMeasurable (fun x => (μ.rnDeriv ν x) ^ α) ν :=
    (Measure.measurable_rnDeriv μ ν).pow_const α |>.aemeasurable
  have hg_ae : AEMeasurable (fun (_ : Ω) => (1 : ℝ≥0∞)) ν := aemeasurable_const
  have holder := lintegral_mul_norm_pow_le hf_ae hg_ae hα_inv_pos.le hq_nn hpq
  have hleft : ∫⁻ a, ((μ.rnDeriv ν a) ^ α) ^ (1 / α) * (1 : ℝ≥0∞) ^ (1 - 1 / α) ∂ν = 1 := by
    simp_rw [one_rpow, mul_one, ← rpow_mul, show α * (1 / α) = 1 from by field_simp, rpow_one]
    rw [Measure.lintegral_rnDeriv hac, measure_univ]
  have hright : (∫⁻ a, (μ.rnDeriv ν a) ^ α ∂ν) ^ (1 / α) *
      (∫⁻ (_ : Ω), (1 : ℝ≥0∞) ∂ν) ^ (1 - 1 / α) = (renyiMoment α μ ν) ^ (1 / α) := by
    simp only [lintegral_one, measure_univ, one_rpow, mul_one, renyiMoment]
  rw [hleft, hright] at holder
  rwa [← one_rpow (1 / α : ℝ), rpow_le_rpow_iff hα_inv_pos] at holder

/-- The Rényi divergence is non-negative for probability measures. -/
theorem renyiDivergence_nonneg {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {α : ℝ} (hα : 1 < α) (hac : μ ≪ ν) :
    0 ≤ renyiDivergence α μ ν := by
  simp only [renyiDivergence]
  by_cases hfin : renyiMoment α μ ν = ⊤
  · simp [hfin, toReal_top, Real.log_zero]
  · apply mul_nonneg
    · exact inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ α - 1)
    · exact Real.log_nonneg (by
        rw [← toReal_one]
        exact toReal_mono hfin (renyiMoment_ge_one hα hac))

/-- Equivalent characterization: D_α ≤ ε iff the Rényi moment ≤ exp((α-1)·ε). -/
theorem renyiDivergence_le_iff {μ ν : Measure Ω} {α : ℝ} (hα : 1 < α)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfin : renyiMoment α μ ν ≠ ⊤) :
    renyiDivergence α μ ν ≤ ε ↔
    renyiMoment α μ ν ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε)) := by
  have hα_pos : (0 : ℝ) < α - 1 := by linarith
  simp only [renyiDivergence]
  by_cases hM : renyiMoment α μ ν = 0
  · simp only [hM, ENNReal.toReal_zero, Real.log_zero, mul_zero]
    exact ⟨fun _ => bot_le, fun _ => hε⟩
  · have hM_pos : 0 < (renyiMoment α μ ν).toReal := ENNReal.toReal_pos hM hfin
    rw [inv_mul_le_iff₀ hα_pos, Real.log_le_iff_le_exp hM_pos,
        ENNReal.le_ofReal_iff_toReal_le hfin (Real.exp_pos _).le]

-- ============================================================================
-- Data Processing Inequality: Rényi Moment Monotonicity under Pushforward
-- ============================================================================

section DataProcessing

variable {Ω₂ : Type*} [MeasurableSpace Ω₂]

/-- **Data Processing Inequality for Rényi Moment.**
    Applying a measurable function cannot increase the Rényi moment:
    `M_α(g#μ ‖ g#ν) ≤ M_α(μ ‖ ν)`.
    Requires: `μ ≪ ν`, `α ≥ 1`, and the original moment is finite.

    Proof via Jensen's inequality for conditional expectation:
    the pushforward rnDeriv is the conditional expectation of the original rnDeriv,
    and `t ↦ t^α` is convex for α ≥ 1. -/
theorem renyiMoment_map_le {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : Ω → Ω₂} (hg : Measurable g)
    {α : ℝ} (hα : 1 ≤ α) (hfin : renyiMoment α μ ν ≠ ⊤) :
    renyiMoment α (μ.map g) (ν.map g) ≤ renyiMoment α μ ν := by
  simp only [renyiMoment] at hfin ⊢
  have hα_nn : (0 : ℝ) ≤ α := by linarith
  -- Step 1: Pull back the pushforward integral via lintegral_map
  rw [lintegral_map ((Measure.measurable_rnDeriv _ _).pow_const α) hg]
  -- Goal: ∫⁻ x, ((μ.map g).rnDeriv (ν.map g) (g x)) ^ α ∂ν ≤ ∫⁻ x, (μ.rnDeriv ν x) ^ α ∂ν
  -- Step 2: a.e. equalities converting ENNReal rpow to ofReal(Real rpow)
  have h_ae_orig : (fun x => (μ.rnDeriv ν x) ^ α) =ᵐ[ν]
      fun x => ENNReal.ofReal ((μ.rnDeriv ν x).toReal ^ α) := by
    filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
    rw [← ENNReal.ofReal_toReal (rpow_ne_top_of_nonneg hα_nn hx), ENNReal.toReal_rpow]
  have h_ae_mapped : (fun x => ((μ.map g).rnDeriv (ν.map g) (g x)) ^ α) =ᵐ[ν]
      fun x => ENNReal.ofReal (((μ.map g).rnDeriv (ν.map g) (g x)).toReal ^ α) := by
    have := ae_of_ae_map hg.aemeasurable (Measure.rnDeriv_ne_top (μ.map g) (ν.map g))
    filter_upwards [this] with x hx
    rw [← ENNReal.ofReal_toReal (rpow_ne_top_of_nonneg hα_nn hx), ENNReal.toReal_rpow]
  -- Step 3: Integrability of (rnDeriv.toReal)^α w.r.t. ν (from finiteness hypothesis)
  have h_int : Integrable (fun x => (μ.rnDeriv ν x).toReal ^ α) ν := by
    rw [show (fun x => (μ.rnDeriv ν x).toReal ^ α) =
        fun x => ((μ.rnDeriv ν x) ^ α).toReal from
      funext fun x => ENNReal.toReal_rpow _ _]
    exact integrable_toReal_of_lintegral_ne_top
      ((Measure.measurable_rnDeriv μ ν).pow_const α |>.aemeasurable)
      hfin
  -- Step 4: Integrability of mapped version w.r.t. ν (from DPI infrastructure)
  have h_int_map : Integrable (fun x => ((μ.map g).rnDeriv (ν.map g) x).toReal ^ α)
      (ν.map g) :=
    (convexOn_rpow hα).integrable_comp_rnDeriv_map hμν hg
      (by fun_prop) (by fun_prop) h_int
  have h_int_comp : Integrable
      (fun x => ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ^ α) ν :=
    h_int_map.comp_measurable hg
  -- Step 5: Pointwise bound from Jensen via comp_rnDeriv_map_le
  have h_bound := (convexOn_rpow hα).comp_rnDeriv_map_le hμν hg
    (by fun_prop) (by fun_prop) h_int
  -- Step 6: Bochner integral comparison
  have h_mono : ∫ x, ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ^ α ∂ν ≤
      ∫ x, (μ.rnDeriv ν x).toReal ^ α ∂ν := by
    calc ∫ x, ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ^ α ∂ν
        ≤ ∫ x, (ν[fun x => (μ.rnDeriv ν x).toReal ^ α |
            (‹MeasurableSpace Ω₂›).comap g]) x ∂ν :=
          integral_mono_ae h_int_comp integrable_condExp h_bound
      _ = ∫ x, (μ.rnDeriv ν x).toReal ^ α ∂ν := integral_condExp hg.comap_le
  -- Step 7: Convert Bochner inequality back to lintegral inequality
  have h_nn : ∀ x, (0 : ℝ) ≤ (μ.rnDeriv ν x).toReal ^ α :=
    fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg α
  have h_nn_mapped : ∀ x, (0 : ℝ) ≤
      ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ^ α :=
    fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg α
  calc ∫⁻ x, ((μ.map g).rnDeriv (ν.map g) (g x)) ^ α ∂ν
      = ∫⁻ x, ENNReal.ofReal
          (((μ.map g).rnDeriv (ν.map g) (g x)).toReal ^ α) ∂ν :=
        lintegral_congr_ae h_ae_mapped
    _ = ENNReal.ofReal (∫ x,
          ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ^ α ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal h_int_comp
          (ae_of_all _ h_nn_mapped)).symm
    _ ≤ ENNReal.ofReal (∫ x, (μ.rnDeriv ν x).toReal ^ α ∂ν) :=
        ENNReal.ofReal_le_ofReal h_mono
    _ = ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv ν x).toReal ^ α) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal h_int (ae_of_all _ h_nn)
    _ = ∫⁻ x, (μ.rnDeriv ν x) ^ α ∂ν :=
        lintegral_congr_ae h_ae_orig.symm

end DataProcessing

-- ============================================================================
-- Privacy Loss Bounds (for zCDP → approx-DP conversion)
-- ============================================================================

section PrivacyLoss

/-- **Privacy loss decomposition.** For any threshold t:
    μ(S) ≤ t · ν(S) + μ({rnDeriv > t}).

    This splits the measure of S into the "normal" part (where the likelihood
    ratio is bounded by t) and the "tail" part (where it exceeds t). -/
theorem measure_le_mul_add_rnDeriv_tail {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (S : Set Ω) (t : ℝ≥0∞) :
    μ S ≤ t * ν S + μ {x | t < μ.rnDeriv ν x} := by
  set r := μ.rnDeriv ν
  set A := {x | r x ≤ t}
  have hA : MeasurableSet A := (Measure.measurable_rnDeriv μ ν) measurableSet_Iic
  rw [← Measure.setLIntegral_rnDeriv hμν S,
      ← Measure.setLIntegral_rnDeriv hμν {x | t < r x}]
  calc ∫⁻ x in S, r x ∂ν
      = ∫⁻ x in S ∩ A, r x ∂ν + ∫⁻ x in S \ A, r x ∂ν :=
        (lintegral_inter_add_sdiff r S hA).symm
    _ ≤ (t * ν S) + ∫⁻ x in {x | t < r x}, r x ∂ν := by
        apply add_le_add
        · calc ∫⁻ x in S ∩ A, r x ∂ν
              ≤ ∫⁻ x in S ∩ A, t ∂ν :=
                setLIntegral_mono measurable_const (fun x hx => hx.2)
            _ = t * ν (S ∩ A) := setLIntegral_const _ _
            _ ≤ t * ν S := by gcongr; exact Set.inter_subset_left
        · exact lintegral_mono_set (show S \ A ⊆ {x | t < r x} from
            fun x hx => show t < r x from not_le.1 hx.2)

/-- **Tail bound via Rényi moment.** The μ-measure of the set where the
    likelihood ratio exceeds t is bounded by the Rényi moment divided by t^(α-1):

    μ({rnDeriv > t}) ≤ renyiMoment(α) / t^(α-1)

    Proof: on {r > t}, we have r ≤ r^α / t^(α-1), so integrating gives the bound. -/
theorem rnDeriv_tail_le_renyiMoment_div {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {α : ℝ} (hα : 1 ≤ α) {t : ℝ≥0∞} (ht : t ≠ 0) (ht_top : t ≠ ⊤) :
    μ {x | t < μ.rnDeriv ν x} ≤ renyiMoment α μ ν / t ^ (α - 1) := by
  set r := μ.rnDeriv ν
  rw [← Measure.setLIntegral_rnDeriv hμν {x | t < r x}, ENNReal.div_eq_inv_mul]
  have hr_meas := Measure.measurable_rnDeriv μ ν
  have hS_meas : MeasurableSet {x | t < r x} := hr_meas measurableSet_Ioi
  have hα_sub : (0 : ℝ) ≤ α - 1 := by linarith
  have ht_rpow_ne : t ^ (α - 1) ≠ 0 :=
    (rpow_pos_of_nonneg (pos_iff_ne_zero.mpr ht) hα_sub).ne'
  have ht_rpow_ne_top : t ^ (α - 1) ≠ ⊤ := rpow_ne_top_of_nonneg hα_sub ht_top
  calc ∫⁻ x in {x | t < r x}, r x ∂ν
      ≤ ∫⁻ x in {x | t < r x}, (t ^ (α - 1))⁻¹ * r x ^ α ∂ν := by
        apply setLIntegral_mono' hS_meas
        intro x (hx : t < r x)
        have hrx_ne : r x ≠ 0 := ne_bot_of_gt hx
        by_cases hrx_top : r x = ⊤
        · rw [hrx_top, ENNReal.top_rpow_of_pos (show (0 : ℝ) < α by linarith)]
          simp [show (t ^ (α - 1))⁻¹ ≠ 0 from by rwa [ne_eq, ENNReal.inv_eq_zero]]
        · suffices h : r x * t ^ (α - 1) ≤ r x ^ α by
            calc r x = 1 * r x := (one_mul _).symm
              _ = (t ^ (α - 1))⁻¹ * t ^ (α - 1) * r x := by
                  rw [ENNReal.inv_mul_cancel ht_rpow_ne ht_rpow_ne_top]
              _ = (t ^ (α - 1))⁻¹ * (t ^ (α - 1) * r x) := mul_assoc _ _ _
              _ ≤ (t ^ (α - 1))⁻¹ * r x ^ α := by
                  gcongr; rwa [mul_comm] at h
          calc r x * t ^ (α - 1)
              = r x ^ (1 : ℝ) * t ^ (α - 1) := by rw [rpow_one]
            _ ≤ r x ^ (1 : ℝ) * r x ^ (α - 1) := by
                gcongr
            _ = r x ^ α := by
                rw [show r x ^ (1 : ℝ) * r x ^ (α - 1) = r x ^ (1 + (α - 1)) from
                  (ENNReal.rpow_add 1 (α - 1) hrx_ne hrx_top).symm,
                  show (1 : ℝ) + (α - 1) = α from by ring]
    _ = (t ^ (α - 1))⁻¹ * ∫⁻ x in {x | t < r x}, r x ^ α ∂ν :=
        lintegral_const_mul _ (hr_meas.pow_const α)
    _ ≤ (t ^ (α - 1))⁻¹ * renyiMoment α μ ν := by
        gcongr; exact setLIntegral_le_lintegral _ _

end PrivacyLoss

-- ============================================================================
-- Product Measures: Rényi Moment Multiplicativity
-- ============================================================================

section Product

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

private lemma rnDeriv_prod {μ₁ ν₁ : Measure Ω₁} {μ₂ ν₂ : Measure Ω₂}
    [SigmaFinite μ₁] [SigmaFinite ν₁] [SigmaFinite μ₂] [SigmaFinite ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂) :
    (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) =ᵐ[ν₁.prod ν₂]
      fun p => μ₁.rnDeriv ν₁ p.1 * μ₂.rnDeriv ν₂ p.2 := by
  have hf₁ : Measurable (μ₁.rnDeriv ν₁) := Measure.measurable_rnDeriv μ₁ ν₁
  have hf₂ : Measurable (μ₂.rnDeriv ν₂) := Measure.measurable_rnDeriv μ₂ ν₂
  set g : Ω₁ × Ω₂ → ℝ≥0∞ := fun p => μ₁.rnDeriv ν₁ p.1 * μ₂.rnDeriv ν₂ p.2
  have hg : Measurable g := (hf₁.comp measurable_fst).mul (hf₂.comp measurable_snd)
  have h_eq : μ₁.prod μ₂ = (ν₁.prod ν₂).withDensity g := by
    have h_wd : (ν₁.withDensity (μ₁.rnDeriv ν₁)).prod (ν₂.withDensity (μ₂.rnDeriv ν₂)) =
        (ν₁.prod ν₂).withDensity g := prod_withDensity hf₁ hf₂
    rw [Measure.withDensity_rnDeriv_eq μ₁ ν₁ h₁,
        Measure.withDensity_rnDeriv_eq μ₂ ν₂ h₂] at h_wd
    exact h_wd
  have key := Measure.rnDeriv_withDensity (ν₁.prod ν₂) hg
  rwa [← h_eq] at key

theorem renyiMoment_prod {μ₁ ν₁ : Measure Ω₁} {μ₂ ν₂ : Measure Ω₂}
    [SigmaFinite μ₁] [SigmaFinite ν₁] [SigmaFinite μ₂] [SigmaFinite ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂) {α : ℝ} (hα : 0 ≤ α) :
    renyiMoment α (μ₁.prod μ₂) (ν₁.prod ν₂) =
    renyiMoment α μ₁ ν₁ * renyiMoment α μ₂ ν₂ := by
  simp only [renyiMoment]
  have h_ae : (fun p => ((μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) p) ^ α) =ᵐ[ν₁.prod ν₂]
      fun p => (μ₁.rnDeriv ν₁ p.1) ^ α * (μ₂.rnDeriv ν₂ p.2) ^ α := by
    filter_upwards [rnDeriv_prod h₁ h₂] with p hp
    rw [hp, mul_rpow_of_nonneg _ _ hα]
  rw [lintegral_congr_ae h_ae]
  exact lintegral_prod_mul
    ((Measure.measurable_rnDeriv μ₁ ν₁).pow_const α |>.aemeasurable)
    ((Measure.measurable_rnDeriv μ₂ ν₂).pow_const α |>.aemeasurable)

end Product

-- ============================================================================
-- Pi (Finite Product) Measures: Rényi Moment Multiplicativity
-- ============================================================================

section PiMeasure

open Finset

/-- Rényi moment is preserved under measurable equivalences.
    If `e : Ω₁ ≃ᵐ Ω₂` and `μ₂ = μ₁.map e`, `ν₂ = ν₁.map e`, then
    `renyiMoment α μ₂ ν₂ = renyiMoment α μ₁ ν₁`. -/
theorem renyiMoment_map_measurableEquiv {Ω₁ Ω₂ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ ν : Measure Ω₁} [SigmaFinite μ] [SigmaFinite ν]
    (e : Ω₁ ≃ᵐ Ω₂) {α : ℝ} (hα : 0 ≤ α) :
    renyiMoment α (μ.map e) (ν.map e) = renyiMoment α μ ν := by
  simp only [renyiMoment]
  rw [lintegral_map_equiv _ e]
  apply lintegral_congr_ae
  have h_emb := e.measurableEmbedding
  filter_upwards [h_emb.rnDeriv_map μ ν] with x hx
  exact congr_arg (· ^ α) hx

private theorem absolutelyContinuous_pi_fin {n : ℕ}
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ ν : ∀ i, Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (hac : ∀ i, μ i ≪ ν i) :
    Measure.pi μ ≪ Measure.pi ν := by
  induction n with
  | zero => rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | succ n ih =>
    set e := MeasurableEquiv.piFinSuccAbove Ω 0
    have hmp_μ := (measurePreserving_piFinSuccAbove μ 0).map_eq
    have hmp_ν := (measurePreserving_piFinSuccAbove ν 0).map_eq
    have h_tail := ih (fun j => hac (Fin.succAbove 0 j))
    have h_prod := (hac 0).prod h_tail
    rw [← hmp_μ, ← hmp_ν] at h_prod
    have h2 := e.symm.measurableEmbedding.absolutelyContinuous_map h_prod
    rwa [Measure.map_map e.symm.measurable e.measurable,
         e.symm_comp_self, Measure.map_id,
         Measure.map_map e.symm.measurable e.measurable,
         e.symm_comp_self, Measure.map_id] at h2

/-- Absolute continuity for pi measures: if each component measure is
    absolutely continuous, so is the product measure. -/
theorem absolutelyContinuous_pi {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ ν : ∀ i, Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (hac : ∀ i, μ i ≪ ν i) :
    Measure.pi μ ≪ Measure.pi ν := by
  set f := (Fintype.equivFin ι).symm
  set e := MeasurableEquiv.piCongrLeft Ω f
  have h_fin := absolutelyContinuous_pi_fin (fun j => hac (f j))
  have h_map := e.measurableEmbedding.absolutelyContinuous_map h_fin
  rwa [(measurePreserving_piCongrLeft μ f).map_eq,
       (measurePreserving_piCongrLeft ν f).map_eq] at h_map

/-- Rényi moment multiplicativity for `Fin n`-indexed pi measures.
    `renyiMoment α (Measure.pi μ) (Measure.pi ν) = ∏ i, renyiMoment α (μ i) (ν i)` -/
private theorem renyiMoment_pi_fin {n : ℕ}
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ ν : ∀ i, Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (hac : ∀ i, μ i ≪ ν i) {α : ℝ} (hα : 0 ≤ α) :
    renyiMoment α (Measure.pi μ) (Measure.pi ν) =
    ∏ i : Fin n, renyiMoment α (μ i) (ν i) := by
  induction n with
  | zero =>
    simp only [univ_eq_empty, prod_empty]
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
    simp only [renyiMoment]
    have h_ae : (fun y => ((Measure.dirac (isEmptyElim : ∀ a : Fin 0, Ω a)).rnDeriv
        (Measure.dirac isEmptyElim) y) ^ α) =ᵐ[Measure.dirac isEmptyElim] fun _ => 1 := by
      filter_upwards [Measure.rnDeriv_self (Measure.dirac (isEmptyElim : ∀ a : Fin 0, Ω a))]
        with y hy
      simp [hy, one_rpow]
    rw [lintegral_congr_ae h_ae, lintegral_one, measure_univ]
  | succ n ih =>
    set e := MeasurableEquiv.piFinSuccAbove Ω 0
    have h_tail_ac := absolutelyContinuous_pi_fin (fun j => hac (Fin.succAbove 0 j))
    have h1 : renyiMoment α (Measure.pi μ) (Measure.pi ν) =
        renyiMoment α ((Measure.pi μ).map e) ((Measure.pi ν).map e) :=
      (renyiMoment_map_measurableEquiv e hα).symm
    rw [h1, (measurePreserving_piFinSuccAbove μ 0).map_eq,
        (measurePreserving_piFinSuccAbove ν 0).map_eq,
        renyiMoment_prod (hac 0) h_tail_ac hα,
        ih (fun j => hac (Fin.succAbove 0 j))]
    exact (Fin.prod_univ_succAbove (fun i => renyiMoment α (μ i) (ν i)) 0).symm

/-- **Rényi moment multiplicativity for finite product measures.**
    For independent pairs (μ i, ν i), the Rényi moment of the joint
    distribution equals the product of the marginal Rényi moments. -/
theorem renyiMoment_pi {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ ν : ∀ i, Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (hac : ∀ i, μ i ≪ ν i) {α : ℝ} (hα : 0 ≤ α) :
    renyiMoment α (Measure.pi μ) (Measure.pi ν) =
    ∏ i, renyiMoment α (μ i) (ν i) := by
  set f := (Fintype.equivFin ι).symm
  set e := MeasurableEquiv.piCongrLeft Ω f
  have hmp_μ := (measurePreserving_piCongrLeft μ f).map_eq
  have hmp_ν := (measurePreserving_piCongrLeft ν f).map_eq
  have h_eq : renyiMoment α (Measure.pi μ) (Measure.pi ν) =
      renyiMoment α (Measure.pi (fun j => μ (f j))) (Measure.pi (fun j => ν (f j))) := by
    rw [← hmp_μ, ← hmp_ν, ← renyiMoment_map_measurableEquiv e hα]
  rw [h_eq, renyiMoment_pi_fin (fun j => hac (f j)) hα]
  exact f.prod_comp (fun i => renyiMoment α (μ i) (ν i))

end PiMeasure

end DPlean4
