/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.RenyiDivergence
import DPlean4.Privacy.Approximate
import DPlean4.Probability.Mechanism

/-!
# Zero-Concentrated Differential Privacy (zCDP)

This file defines ρ-zCDP (Bun & Dwork, 2016) and proves the key conversion
theorem from zCDP to (ε,δ)-approximate DP.

## Main Definitions

* `IsZCDP adj M ρ`: Mechanism M satisfies ρ-zCDP

## Main Results

* `isZCDP_to_isApproxDP`: ρ-zCDP implies (ε,δ)-DP for ε ≥ ρ + 2√(ρ·log(1/δ))
* `isZCDP_postprocess`: zCDP is preserved under measurable postprocessing

## Design Notes

zCDP is defined via Rényi divergence: M is ρ-zCDP if for all adjacent d₁, d₂
and all α > 1, D_α(M(d₁)‖M(d₂)) ≤ ρ·α.

The conversion to (ε,δ)-DP uses:
1. Privacy loss decomposition: P(S) ≤ exp(ε)·Q(S) + P({log(dP/dQ) > ε})
2. Markov's inequality on exp(t·log(dP/dQ))
3. The zCDP bound on the Rényi moment
4. Optimization over t (choosing t = (ε-ρ)/(2ρ))
-/

namespace DPlean4

open MeasureTheory ENNReal Real

variable {D O : Type*} [MeasurableSpace O]

/-- A mechanism satisfies ρ-zCDP (zero-concentrated differential privacy)
    if for all adjacent databases d₁, d₂ and all α > 1:
    D_α(M(d₁)‖M(d₂)) ≤ ρ·α

    Equivalently, the Rényi moment satisfies:
    ∫ (dM(d₁)/dM(d₂))^α dM(d₂) ≤ exp((α-1)·ρ·α) -/
def IsZCDP (adj : D → D → Prop) (M : Mechanism D O) (ρ : NNReal) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → ∀ α : ℝ, 1 < α →
    renyiDivergence α (M d₁).toMeasure (M d₂).toMeasure ≤ ρ * α

/-- zCDP is monotone: if M is ρ₁-zCDP and ρ₁ ≤ ρ₂, then M is ρ₂-zCDP. -/
theorem isZCDP_mono {adj : D → D → Prop} {M : Mechanism D O} {ρ₁ ρ₂ : NNReal}
    (h : IsZCDP adj M ρ₁) (hle : ρ₁ ≤ ρ₂) :
    IsZCDP adj M ρ₂ := by
  intro d₁ d₂ hadj α hα
  calc renyiDivergence α (M d₁).toMeasure (M d₂).toMeasure
      ≤ ↑ρ₁ * α := h d₁ d₂ hadj α hα
    _ ≤ ↑ρ₂ * α := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hle
        · linarith

/-- **zCDP → (ε,δ)-DP conversion** (Bun & Dwork, 2016, Proposition 3).

    If M is ρ-zCDP with ρ > 0, then for any δ ∈ (0,1) and ε ≥ ρ + 2√(ρ·log(1/δ)),
    M satisfies (ε,δ)-approximate DP.

    **Proof sketch:**
    1. For any event S: P(S) ≤ exp(ε)·Q(S) + P({log(dP/dQ) > ε})
    2. P({log(dP/dQ) > ε}) ≤ E_Q[(dP/dQ)^α] / exp((α-1)ε)  [Markov]
    3. ≤ exp((α-1)(ρα - ε))  [zCDP bound]
    4. Choose α = 1 + √(log(1/δ)/ρ) to get ≤ exp(-log(1/δ)) = δ -/
theorem isZCDP_to_isApproxDP {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (hM : IsZCDP adj M ρ) (hρ : 0 < ρ)
    (hac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure)
    (hfin : ∀ d₁ d₂, adj d₁ d₂ → ∀ α : ℝ, 1 < α →
      renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤)
    {ε δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hε : (ε : ℝ) ≥ ↑ρ + 2 * sqrt (↑ρ * log (1 / ↑δ))) :
    IsApproxDP adj M ε δ := by
  have hρ' : (0 : ℝ) < ↑ρ := by exact_mod_cast hρ
  have hδ' : (0 : ℝ) < ↑δ := by exact_mod_cast hδ
  set L := log (1 / (δ : ℝ))
  have hL : 0 < L := log_pos (by rw [one_div]; exact (one_lt_inv₀ hδ').mpr (by linarith))
  set α := 1 + sqrt (L / ↑ρ) with hα_def
  have hα : 1 < α := by linarith [sqrt_pos.mpr (div_pos hL hρ')]
  intro d₁ d₂ hadj S hS
  set μ := (M d₁).toMeasure
  set ν := (M d₂).toMeasure
  have hac' := hac d₁ d₂ hadj
  have hfin' := hfin d₁ d₂ hadj α hα
  -- Step 1: Set threshold t = exp(ε)
  set t := ENNReal.ofReal (exp ↑ε) with ht_def
  have ht_ne : t ≠ 0 := by
    simp only [t, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact exp_pos _
  have ht_top : t ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Step 2: Privacy loss decomposition + tail bound
  have h_decomp := measure_le_mul_add_rnDeriv_tail hac' S t
  have h_tail := rnDeriv_tail_le_renyiMoment_div hac' (le_of_lt hα) ht_ne ht_top
  -- Step 3: Bound renyiMoment via zCDP
  have h_zcdp := hM d₁ d₂ hadj α hα
  have h_moment := (renyiDivergence_le_iff hα (by positivity : (0:ℝ) ≤ ↑ρ * α) hfin').mp h_zcdp
  -- Step 4: Show tail ≤ δ
  suffices h_tail_le : renyiMoment α μ ν / t ^ (α - 1) ≤ (δ : ENNReal) by
    calc μ S ≤ t * ν S + μ {x | t < μ.rnDeriv ν x} := h_decomp
      _ ≤ t * ν S + renyiMoment α μ ν / t ^ (α - 1) := by gcongr
      _ ≤ t * ν S + (δ : ENNReal) := by gcongr
      _ = ENNReal.ofReal (exp ↑ε) * ν S + (δ : ENNReal) := rfl
  -- Prove the tail bound: renyiMoment / t^(α-1) ≤ δ
  -- Using div_le_iff: renyiMoment ≤ δ * t^(α-1)
  have hα_sub : (0 : ℝ) ≤ α - 1 := by linarith
  have ht_rpow_ne : t ^ (α - 1) ≠ 0 :=
    (rpow_pos_of_nonneg (by rwa [pos_iff_ne_zero]) hα_sub).ne'
  have ht_rpow_ne_top : t ^ (α - 1) ≠ ⊤ := rpow_ne_top_of_nonneg hα_sub ht_top
  rw [ENNReal.div_le_iff ht_rpow_ne ht_rpow_ne_top]
  -- Goal: renyiMoment α μ ν ≤ δ * t^(α-1)
  -- Strategy: renyiMoment ≤ ofReal(exp((α-1)*ρ*α)) ≤ δ * t^(α-1)
  calc renyiMoment α μ ν
      ≤ ENNReal.ofReal (exp ((α - 1) * (↑ρ * α))) := h_moment
    _ ≤ (δ : ENNReal) * t ^ (α - 1) := by
        -- Convert t^(α-1) = ofReal(exp(ε*(α-1)))
        have h_t_rpow : t ^ (α - 1) = ENNReal.ofReal (exp (↑ε * (α - 1))) := by
          rw [ht_def, ENNReal.ofReal_rpow_of_pos (exp_pos _)]
          congr 1; rw [rpow_def_of_pos (exp_pos _), log_exp, mul_comm]
        rw [h_t_rpow]
        -- Convert δ * ofReal(exp(...)) = ofReal(δ * exp(...))
        rw [show (δ : ENNReal) = ENNReal.ofReal (↑δ) from (ENNReal.ofReal_coe_nnreal).symm,
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ↑δ)]
        apply ENNReal.ofReal_le_ofReal
        -- Pure ℝ: exp((α-1)*ρα) ≤ δ * exp(ε*(α-1))
        -- Factor LHS = exp((α-1)*(ρα-ε)) * exp(ε*(α-1)), then bound first factor
        suffices h_exp_bound : exp ((α - 1) * (↑ρ * α - ↑ε)) ≤ ↑δ by
          calc exp ((α - 1) * (↑ρ * α))
              = exp ((α - 1) * (↑ρ * α - ↑ε) + ↑ε * (α - 1)) := by congr 1; ring
            _ = exp ((α - 1) * (↑ρ * α - ↑ε)) * exp (↑ε * (α - 1)) := exp_add _ _
            _ ≤ ↑δ * exp (↑ε * (α - 1)) :=
                mul_le_mul_of_nonneg_right h_exp_bound (exp_pos _).le
        -- Prove exp((α-1)*(ρα-ε)) ≤ δ via choice of α = 1 + √(L/ρ)
        have h_ρα1_sq : ↑ρ * (α - 1) ^ 2 = L := by
          rw [hα_def, show 1 + sqrt (L / ↑ρ) - 1 = sqrt (L / ↑ρ) from by ring,
              sq_sqrt (div_nonneg hL.le hρ'.le)]
          field_simp
        have h_α1_sqrtρL : (α - 1) * sqrt (↑ρ * L) = L := by
          rw [hα_def, show 1 + sqrt (L / ↑ρ) - 1 = sqrt (L / ↑ρ) from by ring,
              ← sqrt_mul (div_nonneg hL.le hρ'.le),
              show L / ↑ρ * (↑ρ * L) = L ^ 2 from by field_simp,
              sqrt_sq hL.le]
        have h_εα1 : (α - 1) * ↑ε ≥ (α - 1) * ↑ρ + 2 * L := by
          have := mul_le_mul_of_nonneg_left
            (show ↑ρ + 2 * sqrt (↑ρ * L) ≤ ↑ε from by linarith)
            (show (0 : ℝ) ≤ α - 1 from by linarith)
          calc (α - 1) * ↑ε
              ≥ (α - 1) * (↑ρ + 2 * sqrt (↑ρ * L)) := this
            _ = (α - 1) * ↑ρ + 2 * ((α - 1) * sqrt (↑ρ * L)) := by ring
            _ = (α - 1) * ↑ρ + 2 * L := by rw [h_α1_sqrtρL]
        have h_bound : (α - 1) * (↑ρ * α - ↑ε) ≤ -L := by
          have : (α - 1) * (↑ρ * α - ↑ε) =
              (α - 1) * ↑ρ + ↑ρ * (α - 1) ^ 2 - (α - 1) * ↑ε := by ring
          rw [this, h_ρα1_sq]; linarith
        calc exp ((α - 1) * (↑ρ * α - ↑ε))
            ≤ exp (-L) := exp_le_exp.mpr h_bound
          _ = ↑δ := by
              rw [show L = log (1 / ↑δ) from rfl, exp_neg,
                  exp_log (show (0 : ℝ) < 1 / ↑δ from by positivity)]
              field_simp

/-- A weaker but simpler form: zCDP with explicit ε computation. -/
theorem isZCDP_to_isApproxDP' {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (hM : IsZCDP adj M ρ) (hρ : 0 < ρ)
    (hac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure)
    (hfin : ∀ d₁ d₂, adj d₁ d₂ → ∀ α : ℝ, 1 < α →
      renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) :
    ∃ ε : NNReal, IsApproxDP adj M ε δ := by
  refine ⟨⟨↑ρ + 2 * sqrt (↑ρ * log (1 / ↑δ)),
    add_nonneg (NNReal.coe_nonneg ρ) (mul_nonneg (by norm_num) (sqrt_nonneg _))⟩,
    isZCDP_to_isApproxDP hM hρ hac hfin hδ hδ1 (le_refl _)⟩

/-- zCDP implies approximate DP for any ε > ρ with suitable δ. -/
theorem isZCDP_to_isPureDP_trivial {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (hM : IsZCDP adj M ρ) (hρ : 0 < ρ)
    (hac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure)
    (hfin : ∀ d₁ d₂, adj d₁ d₂ → ∀ α : ℝ, 1 < α →
      renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤) :
    ∀ ε : NNReal, (ε : ℝ) > ρ → ∃ δ : NNReal, IsApproxDP adj M ε δ := by
  intro ε hε
  have hρ' : (0 : ℝ) < ↑ρ := by exact_mod_cast hρ
  have hερ : (↑ε : ℝ) - ↑ρ > 0 := by linarith
  set c : ℝ := ((↑ε : ℝ) - ↑ρ) ^ 2 / (4 * ↑ρ)
  have hc_pos : 0 < c := div_pos (sq_pos_of_pos hερ) (by positivity)
  refine ⟨⟨exp (-c), (exp_pos _).le⟩,
    isZCDP_to_isApproxDP hM hρ hac hfin ?_ ?_ ?_⟩
  · exact_mod_cast exp_pos (-c)
  · change exp (-c) < 1
    exact exp_lt_one_iff.mpr (by linarith)
  · change (↑ε : ℝ) ≥ ↑ρ + 2 * sqrt (↑ρ * log (1 / exp (-c)))
    have h_log : Real.log (1 / exp (-c)) = c := by
      rw [one_div, ← exp_neg, neg_neg, log_exp]
    rw [h_log]
    have h_sqrt : sqrt ((↑ρ : ℝ) * c) = ((↑ε : ℝ) - ↑ρ) / 2 := by
      have : (↑ρ : ℝ) * c = (((↑ε : ℝ) - ↑ρ) / 2) ^ 2 := by
        simp only [c]; field_simp; ring
      rw [this, sqrt_sq (by linarith : (0 : ℝ) ≤ ((↑ε : ℝ) - ↑ρ) / 2)]
    rw [h_sqrt]; linarith

section Postprocessing

variable {O₂ : Type*} [MeasurableSpace O₂]

/-- zCDP is preserved under measurable postprocessing.

    This follows from the data processing inequality for Rényi divergence:
    D_α(f#μ ‖ f#ν) ≤ D_α(μ ‖ ν) for any measurable f.

    Requires absolute continuity and finite Rényi moments (both implied by the
    mathematical zCDP definition, but made explicit here due to our convention
    that `renyiDivergence = 0` when the moment is `⊤`). -/
theorem isZCDP_postprocess {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (hM : IsZCDP adj M ρ) {f : O → O₂} (hf : Measurable f)
    (hac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure)
    (hfin : ∀ d₁ d₂, adj d₁ d₂ → ∀ α : ℝ, 1 < α →
      renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤) :
    IsZCDP adj (fun d => (M d).map hf.aemeasurable) ρ := by
  intro d₁ d₂ hadj α hα
  simp only [ProbabilityMeasure.toMeasure_map]
  set μ := (M d₁).toMeasure
  set ν := (M d₂).toMeasure
  have hac' := hac d₁ d₂ hadj
  have hfin' := hfin d₁ d₂ hadj α hα
  have h_moment := renyiMoment_map_le hac' hf (le_of_lt hα) hfin'
  have h_mapped_fin : renyiMoment α (μ.map f) (ν.map f) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin' h_moment
  have : IsProbabilityMeasure (μ.map f) := μ.isProbabilityMeasure_map hf.aemeasurable
  have : IsProbabilityMeasure (ν.map f) := ν.isProbabilityMeasure_map hf.aemeasurable
  have h_mapped_ge : 1 ≤ renyiMoment α (μ.map f) (ν.map f) :=
    renyiMoment_ge_one hα (hac'.map hf)
  have h_mapped_pos : renyiMoment α (μ.map f) (ν.map f) ≠ 0 := by
    intro h; rw [h] at h_mapped_ge; simp at h_mapped_ge
  simp only [renyiDivergence]
  have hα_pos : (0 : ℝ) < α - 1 := by linarith
  calc (α - 1)⁻¹ * log (renyiMoment α (μ.map f) (ν.map f)).toReal
      ≤ (α - 1)⁻¹ * log (renyiMoment α μ ν).toReal := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hα_pos.le)
        exact log_le_log (ENNReal.toReal_pos h_mapped_pos h_mapped_fin)
          (ENNReal.toReal_mono hfin' h_moment)
    _ ≤ ↑ρ * α := hM d₁ d₂ hadj α hα

end Postprocessing

section Composition

variable {O₁ O₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]

/-- Independent composition for zCDP: if M₁ is ρ₁-zCDP and M₂ is ρ₂-zCDP,
    then their product mechanism is (ρ₁+ρ₂)-zCDP.

    This follows from the additivity of Rényi divergence for product measures:
    D_α(μ₁⊗μ₂ ‖ ν₁⊗ν₂) = D_α(μ₁‖ν₁) + D_α(μ₂‖ν₂). -/
theorem isZCDP_prod {adj : D → D → Prop}
    {M₁ : Mechanism D O₁} {M₂ : Mechanism D O₂} {ρ₁ ρ₂ : NNReal}
    (h₁ : IsZCDP adj M₁ ρ₁) (h₂ : IsZCDP adj M₂ ρ₂)
    (hac₁ : ∀ d₁ d₂, adj d₁ d₂ → (M₁ d₁).toMeasure ≪ (M₁ d₂).toMeasure)
    (hac₂ : ∀ d₁ d₂, adj d₁ d₂ → (M₂ d₁).toMeasure ≪ (M₂ d₂).toMeasure) :
    IsZCDP adj (M₁.prod M₂) (ρ₁ + ρ₂) := by
  intro d₁ d₂ hadj α hα
  simp only [Mechanism.prod_toMeasure]
  have hac₁' := hac₁ d₁ d₂ hadj
  have hac₂' := hac₂ d₁ d₂ hadj
  have hd₁ := h₁ d₁ d₂ hadj α hα
  have hd₂ := h₂ d₁ d₂ hadj α hα
  simp only [renyiDivergence] at hd₁ hd₂ ⊢
  rw [renyiMoment_prod hac₁' hac₂' (by linarith : (0 : ℝ) ≤ α), ENNReal.toReal_mul]
  set m₁ := (renyiMoment α (M₁ d₁).toMeasure (M₁ d₂).toMeasure).toReal
  set m₂ := (renyiMoment α (M₂ d₁).toMeasure (M₂ d₂).toMeasure).toReal
  by_cases hm₁ : m₁ = 0
  · simp only [hm₁, zero_mul, Real.log_zero, mul_zero]
    positivity
  · by_cases hm₂ : m₂ = 0
    · simp only [hm₂, mul_zero, Real.log_zero, mul_zero]
      positivity
    · rw [Real.log_mul hm₁ hm₂, mul_add]
      have : ↑(ρ₁ + ρ₂) * α = ↑ρ₁ * α + ↑ρ₂ * α := by push_cast; ring
      linarith

end Composition

end DPlean4
