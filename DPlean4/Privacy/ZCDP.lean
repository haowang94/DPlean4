/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.RenyiDivergence
import DPlean4.Privacy.Approximate
import DPlean4.Probability.Mechanism
import DPlean4.Probability.AdaptiveComposition
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Zero-Concentrated Differential Privacy (zCDP)

This file defines ρ-zCDP (Bun & Dwork, 2016) and proves the key conversion
theorem from zCDP to (ε,δ)-approximate DP.

## Main Definitions

* `IsZCDP adj M ρ`: Mechanism M satisfies ρ-zCDP

## Main Results

* `isApproxDP_of_isZCDP`: ρ-zCDP implies (ε,δ)-DP for ε ≥ ρ + 2√(ρ·log(1/δ))
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

    This definition bundles absolute continuity and Rényi moment finiteness
    alongside the divergence bound, ensuring IsZCDP is a self-contained
    privacy guarantee. (Without these conditions, the Rényi divergence
    convention `renyiDivergence = 0` when the moment is `⊤` would make
    IsZCDP vacuously satisfiable by non-private mechanisms.) -/
structure IsZCDP (adj : D → D → Prop) (M : Mechanism D O) (ρ : NNReal) : Prop where
  ac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure
  fin : ∀ d₁ d₂, adj d₁ d₂ → ∀ α : ℝ, 1 < α →
    renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤
  bound : ∀ d₁ d₂, adj d₁ d₂ → ∀ α : ℝ, 1 < α →
    renyiDivergence α (M d₁).toMeasure (M d₂).toMeasure ≤ ρ * α

/-- zCDP is monotone: if M is ρ₁-zCDP and ρ₁ ≤ ρ₂, then M is ρ₂-zCDP. -/
theorem isZCDP_mono {adj : D → D → Prop} {M : Mechanism D O} {ρ₁ ρ₂ : NNReal}
    (h : IsZCDP adj M ρ₁) (hle : ρ₁ ≤ ρ₂) :
    IsZCDP adj M ρ₂ where
  ac := h.ac
  fin := h.fin
  bound d₁ d₂ hadj α hα :=
    calc renyiDivergence α (M d₁).toMeasure (M d₂).toMeasure
        ≤ ↑ρ₁ * α := h.bound d₁ d₂ hadj α hα
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
theorem isApproxDP_of_isZCDP {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (hM : IsZCDP adj M ρ) (hρ : 0 < ρ)
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
  have hac' := hM.ac d₁ d₂ hadj
  have hfin' := hM.fin d₁ d₂ hadj α hα
  -- Step 1: Set threshold t = exp(ε)
  set t := ENNReal.ofReal (exp ↑ε) with ht_def
  have ht_ne : t ≠ 0 := by
    simp only [t, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact exp_pos _
  have ht_top : t ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Step 2: Privacy loss decomposition + tail bound
  have h_decomp := measure_le_mul_add_rnDeriv_tail hac' S t
  have h_tail := rnDeriv_tail_le_renyiMoment_div hac' (le_of_lt hα) ht_ne ht_top
  -- Step 3: Bound renyiMoment via zCDP
  have h_zcdp := hM.bound d₁ d₂ hadj α hα
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
theorem isApproxDP_of_isZCDP' {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (hM : IsZCDP adj M ρ) (hρ : 0 < ρ)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) :
    ∃ ε : NNReal, IsApproxDP adj M ε δ := by
  refine ⟨⟨↑ρ + 2 * sqrt (↑ρ * log (1 / ↑δ)),
    add_nonneg (NNReal.coe_nonneg ρ) (mul_nonneg (by norm_num) (sqrt_nonneg _))⟩,
    isApproxDP_of_isZCDP hM hρ hδ hδ1 (le_refl _)⟩

/-- zCDP implies approximate DP for any ε > ρ with suitable δ. -/
theorem isApproxDP_of_isZCDP_of_gt {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (hM : IsZCDP adj M ρ) (hρ : 0 < ρ) :
    ∀ ε : NNReal, (ε : ℝ) > ρ → ∃ δ : NNReal, IsApproxDP adj M ε δ := by
  intro ε hε
  have hρ' : (0 : ℝ) < ↑ρ := by exact_mod_cast hρ
  have hερ : (↑ε : ℝ) - ↑ρ > 0 := by linarith
  set c : ℝ := ((↑ε : ℝ) - ↑ρ) ^ 2 / (4 * ↑ρ)
  have hc_pos : 0 < c := div_pos (sq_pos_of_pos hερ) (by positivity)
  refine ⟨⟨exp (-c), (exp_pos _).le⟩,
    isApproxDP_of_isZCDP hM hρ ?_ ?_ ?_⟩
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
    D_α(f#μ ‖ f#ν) ≤ D_α(μ ‖ ν) for any measurable f. -/
theorem isZCDP_postprocess {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (hM : IsZCDP adj M ρ) {f : O → O₂} (hf : Measurable f) :
    IsZCDP adj (fun d => (M d).map hf.aemeasurable) ρ where
  ac d₁ d₂ hadj := by
    simp only [ProbabilityMeasure.toMeasure_map]
    exact (hM.ac d₁ d₂ hadj).map hf
  fin d₁ d₂ hadj α hα := by
    simp only [ProbabilityMeasure.toMeasure_map]
    exact ne_top_of_le_ne_top (hM.fin d₁ d₂ hadj α hα)
      (renyiMoment_map_le (hM.ac d₁ d₂ hadj) hf (le_of_lt hα) (hM.fin d₁ d₂ hadj α hα))
  bound d₁ d₂ hadj α hα := by
    simp only [ProbabilityMeasure.toMeasure_map]
    set μ := (M d₁).toMeasure
    set ν := (M d₂).toMeasure
    have hac' := hM.ac d₁ d₂ hadj
    have hfin' := hM.fin d₁ d₂ hadj α hα
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
      _ ≤ ↑ρ * α := hM.bound d₁ d₂ hadj α hα

end Postprocessing

section Composition

variable {O₁ O₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]

/-- Independent composition for zCDP: if M₁ is ρ₁-zCDP and M₂ is ρ₂-zCDP,
    then their product mechanism is (ρ₁+ρ₂)-zCDP.

    This follows from the additivity of Rényi divergence for product measures:
    D_α(μ₁⊗μ₂ ‖ ν₁⊗ν₂) = D_α(μ₁‖ν₁) + D_α(μ₂‖ν₂). -/
theorem isZCDP_prod {adj : D → D → Prop}
    {M₁ : Mechanism D O₁} {M₂ : Mechanism D O₂} {ρ₁ ρ₂ : NNReal}
    (h₁ : IsZCDP adj M₁ ρ₁) (h₂ : IsZCDP adj M₂ ρ₂) :
    IsZCDP adj (M₁.prod M₂) (ρ₁ + ρ₂) where
  ac d₁ d₂ hadj := by
    simp only [Mechanism.prod_toMeasure]
    exact Measure.AbsolutelyContinuous.prod (h₁.ac d₁ d₂ hadj) (h₂.ac d₁ d₂ hadj)
  fin d₁ d₂ hadj α hα := by
    simp only [Mechanism.prod_toMeasure]
    rw [renyiMoment_prod (h₁.ac d₁ d₂ hadj) (h₂.ac d₁ d₂ hadj) (by linarith : (0 : ℝ) ≤ α)]
    exact ENNReal.mul_ne_top (h₁.fin d₁ d₂ hadj α hα) (h₂.fin d₁ d₂ hadj α hα)
  bound d₁ d₂ hadj α hα := by
    simp only [Mechanism.prod_toMeasure]
    have hac₁' := h₁.ac d₁ d₂ hadj
    have hac₂' := h₂.ac d₁ d₂ hadj
    have hd₁ := h₁.bound d₁ d₂ hadj α hα
    have hd₂ := h₂.bound d₁ d₂ hadj α hα
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

-- ============================================================================
-- Pi (Finite Product) Composition for zCDP
-- ============================================================================

section PiComposition

open Finset

variable {ι : Type*} [Fintype ι] {O' : ι → Type*} [∀ i, MeasurableSpace (O' i)]

/-- **N-ary independent composition for zCDP**: if each Mᵢ is ρᵢ-zCDP, then
    the product mechanism `Mechanism.pi M` is (∑ᵢ ρᵢ)-zCDP.

    This generalizes `isZCDP_prod` from binary to finite products, using
    the multiplicativity of Rényi moments (`renyiMoment_pi`). -/
theorem isZCDP_pi {adj : D → D → Prop}
    {M : ∀ i, Mechanism D (O' i)} {ρ : ι → NNReal}
    (h : ∀ i, IsZCDP adj (M i) (ρ i)) :
    IsZCDP adj (Mechanism.pi M) (∑ i, ρ i) where
  ac d₁ d₂ hadj := by
    simp only [Mechanism.pi_toMeasure]
    exact absolutelyContinuous_pi (fun i => (h i).ac d₁ d₂ hadj)
  fin d₁ d₂ hadj α hα := by
    simp only [Mechanism.pi_toMeasure]
    rw [renyiMoment_pi (fun i => (h i).ac d₁ d₂ hadj) (by linarith : (0 : ℝ) ≤ α)]
    exact ENNReal.prod_ne_top fun i _ => (h i).fin d₁ d₂ hadj α hα
  bound d₁ d₂ hadj α hα := by
    simp only [Mechanism.pi_toMeasure]
    have hac' : ∀ i, (M i d₁).toMeasure ≪ (M i d₂).toMeasure := fun i => (h i).ac d₁ d₂ hadj
    have hfin' : ∀ i, renyiMoment α (M i d₁).toMeasure (M i d₂).toMeasure ≠ ⊤ :=
      fun i => (h i).fin d₁ d₂ hadj α hα
    have hα_pos : (0 : ℝ) < α - 1 := by linarith
    have h_bound : ∀ i,
        renyiDivergence α (M i d₁).toMeasure (M i d₂).toMeasure ≤ ↑(ρ i) * α :=
      fun i => (h i).bound d₁ d₂ hadj α hα
    simp only [renyiDivergence] at h_bound ⊢
    rw [renyiMoment_pi hac' (by linarith : (0 : ℝ) ≤ α), ENNReal.toReal_prod]
    have h_ne : ∀ i, (renyiMoment α (M i d₁).toMeasure (M i d₂).toMeasure).toReal ≠ 0 :=
      fun i => ne_of_gt (ENNReal.toReal_pos
        (ne_of_gt (lt_of_lt_of_le one_pos (renyiMoment_ge_one hα (hac' i))))
        (hfin' i))
    calc (α - 1)⁻¹ * Real.log (∏ i, (renyiMoment α (M i d₁).toMeasure
              (M i d₂).toMeasure).toReal)
        = (α - 1)⁻¹ * ∑ i, Real.log ((renyiMoment α (M i d₁).toMeasure
              (M i d₂).toMeasure).toReal) :=
          congr_arg _ (Real.log_prod fun i _ => h_ne i)
      _ = ∑ i, (α - 1)⁻¹ * Real.log ((renyiMoment α (M i d₁).toMeasure
              (M i d₂).toMeasure).toReal) := mul_sum _ _ _
      _ ≤ ∑ i, ↑(ρ i) * α := sum_le_sum fun i _ => h_bound i
      _ = ↑(∑ i, ρ i) * α := by push_cast; rw [sum_mul]

/-- **Uniform n-ary zCDP composition**: running the same ρ-zCDP mechanism k times
    independently gives (k·ρ)-zCDP.

    This is a corollary of `isZCDP_pi` for the common case where all mechanisms
    and privacy costs are identical. -/
theorem isZCDP_piCopy {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (h : IsZCDP adj M ρ) {k : ℕ} :
    IsZCDP adj (M.piCopy k) (k * ρ) := by
  have h_eq : M.piCopy k = Mechanism.pi (fun (_ : Fin k) => M) :=
    funext (fun d => by simp [Mechanism.piCopy, Mechanism.pi])
  rw [h_eq]
  have key := isZCDP_pi (fun (_ : Fin k) => h)
  simp only [sum_const, card_fin, nsmul_eq_mul] at key
  exact key

end PiComposition

-- ============================================================================
-- Adaptive (Sequential) Composition for zCDP
-- ============================================================================

section AdaptiveComposition

variable {O₁ O₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]

open ProbabilityTheory MeasureTheory.Measure

private noncomputable def contKernel [Fintype O₁] [MeasurableSingletonClass O₁]
    (K : O₁ → Mechanism D O₂) (d : D) : Kernel O₁ O₂ where
  toFun o₁ := (K o₁ d).toMeasure
  measurable' := measurable_of_finite _

private instance contKernel_isMarkov [Fintype O₁] [MeasurableSingletonClass O₁]
    (K : O₁ → Mechanism D O₂) (d : D) : IsMarkovKernel (contKernel K d) :=
  ⟨fun a => by change IsProbabilityMeasure (K a d).toMeasure; infer_instance⟩

private noncomputable def contKernelOfMeas
    (K : O₁ → Mechanism D O₂) (d : D)
    (h : Measurable (fun o₁ => (K o₁ d).toMeasure)) : Kernel O₁ O₂ where
  toFun o₁ := (K o₁ d).toMeasure
  measurable' := h

private instance contKernelOfMeas_isMarkov
    (K : O₁ → Mechanism D O₂) (d : D)
    (h : Measurable (fun o₁ => (K o₁ d).toMeasure)) :
    IsMarkovKernel (contKernelOfMeas K d h) :=
  ⟨fun a => by change IsProbabilityMeasure (K a d).toMeasure; infer_instance⟩

private lemma seqFinite_eq_compProd [Fintype O₁] [MeasurableSingletonClass O₁]
    (M₁ : Mechanism D O₁) (K : O₁ → Mechanism D O₂) (d : D) :
    (M₁.seqFinite K d).toMeasure = (M₁ d).toMeasure ⊗ₘ contKernel K d := by
  ext s hs
  change ((M₁ d).toMeasure.bind
    (fun o₁ => ((K o₁ d).toMeasure).map (Prod.mk o₁))) s = _
  rw [Measure.bind_apply hs (measurable_of_finite _).aemeasurable,
      Measure.compProd_apply hs]
  congr 1; ext o₁
  exact Measure.map_apply measurable_prodMk_left hs

private lemma seq_eq_compProd
    {M₁ : Mechanism D O₁} {K : O₁ → Mechanism D O₂}
    (hK : ∀ d, AEMeasurable (fun o₁ => ((K o₁ d).toMeasure).map (Prod.mk o₁))
      (M₁ d).toMeasure)
    (hK_meas : ∀ d, Measurable (fun o₁ => (K o₁ d).toMeasure))
    (d : D) :
    (M₁.seq K hK d).toMeasure =
      (M₁ d).toMeasure ⊗ₘ contKernelOfMeas K d (hK_meas d) := by
  ext s hs
  change ((M₁ d).toMeasure.bind
    (fun o₁ => ((K o₁ d).toMeasure).map (Prod.mk o₁))) s = _
  rw [Measure.bind_apply hs (hK d), Measure.compProd_apply hs]
  congr 1; ext o₁
  exact Measure.map_apply measurable_prodMk_left hs

private lemma rnDeriv_compProd_same_marginal
    [MeasurableSpace.CountableOrCountablyGenerated O₁ O₂]
    {μ : Measure O₁} {κ₁ κ₂ : Kernel O₁ O₂}
    [IsProbabilityMeasure μ] [IsMarkovKernel κ₁] [IsMarkovKernel κ₂]
    (hκ : ∀ o₁, κ₁ o₁ ≪ κ₂ o₁) :
    (μ ⊗ₘ κ₁).rnDeriv (μ ⊗ₘ κ₂) =ᵐ[μ ⊗ₘ κ₂]
      fun p => Kernel.rnDeriv κ₁ κ₂ p.1 p.2 := by
  have hκ_eq : κ₂.withDensity (κ₁.rnDeriv κ₂) = κ₁ := by
    ext o₁ : 1; exact Kernel.withDensity_rnDeriv_eq (hκ o₁)
  haveI : IsSFiniteKernel (κ₂.withDensity (κ₁.rnDeriv κ₂)) := hκ_eq ▸ inferInstance
  have h_eq : μ ⊗ₘ κ₁ = (μ ⊗ₘ κ₂).withDensity (fun p => κ₁.rnDeriv κ₂ p.1 p.2) := by
    conv_lhs => rw [← hκ_eq]
    exact Measure.compProd_withDensity (Kernel.measurable_rnDeriv κ₁ κ₂)
  rw [h_eq]
  exact Measure.rnDeriv_withDensity _ (Kernel.measurable_rnDeriv κ₁ κ₂)

private lemma kernel_rnDeriv_eq_measure_rnDeriv
    [MeasurableSpace.CountableOrCountablyGenerated O₁ O₂]
    {κ₁ κ₂ : Kernel O₁ O₂} [IsFiniteKernel κ₁] [IsFiniteKernel κ₂]
    {a : O₁} (hac : κ₁ a ≪ κ₂ a) :
    Kernel.rnDeriv κ₁ κ₂ a =ᵐ[κ₂ a] (κ₁ a).rnDeriv (κ₂ a) := by
  have h_eq : (κ₂ a).withDensity (Kernel.rnDeriv κ₁ κ₂ a) = κ₁ a := by
    rw [← Kernel.withDensity_apply κ₂ (Kernel.measurable_rnDeriv κ₁ κ₂)]
    exact Kernel.withDensity_rnDeriv_eq hac
  rw [← h_eq]
  exact (Measure.rnDeriv_withDensity (κ₂ a) (Kernel.measurable_rnDeriv_right κ₁ κ₂ a)).symm

private lemma renyiMoment_seqFinite_le [Fintype O₁] [MeasurableSingletonClass O₁]
    {M₁ : Mechanism D O₁} {K : O₁ → Mechanism D O₂}
    {d₁ d₂ : D}
    (hac_μ : (M₁ d₁).toMeasure ≪ (M₁ d₂).toMeasure)
    (hac_κ : ∀ o₁, (K o₁ d₁).toMeasure ≪ (K o₁ d₂).toMeasure)
    {α : ℝ} (hα : 1 < α)
    {B : ℝ≥0∞} (hB : ∀ o₁, renyiMoment α (K o₁ d₁).toMeasure (K o₁ d₂).toMeasure ≤ B) :
    renyiMoment α (M₁.seqFinite K d₁).toMeasure (M₁.seqFinite K d₂).toMeasure ≤
      renyiMoment α (M₁ d₁).toMeasure (M₁ d₂).toMeasure * B := by
  set μ₁ := (M₁ d₁).toMeasure
  set μ₂ := (M₁ d₂).toMeasure
  set κ₁ := contKernel K d₁
  set κ₂ := contKernel K d₂
  have hα_pos : (0 : ℝ) < α := by linarith
  have hα_nn : (0 : ℝ) ≤ α := hα_pos.le
  have hac_κ' : ∀ o₁, κ₁ o₁ ≪ κ₂ o₁ := hac_κ
  have h_ac_same : μ₁ ⊗ₘ κ₁ ≪ μ₁ ⊗ₘ κ₂ :=
    Measure.AbsolutelyContinuous.compProd_right (ae_of_all _ hac_κ')
  -- Measurability
  have hm_F_rpow : Measurable (fun x : O₁ × O₂ => (μ₁.rnDeriv μ₂ x.1) ^ α) :=
    ENNReal.continuous_rpow_const.measurable.comp
      ((Measure.measurable_rnDeriv μ₁ μ₂).comp measurable_fst)
  have hm_C : Measurable ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂)) :=
    Measure.measurable_rnDeriv _ _
  have hm_C_rpow : Measurable (fun x : O₁ × O₂ =>
      ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) x) ^ α) :=
    ENNReal.continuous_rpow_const.measurable.comp hm_C
  -- Chain rule and fiber decomposition
  have h_factor := rnDeriv_compProd h_ac_same μ₂
  have h_fiber := ae_ae_of_ae_compProd (rnDeriv_compProd_same_marginal (μ := μ₁) hac_κ')
  -- Inner integral bound for μ₁-ae o₁
  have h_inner_le : ∀ᵐ o₁ ∂μ₁,
      ∫⁻ o₂, ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) (o₁, o₂)) ^ α ∂(κ₂ o₁) ≤ B := by
    filter_upwards [h_fiber] with o₁ ho₁
    calc ∫⁻ o₂, ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) (o₁, o₂)) ^ α ∂(κ₂ o₁)
        = ∫⁻ o₂, (Kernel.rnDeriv κ₁ κ₂ o₁ o₂) ^ α ∂(κ₂ o₁) :=
          lintegral_congr_ae (ho₁.mono fun o₂ ho₂ => by simp only [ho₂])
      _ = ∫⁻ o₂, ((κ₁ o₁).rnDeriv (κ₂ o₁) o₂) ^ α ∂(κ₂ o₁) :=
          lintegral_congr_ae ((kernel_rnDeriv_eq_measure_rnDeriv (hac_κ' o₁)).mono
            fun o₂ ho₂ => by simp only [ho₂])
      _ ≤ B := hB o₁
  -- Transfer from μ₁ to μ₂
  have h_transfer := ae_rnDeriv_ne_zero_imp_of_ae (ν := μ₂) h_inner_le
  -- Main bound
  have hrw₁ : (M₁.seqFinite K d₁).toMeasure = μ₁ ⊗ₘ κ₁ := seqFinite_eq_compProd M₁ K d₁
  have hrw₂ : (M₁.seqFinite K d₂).toMeasure = μ₂ ⊗ₘ κ₂ := seqFinite_eq_compProd M₁ K d₂
  simp only [renyiMoment, hrw₁, hrw₂]
  calc ∫⁻ x, ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₂ ⊗ₘ κ₂) x) ^ α ∂(μ₂ ⊗ₘ κ₂)
      = ∫⁻ x, (μ₁.rnDeriv μ₂ x.1 * (μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) x) ^ α
          ∂(μ₂ ⊗ₘ κ₂) :=
        lintegral_congr_ae (h_factor.mono fun x hx => by simp only [hx])
    _ = ∫⁻ x, (μ₁.rnDeriv μ₂ x.1) ^ α * ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) x) ^ α
          ∂(μ₂ ⊗ₘ κ₂) := by
        congr 1; ext x; exact ENNReal.mul_rpow_of_nonneg _ _ hα_nn
    _ = ∫⁻ o₁, ∫⁻ o₂, (μ₁.rnDeriv μ₂ o₁) ^ α *
          ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) (o₁, o₂)) ^ α ∂(κ₂ o₁) ∂μ₂ :=
        lintegral_compProd (hm_F_rpow.mul hm_C_rpow)
    _ = ∫⁻ o₁, (μ₁.rnDeriv μ₂ o₁) ^ α *
          ∫⁻ o₂, ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) (o₁, o₂)) ^ α ∂(κ₂ o₁) ∂μ₂ := by
        congr 1; ext o₁
        exact lintegral_const_mul _ (hm_C_rpow.comp measurable_prodMk_left)
    _ ≤ ∫⁻ o₁, (μ₁.rnDeriv μ₂ o₁) ^ α * B ∂μ₂ := by
        apply lintegral_mono_ae
        filter_upwards [h_transfer] with o₁ ho₁
        by_cases hF : μ₁.rnDeriv μ₂ o₁ = 0
        · simp [hF, ENNReal.zero_rpow_of_pos hα_pos]
        · exact mul_le_mul' le_rfl (ho₁ hF)
    _ = B * ∫⁻ o₁, (μ₁.rnDeriv μ₂ o₁) ^ α ∂μ₂ := by
        trans (∫⁻ o₁, B * (μ₁.rnDeriv μ₂ o₁) ^ α ∂μ₂)
        · exact lintegral_congr fun o₁ => mul_comm _ _
        · exact lintegral_const_mul _
            (ENNReal.continuous_rpow_const.measurable.comp (Measure.measurable_rnDeriv μ₁ μ₂))
    _ = (∫⁻ o₁, (μ₁.rnDeriv μ₂ o₁) ^ α ∂μ₂) * B := mul_comm _ _

private lemma renyiMoment_seq_le
    [MeasurableSpace.CountableOrCountablyGenerated O₁ O₂]
    {M₁ : Mechanism D O₁} {K : O₁ → Mechanism D O₂}
    {d₁ d₂ : D}
    (hac_μ : (M₁ d₁).toMeasure ≪ (M₁ d₂).toMeasure)
    (hac_κ : ∀ o₁, (K o₁ d₁).toMeasure ≪ (K o₁ d₂).toMeasure)
    {α : ℝ} (hα : 1 < α)
    {B : ℝ≥0∞} (hB : ∀ o₁, renyiMoment α (K o₁ d₁).toMeasure (K o₁ d₂).toMeasure ≤ B)
    (hK : ∀ d, AEMeasurable (fun o₁ => ((K o₁ d).toMeasure).map (Prod.mk o₁))
      (M₁ d).toMeasure)
    (hK_meas : ∀ d, Measurable (fun o₁ => (K o₁ d).toMeasure)) :
    renyiMoment α (M₁.seq K hK d₁).toMeasure (M₁.seq K hK d₂).toMeasure ≤
      renyiMoment α (M₁ d₁).toMeasure (M₁ d₂).toMeasure * B := by
  set μ₁ := (M₁ d₁).toMeasure
  set μ₂ := (M₁ d₂).toMeasure
  set κ₁ := contKernelOfMeas K d₁ (hK_meas d₁)
  set κ₂ := contKernelOfMeas K d₂ (hK_meas d₂)
  have hα_pos : (0 : ℝ) < α := by linarith
  have hα_nn : (0 : ℝ) ≤ α := hα_pos.le
  have hac_κ' : ∀ o₁, κ₁ o₁ ≪ κ₂ o₁ := hac_κ
  have h_ac_same : μ₁ ⊗ₘ κ₁ ≪ μ₁ ⊗ₘ κ₂ :=
    Measure.AbsolutelyContinuous.compProd_right (ae_of_all _ hac_κ')
  have hm_F_rpow : Measurable (fun x : O₁ × O₂ => (μ₁.rnDeriv μ₂ x.1) ^ α) :=
    ENNReal.continuous_rpow_const.measurable.comp
      ((Measure.measurable_rnDeriv μ₁ μ₂).comp measurable_fst)
  have hm_C : Measurable ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂)) :=
    Measure.measurable_rnDeriv _ _
  have hm_C_rpow : Measurable (fun x : O₁ × O₂ =>
      ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) x) ^ α) :=
    ENNReal.continuous_rpow_const.measurable.comp hm_C
  have h_factor := rnDeriv_compProd h_ac_same μ₂
  have h_fiber := ae_ae_of_ae_compProd (rnDeriv_compProd_same_marginal (μ := μ₁) hac_κ')
  have h_inner_le : ∀ᵐ o₁ ∂μ₁,
      ∫⁻ o₂, ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) (o₁, o₂)) ^ α ∂(κ₂ o₁) ≤ B := by
    filter_upwards [h_fiber] with o₁ ho₁
    calc ∫⁻ o₂, ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) (o₁, o₂)) ^ α ∂(κ₂ o₁)
        = ∫⁻ o₂, (Kernel.rnDeriv κ₁ κ₂ o₁ o₂) ^ α ∂(κ₂ o₁) :=
          lintegral_congr_ae (ho₁.mono fun o₂ ho₂ => by simp only [ho₂])
      _ = ∫⁻ o₂, ((κ₁ o₁).rnDeriv (κ₂ o₁) o₂) ^ α ∂(κ₂ o₁) :=
          lintegral_congr_ae ((kernel_rnDeriv_eq_measure_rnDeriv (hac_κ' o₁)).mono
            fun o₂ ho₂ => by simp only [ho₂])
      _ ≤ B := hB o₁
  have h_transfer := ae_rnDeriv_ne_zero_imp_of_ae (ν := μ₂) h_inner_le
  have hrw₁ : (M₁.seq K hK d₁).toMeasure = μ₁ ⊗ₘ κ₁ := seq_eq_compProd hK hK_meas d₁
  have hrw₂ : (M₁.seq K hK d₂).toMeasure = μ₂ ⊗ₘ κ₂ := seq_eq_compProd hK hK_meas d₂
  simp only [renyiMoment, hrw₁, hrw₂]
  calc ∫⁻ x, ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₂ ⊗ₘ κ₂) x) ^ α ∂(μ₂ ⊗ₘ κ₂)
      = ∫⁻ x, (μ₁.rnDeriv μ₂ x.1 * (μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) x) ^ α
          ∂(μ₂ ⊗ₘ κ₂) :=
        lintegral_congr_ae (h_factor.mono fun x hx => by simp only [hx])
    _ = ∫⁻ x, (μ₁.rnDeriv μ₂ x.1) ^ α * ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) x) ^ α
          ∂(μ₂ ⊗ₘ κ₂) := by
        congr 1; ext x; exact ENNReal.mul_rpow_of_nonneg _ _ hα_nn
    _ = ∫⁻ o₁, ∫⁻ o₂, (μ₁.rnDeriv μ₂ o₁) ^ α *
          ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) (o₁, o₂)) ^ α ∂(κ₂ o₁) ∂μ₂ :=
        lintegral_compProd (hm_F_rpow.mul hm_C_rpow)
    _ = ∫⁻ o₁, (μ₁.rnDeriv μ₂ o₁) ^ α *
          ∫⁻ o₂, ((μ₁ ⊗ₘ κ₁).rnDeriv (μ₁ ⊗ₘ κ₂) (o₁, o₂)) ^ α ∂(κ₂ o₁) ∂μ₂ := by
        congr 1; ext o₁
        exact lintegral_const_mul _ (hm_C_rpow.comp measurable_prodMk_left)
    _ ≤ ∫⁻ o₁, (μ₁.rnDeriv μ₂ o₁) ^ α * B ∂μ₂ := by
        apply lintegral_mono_ae
        filter_upwards [h_transfer] with o₁ ho₁
        by_cases hF : μ₁.rnDeriv μ₂ o₁ = 0
        · simp [hF, ENNReal.zero_rpow_of_pos hα_pos]
        · exact mul_le_mul' le_rfl (ho₁ hF)
    _ = B * ∫⁻ o₁, (μ₁.rnDeriv μ₂ o₁) ^ α ∂μ₂ := by
        trans (∫⁻ o₁, B * (μ₁.rnDeriv μ₂ o₁) ^ α ∂μ₂)
        · exact lintegral_congr fun o₁ => mul_comm _ _
        · exact lintegral_const_mul _
            (ENNReal.continuous_rpow_const.measurable.comp (Measure.measurable_rnDeriv μ₁ μ₂))
    _ = (∫⁻ o₁, (μ₁.rnDeriv μ₂ o₁) ^ α ∂μ₂) * B := mul_comm _ _

/-- **Adaptive composition for zCDP**: if M₁ is ρ₁-zCDP and for every
    first-stage output o₁, the continuation K(o₁) is ρ₂-zCDP (uniformly),
    then the sequential composition `M₁.seq K` is (ρ₁+ρ₂)-zCDP.

    This is the key theorem for algorithms like AIM where the second step
    (measurement) depends on the first step's output (selection).

    The uniform bound requirement — K(o₁) is ρ₂-zCDP for ALL o₁ —
    is exactly what holds in AIM: the Gaussian measurement has the same
    privacy cost regardless of which marginal was selected.

    The proof works with Rényi *moments* in `ℝ≥0∞`, not with an additive
    divergence chain rule. (Rényi divergence does not satisfy the additive
    conditional chain rule that KL divergence does, so no equation of the form
    `D_α(P₁ ⊗ K₁ ‖ P₂ ⊗ K₂) = D_α(P₁ ‖ P₂) + E_{P₁}[D_α(K₁ ‖ K₂)]` is used or
    valid here.) Instead `renyiMoment_seq_le` proves the multiplicative bound
        M_α(seq · d₁ ‖ seq · d₂) ≤ M_α(M₁ d₁ ‖ M₁ d₂) · B,
    where `B = exp((α−1)·ρ₂·α)` is a *uniform* bound on every continuation's
    moment `M_α(K o₁ d₁ ‖ K o₁ d₂)` (obtained from `h₂ o₁`). Taking logs turns
    this product into the sum of the ρ₁α and ρ₂α budgets:
        D_α(seq · d₁ ‖ seq · d₂) ≤ ρ₁α + ρ₂α = (ρ₁+ρ₂)α.

    The `hK_meas` hypothesis provides kernel-level measurability of the
    continuation, enabling `compProd` decomposition. For finite first-stage
    output types, use `isZCDP_seqFinite` which discharges this automatically. -/
theorem isZCDP_seq
    [MeasurableSpace.CountableOrCountablyGenerated O₁ O₂]
    {adj : D → D → Prop}
    {M₁ : Mechanism D O₁} {K : O₁ → Mechanism D O₂} {ρ₁ ρ₂ : NNReal}
    (h₁ : IsZCDP adj M₁ ρ₁)
    (h₂ : ∀ o₁, IsZCDP adj (K o₁) ρ₂)
    (hK : ∀ d, AEMeasurable (fun o₁ => ((K o₁ d).toMeasure).map (Prod.mk o₁))
      (M₁ d).toMeasure)
    (hK_meas : ∀ d, Measurable (fun o₁ => (K o₁ d).toMeasure)) :
    IsZCDP adj (M₁.seq K hK) (ρ₁ + ρ₂) where
  ac d₁ d₂ hadj := by
    set f : D → O₁ → Measure (O₁ × O₂) :=
      fun d o₁ => ((K o₁ d).toMeasure).map (Prod.mk o₁)
    change (M₁ d₁).toMeasure.bind (f d₁) ≪ (M₁ d₂).toMeasure.bind (f d₂)
    apply Measure.AbsolutelyContinuous.mk
    intro S hS_meas hS_zero
    rw [Measure.bind_apply hS_meas (hK d₂)] at hS_zero
    have hmeas₂ : AEMeasurable (fun o₁ => f d₂ o₁ S) (M₁ d₂).toMeasure :=
      (Measure.measurable_coe hS_meas).comp_aemeasurable (hK d₂)
    have h_ae : ∀ᵐ o₁ ∂(M₁ d₂).toMeasure, f d₂ o₁ S = 0 :=
      (lintegral_eq_zero_iff' hmeas₂).mp hS_zero
    have h_ae₁ : ∀ᵐ o₁ ∂(M₁ d₂).toMeasure, f d₁ o₁ S = 0 := by
      filter_upwards [h_ae] with o₁ ho₁
      exact (((h₂ o₁).ac d₁ d₂ hadj).map measurable_prodMk_left) ho₁
    have h_ae₂ : ∀ᵐ o₁ ∂(M₁ d₁).toMeasure, f d₁ o₁ S = 0 :=
      (h₁.ac d₁ d₂ hadj).ae_le h_ae₁
    rw [Measure.bind_apply hS_meas (hK d₁)]
    have hmeas₁ : AEMeasurable (fun o₁ => f d₁ o₁ S) (M₁ d₁).toMeasure :=
      (Measure.measurable_coe hS_meas).comp_aemeasurable (hK d₁)
    exact (lintegral_eq_zero_iff' hmeas₁).mpr h_ae₂
  fin d₁ d₂ hadj α hα := by
    have h_κ_bound : ∀ o₁,
        renyiMoment α (K o₁ d₁).toMeasure (K o₁ d₂).toMeasure ≤
          ENNReal.ofReal (Real.exp ((α - 1) * (↑ρ₂ * α))) :=
      fun o₁ => (renyiDivergence_le_iff hα (by positivity)
        ((h₂ o₁).fin d₁ d₂ hadj α hα)).mp ((h₂ o₁).bound d₁ d₂ hadj α hα)
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (h₁.fin d₁ d₂ hadj α hα) ENNReal.ofReal_ne_top)
      (renyiMoment_seq_le (h₁.ac d₁ d₂ hadj)
        (fun o₁ => (h₂ o₁).ac d₁ d₂ hadj) hα h_κ_bound hK hK_meas)
  bound d₁ d₂ hadj α hα := by
    have h_κ_bound : ∀ o₁,
        renyiMoment α (K o₁ d₁).toMeasure (K o₁ d₂).toMeasure ≤
          ENNReal.ofReal (Real.exp ((α - 1) * (↑ρ₂ * α))) :=
      fun o₁ => (renyiDivergence_le_iff hα (by positivity)
        ((h₂ o₁).fin d₁ d₂ hadj α hα)).mp ((h₂ o₁).bound d₁ d₂ hadj α hα)
    have h_moment := renyiMoment_seq_le (h₁.ac d₁ d₂ hadj)
      (fun o₁ => (h₂ o₁).ac d₁ d₂ hadj) hα h_κ_bound hK hK_meas
    have hfin : renyiMoment α (M₁.seq K hK d₁).toMeasure
        (M₁.seq K hK d₂).toMeasure ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (h₁.fin d₁ d₂ hadj α hα) ENNReal.ofReal_ne_top) h_moment
    have h₁_moment := (renyiDivergence_le_iff hα (by positivity : (0 : ℝ) ≤ ↑ρ₁ * α)
      (h₁.fin d₁ d₂ hadj α hα)).mp (h₁.bound d₁ d₂ hadj α hα)
    simp only [NNReal.coe_add]
    rw [renyiDivergence_le_iff hα (by positivity) hfin]
    calc renyiMoment α (M₁.seq K hK d₁).toMeasure (M₁.seq K hK d₂).toMeasure
        ≤ renyiMoment α (M₁ d₁).toMeasure (M₁ d₂).toMeasure *
            ENNReal.ofReal (Real.exp ((α - 1) * (↑ρ₂ * α))) := h_moment
      _ ≤ ENNReal.ofReal (Real.exp ((α - 1) * (↑ρ₁ * α))) *
            ENNReal.ofReal (Real.exp ((α - 1) * (↑ρ₂ * α))) :=
          mul_le_mul_left h₁_moment _
      _ = ENNReal.ofReal (Real.exp ((α - 1) * ((↑ρ₁ + ↑ρ₂) * α))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 1; congr 1; ring

/-- Convenient version of `isZCDP_seq` for finite first-stage output types.
    Discharges the `Measurable` and `CountableOrCountablyGenerated` requirements
    automatically via `measurable_of_finite` and `Countable`. -/
theorem isZCDP_seqFinite [Fintype O₁] [MeasurableSingletonClass O₁]
    {adj : D → D → Prop}
    {M₁ : Mechanism D O₁} {K : O₁ → Mechanism D O₂} {ρ₁ ρ₂ : NNReal}
    (h₁ : IsZCDP adj M₁ ρ₁)
    (h₂ : ∀ o₁, IsZCDP adj (K o₁) ρ₂) :
    IsZCDP adj (M₁.seqFinite K) (ρ₁ + ρ₂) :=
  isZCDP_seq h₁ h₂ _ (fun _ => measurable_of_finite _)

end AdaptiveComposition

end DPlean4
