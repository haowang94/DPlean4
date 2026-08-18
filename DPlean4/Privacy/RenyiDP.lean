/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.ZCDP
import DPlean4.Privacy.Pure
import DPlean4.Probability.Mechanism

/-!
# Rényi Differential Privacy (RDP)

This file defines (α, ε)-Rényi Differential Privacy (Mironov, 2017) and proves
its key properties, including the relationship with zCDP and approximate DP.

## Main Definitions

* `IsRenyiDP adj M α ε_α`: Mechanism M satisfies (α, ε_α)-RDP

## Main Results

* `isRenyiDP_composition`: RDP composes linearly: (α, ε₁) + (α, ε₂) = (α, ε₁+ε₂)
* `isRenyiDP_postprocess`: RDP is preserved under postprocessing
* `isZCDP_of_isRenyiDP`: (α, ρα)-RDP for all α > 1 implies ρ-zCDP (with ρ = sup ε_α/α)
* `isRenyiDP_of_isZCDP`: ρ-zCDP implies (α, ρα)-RDP for all α > 1
* `isApproxDP_of_isRenyiDP`: (α, ε_α)-RDP implies (ε_α + log(1/δ)/(α-1), δ)-DP

## Design Notes

RDP is a more fine-grained privacy notion than zCDP. While zCDP bounds the
Rényi divergence at ALL orders α > 1 simultaneously (with a specific linear
relationship ρ·α), RDP bounds it at a SINGLE order α with an arbitrary bound ε_α.

RDP is the standard accounting framework in modern DP-SGD implementations
(TensorFlow Privacy, Opacus, etc.) because:
1. It allows order-specific bounds that may be tighter than zCDP
2. The conversion to (ε,δ)-DP can be optimized over α
3. Subsampling amplification has clean RDP characterizations

## References

* Mironov (2017), "Rényi Differential Privacy"
* Mironov et al. (2019), "Rényi Differential Privacy of the Sampled Gaussian Mechanism"
* Balle et al. (2020), "Hypothesis Testing Interpretations and Renyi Differential Privacy"
-/

noncomputable section

namespace DPlean4

open MeasureTheory ENNReal Real

variable {D O O₁ O₂ : Type*} [MeasurableSpace O]

-- ============================================================================
-- Definition
-- ============================================================================

/-- A mechanism satisfies (α, ε_α)-Rényi Differential Privacy if for all
    adjacent databases d₁, d₂:
    D_α(M(d₁)‖M(d₂)) ≤ ε_α

    This is a single-order version of zCDP: it bounds the Rényi divergence
    at a specific order α, rather than requiring a bound at all orders.

    The structure also records the valid order, absolute continuity, and
    finiteness needed for the real-valued divergence formula.

    Reference: Mironov (2017), Definition 4. -/
structure IsRenyiDP (adj : D → D → Prop) (M : Mechanism D O) (α : ℝ) (ε_α : ℝ) : Prop where
  order : 1 < α
  ac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure
  fin : ∀ d₁ d₂, adj d₁ d₂ →
    renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤
  bound : ∀ d₁ d₂, adj d₁ d₂ →
    renyiDivergence α (M d₁).toMeasure (M d₂).toMeasure ≤ ε_α

-- ============================================================================
-- Basic Properties
-- ============================================================================

/-- RDP is monotone in ε: if M is (α, ε₁)-RDP and ε₁ ≤ ε₂, then M is (α, ε₂)-RDP. -/
theorem isRenyiDP_mono {adj : D → D → Prop} {M : Mechanism D O} {α ε₁ ε₂ : ℝ}
    (h : IsRenyiDP adj M α ε₁) (hle : ε₁ ≤ ε₂) :
    IsRenyiDP adj M α ε₂ where
  order := h.order
  ac := h.ac
  fin := h.fin
  bound d₁ d₂ hadj := le_trans (h.bound d₁ d₂ hadj) hle

-- ============================================================================
-- Relationship with zCDP
-- ============================================================================

/-- **zCDP implies RDP**: ρ-zCDP implies (α, ρα)-RDP for every α > 1.

    This is the "pointwise" direction: zCDP gives a uniform bound at all orders,
    so it certainly gives a bound at any specific order. -/
theorem isRenyiDP_of_isZCDP {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (h : IsZCDP adj M ρ) {α : ℝ} (hα : 1 < α) :
    IsRenyiDP adj M α (ρ * α) where
  order := hα
  ac := h.ac
  fin d₁ d₂ hadj := h.fin d₁ d₂ hadj α hα
  bound d₁ d₂ hadj := h.bound d₁ d₂ hadj α hα

/-- **RDP at all orders implies zCDP**: if M is (α, ρα)-RDP for all α > 1
    (with the specific linear form), then M is ρ-zCDP.

    This is the converse: zCDP is equivalent to RDP at all orders with
    a linear dependence on α. -/
theorem isZCDP_of_forall_isRenyiDP {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (h : ∀ α : ℝ, 1 < α → IsRenyiDP adj M α (ρ * α))
    (hac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure)
    (hfin : ∀ d₁ d₂, adj d₁ d₂ → ∀ α : ℝ, 1 < α →
      renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤) :
    IsZCDP adj M ρ where
  ac := hac
  fin := hfin
  bound d₁ d₂ hadj α hα := (h α hα).bound d₁ d₂ hadj

-- ============================================================================
-- Relationship with pure DP
-- ============================================================================

/-- **Pure DP implies Rényi moment bound**: if μ ≤[ε] ν (pure DP closeness),
    then the Rényi moment is bounded by exp(αε).

    The proof uses: PureMeasureClose gives rnDeriv μ ν ≤ exp(ε) a.e.,
    so (rnDeriv)^α ≤ exp(αε) a.e., and the integral is at most exp(αε).

    A tighter bound exp((α-1)ε) exists via change of measure but requires
    more sophisticated machinery. -/
theorem renyiMoment_le_of_pureMeasureClose {ε : NNReal}
    {μ ν : ProbabilityMeasure O}
    (h : PureMeasureClose ε μ ν) {α : ℝ} (hα : 1 < α) :
    renyiMoment α μ.toMeasure ν.toMeasure ≤
      ENNReal.ofReal (Real.exp (α * ε)) := by
  set c := ENNReal.ofReal (Real.exp ε)
  have hc_ne : c ≠ 0 := ENNReal.ofReal_pos.mpr (Real.exp_pos _) |>.ne'
  have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_le : μ.toMeasure ≤ c • ν.toMeasure := by
    rw [Measure.le_iff]
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    have := h s hs
    simp only [ENNReal.coe_zero, add_zero] at this
    exact this
  have : SigmaFinite (c • ν.toMeasure) :=
    haveI := ν.toMeasure.smul_finite hc_ne_top (c := c)
    IsFiniteMeasure.toSigmaFinite _
  have h_rnDeriv_le : μ.toMeasure.rnDeriv ν.toMeasure ≤ᵐ[ν.toMeasure] fun _ => c := by
    have h_scaled := Measure.rnDeriv_le_one_of_le h_le
    have h_smul := Measure.rnDeriv_smul_right_of_ne_top μ.toMeasure ν.toMeasure hc_ne hc_ne_top
    filter_upwards [h_scaled.filter_mono (Measure.absolutelyContinuous_smul hc_ne).ae_le,
                    h_smul] with x h1 h2
    simp only [Pi.one_apply] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    rw [h2] at h1
    rw [ENNReal.inv_mul_le_iff hc_ne hc_ne_top] at h1
    simpa [mul_one] using h1
  simp only [renyiMoment]
  calc ∫⁻ x, (μ.toMeasure.rnDeriv ν.toMeasure x) ^ α ∂ν.toMeasure
      ≤ ∫⁻ _, c ^ α ∂ν.toMeasure := by
        apply lintegral_mono_ae
        filter_upwards [h_rnDeriv_le] with x hx
        exact ENNReal.rpow_le_rpow hx (by linarith)
    _ = c ^ α * ν.toMeasure Set.univ := by rw [lintegral_const]
    _ = c ^ α := by rw [measure_univ, mul_one]
    _ = ENNReal.ofReal (Real.exp (α * ε)) := by
        rw [show c = ENNReal.ofReal (Real.exp ε) from rfl,
            ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
            ← Real.exp_mul, mul_comm]

/-- **Tighter Rényi moment bound via change of measure**:
    if μ ≤[ε] ν (pure DP closeness), then the Rényi moment is bounded
    by exp((α-1)ε), which is tighter than exp(αε).

    Proof: ∫ (dμ/dν)^α dν = ∫ (dμ/dν)^(α-1) · (dμ/dν) dν
                            = ∫ (dμ/dν)^(α-1) dμ     [change of measure]
                            ≤ exp(ε)^(α-1) · μ(Ω)   [since dμ/dν ≤ exp(ε) a.e.]
                            = exp((α-1)ε)            [μ is a probability measure] -/
theorem renyiMoment_le_of_pureMeasureClose' {ε : NNReal}
    {μ ν : ProbabilityMeasure O}
    (h : PureMeasureClose ε μ ν) {α : ℝ} (hα : 1 < α)
    (hac : μ.toMeasure ≪ ν.toMeasure) :
    renyiMoment α μ.toMeasure ν.toMeasure ≤
      ENNReal.ofReal (Real.exp ((α - 1) * ε)) := by
  set c := ENNReal.ofReal (Real.exp ε)
  have hc_ne : c ≠ 0 := ENNReal.ofReal_pos.mpr (Real.exp_pos _) |>.ne'
  have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_le : μ.toMeasure ≤ c • ν.toMeasure := by
    rw [Measure.le_iff]
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    have := h s hs
    simp only [ENNReal.coe_zero, add_zero] at this
    exact this
  have : SigmaFinite (c • ν.toMeasure) :=
    haveI := ν.toMeasure.smul_finite hc_ne_top (c := c)
    IsFiniteMeasure.toSigmaFinite _
  have h_rnDeriv_le : μ.toMeasure.rnDeriv ν.toMeasure ≤ᵐ[ν.toMeasure] fun _ => c := by
    have h_scaled := Measure.rnDeriv_le_one_of_le h_le
    have h_smul := Measure.rnDeriv_smul_right_of_ne_top μ.toMeasure ν.toMeasure hc_ne hc_ne_top
    filter_upwards [h_scaled.filter_mono (Measure.absolutelyContinuous_smul hc_ne).ae_le,
                    h_smul] with x h1 h2
    simp only [Pi.one_apply] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    rw [h2] at h1
    rw [ENNReal.inv_mul_le_iff hc_ne hc_ne_top] at h1
    simpa [mul_one] using h1
  have hα_sub : (0 : ℝ) < α - 1 := by linarith
  have h_ptwise : ∀ (a : ℝ≥0∞), a ≤ c → a ^ α ≤ c ^ (α - 1) * a := by
    intro a ha
    rcases eq_or_ne a 0 with rfl | ha0
    · simp [ENNReal.zero_rpow_of_pos (by linarith : 0 < α)]
    · have ha_ne_top : a ≠ ⊤ := ne_top_of_le_ne_top hc_ne_top ha
      have h_split : a ^ α = a ^ (α - 1) * a := by
        conv_lhs => rw [show α = (α - 1) + 1 from by ring]
        rw [ENNReal.rpow_add _ _ ha0 ha_ne_top, ENNReal.rpow_one]
      rw [h_split]; gcongr
  simp only [renyiMoment]
  calc ∫⁻ x, (μ.toMeasure.rnDeriv ν.toMeasure x) ^ α ∂ν.toMeasure
      ≤ ∫⁻ x, c ^ (α - 1) * (μ.toMeasure.rnDeriv ν.toMeasure x) ∂ν.toMeasure := by
        apply lintegral_mono_ae
        filter_upwards [h_rnDeriv_le] with x hx
        exact h_ptwise _ hx
    _ = c ^ (α - 1) * ∫⁻ x, μ.toMeasure.rnDeriv ν.toMeasure x ∂ν.toMeasure :=
        lintegral_const_mul _ (Measure.measurable_rnDeriv _ _)
    _ = c ^ (α - 1) * μ.toMeasure Set.univ := by
        rw [Measure.lintegral_rnDeriv hac]
    _ = c ^ (α - 1) := by rw [measure_univ, mul_one]
    _ = ENNReal.ofReal (Real.exp ((α - 1) * ε)) := by
        rw [show c = ENNReal.ofReal (Real.exp ε) from rfl,
            ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
            ← Real.exp_mul, mul_comm]

/-- **Pure ε-DP implies ε-zCDP.**

    A pure ε-DP mechanism satisfies ε-zCDP: for all α > 1,
    D_α(M(d₁)‖M(d₂)) ≤ ε ≤ ε·α.

    The tighter change-of-measure bound gives D_α ≤ ε directly (constant
    in α, not αε/(α-1)). Since ε ≤ ε·α for α > 1, this implies ε-zCDP.

    Note: the optimal bound is (ε²/2)-zCDP via Hoeffding's lemma, but
    ε-zCDP is the simplest provable conversion and already useful. -/
theorem isZCDP_of_isPureDP {adj : D → D → Prop} {M : Mechanism D O} {ε : NNReal}
    (h : IsPureDP adj M ε)
    (hac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure)
    (hfin : ∀ d₁ d₂, adj d₁ d₂ → ∀ α : ℝ, 1 < α →
      renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤) :
    IsZCDP adj M ε where
  ac := hac
  fin := hfin
  bound d₁ d₂ hadj α hα := by
    have hα_pos : (0 : ℝ) < α - 1 := by linarith
    have hac' := hac d₁ d₂ hadj
    have hfin' := hfin d₁ d₂ hadj α hα
    have h_moment := renyiMoment_le_of_pureMeasureClose' (h d₁ d₂ hadj) hα hac'
    have hε_nn : (0 : ℝ) ≤ (ε : ℝ) := NNReal.coe_nonneg _
    rw [renyiDivergence_le_iff hα (by positivity : (0 : ℝ) ≤ ↑ε * α) hfin']
    calc renyiMoment α (M d₁).toMeasure (M d₂).toMeasure
        ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε)) := h_moment
      _ ≤ ENNReal.ofReal (Real.exp ((α - 1) * (↑ε * α))) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp_of_le
          apply mul_le_mul_of_nonneg_left _ hα_pos.le
          linarith [mul_le_mul_of_nonneg_left (le_of_lt hα) hε_nn]

/-- **Pure ε-DP implies (α, αε/(α-1))-RDP.**

    For pure ε-DP mechanisms, the Rényi divergence at order α is bounded by
    αε/(α-1), which approaches ε as α → ∞. This connects pure DP to the
    RDP framework.

    Note: a tighter bound of ε (flat, independent of α) exists but requires
    change-of-measure arguments. The bound αε/(α-1) is sufficient for
    practical RDP accounting. -/
theorem isRenyiDP_of_isPureDP {adj : D → D → Prop} {M : Mechanism D O} {ε : NNReal}
    (h : IsPureDP adj M ε) {α : ℝ} (hα : 1 < α)
    (hac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure) :
    IsRenyiDP adj M α (α * ε / (α - 1)) where
  order := hα
  ac := hac
  fin d₁ d₂ hadj := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (renyiMoment_le_of_pureMeasureClose (h d₁ d₂ hadj) hα)
  bound d₁ d₂ hadj := by
    have hα_pos : (0 : ℝ) < α - 1 := by linarith
    have h_moment := renyiMoment_le_of_pureMeasureClose (h d₁ d₂ hadj) hα
    by_cases hfin : renyiMoment α (M d₁).toMeasure (M d₂).toMeasure = ⊤
    · exfalso
      have : renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≤
          ENNReal.ofReal (Real.exp (α * ε)) := h_moment
      rw [hfin] at this
      exact (not_le.mpr (ENNReal.ofReal_lt_top)) this
    rw [renyiDivergence_le_iff hα (by positivity) hfin]
    calc renyiMoment α (M d₁).toMeasure (M d₂).toMeasure
        ≤ ENNReal.ofReal (Real.exp (α * ε)) := h_moment
      _ = ENNReal.ofReal (Real.exp ((α - 1) * (α * ↑ε / (α - 1)))) := by
          congr 1; field_simp

-- ============================================================================
-- Composition
-- ============================================================================

section Composition

variable [MeasurableSpace O₁] [MeasurableSpace O₂]

/-- **RDP composition**: the product of an (α, ε₁)-RDP mechanism and an
    (α, ε₂)-RDP mechanism is (α, ε₁+ε₂)-RDP.

    This is analogous to zCDP composition but at a single Rényi order.
    The proof uses multiplicativity of Rényi moments for product measures. -/
theorem isRenyiDP_prod {adj : D → D → Prop}
    {M₁ : Mechanism D O₁} {M₂ : Mechanism D O₂}
    {α ε₁ ε₂ : ℝ} (hα : 1 < α)
    (h₁ : IsRenyiDP adj M₁ α ε₁) (h₂ : IsRenyiDP adj M₂ α ε₂)
    (hac₁ : ∀ d₁ d₂, adj d₁ d₂ → (M₁ d₁).toMeasure ≪ (M₁ d₂).toMeasure)
    (hac₂ : ∀ d₁ d₂, adj d₁ d₂ → (M₂ d₁).toMeasure ≪ (M₂ d₂).toMeasure) :
    IsRenyiDP adj (M₁.prod M₂) α (ε₁ + ε₂) where
  order := hα
  ac d₁ d₂ hadj := by
    simp only [Mechanism.prod_toMeasure]
    exact (hac₁ d₁ d₂ hadj).prod (hac₂ d₁ d₂ hadj)
  fin d₁ d₂ hadj := by
    simp only [Mechanism.prod_toMeasure]
    rw [renyiMoment_prod (hac₁ d₁ d₂ hadj) (hac₂ d₁ d₂ hadj)
      (by linarith : (0 : ℝ) ≤ α)]
    exact ENNReal.mul_ne_top (h₁.fin d₁ d₂ hadj) (h₂.fin d₁ d₂ hadj)
  bound d₁ d₂ hadj := by
    simp only [Mechanism.prod_toMeasure]
    have hd₁ := h₁.bound d₁ d₂ hadj
    have hd₂ := h₂.bound d₁ d₂ hadj
    have hε₁ : 0 ≤ ε₁ := le_trans (renyiDivergence_nonneg hα (hac₁ d₁ d₂ hadj)) hd₁
    have hε₂ : 0 ≤ ε₂ := le_trans (renyiDivergence_nonneg hα (hac₂ d₁ d₂ hadj)) hd₂
    simp only [renyiDivergence] at hd₁ hd₂ ⊢
    rw [renyiMoment_prod (hac₁ d₁ d₂ hadj) (hac₂ d₁ d₂ hadj) (by linarith : (0 : ℝ) ≤ α),
        ENNReal.toReal_mul]
    set m₁ := (renyiMoment α (M₁ d₁).toMeasure (M₁ d₂).toMeasure).toReal
    set m₂ := (renyiMoment α (M₂ d₁).toMeasure (M₂ d₂).toMeasure).toReal
    by_cases hm₁ : m₁ = 0
    · simp only [hm₁, zero_mul, Real.log_zero, mul_zero]; linarith
    · by_cases hm₂ : m₂ = 0
      · simp only [hm₂, mul_zero, Real.log_zero, mul_zero]; linarith
      · rw [Real.log_mul hm₁ hm₂, mul_add]
        linarith

end Composition

-- ============================================================================
-- Postprocessing
-- ============================================================================

/-- **RDP postprocessing**: if M is (α, ε_α)-RDP and f is measurable,
    then f ∘ M is also (α, ε_α)-RDP.

    The proof follows from the Data Processing Inequality for Rényi divergence. -/
theorem isRenyiDP_postprocess {adj : D → D → Prop} {M : Mechanism D O} {α ε_α : ℝ}
    (hα : 1 < α) (hM : IsRenyiDP adj M α ε_α) [MeasurableSpace O₂]
    {f : O → O₂} (hf : Measurable f)
    (hac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure)
    (hfin : ∀ d₁ d₂, adj d₁ d₂ →
      renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤) :
    IsRenyiDP adj (fun d => (M d).map hf.aemeasurable) α ε_α where
  order := hα
  ac d₁ d₂ hadj := by
    simp only [ProbabilityMeasure.toMeasure_map]
    exact (hac d₁ d₂ hadj).map hf
  fin d₁ d₂ hadj := by
    simp only [ProbabilityMeasure.toMeasure_map]
    exact ne_top_of_le_ne_top (hfin d₁ d₂ hadj)
      (renyiMoment_map_le (hac d₁ d₂ hadj) hf (le_of_lt hα) (hfin d₁ d₂ hadj))
  bound d₁ d₂ hadj := by
    simp only [ProbabilityMeasure.toMeasure_map]
    have hac' := hac d₁ d₂ hadj
    have hfin' := hfin d₁ d₂ hadj
    have h_moment := renyiMoment_map_le hac' hf (le_of_lt hα) hfin'
    have h_mapped_fin : renyiMoment α ((M d₁).toMeasure.map f)
        ((M d₂).toMeasure.map f) ≠ ⊤ := ne_top_of_le_ne_top hfin' h_moment
    have : IsProbabilityMeasure ((M d₁).toMeasure.map f) :=
      (M d₁).toMeasure.isProbabilityMeasure_map hf.aemeasurable
    have : IsProbabilityMeasure ((M d₂).toMeasure.map f) :=
      (M d₂).toMeasure.isProbabilityMeasure_map hf.aemeasurable
    have h_mapped_ge : 1 ≤ renyiMoment α ((M d₁).toMeasure.map f)
        ((M d₂).toMeasure.map f) := renyiMoment_ge_one hα (hac'.map hf)
    have h_mapped_pos : 0 < (renyiMoment α ((M d₁).toMeasure.map f)
        ((M d₂).toMeasure.map f)).toReal :=
      ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one h_mapped_ge).ne' h_mapped_fin
    rw [renyiDivergence]
    calc (α - 1)⁻¹ * log (renyiMoment α ((M d₁).toMeasure.map f)
            ((M d₂).toMeasure.map f)).toReal
        ≤ (α - 1)⁻¹ * log (renyiMoment α (M d₁).toMeasure (M d₂).toMeasure).toReal := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by linarith))
          exact Real.log_le_log h_mapped_pos
            (ENNReal.toReal_le_toReal h_mapped_fin hfin' |>.mpr h_moment)
      _ ≤ ε_α := hM.bound d₁ d₂ hadj

-- ============================================================================
-- Conversion to Approximate DP (via zCDP)
-- ============================================================================

/-- **Direct RDP → (ε,δ)-DP conversion** (Mironov 2017, Proposition 3):
    if M is (α, ε_α)-RDP, then M is (ε_α + log(1/δ)/(α-1), δ)-DP.

    This is the standard conversion used in RDP accounting (TensorFlow Privacy,
    Opacus). In practice, one computes the RDP bound ε_α at multiple orders α
    and picks the α that minimizes ε_α + log(1/δ)/(α-1).

    The proof uses the privacy loss decomposition and Markov-type tail bound:
    μ(S) ≤ exp(ε)·ν(S) + μ({rnDeriv > exp(ε)})
    where the tail μ({rnDeriv > exp(ε)}) ≤ renyiMoment / exp(ε)^(α-1) ≤ δ. -/
theorem isApproxDP_of_isRenyiDP {adj : D → D → Prop} {M : Mechanism D O}
    {α ε_α : ℝ} (hα : 1 < α) (hM : IsRenyiDP adj M α ε_α)
    (hac : ∀ d₁ d₂, adj d₁ d₂ → (M d₁).toMeasure ≪ (M d₂).toMeasure)
    (hfin : ∀ d₁ d₂, adj d₁ d₂ →
      renyiMoment α (M d₁).toMeasure (M d₂).toMeasure ≠ ⊤)
    {ε : NNReal} {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hε : (ε : ℝ) ≥ ε_α + Real.log (1 / ↑δ) / (α - 1)) :
    IsApproxDP adj M ε δ := by
  have hα_pos : (0 : ℝ) < α - 1 := by linarith
  have hδ' : (0 : ℝ) < ↑δ := by exact_mod_cast hδ
  have hL : 0 < Real.log (1 / (δ : ℝ)) :=
    Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hδ').mpr (by linarith))
  intro d₁ d₂ hadj S hS
  set μ := (M d₁).toMeasure
  set ν := (M d₂).toMeasure
  have hac' := hac d₁ d₂ hadj
  have hfin' := hfin d₁ d₂ hadj
  have h_rdp := hM.bound d₁ d₂ hadj
  set t := ENNReal.ofReal (Real.exp ↑ε) with ht_def
  have ht_ne : t ≠ 0 := by
    simp only [t, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  have ht_top : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_decomp := measure_le_mul_add_rnDeriv_tail hac' S t
  have h_tail := rnDeriv_tail_le_renyiMoment_div hac' (le_of_lt hα) ht_ne ht_top
  have h_moment := (renyiDivergence_le_iff hα (by
    exact le_trans (renyiDivergence_nonneg hα hac') h_rdp) hfin').mp h_rdp
  suffices h_tail_le : renyiMoment α μ ν / t ^ (α - 1) ≤ (δ : ENNReal) by
    calc μ S ≤ t * ν S + μ {x | t < μ.rnDeriv ν x} := h_decomp
      _ ≤ t * ν S + renyiMoment α μ ν / t ^ (α - 1) := by gcongr
      _ ≤ t * ν S + (δ : ENNReal) := by gcongr
      _ = ENNReal.ofReal (Real.exp ↑ε) * ν S + (δ : ENNReal) := rfl
  have hα_sub : (0 : ℝ) ≤ α - 1 := by linarith
  have ht_rpow_ne : t ^ (α - 1) ≠ 0 :=
    (rpow_pos_of_nonneg (by rwa [pos_iff_ne_zero]) hα_sub).ne'
  have ht_rpow_ne_top : t ^ (α - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hα_sub ht_top
  rw [ENNReal.div_le_iff ht_rpow_ne ht_rpow_ne_top]
  calc renyiMoment α μ ν
      ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε_α)) := h_moment
    _ ≤ (δ : ENNReal) * t ^ (α - 1) := by
        have h_t_rpow : t ^ (α - 1) = ENNReal.ofReal (Real.exp (↑ε * (α - 1))) := by
          rw [ht_def, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]
          congr 1
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
        rw [h_t_rpow,
            show (δ : ENNReal) = ENNReal.ofReal (↑δ) from (ENNReal.ofReal_coe_nnreal).symm,
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ↑δ)]
        apply ENNReal.ofReal_le_ofReal
        have h_ε_bound : ε_α ≤ ↑ε - Real.log (1 / ↑δ) / (α - 1) := by linarith
        calc Real.exp ((α - 1) * ε_α)
            ≤ Real.exp ((α - 1) * (↑ε - Real.log (1 / ↑δ) / (α - 1))) :=
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h_ε_bound (le_of_lt hα_pos))
          _ = Real.exp (↑ε * (α - 1) - Real.log (1 / ↑δ)) := by
              congr 1; field_simp
          _ = Real.exp (↑ε * (α - 1)) * Real.exp (-Real.log (1 / ↑δ)) := Real.exp_add _ _
          _ = Real.exp (↑ε * (α - 1)) * ↑δ := by
              congr 1; rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < 1/↑δ)]
              field_simp
          _ = ↑δ * Real.exp (↑ε * (α - 1)) := mul_comm _ _

/-- **RDP → (ε,δ)-DP via zCDP**: If M is ρ-zCDP (hence (α, ρα)-RDP at every
    order), the conversion to (ε,δ)-DP can be optimized by choosing α to
    minimize ε = ρα + log(1/δ)/(α-1).

    This demonstrates the RDP workflow: prove RDP at all orders (= zCDP),
    then convert to (ε,δ)-DP with the tightest bound.

    In practice, when RDP bounds are known only at specific orders (not all),
    one picks the α that gives the tightest conversion. Our framework supports
    this by providing `isRenyiDP_of_isZCDP` at any specific α. -/
theorem isRenyiDP_approxDP_via_zCDP {adj : D → D → Prop} {M : Mechanism D O} {ρ : NNReal}
    (hM : IsZCDP adj M ρ) (hρ : 0 < ρ)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) :
    ∃ ε : NNReal, IsApproxDP adj M ε δ :=
  isApproxDP_of_isZCDP' hM hρ hδ hδ1

end DPlean4

end -- noncomputable section
