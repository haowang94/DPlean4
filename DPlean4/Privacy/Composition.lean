/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.Approximate
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Composition Theorems for Differential Privacy

This file proves basic composition theorems for differential privacy.

## Main Results

* `measureClose_trans`: Transitivity with tight δ bound (exp(ε₁)·δ₂+δ₁)
* `pureMeasureClose_prod`: Product composition for pure DP measures
* `isPureDP_prod`: Independent composition: ε₁-DP ⊗ ε₂-DP → (ε₁+ε₂)-DP
* `isPureDP_parallel`: Parallel composition: disjoint data → max(ε₁,ε₂)-DP
* `isApproxDP_parallel`: Approximate DP parallel composition
* `isPureDP_group`: Group privacy for k-hop adjacency chains

## Design Notes

We prove **independent** (non-adaptive) composition first. The two mechanisms
operate on the same input database but produce independent outputs.

Adaptive composition (where the second mechanism depends on the first's output)
requires a separate Markov-kernel interface and is not provided here.

### Proof Strategy for Product Composition

For independent mechanisms M₁, M₂, the joint output is the product measure
M₁(d) ⊗ M₂(d). For any measurable rectangle A × B:

  (M₁(d₁) ⊗ M₂(d₁))(A × B) = M₁(d₁)(A) · M₂(d₁)(B)
    ≤ (exp(ε₁) · M₁(d₂)(A) + δ₁) · M₂(d₁)(B)

This doesn't directly give a product bound on general measurable sets.
Instead, we use the stronger "sequential" composition argument:
the privacy loss of the joint mechanism is at most the sum of individual losses.

For the basic theorem, we compose on the *same output space* using a
generic combiner function, which subsumes both product and sequential patterns.
-/

namespace DPlean4

open MeasureTheory

variable {D O₁ O₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]

section MeasureLevel

variable {O : Type*} [MeasurableSpace O]

/-- Transitivity / chaining of MeasureClose: if μ ≤[ε₁,δ₁] ν and ν ≤[ε₂,δ₂] ρ,
    then μ ≤[ε₁+ε₂, exp(ε₁)·δ₂+δ₁] ρ.

    This is the measure-level fact underlying sequential composition.
    Note: the δ bound is exp(ε₁)·δ₂ + δ₁, which for pure DP (δ₁=δ₂=0) gives 0. -/
theorem measureClose_trans {ε₁ ε₂ : NNReal} {δ₁ δ₂ : NNReal}
    {μ ν ρ : ProbabilityMeasure O}
    (h₁ : MeasureClose ε₁ δ₁ μ ν) (h₂ : MeasureClose ε₂ δ₂ ν ρ) :
    MeasureClose (ε₁ + ε₂) (⟨Real.exp ε₁ * δ₂ + δ₁, by positivity⟩) μ ρ := by
  intro s hs
  have key : μ.toMeasure s ≤ ENNReal.ofReal (Real.exp ↑(ε₁ + ε₂)) * ρ.toMeasure s +
      (ENNReal.ofReal (Real.exp ε₁) * ↑δ₂ + ↑δ₁) := by
    calc μ.toMeasure s
        ≤ ENNReal.ofReal (Real.exp ε₁) * ν.toMeasure s + ↑δ₁ := h₁ s hs
      _ ≤ ENNReal.ofReal (Real.exp ε₁) *
          (ENNReal.ofReal (Real.exp ε₂) * ρ.toMeasure s + ↑δ₂) + ↑δ₁ := by
          gcongr; exact h₂ s hs
      _ = ENNReal.ofReal (Real.exp ε₁) * (ENNReal.ofReal (Real.exp ε₂) * ρ.toMeasure s) +
          ENNReal.ofReal (Real.exp ε₁) * ↑δ₂ + ↑δ₁ := by rw [mul_add]
      _ = ENNReal.ofReal (Real.exp ↑(ε₁ + ε₂)) * ρ.toMeasure s +
          (ENNReal.ofReal (Real.exp ε₁) * ↑δ₂ + ↑δ₁) := by
          rw [add_assoc]; congr 1
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
              ← Real.exp_add, NNReal.coe_add]
  refine le_trans key (le_of_eq ?_)
  congr 1
  rw [ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _), ← ENNReal.coe_mul, ← ENNReal.coe_add]
  norm_cast

/-- Simpler transitivity for pure DP: chaining two pure bounds gives a pure bound. -/
theorem pureMeasureClose_trans {ε₁ ε₂ : NNReal}
    {μ ν ρ : ProbabilityMeasure O}
    (h₁ : PureMeasureClose ε₁ μ ν) (h₂ : PureMeasureClose ε₂ ν ρ) :
    PureMeasureClose (ε₁ + ε₂) μ ρ := by
  intro s hs
  have h1 := h₁ s hs
  have h2 := h₂ s hs
  simp only [PureMeasureClose, MeasureClose, ENNReal.coe_zero, add_zero] at *
  calc μ.toMeasure s
      ≤ ENNReal.ofReal (Real.exp ε₁) * ν.toMeasure s := h1
    _ ≤ ENNReal.ofReal (Real.exp ε₁) * (ENNReal.ofReal (Real.exp ε₂) * ρ.toMeasure s) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (↑(ε₁ + ε₂))) * ρ.toMeasure s := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
            NNReal.coe_add]

end MeasureLevel

section ProductComposition

variable {O₁ O₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]

/-- Product composition for pure DP at the measure level:
    if μ₁ ≤[ε₁] ν₁ and μ₂ ≤[ε₂] ν₂, then μ₁⊗μ₂ ≤[ε₁+ε₂] ν₁⊗ν₂.

    This is the measure-level fact underlying independent composition for pure DP. -/
theorem pureMeasureClose_prod {ε₁ ε₂ : NNReal}
    {μ₁ ν₁ : ProbabilityMeasure O₁} {μ₂ ν₂ : ProbabilityMeasure O₂}
    (h₁ : PureMeasureClose ε₁ μ₁ ν₁) (h₂ : PureMeasureClose ε₂ μ₂ ν₂) :
    PureMeasureClose (ε₁ + ε₂) (μ₁.prod μ₂) (ν₁.prod ν₂) := by
  intro s hs
  simp only [PureMeasureClose, MeasureClose, ENNReal.coe_zero, add_zero] at *
  rw [ProbabilityMeasure.toMeasure_prod, ProbabilityMeasure.toMeasure_prod]
  set c₁ := ENNReal.ofReal (Real.exp ↑ε₁)
  set c₂ := ENNReal.ofReal (Real.exp ↑ε₂)
  have hle₁ : μ₁.toMeasure ≤ c₁ • ν₁.toMeasure := by
    rw [Measure.le_iff]
    intro t ht
    rw [Measure.smul_apply]
    exact h₁ t ht
  have hle₂ : μ₂.toMeasure ≤ c₂ • ν₂.toMeasure := by
    rw [Measure.le_iff]
    intro t ht
    rw [Measure.smul_apply]
    exact h₂ t ht
  calc μ₁.toMeasure.prod μ₂.toMeasure s
      ≤ (c₁ • ν₁.toMeasure).prod (c₂ • ν₂.toMeasure) s :=
        Measure.prod_mono hle₁ hle₂ s
    _ = (c₁ • (ν₁.toMeasure.prod (c₂ • ν₂.toMeasure))) s := by
        rw [Measure.prod_smul_left]
    _ = (c₁ • (c₂ • (ν₁.toMeasure.prod ν₂.toMeasure))) s := by
        rw [Measure.prod_smul_right]
    _ = ((c₁ * c₂) • (ν₁.toMeasure.prod ν₂.toMeasure)) s := by
        rw [smul_smul]
    _ = ENNReal.ofReal (Real.exp ↑(ε₁ + ε₂)) * (ν₁.toMeasure.prod ν₂.toMeasure) s := by
        rw [Measure.smul_apply]
        congr 1
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, NNReal.coe_add]

/-- Fixing the left component preserves MeasureClose in the right component. -/
theorem measureClose_prod_left {ε : NNReal} {δ : NNReal}
    {μ : ProbabilityMeasure O₁} {ν₁ ν₂ : ProbabilityMeasure O₂}
    (h : MeasureClose ε δ ν₁ ν₂) :
    MeasureClose ε δ (μ.prod ν₁) (μ.prod ν₂) := by
  intro s hs
  rw [ProbabilityMeasure.toMeasure_prod, ProbabilityMeasure.toMeasure_prod,
      Measure.prod_apply hs, Measure.prod_apply hs]
  calc ∫⁻ x, ν₁.toMeasure (Prod.mk x ⁻¹' s) ∂μ.toMeasure
      ≤ ∫⁻ x, (ENNReal.ofReal (Real.exp ↑ε) * ν₂.toMeasure (Prod.mk x ⁻¹' s) + ↑δ)
          ∂μ.toMeasure := by
        apply lintegral_mono; intro x
        exact h _ (hs.preimage measurable_prodMk_left)
    _ = ENNReal.ofReal (Real.exp ↑ε) * ∫⁻ x, ν₂.toMeasure (Prod.mk x ⁻¹' s)
          ∂μ.toMeasure + ↑δ := by
        rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul _ (measurable_measure_prodMk_left hs),
            lintegral_const, measure_univ, mul_one]

/-- Fixing the right component preserves MeasureClose in the left component. -/
theorem measureClose_prod_right {ε : NNReal} {δ : NNReal}
    {μ₁ μ₂ : ProbabilityMeasure O₁} {ν : ProbabilityMeasure O₂}
    (h : MeasureClose ε δ μ₁ μ₂) :
    MeasureClose ε δ (μ₁.prod ν) (μ₂.prod ν) := by
  intro s hs
  rw [ProbabilityMeasure.toMeasure_prod, ProbabilityMeasure.toMeasure_prod,
      Measure.prod_apply_symm hs, Measure.prod_apply_symm hs]
  calc ∫⁻ y, μ₁.toMeasure ((fun x => (x, y)) ⁻¹' s) ∂ν.toMeasure
      ≤ ∫⁻ y, (ENNReal.ofReal (Real.exp ↑ε) * μ₂.toMeasure ((fun x => (x, y)) ⁻¹' s) + ↑δ)
          ∂ν.toMeasure := by
        apply lintegral_mono; intro y
        exact h _ (hs.preimage (measurable_id.prodMk measurable_const))
    _ = ENNReal.ofReal (Real.exp ↑ε) * ∫⁻ y, μ₂.toMeasure ((fun x => (x, y)) ⁻¹' s)
          ∂ν.toMeasure + ↑δ := by
        rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul _ (measurable_measure_prodMk_right hs),
            lintegral_const, measure_univ, mul_one]

/-- Product composition for approximate DP at the measure level:
    if μ₁ ≤[ε₁,δ₁] ν₁ and μ₂ ≤[ε₂,δ₂] ν₂, then
    μ₁⊗μ₂ ≤[ε₁+ε₂, exp(ε₂)·δ₁ + δ₂] ν₁⊗ν₂.

    Proof via iterated Fubini:
    (μ₁⊗μ₂)(S) = ∫ μ₂(Sₓ) dμ₁(x) ≤ exp(ε₂)·(μ₁⊗ν₂)(S) + δ₂
    (μ₁⊗ν₂)(S) = ∫ μ₁(Sʸ) dν₂(y) ≤ exp(ε₁)·(ν₁⊗ν₂)(S) + δ₁ -/
theorem measureClose_prod {ε₁ ε₂ : NNReal} {δ₁ δ₂ : NNReal}
    {μ₁ ν₁ : ProbabilityMeasure O₁} {μ₂ ν₂ : ProbabilityMeasure O₂}
    (h₁ : MeasureClose ε₁ δ₁ μ₁ ν₁) (h₂ : MeasureClose ε₂ δ₂ μ₂ ν₂) :
    MeasureClose (ε₁ + ε₂) (⟨Real.exp ↑ε₂, Real.exp_nonneg _⟩ * δ₁ + δ₂)
      (μ₁.prod μ₂) (ν₁.prod ν₂) := by
  intro s hs
  rw [ProbabilityMeasure.toMeasure_prod, ProbabilityMeasure.toMeasure_prod]
  set e₁ := ENNReal.ofReal (Real.exp ↑ε₁)
  set e₂ := ENNReal.ofReal (Real.exp ↑ε₂)
  -- Step 1: Fubini on first coordinate, apply DP₂ to sections
  have step1 : μ₁.toMeasure.prod μ₂.toMeasure s ≤
      e₂ * (μ₁.toMeasure.prod ν₂.toMeasure s) + ↑δ₂ := by
    rw [Measure.prod_apply hs, Measure.prod_apply hs]
    calc ∫⁻ x, μ₂.toMeasure (Prod.mk x ⁻¹' s) ∂μ₁.toMeasure
        ≤ ∫⁻ x, (e₂ * ν₂.toMeasure (Prod.mk x ⁻¹' s) + ↑δ₂) ∂μ₁.toMeasure := by
          apply lintegral_mono; intro x
          exact h₂ _ (hs.preimage (measurable_prodMk_left))
      _ = e₂ * ∫⁻ x, ν₂.toMeasure (Prod.mk x ⁻¹' s) ∂μ₁.toMeasure + ↑δ₂ := by
          rw [lintegral_add_right _ measurable_const,
              lintegral_const_mul _ (measurable_measure_prodMk_left hs),
              lintegral_const, measure_univ, mul_one]
  -- Step 2: Fubini on second coordinate, apply DP₁ to sections
  have step2 : μ₁.toMeasure.prod ν₂.toMeasure s ≤
      e₁ * (ν₁.toMeasure.prod ν₂.toMeasure s) + ↑δ₁ := by
    rw [Measure.prod_apply_symm hs, Measure.prod_apply_symm hs]
    calc ∫⁻ y, μ₁.toMeasure ((fun x => (x, y)) ⁻¹' s) ∂ν₂.toMeasure
        ≤ ∫⁻ y, (e₁ * ν₁.toMeasure ((fun x => (x, y)) ⁻¹' s) + ↑δ₁) ∂ν₂.toMeasure := by
          apply lintegral_mono; intro y
          exact h₁ _ (hs.preimage (measurable_id.prodMk measurable_const))
      _ = e₁ * ∫⁻ y, ν₁.toMeasure ((fun x => (x, y)) ⁻¹' s) ∂ν₂.toMeasure + ↑δ₁ := by
          rw [lintegral_add_right _ measurable_const,
              lintegral_const_mul _ (measurable_measure_prodMk_right hs),
              lintegral_const, measure_univ, mul_one]
  -- Step 3: Combine
  have h_exp : e₁ * e₂ = ENNReal.ofReal (Real.exp ↑(ε₁ + ε₂)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, NNReal.coe_add]
  have h_delta : e₂ * ↑δ₁ + ↑δ₂ =
      ↑(⟨Real.exp ↑ε₂, Real.exp_nonneg _⟩ * δ₁ + δ₂) := by
    change ENNReal.ofReal (Real.exp ↑ε₂) * ↑δ₁ + ↑δ₂ = _
    rw [ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg ↑ε₂),
        ← ENNReal.coe_mul, ← ENNReal.coe_add]
    rfl
  calc μ₁.toMeasure.prod μ₂.toMeasure s
      ≤ e₂ * (μ₁.toMeasure.prod ν₂.toMeasure s) + ↑δ₂ := step1
    _ ≤ e₂ * (e₁ * (ν₁.toMeasure.prod ν₂.toMeasure s) + ↑δ₁) + ↑δ₂ := by gcongr
    _ = e₁ * e₂ * (ν₁.toMeasure.prod ν₂.toMeasure s) + (e₂ * ↑δ₁ + ↑δ₂) := by ring
    _ = ENNReal.ofReal (Real.exp ↑(ε₁ + ε₂)) * (ν₁.toMeasure.prod ν₂.toMeasure s) +
        ↑(⟨Real.exp ↑ε₂, Real.exp_nonneg _⟩ * δ₁ + δ₂) := by rw [h_exp, h_delta]

end ProductComposition

/-- Independent composition for approximate DP via product mechanism. -/
theorem isApproxDP_prod {adj : D → D → Prop}
    {M₁ : Mechanism D O₁} {M₂ : Mechanism D O₂}
    {ε₁ ε₂ : NNReal} {δ₁ δ₂ : NNReal}
    (h₁ : IsApproxDP adj M₁ ε₁ δ₁) (h₂ : IsApproxDP adj M₂ ε₂ δ₂) :
    IsApproxDP adj (M₁.prod M₂) (ε₁ + ε₂)
      (⟨Real.exp ↑ε₂, Real.exp_nonneg _⟩ * δ₁ + δ₂) := by
  intro d₁ d₂ hadj
  exact measureClose_prod (h₁ d₁ d₂ hadj) (h₂ d₁ d₂ hadj)

/-- Independent composition for pure DP via product mechanism:
    If M₁ is ε₁-DP and M₂ is ε₂-DP, their product mechanism
    `fun d => (M₁ d, M₂ d)` is (ε₁+ε₂)-DP. -/
theorem isPureDP_prod {adj : D → D → Prop}
    {M₁ : Mechanism D O₁} {M₂ : Mechanism D O₂} {ε₁ ε₂ : NNReal}
    (h₁ : IsPureDP adj M₁ ε₁) (h₂ : IsPureDP adj M₂ ε₂) :
    IsPureDP adj (M₁.prod M₂) (ε₁ + ε₂) := by
  intro d₁ d₂ hadj
  exact pureMeasureClose_prod (h₁ d₁ d₂ hadj) (h₂ d₁ d₂ hadj)

/-- Group privacy for 2 hops: chaining two adjacencies doubles the ε bound. -/
theorem isPureDP_group_2 {adj : D → D → Prop} {M : Mechanism D O₁} {ε : NNReal}
    (hM : IsPureDP adj M ε) {d₁ d₂ d₃ : D}
    (h₁₂ : adj d₁ d₂) (h₂₃ : adj d₂ d₃) :
    PureMeasureClose (ε + ε) (M d₁) (M d₃) :=
  pureMeasureClose_trans (hM d₁ d₂ h₁₂) (hM d₂ d₃ h₂₃)

/-- Approximate DP group privacy for 2 hops: if M is (ε,δ)-DP, then
    for 2-hop adjacent databases d₁, d₃, M(d₁) and M(d₃) are
    (2ε, (e^ε + 1)·δ)-close. -/
theorem isApproxDP_group_2 {adj : D → D → Prop} {M : Mechanism D O₁} {ε δ : NNReal}
    (hM : IsApproxDP adj M ε δ) {d₁ d₂ d₃ : D}
    (h₁₂ : adj d₁ d₂) (h₂₃ : adj d₂ d₃) :
    MeasureClose (ε + ε)
      (⟨Real.exp ε * δ + δ, by positivity⟩) (M d₁) (M d₃) :=
  measureClose_trans (hM d₁ d₂ h₁₂) (hM d₂ d₃ h₂₃)

/-- Group privacy for k hops: if M is ε-DP and d₁,...,dₖ form an adjacency chain
    of length k, then M(d₁) and M(dₖ) are (k*ε)-close.
    Stated via induction on the chain structure. -/
theorem isPureDP_group {adj : D → D → Prop} {M : Mechanism D O₁} {ε : NNReal}
    (hM : IsPureDP adj M ε) {d₁ d₂ : D} {k : ℕ}
    (hchain : ∃ (chain : Fin (k + 2) → D),
      chain ⟨0, by omega⟩ = d₁ ∧
      chain ⟨k + 1, by omega⟩ = d₂ ∧
      ∀ i : Fin (k + 1), adj (chain i.castSucc) (chain i.succ)) :
    PureMeasureClose ((k + 1) * ε) (M d₁) (M d₂) := by
  obtain ⟨chain, hstart, hend, hadj_chain⟩ := hchain
  subst hstart; subst hend
  suffices h : ∀ (m : ℕ) (hm : m + 1 < k + 2),
      PureMeasureClose ((m + 1) * ε) (M (chain ⟨0, by omega⟩))
        (M (chain ⟨m + 1, hm⟩)) from
    h k (by omega)
  intro m hm
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_add, one_mul]
    exact hM _ _ (hadj_chain ⟨0, by omega⟩)
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 : PureMeasureClose ε (M (chain ⟨n + 1, by omega⟩))
        (M (chain ⟨n + 2, hm⟩)) :=
      hM _ _ (hadj_chain ⟨n + 1, by omega⟩)
    have h3 := pureMeasureClose_trans h1 h2
    convert h3 using 1
    push_cast; ring

-- ============================================================================
-- Parallel Composition (disjoint data)
-- ============================================================================

section ParallelComposition

variable {O₁ O₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]

/-- **Parallel composition for pure DP.**

    If M₁ and M₂ operate on disjoint partitions of the data — meaning for
    every adjacent pair, at most one mechanism's output changes — then the
    product mechanism is max(ε₁,ε₂)-DP instead of (ε₁+ε₂)-DP.

    The `disjoint` hypothesis captures: for adjacent d₁ ~ d₂, either M₁'s
    output is unchanged or M₂'s output is unchanged. This holds whenever
    the mechanisms access non-overlapping subsets of the database.

    Reference: Dwork & Roth (2014), §3.5.2 and McSherry (2009, PINQ). -/
theorem isPureDP_parallel {adj : D → D → Prop}
    {M₁ : Mechanism D O₁} {M₂ : Mechanism D O₂} {ε₁ ε₂ : NNReal}
    (h₁ : IsPureDP adj M₁ ε₁) (h₂ : IsPureDP adj M₂ ε₂)
    (disjoint : ∀ d₁ d₂, adj d₁ d₂ → M₁ d₁ = M₁ d₂ ∨ M₂ d₁ = M₂ d₂) :
    IsPureDP adj (M₁.prod M₂) (max ε₁ ε₂) := by
  intro d₁ d₂ hadj
  change PureMeasureClose (max ε₁ ε₂) ((M₁ d₁).prod (M₂ d₁)) ((M₁ d₂).prod (M₂ d₂))
  rcases disjoint d₁ d₂ hadj with hM₁_eq | hM₂_eq
  · rw [hM₁_eq]
    have key := pureMeasureClose_prod (pureMeasureClose_refl (M₁ d₂)) (h₂ d₁ d₂ hadj)
    simp only [zero_add] at key
    exact measureClose_epsilon_mono key (le_max_right ε₁ ε₂)
  · rw [hM₂_eq]
    have key := pureMeasureClose_prod (h₁ d₁ d₂ hadj) (pureMeasureClose_refl (M₂ d₂))
    simp only [add_zero] at key
    exact measureClose_epsilon_mono key (le_max_left ε₁ ε₂)

/-- **Parallel composition for approximate DP.**

    Same as the pure DP version but with (max(ε₁,ε₂), max(δ₁,δ₂))-DP.
    When data is disjoint, only one mechanism's privacy budget is consumed
    per adjacent pair. -/
theorem isApproxDP_parallel {adj : D → D → Prop}
    {M₁ : Mechanism D O₁} {M₂ : Mechanism D O₂}
    {ε₁ ε₂ : NNReal} {δ₁ δ₂ : NNReal}
    (h₁ : IsApproxDP adj M₁ ε₁ δ₁) (h₂ : IsApproxDP adj M₂ ε₂ δ₂)
    (disjoint : ∀ d₁ d₂, adj d₁ d₂ → M₁ d₁ = M₁ d₂ ∨ M₂ d₁ = M₂ d₂) :
    IsApproxDP adj (M₁.prod M₂) (max ε₁ ε₂) (max δ₁ δ₂) := by
  intro d₁ d₂ hadj
  change MeasureClose (max ε₁ ε₂) (max δ₁ δ₂) ((M₁ d₁).prod (M₂ d₁)) ((M₁ d₂).prod (M₂ d₂))
  rcases disjoint d₁ d₂ hadj with hM₁_eq | hM₂_eq
  · rw [hM₁_eq]
    exact measureClose_epsilon_mono (measureClose_delta_mono
      (measureClose_prod_left (h₂ d₁ d₂ hadj)) (le_max_right δ₁ δ₂)) (le_max_right ε₁ ε₂)
  · rw [hM₂_eq]
    exact measureClose_epsilon_mono (measureClose_delta_mono
      (measureClose_prod_right (h₁ d₁ d₂ hadj)) (le_max_left δ₁ δ₂)) (le_max_left ε₁ ε₂)

end ParallelComposition

-- ============================================================================
-- Pi (Finite Product) Composition
-- ============================================================================

private theorem pureMeasureClose_pi_fin {n : ℕ}
    {O' : Fin n → Type*} [∀ i, MeasurableSpace (O' i)]
    {ε : Fin n → NNReal}
    {μ ν : ∀ i, ProbabilityMeasure (O' i)}
    (h : ∀ i, PureMeasureClose (ε i) (μ i) (ν i)) :
    PureMeasureClose (∑ i : Fin n, ε i)
      (ProbabilityMeasure.pi μ) (ProbabilityMeasure.pi ν) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    intro s hs
    simp only [ENNReal.coe_zero, add_zero, NNReal.coe_zero, Real.exp_zero,
               ENNReal.ofReal_one, one_mul, ProbabilityMeasure.toMeasure_pi]
    rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ n ih =>
    rw [Fin.sum_univ_succAbove (fun i => ε i) 0]
    have h_prod := pureMeasureClose_prod (h 0) (ih (fun j => h (Fin.succAbove 0 j)))
    intro s hs
    simp only [PureMeasureClose, MeasureClose, ENNReal.coe_zero, add_zero] at h_prod ⊢
    set e := MeasurableEquiv.piFinSuccAbove O' 0
    have h_meas : MeasurableSet (e '' s) :=
      e.measurableEmbedding.measurableSet_image.mpr hs
    have h_map : ∀ (P : ∀ i, ProbabilityMeasure (O' i)),
        (ProbabilityMeasure.pi P).toMeasure.map e =
        ((P 0).prod (ProbabilityMeasure.pi (fun j => P (Fin.succAbove 0 j)))).toMeasure := by
      intro P
      simp only [ProbabilityMeasure.toMeasure_pi, ProbabilityMeasure.toMeasure_prod]
      exact (measurePreserving_piFinSuccAbove (fun i => (P i).toMeasure) 0).map_eq
    have key : ∀ (P : ∀ i, ProbabilityMeasure (O' i)),
        (ProbabilityMeasure.pi P).toMeasure s =
        ((P 0).prod (ProbabilityMeasure.pi (fun j => P (Fin.succAbove 0 j)))).toMeasure
          (e '' s) := by
      intro P
      rw [← h_map P, Measure.map_apply e.measurable h_meas, e.injective.preimage_image]
    rw [key μ, key ν]
    exact h_prod (e '' s) h_meas

section PiComposition

open Finset

variable {ι : Type*} [Fintype ι] {O : ι → Type*} [∀ i, MeasurableSpace (O i)]

/-- Product composition for pure DP over finite products:
    if each μ i ≤[ε i] ν i, then Measure.pi μ ≤[∑ i, ε i] Measure.pi ν.

    This generalizes `pureMeasureClose_prod` from binary to n-ary products. -/
theorem pureMeasureClose_pi
    {ε : ι → NNReal}
    {μ ν : ∀ i, ProbabilityMeasure (O i)}
    (h : ∀ i, PureMeasureClose (ε i) (μ i) (ν i)) :
    PureMeasureClose (∑ i, ε i)
      (ProbabilityMeasure.pi μ) (ProbabilityMeasure.pi ν) := by
  set f := (Fintype.equivFin ι).symm
  set e := MeasurableEquiv.piCongrLeft O f
  have h_fin := pureMeasureClose_pi_fin (fun j => h (f j))
  intro s hs
  simp only [PureMeasureClose, MeasureClose, ENNReal.coe_zero, add_zero] at h_fin ⊢
  have h_preimage_meas : MeasurableSet (e ⁻¹' s) := e.measurable hs
  have h_μ_eq : (ProbabilityMeasure.pi μ).toMeasure s =
      (ProbabilityMeasure.pi (fun j => μ (f j))).toMeasure (e ⁻¹' s) := by
    simp only [ProbabilityMeasure.toMeasure_pi]
    rw [← (measurePreserving_piCongrLeft (fun i => (μ i).toMeasure) f).map_eq,
        Measure.map_apply e.measurable hs]
  have h_ν_eq : (ProbabilityMeasure.pi ν).toMeasure s =
      (ProbabilityMeasure.pi (fun j => ν (f j))).toMeasure (e ⁻¹' s) := by
    simp only [ProbabilityMeasure.toMeasure_pi]
    rw [← (measurePreserving_piCongrLeft (fun i => (ν i).toMeasure) f).map_eq,
        Measure.map_apply e.measurable hs]
  rw [h_μ_eq, h_ν_eq]
  have h_bound := h_fin (e ⁻¹' s) h_preimage_meas
  rwa [show (∑ j : Fin _, ε (f j) : NNReal) = ∑ i, ε i from f.sum_comp ε] at h_bound

end PiComposition

end DPlean4
