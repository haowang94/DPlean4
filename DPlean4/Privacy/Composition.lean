/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.Approximate
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Composition Theorems for Differential Privacy

This file proves basic composition theorems for differential privacy.

## Main Results

* `measureClose_trans`: Transitivity with tight δ bound (exp(ε₁)·δ₂+δ₁)
* `pureMeasureClose_prod`: Product composition for pure DP measures
* `isPureDP_prod`: Independent composition: ε₁-DP ⊗ ε₂-DP → (ε₁+ε₂)-DP
* `isPureDP_group`: Group privacy for k-hop adjacency chains

## Design Notes

We prove **independent** (non-adaptive) composition first. The two mechanisms
operate on the same input database but produce independent outputs.

Adaptive composition (where the second mechanism depends on the first's output)
requires Markov kernels and will be addressed in a separate file (KernelBridge.lean).

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

end ProductComposition

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

end DPlean4
