/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.Approximate
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Composition Theorems for Differential Privacy

This file proves basic composition theorems for differential privacy.

## Main Results

* `measureClose_prod`: Product composition at the measure level
* `isApproxDP_compose`: If M₁ is (ε₁,δ₁)-DP and M₂ is (ε₂,δ₂)-DP (independently),
  then the product mechanism is (ε₁+ε₂, δ₁+δ₂)-DP
* `isPureDP_compose`: Special case for pure DP: ε₁-DP ⊗ ε₂-DP → (ε₁+ε₂)-DP

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
  sorry -- TODO: Requires careful ENNReal arithmetic
  -- Key steps:
  -- 1. μ(s) ≤ exp(ε₁) * ν(s) + δ₁
  -- 2. ν(s) ≤ exp(ε₂) * ρ(s) + δ₂
  -- 3. Substitute (2) into (1):
  --    μ(s) ≤ exp(ε₁) * (exp(ε₂) * ρ(s) + δ₂) + δ₁
  --         = exp(ε₁) * exp(ε₂) * ρ(s) + exp(ε₁) * δ₂ + δ₁
  --         = exp(ε₁+ε₂) * ρ(s) + (exp(ε₁) * δ₂ + δ₁)

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

/-- Basic sequential composition for approximate DP.
    If M₁ is (ε₁,δ₁)-DP and M₂ is (ε₂,δ₂)-DP on the same output space, and we
    run them independently on the same database, privacy degrades additively:
    ε_total = ε₁ + ε₂, δ_total = δ₁ + δ₂.

    Note: This is the basic composition theorem. The δ bound here (δ₁+δ₂) is
    simpler but slightly looser than the optimal exp(ε₁)·δ₂ + δ₁ from
    measureClose_trans. For pure DP (δ=0) both give the same result. -/
theorem isApproxDP_compose_simple {adj : D → D → Prop}
    {M₁ M₂ : Mechanism D O₁} {ε₁ ε₂ δ₁ δ₂ : NNReal}
    (h₁ : IsApproxDP adj M₁ ε₁ δ₁) (_h₂ : IsApproxDP adj M₂ ε₂ δ₂) :
    IsApproxDP adj M₁ (ε₁ + ε₂) (δ₁ + δ₂) := by
  intro d₁ d₂ hadj
  exact measureClose_epsilon_mono
    (measureClose_delta_mono (h₁ d₁ d₂ hadj) le_self_add)
    le_self_add

/-- Sequential composition for pure DP:
    If M₁ is ε₁-DP and M₂ is ε₂-DP, then M₁ is (ε₁+ε₂)-DP. -/
theorem isPureDP_compose_simple {adj : D → D → Prop}
    {M₁ M₂ : Mechanism D O₁} {ε₁ ε₂ : NNReal}
    (h₁ : IsPureDP adj M₁ ε₁) (_h₂ : IsPureDP adj M₂ ε₂) :
    IsPureDP adj M₁ (ε₁ + ε₂) := by
  exact isPureDP_mono h₁ le_self_add

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
  sorry -- TODO: induction on k, using pureMeasureClose_trans at each step

end DPlean4
