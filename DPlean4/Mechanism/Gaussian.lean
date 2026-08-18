/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.ZCDP
import DPlean4.Basic.Sensitivity
import DPlean4.Basic.Adjacency
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian Mechanism

This file defines the Gaussian mechanism for differential privacy and proves
it satisfies ρ-zCDP (zero-concentrated differential privacy).

## Main Definitions

* `gaussianMech q v`: The Gaussian mechanism that adds N(0,v) noise to query q

## Main Results

* `renyiDivergence_gaussianReal_same_var`: Closed-form Rényi divergence for
  same-variance Gaussians: D_α(N(μ₁,v)‖N(μ₂,v)) = α(μ₁-μ₂)²/(2v)
* `gaussianMech_isZCDP`: The Gaussian mechanism satisfies ρ-zCDP with ρ = Δ²/(2v)
* `gaussianMech_isApproxDP`: Corollary via zCDP→(ε,δ)-DP conversion

## Design Notes

The mechanism uses Mathlib's `gaussianReal μ v : Measure ℝ` which is
parameterized by mean μ and variance v (NOT standard deviation).

### Rényi Divergence for Same-Variance Gaussians

  D_α(N(μ₁,v) ‖ N(μ₂,v)) = α(μ₁-μ₂)²/(2v)

Proof sketch: The density ratio exp(Δ(x-μ₂)/v - Δ²/(2v)) where Δ = μ₁-μ₂.
Raising to power α and integrating against N(μ₂,v) reduces to an MGF
evaluation: exp(-αΔ²/(2v)) · exp(v·(αΔ/v)²/2) = exp(α(α-1)Δ²/(2v)).
-/

noncomputable section

namespace DPlean4

open MeasureTheory Measure ProbabilityTheory

open scoped NNReal ENNReal

variable {D : Type*}

-- ============================================================================
-- Gaussian Mechanism Definition
-- ============================================================================

/-- The Gaussian mechanism: given a query q : D → ℝ, add N(0,v) noise.
    The output for database d is distributed as N(q(d), v).

    Parameters:
    - q : D → ℝ — the query function
    - v : ℝ≥0 — the noise variance (NOT standard deviation) -/
def gaussianMech (q : D → ℝ) (v : ℝ≥0) : Mechanism D ℝ :=
  fun d => ⟨gaussianReal (q d) v, inferInstance⟩

@[simp]
theorem gaussianMech_toMeasure (q : D → ℝ) (v : ℝ≥0) (d : D) :
    (gaussianMech q v d).toMeasure = gaussianReal (q d) v :=
  rfl

-- ============================================================================
-- Rényi Divergence for Same-Variance Gaussians
-- ============================================================================

/-- **Rényi divergence of same-variance Gaussians** (closed form).

    D_α(N(μ₁,v) ‖ N(μ₂,v)) = α(μ₁-μ₂)²/(2v) for α > 1, v > 0.

    The proof requires computing ∫ (dP/dQ)^α dQ via the Gaussian MGF:
    ∫ (p_μ₁/p_μ₂)^α dN(μ₂,v) = exp(-αΔ²/(2v)) · MGF(αΔ/v)
    = exp(-αΔ²/(2v)) · exp(α²Δ²/(2v)) = exp(α(α-1)Δ²/(2v)). -/
theorem renyiDivergence_gaussianReal_same_var {μ₁ μ₂ : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) {α : ℝ} (hα : 1 < α) :
    renyiDivergence α (gaussianReal μ₁ v) (gaussianReal μ₂ v) =
    α * (μ₁ - μ₂) ^ 2 / (2 * ↑v) := by
  sorry

/-- The Rényi moment for same-variance Gaussians. -/
theorem renyiMoment_gaussianReal_same_var {μ₁ μ₂ : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) {α : ℝ} (hα : 1 < α) :
    renyiMoment α (gaussianReal μ₁ v) (gaussianReal μ₂ v) =
    ENNReal.ofReal (Real.exp (α * (α - 1) * (μ₁ - μ₂) ^ 2 / (2 * ↑v))) := by
  sorry

-- ============================================================================
-- Gaussian Mechanism is zCDP
-- ============================================================================

/-- **The Gaussian mechanism satisfies ρ-zCDP** with ρ = Δ²/(2v).

    Given a query with L1 sensitivity Δ (= L2 for scalar queries)
    and Gaussian noise with variance v > 0, the mechanism satisfies
    ρ-zCDP where ρ = Δ²/(2v).

    Proof uses: D_α(N(q(d₁),v) ‖ N(q(d₂),v)) = α|q(d₁)-q(d₂)|²/(2v) ≤ α·Δ²/(2v). -/
theorem gaussianMech_isZCDP {adj : D → D → Prop} {q : D → ℝ} {Δ : ℝ≥0} {v : ℝ≥0}
    (hv : v ≠ 0)
    (hsens : HasL1Sensitivity adj q ↑Δ) :
    IsZCDP adj (gaussianMech q v) (Δ ^ 2 / (2 * v)) := by
  set ρ : ℝ≥0 := Δ ^ 2 / (2 * v)
  intro d₁ d₂ hadj α hα
  rw [gaussianMech_toMeasure, gaussianMech_toMeasure,
      renyiDivergence_gaussianReal_same_var hv hα]
  have hv_pos : (0 : ℝ) < ↑v := by positivity
  have hα_pos : (0 : ℝ) < α := by linarith
  have hsens_bound := hsens d₁ d₂ hadj
  have hΔ_sq : (q d₁ - q d₂) ^ 2 ≤ (↑Δ : ℝ) ^ 2 := by
    calc (q d₁ - q d₂) ^ 2 = |q d₁ - q d₂| ^ 2 := (sq_abs _).symm
      _ ≤ (↑Δ : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hsens_bound 2
  have step1 : α * (q d₁ - q d₂) ^ 2 / (2 * ↑v) ≤ α * (↑Δ : ℝ) ^ 2 / (2 * ↑v) := by
    gcongr
  have hρ_val : (ρ : ℝ) = (↑Δ : ℝ) ^ 2 / (2 * (↑v : ℝ)) := by
    change ((Δ ^ 2 / (2 * v) : ℝ≥0) : ℝ) = _
    simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_ofNat]
  linarith [show (ρ : ℝ) * α = α * (↑Δ : ℝ) ^ 2 / (2 * (↑v : ℝ)) by rw [hρ_val]; ring]

-- ============================================================================
-- Gaussian Mechanism is (ε,δ)-DP
-- ============================================================================

/-- **The Gaussian mechanism satisfies (ε,δ)-approximate DP.**

    For a query with L1 sensitivity Δ, Gaussian noise variance v > 0,
    and any δ ∈ (0,1), the mechanism is (ε,δ)-DP for
    ε ≥ Δ²/(2v) + 2√(Δ²/(2v) · log(1/δ)).

    This follows from: Gaussian is ρ-zCDP with ρ = Δ²/(2v),
    then applying the zCDP → (ε,δ)-DP conversion. -/
theorem gaussianMech_isApproxDP {adj : D → D → Prop} {q : D → ℝ} {Δ : ℝ≥0} {v : ℝ≥0}
    (hv : v ≠ 0)
    (hsens : HasL1Sensitivity adj q ↑Δ)
    {ε δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hε : (ε : ℝ) ≥ ((Δ ^ 2 / (2 * v) : ℝ≥0) : ℝ) +
      2 * Real.sqrt (((Δ ^ 2 / (2 * v) : ℝ≥0) : ℝ) * Real.log (1 / ↑δ))) :
    IsApproxDP adj (gaussianMech q v) ε δ :=
  isZCDP_to_isApproxDP (gaussianMech_isZCDP hv hsens) hδ hδ1 hε

-- ============================================================================
-- Examples
-- ============================================================================

section Examples

variable {α : Type*}

/-- The Gaussian mechanism with Δ=1, v=2 is (1/4)-zCDP for the counting query. -/
theorem gaussian_count_zCDP :
    IsZCDP ListAddRemove
      (gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0))
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0))) := by
  apply gaussianMech_isZCDP (by norm_num : (2 : ℝ≥0) ≠ 0)
  intro l₁ l₂ hadj
  simp only [NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]

end Examples

end DPlean4

end -- noncomputable section
