/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.ZCDP
import DPlean4.Basic.Sensitivity
import DPlean4.Mechanism.Gaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Vector Gaussian Mechanism

This file defines the vector Gaussian mechanism for differential privacy, which adds
independent Gaussian noise to each coordinate of a vector-valued query.

## Main Definitions

* `vectorGaussianMech q v`: adds independent N(0,v) noise to each coordinate of query q

## Main Results

* `vectorGaussianMech_isZCDP`: the mechanism satisfies ρ-zCDP with ρ = Δ²/(2v),
  where Δ is the L2 sensitivity of the query.

## Design Notes

The mechanism output type is `ι → ℝ` (plain function), not `EuclideanSpace ℝ ι`.
This avoids `WithLp` coercions while the measure is defined via `Measure.pi`.

Using `[Fintype ι]` means the same mechanism handles:
- Vectors: `ι = Fin n`
- Matrices: `ι = Fin m × Fin n`
- Tensors: `ι = Fin i₁ × Fin i₂ × ... × Fin iₖ`

The privacy bound uses **L2 sensitivity** (not per-coordinate composition),
which is essential for applications like DP-SGD where per-coordinate composition
gives an n-times-worse bound.

## References

* Bun & Dwork (2016), "Concentrated Differential Privacy"
* Dwork & Roth (2014), "The Algorithmic Foundations of Differential Privacy"
-/

noncomputable section

namespace DPlean4

open MeasureTheory Measure ProbabilityTheory

open scoped NNReal ENNReal

variable {D : Type*}

-- ============================================================================
-- Vector Gaussian Mechanism Definition
-- ============================================================================

/-- The vector Gaussian mechanism: given a query `q : D → ι → ℝ`, add
    independent N(0,v) noise to each coordinate.
    The output for database d is the product measure ∏ᵢ N(q(d)(i), v). -/
def vectorGaussianMech {ι : Type*} [Fintype ι]
    (q : D → ι → ℝ) (v : ℝ≥0) : Mechanism D (ι → ℝ) :=
  fun d => ⟨Measure.pi (fun i => gaussianReal (q d i) v), inferInstance⟩

@[simp]
theorem vectorGaussianMech_toMeasure {ι : Type*} [Fintype ι]
    (q : D → ι → ℝ) (v : ℝ≥0) (d : D) :
    (vectorGaussianMech q v d).toMeasure = Measure.pi (fun i => gaussianReal (q d i) v) :=
  rfl

-- ============================================================================
-- Rényi Divergence for Product Gaussians
-- ============================================================================

/-- Rényi moment of independent same-variance Gaussians with different means.
    The moment factorizes across coordinates, and each factor is the scalar formula.

    Proof depends on `renyiMoment_pi` (n-ary Rényi multiplicativity). -/
theorem renyiMoment_pi_gaussianReal {ι : Type*} [Fintype ι]
    {μ₁ μ₂ : ι → ℝ} {v : ℝ≥0} (hv : v ≠ 0) {α : ℝ} (hα : 1 < α) :
    renyiMoment α (Measure.pi (fun i => gaussianReal (μ₁ i) v))
                   (Measure.pi (fun i => gaussianReal (μ₂ i) v)) =
    ENNReal.ofReal (Real.exp (α * (α - 1) *
      (∑ i, (μ₁ i - μ₂ i) ^ 2) / (2 * ↑v))) := by
  have hac : ∀ i, gaussianReal (μ₁ i) v ≪ gaussianReal (μ₂ i) v :=
    fun i => (gaussianReal_absolutelyContinuous _ hv).trans (gaussianReal_absolutelyContinuous' _ hv)
  rw [renyiMoment_pi hac (le_of_lt (by linarith : (0 : ℝ) < α))]
  simp_rw [renyiMoment_gaussianReal_same_var hv hα]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_nonneg _)]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  simp_rw [← Finset.sum_div, ← Finset.mul_sum]

/-- **Rényi divergence of independent same-variance Gaussians** (closed form).
    D_α(∏ᵢ N(μ₁ᵢ,v) ‖ ∏ᵢ N(μ₂ᵢ,v)) = α · ∑ᵢ(μ₁ᵢ-μ₂ᵢ)² / (2v). -/
theorem renyiDivergence_pi_gaussianReal {ι : Type*} [Fintype ι]
    {μ₁ μ₂ : ι → ℝ} {v : ℝ≥0} (hv : v ≠ 0) {α : ℝ} (hα : 1 < α) :
    renyiDivergence α (Measure.pi (fun i => gaussianReal (μ₁ i) v))
                       (Measure.pi (fun i => gaussianReal (μ₂ i) v)) =
    α * (∑ i, (μ₁ i - μ₂ i) ^ 2) / (2 * ↑v) := by
  simp only [renyiDivergence, renyiMoment_pi_gaussianReal hv hα,
    ENNReal.toReal_ofReal (Real.exp_nonneg _), Real.log_exp]
  have : α - 1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < α - 1)
  field_simp

-- ============================================================================
-- Vector Gaussian Mechanism is zCDP
-- ============================================================================

/-- **The vector Gaussian mechanism satisfies ρ-zCDP** with ρ = Δ²/(2v).

    Given a vector-valued query with L2 sensitivity Δ (meaning
    ∑ᵢ (q d₁ i - q d₂ i)² ≤ Δ² for all adjacent d₁, d₂) and independent
    Gaussian noise with variance v > 0, the mechanism satisfies ρ-zCDP
    where ρ = Δ²/(2v).

    This uses the **direct** multivariate Rényi divergence formula,
    not per-coordinate composition. The difference is critical:
    direct gives ρ = Δ²/(2v), composition gives ρ = (Σᵢ Δᵢ²)/(2v),
    which is n times worse for DP-SGD. -/
theorem vectorGaussianMech_isZCDP {ι : Type*} [Fintype ι]
    {adj : D → D → Prop} {q : D → ι → ℝ} {Δ : ℝ≥0} {v : ℝ≥0}
    (hv : v ≠ 0)
    (hsens : HasL2VectorSensitivity adj q ↑Δ) :
    IsZCDP adj (vectorGaussianMech q v) (Δ ^ 2 / (2 * v)) where
  ac d₁ d₂ _ := by
    simp only [vectorGaussianMech_toMeasure]
    exact absolutelyContinuous_pi (fun i =>
      (gaussianReal_absolutelyContinuous _ hv).trans
        (gaussianReal_absolutelyContinuous' _ hv))
  fin d₁ d₂ _ α hα := by
    simp only [vectorGaussianMech_toMeasure]
    rw [renyiMoment_pi_gaussianReal hv hα]
    exact ENNReal.ofReal_ne_top
  bound d₁ d₂ hadj α hα := by
    set ρ : ℝ≥0 := Δ ^ 2 / (2 * v)
    rw [vectorGaussianMech_toMeasure, vectorGaussianMech_toMeasure,
        renyiDivergence_pi_gaussianReal hv hα]
    have hv_pos : (0 : ℝ) < ↑v := by positivity
    have hsens_bound := hsens d₁ d₂ hadj
    have hρ_val : (ρ : ℝ) = (↑Δ : ℝ) ^ 2 / (2 * (↑v : ℝ)) := by
      change ((Δ ^ 2 / (2 * v) : ℝ≥0) : ℝ) = _
      simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_ofNat]
    have step : α * ∑ i, (q d₁ i - q d₂ i) ^ 2 ≤ α * (↑Δ : ℝ) ^ 2 := by gcongr
    have h2v_pos : (0 : ℝ) < 2 * ↑v := by positivity
    have goal_eq : (ρ : ℝ) * α = α * (↑Δ : ℝ) ^ 2 / (2 * (↑v : ℝ)) := by rw [hρ_val]; ring
    rw [goal_eq]
    exact div_le_div_of_nonneg_right step h2v_pos.le

-- ============================================================================
-- Corollary: (ε,δ)-Approximate DP
-- ============================================================================

/-- **The vector Gaussian mechanism satisfies (ε,δ)-approximate DP.** -/
theorem vectorGaussianMech_isApproxDP {ι : Type*} [Fintype ι]
    {adj : D → D → Prop} {q : D → ι → ℝ} {Δ : ℝ≥0} {v : ℝ≥0}
    (hv : v ≠ 0) (hΔ : Δ ≠ 0)
    (hsens : HasL2VectorSensitivity adj q ↑Δ)
    {ε δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hε : (ε : ℝ) ≥ ((Δ ^ 2 / (2 * v) : ℝ≥0) : ℝ) +
      2 * Real.sqrt (((Δ ^ 2 / (2 * v) : ℝ≥0) : ℝ) * Real.log (1 / ↑δ))) :
    IsApproxDP adj (vectorGaussianMech q v) ε δ :=
  isApproxDP_of_isZCDP (vectorGaussianMech_isZCDP hv hsens) (by positivity) hδ hδ1 hε

end DPlean4

end -- noncomputable section
