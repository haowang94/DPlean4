/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.ZCDP
import DPlean4.Basic.Sensitivity
import DPlean4.Basic.Adjacency
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

/-- The ratio of same-variance Gaussian PDFs is an exponential. -/
private lemma gaussianPDFReal_div_same_var {μ₁ μ₂ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal μ₁ v x / gaussianPDFReal μ₂ v x =
    Real.exp ((μ₁ - μ₂) * (2 * x - μ₁ - μ₂) / (2 * ↑v)) := by
  simp only [gaussianPDFReal]
  have hsqrt_ne : (Real.sqrt (2 * Real.pi * ↑v))⁻¹ ≠ 0 :=
    ne_of_gt (inv_pos.mpr (Real.sqrt_pos_of_pos (by positivity)))
  rw [mul_div_mul_left _ _ hsqrt_ne, ← Real.exp_sub]
  congr 1
  field_simp [NNReal.coe_ne_zero.mpr hv]
  ring

/-- The Rényi moment for same-variance Gaussians. -/
theorem renyiMoment_gaussianReal_same_var {μ₁ μ₂ : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) {α : ℝ} (hα : 1 < α) :
    renyiMoment α (gaussianReal μ₁ v) (gaussianReal μ₂ v) =
    ENNReal.ofReal (Real.exp (α * (α - 1) * (μ₁ - μ₂) ^ 2 / (2 * ↑v))) := by
  simp only [renyiMoment]
  set ν₂ := gaussianReal μ₂ v
  have hv_pos : (0 : ℝ) < ↑v := by positivity
  have hv_ne : (↑v : ℝ) ≠ 0 := ne_of_gt hv_pos
  have hac₂ : ν₂ ≪ volume := gaussianReal_absolutelyContinuous μ₂ hv
  set t := α * (μ₁ - μ₂) / ↑v
  set c := -(α * (μ₁ - μ₂) * (μ₁ + μ₂) / (2 * ↑v))
  -- Step 1: Rewrite (rnDeriv)^α as ofReal(exp(c) * exp(t * x))
  have h_integrand : (fun x ↦ ((gaussianReal μ₁ v).rnDeriv ν₂ x) ^ α) =ᵐ[ν₂]
      fun x ↦ ENNReal.ofReal (Real.exp c * Real.exp (t * x)) := by
    have h_div := Measure.rnDeriv_eq_div (gaussianReal_absolutelyContinuous μ₁ hv) hac₂
    have h_rd₁ := hac₂.ae_eq (rnDeriv_gaussianReal μ₁ v)
    have h_rd₂ := hac₂.ae_eq (rnDeriv_gaussianReal μ₂ v)
    filter_upwards [h_div, h_rd₁, h_rd₂] with x hx h₁ h₂
    rw [hx, h₁, h₂, gaussianPDF, gaussianPDF,
        ← ENNReal.ofReal_div_of_pos (gaussianPDFReal_pos μ₂ v x hv),
        ENNReal.ofReal_rpow_of_pos (div_pos (gaussianPDFReal_pos μ₁ v x hv)
          (gaussianPDFReal_pos μ₂ v x hv)),
        gaussianPDFReal_div_same_var hv x, ← Real.exp_mul]
    congr 1; rw [← Real.exp_add]; congr 1
    simp only [c, t]; field_simp; ring
  rw [lintegral_congr_ae h_integrand]
  -- Step 2: Convert lintegral to Bochner integral
  have hg_int : Integrable (fun x ↦ Real.exp c * Real.exp (t * x)) ν₂ :=
    (integrable_exp_mul_gaussianReal t).const_mul _
  have hg_nn : 0 ≤ᵐ[ν₂] (fun x ↦ Real.exp c * Real.exp (t * x)) :=
    ae_of_all _ (fun x ↦ mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  rw [← ofReal_integral_eq_lintegral_ofReal hg_int hg_nn]
  -- Step 3: Evaluate the integral via MGF
  congr 1
  rw [integral_const_mul]
  have h_mgf : ∫ x, Real.exp (t * x) ∂ν₂ = Real.exp (μ₂ * t + ↑v * t ^ 2 / 2) := by
    have := congr_fun (mgf_fun_id_gaussianReal (μ := μ₂) (v := v)) t
    simp only [mgf] at this; exact this
  rw [h_mgf, ← Real.exp_add]
  congr 1
  simp only [c, t]
  field_simp
  ring

/-- **Rényi divergence of same-variance Gaussians** (closed form).

    D_α(N(μ₁,v) ‖ N(μ₂,v)) = α(μ₁-μ₂)²/(2v) for α > 1, v > 0. -/
theorem renyiDivergence_gaussianReal_same_var {μ₁ μ₂ : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) {α : ℝ} (hα : 1 < α) :
    renyiDivergence α (gaussianReal μ₁ v) (gaussianReal μ₂ v) =
    α * (μ₁ - μ₂) ^ 2 / (2 * ↑v) := by
  simp only [renyiDivergence, renyiMoment_gaussianReal_same_var hv hα,
    ENNReal.toReal_ofReal (Real.exp_nonneg _), Real.log_exp]
  have : α - 1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < α - 1)
  field_simp

-- ============================================================================
-- Gaussian Mechanism is zCDP
-- ============================================================================

/-- **The Gaussian mechanism satisfies ρ-zCDP** with ρ = Δ²/(2v).

    Given a query with L2 sensitivity Δ and Gaussian noise with variance v > 0,
    the mechanism satisfies ρ-zCDP where ρ = Δ²/(2v).

    Proof uses: D_α(N(q(d₁),v) ‖ N(q(d₂),v)) = α|q(d₁)-q(d₂)|²/(2v) ≤ α·Δ²/(2v). -/
theorem gaussianMech_isZCDP {adj : D → D → Prop} {q : D → ℝ} {Δ : ℝ≥0} {v : ℝ≥0}
    (hv : v ≠ 0)
    (hsens : HasL2Sensitivity adj q Δ) :
    IsZCDP adj (gaussianMech q v) (Δ ^ 2 / (2 * v)) where
  ac d₁ d₂ _ := by
    simp only [gaussianMech_toMeasure]
    exact (gaussianReal_absolutelyContinuous _ hv).trans
      (gaussianReal_absolutelyContinuous' _ hv)
  fin d₁ d₂ _ α hα := by
    simp only [gaussianMech_toMeasure]
    rw [renyiMoment_gaussianReal_same_var hv hα]
    exact ENNReal.ofReal_ne_top
  bound d₁ d₂ hadj α hα := by
    set ρ : ℝ≥0 := Δ ^ 2 / (2 * v)
    rw [gaussianMech_toMeasure, gaussianMech_toMeasure,
        renyiDivergence_gaussianReal_same_var hv hα]
    have hv_pos : (0 : ℝ) < ↑v := by positivity
    have hα_pos : (0 : ℝ) < α := by linarith
    have hsens_bound := hsens d₁ d₂ hadj
    rw [Real.norm_eq_abs] at hsens_bound
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

    For a query with L2 sensitivity Δ, Gaussian noise variance v > 0,
    and any δ ∈ (0,1), the mechanism is (ε,δ)-DP for
    ε ≥ Δ²/(2v) + 2√(Δ²/(2v) · log(1/δ)).

    This follows from: Gaussian is ρ-zCDP with ρ = Δ²/(2v),
    then applying the zCDP → (ε,δ)-DP conversion. -/
theorem gaussianMech_isApproxDP {adj : D → D → Prop} {q : D → ℝ} {Δ : ℝ≥0} {v : ℝ≥0}
    (hv : v ≠ 0) (hΔ : Δ ≠ 0)
    (hsens : HasL2Sensitivity adj q Δ)
    {ε δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hε : (ε : ℝ) ≥ ((Δ ^ 2 / (2 * v) : ℝ≥0) : ℝ) +
      2 * Real.sqrt (((Δ ^ 2 / (2 * v) : ℝ≥0) : ℝ) * Real.log (1 / ↑δ))) :
    IsApproxDP adj (gaussianMech q v) ε δ :=
  isApproxDP_of_isZCDP (gaussianMech_isZCDP hv hsens) (by positivity) hδ hδ1 hε

-- ============================================================================
-- Examples
-- ============================================================================

section Examples

variable {α : Type*}

/-- The Gaussian mechanism with Δ=1, v=2 is (1/4)-zCDP for the counting query. -/
theorem gaussian_count_zCDP :
    IsZCDP ListHeadAddRemove
      (gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0))
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0))) := by
  apply gaussianMech_isZCDP (by norm_num : (2 : ℝ≥0) ≠ 0)
  exact HasL1Sensitivity.toL2 (fun l₁ l₂ hadj => by
    simp only [NNReal.coe_one]
    obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
    · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
    · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one])

/-- **Gaussian composition via zCDP**: Two independent counting queries with
    Gaussian noise (v=2 each) compose to (1/2)-zCDP.

    This demonstrates the zCDP composition theorem (isZCDP_prod):
    (1/4)-zCDP + (1/4)-zCDP = (1/2)-zCDP. -/
theorem gaussian_count_compose_zCDP :
    IsZCDP ListHeadAddRemove
      ((gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0)).prod
       (gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0)))
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0)) + (1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0))) :=
  isZCDP_prod gaussian_count_zCDP gaussian_count_zCDP

end Examples

end DPlean4

end -- noncomputable section
