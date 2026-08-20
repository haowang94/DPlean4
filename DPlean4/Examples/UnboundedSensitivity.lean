/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Basic.Sensitivity
import DPlean4.Basic.Adjacency

/-!
# Unbounded Sensitivity: Why Data Bounds Matter

This file proves that certain natural query functions have **unbounded
sensitivity**, meaning no finite Δ bounds the sensitivity under add/remove
adjacency. Such queries cannot be answered with bounded Laplace or Gaussian
noise while maintaining differential privacy.

## Main Results

* `maxQuery_unbounded_sensitivity`: The maximum of a list has no finite L1
  sensitivity bound. For any Δ, there exist adjacent databases where the max
  differs by more than Δ.

* `sumQuery_unbounded_sensitivity`: The (unclamped) sum of a list has no
  finite L1 sensitivity bound. Adding a large element changes the sum
  arbitrarily.

## Significance

These results formalize why **data bounds are essential** for differential
privacy. Papers that claim DP for unbounded-domain queries without clamping
are making an error. The correct approach is:
1. **Clamp** data to a known range [lo, hi] (as in `PrivateMeanEstimation.lean`)
2. Then apply the DP mechanism with sensitivity derived from the clamp bounds

## References

* Dwork & Roth (2014), §3.3: "The sensitivity of f [...] depends on the range"
* A common pitfall discussed in Kifer & Machanavajjhala (2011),
  "No free lunch in data privacy"
-/

namespace DPlean4.Examples

open DPlean4
open scoped NNReal

-- ============================================================================
-- Maximum query: unbounded sensitivity
-- ============================================================================

/-- The maximum query: return the maximum element, or 0 for empty lists. -/
def maxQuery (l : List ℝ) : ℝ :=
  l.foldl max 0

/-- **The maximum query has unbounded sensitivity.**

    For any proposed sensitivity bound Δ, we construct adjacent databases
    (l₁ = [↑Δ + 1], l₂ = []) where |maxQuery l₁ - maxQuery l₂| = ↑Δ + 1 > ↑Δ.

    This means the Laplace mechanism with ANY finite noise scale would fail
    to provide ε-DP for the maximum query on unbounded data. -/
theorem maxQuery_unbounded_sensitivity :
    ∀ Δ : ℝ≥0, ¬ HasL1Sensitivity ListHeadAddRemove maxQuery Δ := by
  intro Δ hΔ
  have h_adj : ListHeadAddRemove [(↑Δ : ℝ) + 1] [] := by
    left; exact ⟨(↑Δ : ℝ) + 1, [], rfl, rfl⟩
  have h_sens := hΔ [(↑Δ : ℝ) + 1] [] h_adj
  simp only [maxQuery, List.foldl, sub_zero] at h_sens
  have h1 : (0 : ℝ) ≤ max 0 ((↑Δ : ℝ) + 1) := le_max_left _ _
  rw [abs_of_nonneg h1] at h_sens
  linarith [le_max_right (0 : ℝ) ((↑Δ : ℝ) + 1)]

-- ============================================================================
-- Sum query (unclamped): unbounded sensitivity
-- ============================================================================

/-- The unclamped sum query: return the sum of all elements. -/
def sumQuery (l : List ℝ) : ℝ :=
  l.sum

/-- **The unclamped sum has unbounded sensitivity.**

    For any Δ, adjacent databases ([↑Δ + 1], []) differ by ↑Δ + 1 > ↑Δ in sum.
    This is why `PrivateMeanEstimation.lean` uses clamped sums. -/
theorem sumQuery_unbounded_sensitivity :
    ∀ Δ : ℝ≥0, ¬ HasL1Sensitivity ListHeadAddRemove sumQuery Δ := by
  intro Δ hΔ
  have h_adj : ListHeadAddRemove [(↑Δ : ℝ) + 1] ([] : List ℝ) := by
    left; exact ⟨(↑Δ : ℝ) + 1, [], rfl, rfl⟩
  have h_sens := hΔ [(↑Δ : ℝ) + 1] [] h_adj
  simp only [sumQuery, List.sum_cons, List.sum_nil, add_zero, sub_zero] at h_sens
  linarith [le_abs_self ((↑Δ : ℝ) + 1)]

end DPlean4.Examples
