/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.VectorGaussian
import DPlean4.Mechanism.Exponential
import DPlean4.Privacy.ZCDP
import DPlean4.Privacy.TightZCDP
import DPlean4.Basic.TabularData

/-!
# AIM: Adaptive and Iterative Mechanism for DP Synthetic Data

This file formalizes the privacy analysis of the AIM algorithm
(McKenna, Mullins, Sheldon, Miklau 2022), which iteratively selects and
measures marginals to produce differentially private synthetic data.

## Algorithm Overview

AIM runs for T rounds. Each round:

1. **Select**: Use the exponential mechanism to pick the marginal with
   highest error on the current synthetic data. (εₜ-pure DP → εₜ²/2-zCDP)
2. **Measure**: Use the Gaussian mechanism to privately measure the
   *selected* marginal. (ρₜ-zCDP)
3. **Update** (post-processing): Update the PGM model with the new noisy
   measurement and regenerate synthetic data. No privacy cost.

## Privacy Analysis

- Selection: exponential mechanism is εₜ-pure DP → (εₜ²/2)-zCDP (tight conversion)
- Measurement: Gaussian mechanism is ρₜ-zCDP
- Per-round cost: (εₜ²/2 + ρₜ)-zCDP by adaptive composition (selection feeds measurement)
- T rounds compose: ∑ₜ (εₜ²/2 + ρₜ)-zCDP by n-ary composition
- Convert to (ε,δ)-DP via zCDP→approxDP theorem

## Design Notes

Each round is modeled as an adaptive composition using `Mechanism.seqFinite`:
the exponential mechanism selects a marginal, and the selected marginal
determines which Gaussian measurement to run. This matches the actual AIM
algorithm where the measurement step depends on the selection output.

## References

* McKenna, Mullins, Sheldon, Miklau (2022), "AIM: An Adaptive and Iterative
  Mechanism for Differentially Private Synthetic Data"
* Bun & Dwork (2016), "Concentrated Differential Privacy"
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory Finset
open scoped NNReal ENNReal

variable {Attr : Type*} {dom : Attr → Type*} [∀ a, DecidableEq (dom a)]

-- ============================================================================
-- Per-round configuration
-- ============================================================================

/-- Configuration for one round of AIM: which marginal to measure and the
    noise parameters for selection and measurement. -/
structure AIMRoundConfig (Attr : Type*) (dom : Attr → Type*) where
  a₁ : Attr
  a₂ : Attr
  [inst₁ : Fintype (dom a₁)]
  [inst₂ : Fintype (dom a₂)]
  measureV : ℝ≥0

-- ============================================================================
-- Per-round mechanisms
-- ============================================================================

variable {Marginal : Type*} [Fintype Marginal] [Nonempty Marginal]
  [MeasurableSpace Marginal] [MeasurableSingletonClass Marginal]

/-- AIM selection step: use exponential mechanism to choose a marginal
    based on a utility/error function.

    In AIM, the utility function scores each candidate marginal by the
    error of the current synthetic data on that marginal. We leave this
    abstract — the privacy guarantee holds for any utility function with
    bounded sensitivity. -/
def aimSelect (u : TabularDataset Attr dom → Marginal → ℝ)
    (Δ : ℝ≥0) (εₜ : NNReal) :
    Mechanism (TabularDataset Attr dom) Marginal :=
  expMech u εₜ Δ

omit [∀ a, DecidableEq (dom a)] in
/-- AIM selection satisfies εₜ-pure DP. -/
theorem aimSelect_isPureDP
    {u : TabularDataset Attr dom → Marginal → ℝ} {Δ : ℝ≥0} (hΔ : Δ ≠ 0) {εₜ : NNReal}
    (hsens : HasUtilitySensitivity (@ListHeadAddRemove (TabularRow Attr dom)) u Δ) :
    IsPureDP (@ListHeadAddRemove (TabularRow Attr dom)) (aimSelect u Δ εₜ) εₜ :=
  expMech_isPureDP hΔ hsens

omit [∀ a, DecidableEq (dom a)] in
/-- AIM selection satisfies (εₜ²/2)-zCDP (tight conversion from pure DP).
    Uses symmetric adjacency of `ListHeadAddRemove`. -/
theorem aimSelect_isZCDP_tight
    {u : TabularDataset Attr dom → Marginal → ℝ} {Δ : ℝ≥0} (hΔ : Δ ≠ 0) {εₜ : NNReal}
    (hsens : HasUtilitySensitivity (@ListHeadAddRemove (TabularRow Attr dom)) u Δ) :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom)) (aimSelect u Δ εₜ) (εₜ ^ 2 / 2) :=
  expMech_isZCDP_tight hΔ hsens listHeadAddRemove_symm

/-- AIM measurement step: privately measure a 2-way marginal using the
    vector Gaussian mechanism. -/
def aimMeasure (a₁ a₂ : Attr) [Fintype (dom a₁)] [Fintype (dom a₂)]
    (vₜ : ℝ≥0) :
    Mechanism (TabularDataset Attr dom) (dom a₁ × dom a₂ → ℝ) :=
  vectorGaussianMech (marginalVector2 a₁ a₂) vₜ

/-- AIM measurement satisfies (1/(2·vₜ))-zCDP (L2 sensitivity of marginals is 1). -/
theorem aimMeasure_isZCDP (a₁ a₂ : Attr) [Fintype (dom a₁)] [Fintype (dom a₂)]
    {vₜ : ℝ≥0} (hvₜ : vₜ ≠ 0) :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom))
      (aimMeasure a₁ a₂ vₜ)
      ((1 : ℝ≥0) ^ 2 / (2 * vₜ)) :=
  vectorGaussianMech_isZCDP hvₜ (marginalVector2_L2Sensitivity a₁ a₂)

-- ============================================================================
-- Single round: adaptive select → measure
-- ============================================================================

omit [∀ a, DecidableEq (dom a)] in
/-- **One adaptive round costs (εₜ²/2 + ρ₂)-zCDP.**

    The selection cost uses the tight εₜ²/2-zCDP conversion, and the
    measurement cost is given by a uniform bound over all possible selections.
    Adaptive composition (`isZCDP_seqFinite`) composes them.

    The measurement function `measureFor` maps each selected marginal to a
    mechanism, modeling the true AIM algorithm where measurement depends on
    selection output. The uniform bound `hmeas` is naturally satisfied when
    all marginals have the same L2 sensitivity (e.g., all 2-way marginals
    have L2 sensitivity 1). -/
theorem aimAdaptiveRound_isZCDP
    {MeasOutput : Type*} [MeasurableSpace MeasOutput]
    {u : TabularDataset Attr dom → Marginal → ℝ} {Δ : ℝ≥0} (hΔ : Δ ≠ 0)
    (hsens : HasUtilitySensitivity (@ListHeadAddRemove (TabularRow Attr dom)) u Δ)
    {εₜ : NNReal} {ρ₂ : NNReal}
    {measureFor : Marginal → Mechanism (TabularDataset Attr dom) MeasOutput}
    (hmeas : ∀ m, IsZCDP (@ListHeadAddRemove (TabularRow Attr dom)) (measureFor m) ρ₂) :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom))
      ((aimSelect u Δ εₜ).seqFinite measureFor)
      (εₜ ^ 2 / 2 + ρ₂) :=
  isZCDP_seqFinite (aimSelect_isZCDP_tight hΔ hsens) hmeas

-- ============================================================================
-- T-round AIM pipeline
-- ============================================================================

/-- T rounds of AIM measurements (without the selection step).

    This simplified version models AIM as T independent Gaussian measurements
    on pre-selected marginals. The selection step's privacy cost is accounted
    separately. -/
def aimMeasurePipeline {T : ℕ} (rounds : Fin T → AIMRoundConfig Attr dom) :
    Mechanism (TabularDataset Attr dom)
      (∀ t : Fin T, dom (rounds t).a₁ × dom (rounds t).a₂ → ℝ) :=
  Mechanism.pi (fun t =>
    @aimMeasure Attr dom _ (rounds t).a₁ (rounds t).a₂
      (rounds t).inst₁ (rounds t).inst₂ (rounds t).measureV)

/-- T rounds of measurements cost ∑_t 1/(2·v_t) zCDP. -/
theorem aimMeasurePipeline_isZCDP {T : ℕ} (rounds : Fin T → AIMRoundConfig Attr dom)
    (hv : ∀ t, (rounds t).measureV ≠ 0) :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom))
      (aimMeasurePipeline rounds)
      (∑ t : Fin T, (1 : ℝ≥0) ^ 2 / (2 * (rounds t).measureV)) :=
  isZCDP_pi (fun t =>
    @aimMeasure_isZCDP Attr dom _ (rounds t).a₁ (rounds t).a₂
      (rounds t).inst₁ (rounds t).inst₂ (rounds t).measureV (hv t))

-- ============================================================================
-- Full AIM privacy theorem (with tight selection accounting)
-- ============================================================================

omit [∀ a, DecidableEq (dom a)] in
/-- **Full AIM privacy accounting (tight).**

    For T rounds of AIM with:
    - Round t selection: exponential mechanism with budget εₜ (pure DP → (εₜ²/2)-zCDP)
    - Round t measurement: parametric mechanism with budget ρ₂(t)-zCDP

    Total privacy cost: ∑ₜ (εₜ²/2 + ρ₂(t)) zCDP

    Each round is modeled as an adaptive composition via `seqFinite`: the
    exponential mechanism selects a marginal, and `measureFor t` maps the
    selected marginal to the appropriate measurement mechanism. The T rounds
    are composed independently via `isZCDP_pi`. -/
theorem aim_total_isZCDP {T : ℕ}
    {MeasOutput : Type*} [MeasurableSpace MeasOutput]
    {u : Fin T → TabularDataset Attr dom → Marginal → ℝ}
    {Δ : ℝ≥0} (hΔ : Δ ≠ 0)
    {selectε : Fin T → NNReal}
    (hsens : ∀ t, HasUtilitySensitivity
      (@ListHeadAddRemove (TabularRow Attr dom)) (u t) Δ)
    {ρ₂ : Fin T → NNReal}
    {measureFor : Fin T → Marginal → Mechanism (TabularDataset Attr dom) MeasOutput}
    (hmeas : ∀ t m, IsZCDP (@ListHeadAddRemove (TabularRow Attr dom)) (measureFor t m) (ρ₂ t)) :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom))
      (Mechanism.pi (fun t => (aimSelect (u t) Δ (selectε t)).seqFinite (measureFor t)))
      (∑ t, (selectε t ^ 2 / 2 + ρ₂ t)) :=
  isZCDP_pi (fun t => aimAdaptiveRound_isZCDP hΔ (hsens t) (hmeas t))

omit [∀ a, DecidableEq (dom a)] in
/-- AIM satisfies (ε,δ)-approximate DP via zCDP→approxDP conversion.

    The total zCDP cost ρ = ∑ₜ (εₜ²/2 + ρ₂(t)) is converted to (ε,δ)-DP
    using the standard zCDP→approxDP formula. -/
theorem aim_isApproxDP {T : ℕ}
    {MeasOutput : Type*} [MeasurableSpace MeasOutput]
    {u : Fin T → TabularDataset Attr dom → Marginal → ℝ}
    {Δ : ℝ≥0} (hΔ : Δ ≠ 0)
    {selectε : Fin T → NNReal}
    (hsens : ∀ t, HasUtilitySensitivity
      (@ListHeadAddRemove (TabularRow Attr dom)) (u t) Δ)
    {ρ₂ : Fin T → NNReal}
    {measureFor : Fin T → Marginal → Mechanism (TabularDataset Attr dom) MeasOutput}
    (hmeas : ∀ t m, IsZCDP (@ListHeadAddRemove (TabularRow Attr dom)) (measureFor t m) (ρ₂ t))
    {ε δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    {ρ : NNReal}
    (hρ_eq : ρ = ∑ t, (selectε t ^ 2 / 2 + ρ₂ t))
    (hρ_pos : 0 < ρ)
    (hε : (ε : ℝ) ≥ ↑ρ + 2 * Real.sqrt (↑ρ * Real.log (1 / ↑δ))) :
    IsApproxDP (@ListHeadAddRemove (TabularRow Attr dom))
      (Mechanism.pi (fun t => (aimSelect (u t) Δ (selectε t)).seqFinite (measureFor t)))
      ε δ := by
  rw [hρ_eq] at hρ_pos hε
  exact isApproxDP_of_isZCDP
    (aim_total_isZCDP hΔ hsens hmeas) hρ_pos hδ hδ1 hε

end DPlean4.Examples

end -- noncomputable section
