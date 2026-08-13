/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Mechanisms for Differential Privacy

This file defines the core representation of a differential privacy mechanism.

## Main Definitions

* `Mechanism D O`: A randomized algorithm mapping databases of type `D` to
  probability distributions over outputs of type `O`.

## Design Notes

We use `D → ProbabilityMeasure O` rather than Markov kernels for the primary representation.

**Why not kernel-first?**
A `Kernel` requires both input and output to be measurable spaces, but databases
(e.g., `List T`) do not need a measurable structure for the elementary DP definition
`∀ x x', Adjacent x x' → ...`. Using `D → ProbabilityMeasure O` avoids forcing databases
into an artificial measurable space.

For adaptive composition (where a second mechanism depends measurably on the first's output),
we provide kernel-facing utilities in `KernelBridge.lean`. That layer requires explicit
measurability of the continuation.

This design aligns with the plan's principle: prototype both representations, select the
public API after concrete experience with postprocessing and composition proofs.
-/

namespace DPlean4

open MeasureTheory

variable (D : Type*) (O : Type*) [MeasurableSpace O]

/-- A mechanism is a function from databases to probability measures on outputs.

The database type `D` need not be measurable. The output type `O` must have a
measurable space structure so we can reason about measurable events.

Example:
```lean
-- Randomized response on binary data
def randomizedResponse (ε : ℝ) (b : Bool) : ProbabilityMeasure Bool :=
  ...
```
-/
abbrev Mechanism := D → ProbabilityMeasure O

/-- A constant mechanism always returns the same probability measure, regardless
of the input database. -/
def constantMechanism (μ : ProbabilityMeasure O) : Mechanism D O :=
  fun _ => μ

-- Note: A deterministic mechanism (Dirac measure) will be added when we have
-- proper discrete probability measure utilities

end DPlean4
