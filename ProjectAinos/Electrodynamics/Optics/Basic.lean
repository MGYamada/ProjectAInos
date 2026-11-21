/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Geometrical optics: shared definitions

Definitions shared by the files on geometrical optics (Landau–Lifshitz, *The Classical Theory of
Fields*, §§53–58). A medium is a refractive index `n : ℝ³ → ℝ` on
`ℝ³ = EuclideanSpace ℝ (Fin 3)`.

* `opticalLength n γ a b`: the optical length `∫ₐᵇ n(γ(t)) |γ′(t)| dt` of a path, whose stationary
  points are the rays (Fermat's principle).
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics.Optics

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The optical length `∫ₐᵇ n(γ(t)) |γ′(t)| dt` of a path `γ` in a medium of index `n`. -/
def opticalLength (n : E3 → ℝ) (γ : ℝ → E3) (a b : ℝ) : ℝ :=
  ∫ t in a..b, n (γ t) * ‖deriv γ t‖

end ProjectAinos.Electrodynamics.Optics
