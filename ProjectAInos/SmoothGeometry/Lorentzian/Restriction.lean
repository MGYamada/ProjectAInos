/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Manifold.OpenSubset
public import ProjectAInos.SmoothGeometry.Lorentzian.Naturality

/-! # Restriction of Lorentz metrics and connections to open submanifolds -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open TopologicalSpace VectorField
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Restrict the metric along the inclusion of an open submanifold.
Tangent vectors are identified using the actual derivative of the inclusion. -/
def restrict (U : Opens M) : LorentzMetric σ d U :=
  g.pullback Subtype.val contMDiff_subtype_val (Manifold.isInvertible_mfderiv_subtype_val I U)

@[simp] theorem restrict_form (U : Opens M) (x : U) (v w : TangentSpace I x) :
    (g.restrict U).form x v w = g.form x.val
      (mfderiv I I (Subtype.val : U → M) x v)
      (mfderiv I I (Subtype.val : U → M) x w) :=
  g.pullback_form _ _ _ x v w

/-- Restriction of the constructed connection agrees with restriction of its
action on every ambient field differentiable at the evaluation point. -/
theorem leviCivita_restrict (U : Opens M) {x : U}
    {Y : ∀ y : M, TangentSpace I y}
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x.val)
    (v : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x
      ((g.restrict U).leviCivita (mpullback I I (Subtype.val : U → M) Y) x v) =
      g.leviCivita Y x.val (mfderiv I I (Subtype.val : U → M) x v) :=
  g.leviCivita_pullback contMDiff_subtype_val
    (Manifold.isInvertible_mfderiv_subtype_val I U) hY v

end ProjectAInos.SmoothGeometry.LorentzMetric
