/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Smooth positive conformal rescaling of Lorentz metrics -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Multiplication by `exp (2 φ)` preserves Lorentz signature on the actual
tangent bundle. The sign convention and underlying manifold are unchanged. -/
def conformal (g : LorentzMetric σ d M) (φ : C^∞⟮I, M; ℝ⟯) : LorentzMetric σ d M where
  form x := Real.exp (2 * φ x) • g.form x
  smooth := (Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul φ.contMDiff)).smul_section
    g.smooth
  signature x := by
    obtain ⟨e, he⟩ := g.signature x
    let s := (LinearEquiv.smulOfNeZero ℝ (MinkowskiModel d) (Real.exp (φ x))
      (Real.exp_ne_zero _)).toContinuousLinearEquiv
    refine ⟨e.trans s, fun v w => ?_⟩
    change Real.exp (2 * φ x) * g.form x v w =
      minkowskiForm σ d (Real.exp (φ x) • e v) (Real.exp (φ x) • e w)
    simp only [map_smul, smul_apply, smul_eq_mul, he, two_mul, Real.exp_add]
    ring

@[simp] theorem conformal_form (g : LorentzMetric σ d M) (φ : C^∞⟮I, M; ℝ⟯) (x : M) :
    (g.conformal φ).form x = Real.exp (2 * φ x) • g.form x := rfl

end ProjectAInos.SmoothGeometry.LorentzMetric
