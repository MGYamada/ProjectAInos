/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Models
public import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.NormNum

/-!
# Differentiating smooth substitution

On the free smooth-function ring the ordinary directional derivative at a
point satisfies the chain rule for every finite smooth operation.
-/

@[expose] public section

namespace ProjectAInos.SmoothAlgebra.SmoothOperation

variable {n m : ℕ}

/-- The directional derivative at a point, using the ordinary real calculus
of the concrete model. -/
noncomputable def directionalEvaluation (x v : Fin n → ℝ) (g : SmoothOperation n) : ℝ :=
  fderiv ℝ g x v

/-- Directional evaluation obeys the chain rule for arbitrary smooth operations. -/
theorem directionalEvaluation_op (f : SmoothOperation m) (g : Fin m → SmoothOperation n)
    (x v : Fin n → ℝ) :
    directionalEvaluation x v (SmoothRing.op f g) =
      directionalEvaluation (fun i => eval x (g i)) (fun i => directionalEvaluation x v (g i)) f := by
  have hg (i : Fin m) : DifferentiableAt ℝ (g i) x :=
    ((g i).contMDiff.contDiff.differentiable (by norm_num)) x
  have hf : DifferentiableAt ℝ f (fun i => g i x) :=
    (f.contMDiff.contDiff.differentiable (by norm_num)) _
  have h := hf.hasFDerivAt.comp x (hasFDerivAt_pi.mpr fun i => (hg i).hasFDerivAt)
  exact congrArg (fun D : (Fin n → ℝ) →L[ℝ] ℝ => D v) h.fderiv

end ProjectAInos.SmoothAlgebra.SmoothOperation
