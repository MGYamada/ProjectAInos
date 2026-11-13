/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.External.YM.Analysis.SmoothJets
public import ProjectAInos.Variational.Local

/-!
# Compatibility between the shared first jet and imported directional derivatives

The imported Yang--Mills analysis uses the same totalized Fréchet derivative
as the existing P⊗AI first-jet API. This identifies their first-order
components without claiming an equivalence with a global higher jet bundle.
-/

@[expose] public section

namespace ProjectAInos.Variational

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative part of P⊗AI's first jet evaluates to the imported
directional derivative, even at nondifferentiable points (both use the same
totalized `fderiv`). -/
theorem jet_derivative_eq_ym_directional (u : E → F) (x v : E) :
    (jet u x).2 v = YM.Analysis.D v u x := rfl

end ProjectAInos.Variational
