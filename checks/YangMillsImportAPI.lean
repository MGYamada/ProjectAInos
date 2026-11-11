/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos

/-! A public API smoke test for the independently ported Yang--Mills modules.
    This file checks the names and types, not the physical validity of any
    specified construction or positive-mass-gap claim. -/

#check YM.Analytic.param
#check YM.Analysis.sym_Jet
#check YM.Tensor.Euler
#check YM.Kernel.host
#check YM.Wilson.law
#check YM.Wilson.law_gauge
#check YangMills.GaugeGroup.core
#check YangMills.wilsonEnergy_eq_core
#check YangMills.wilsonLaw_eq_core
#check YangMills.WilsonFamily.haar_eq_core
#check YangMills.WilsonFamily.law_eq_core
#check YangMills.WilsonFamily.finiteMoment_eq_core
#check YangMills.WilsonFamily.Converges
#check YangMills.JointExistence
#check ProjectAInos.Variational.jet_derivative_eq_ym_directional
#check ProjectAInos.SmoothGeometry.YangMillsCoordinates.pointLinear
#check ProjectAInos.SmoothGeometry.YangMillsCoordinates.time_eq
#check ProjectAInos.SmoothGeometry.YangMillsCoordinates.minkowskiSquare_eq
#check ProjectAInos.SmoothGeometry.YangMillsCoordinates.configurations_injective

example : YangMills.JointExistence → YangMills.JointExistence := id

namespace YangMillsImportChecks
open YangMills ProjectAInos.SmoothGeometry
open ProjectAInos.SmoothGeometry.YangMillsCoordinates
open ProjectAInos.SpecialRelativity

example {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C} {order : ℕ → ℕ}
    (h : T.IntegratedProperties order) :
    C.Converges order (fun v => T.correlation (some T.selected) (T.project ∘ v)) :=
  h.selectedWilson

example {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}
    (h : T.CorrelatorAlgebra) {n : ℕ}
    (s : Option T.Character) (a b : Fin n → T.Tag) (x : Points n)
    (hx : x ∈ WilsonFamily.separated n)
    (heq : ∀ i, T.toLabel (a i).1 (a i).2 = T.toLabel (b i).1 (b i).2) :
    T.correlation s a x = T.correlation s b x :=
  h.correlation_eq_of_labels s a b x hx heq

example (β : Velocity 3) (x : FourVector) :
    (properLorentz (boostProperOrthochronous β)).val.val (pointLinear x) =
      pointLinear ((boost β).val x) :=
  lorentzLinear_apply (boost β) x

#check Hierarchy.selectedWilsonLimit_iff
#check Hierarchy.CorrelatorAlgebra.correlation_eq_zero
#check Hierarchy.CorrelatorAlgebra.weight_eq
#check Hierarchy.CorrelatorAlgebra.sum_not_tag
#check poincare_apply
#check poincare_pullback_point
#check physicalMomentum_futureCausal
#check fourierMomentum_covariance
#check spectralRepresentation_minkowski

end YangMillsImportChecks
