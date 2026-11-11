module
public import ProjectAInos.Electrodynamics.Field

/-! # Potential components and the homogeneous Maxwell identity -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace ProjectAInos.Electrodynamics
open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-- A = -φ dt + a · dx, with time first. -/
def potentialOf (φ : Spacetime → ℝ) (a : Spacetime → Fin 3 → ℝ) : Potential :=
  fun x => oneCovector.symm (-φ x • (ContinuousLinearMap.proj 0) +
    ∑ i : Fin 3, a x i • (ContinuousLinearMap.proj i.succ))

theorem potentialOf_apply (φ : Spacetime → ℝ) (a : Spacetime → Fin 3 → ℝ)
    (x v : Spacetime) :
    oneCovector (potentialOf φ a x) v = -φ x * v 0 + ∑ i : Fin 3, a x i * v i.succ := by
  simp [potentialOf]

def potentialComponent (A : Potential) (ν : Fin 4) (x : Spacetime) : ℝ :=
  oneCovector (A x) (Pi.single ν 1)

theorem fderiv_potentialComponent {A : Potential} {x : Spacetime}
    (hA : DifferentiableAt ℝ A x) (ν : Fin 4) (v : Spacetime) :
    fderiv ℝ (potentialComponent A ν) x v = oneCovector (fderiv ℝ A x v) (Pi.single ν 1) := by
  let ev : OneForm →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single ν 1)).comp oneCovector.toContinuousLinearMap
  have hd : HasFDerivAt (potentialComponent A ν) (ev.comp (fderiv ℝ A x)) x :=
    ev.hasFDerivAt.comp x hA.hasFDerivAt
  rw [hd.fderiv]
  rfl

theorem fieldTensor_component {A : Potential} {x : Spacetime}
    (hA : DifferentiableAt ℝ A x) (μ ν : Fin 4) :
    component (fieldTensor A x) μ ν =
      fderiv ℝ (potentialComponent A ν) x (Pi.single μ 1) -
        fderiv ℝ (potentialComponent A μ) x (Pi.single ν 1) := by
  rw [fderiv_potentialComponent hA, fderiv_potentialComponent hA]
  exact fieldTensor_apply A x _ _

/-- Bianchi in arbitrary constant directions, hence also on coordinate axes. -/
theorem bianchi_components (A : Potential) {U : Set Spacetime} (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) {x : Spacetime} (hx : x ∈ U) (u v w : Spacetime) :
    fderiv ℝ (fieldTensor A) x u ![v, w] + fderiv ℝ (fieldTensor A) x v ![w, u] +
      fderiv ℝ (fieldTensor A) x w ![u, v] = 0 := by
  have h := congrArg (fun F => F ![u, v, w]) (bianchi_on A hU hA hx)
  have h0 : Fin.removeNth (0 : Fin 3) ![u, v, w] = ![v, w] := by
    ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 3) ![u, v, w] = ![u, w] := by
    ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 3) ![u, v, w] = ![u, v] := by
    ext i; fin_cases i <;> rfl
  simp only [exteriorDerivative, extDeriv,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply] at h
  rw [Fin.sum_univ_three, h0, h1, h2] at h
  norm_num at h
  have hs := twoForm_swap (fderiv ℝ (fieldTensor A) x v) u w
  linarith

theorem fieldTensor_lorentz (L : LorentzGroup 3) (A : Potential) (hA : Differentiable ℝ A) :
    fieldTensor (pullback L.val A) = pullback L.val (fieldTensor A) :=
  fieldTensor_pullback L.val A (LorentzGroup.toContinuousLinearEquiv L).contDiff hA

theorem fieldTensor_poincare (P : PoincareGroup 3) (A : Potential) (hA : Differentiable ℝ A) :
    fieldTensor (pullback P.val A) = pullback P.val (fieldTensor A) :=
  fieldTensor_pullback P.val A (PoincareGroup.contDiff P |>.of_le (by norm_num)) hA

end ProjectAInos.Electrodynamics
