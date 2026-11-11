module
public import ProjectAInos.Electrodynamics.PolynomialBridge

/-! # Nonzero degree-zero and degree-one Maxwell jets -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ProjectAInos.Electrodynamics.Polynomial
open YM YM.Tensor YM.Analysis YM.Maxwell
open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

def planeCoefficient (i k : Axis) : ℝ :=
  (if i = 3 then 1 else 0) * (if k = 1 then 1 else 0) -
    (if i = 1 then 1 else 0) * (if k = 3 then 1 else 0)

def constantJet : TwoJet ℝ 0 := fun i k =>
  ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E4) (planeCoefficient i k)

theorem constantJet_closed : ClosedJet constantJet := by
  refine ⟨fun _ _ _ _ => rfl, ?_, ?_⟩
  · intro i k
    ext v
    change planeCoefficient i k = -planeCoefficient k i
    unfold planeCoefficient
    ring
  · intro a b c x
    change fderiv ℝ (fun _ : E4 => planeCoefficient b c) x (basis a) +
      fderiv ℝ (fun _ : E4 => planeCoefficient c a) x (basis b) +
      fderiv ℝ (fun _ : E4 => planeCoefficient a b) x (basis c) = 0
    simp

def linearJet : TwoJet ℝ 1 := fun i k =>
  ContinuousMultilinearMap.ofSubsingleton ℝ E4 ℝ (0 : Fin 1)
    (planeCoefficient i k • compAxis 3)

theorem linearJet_diagonal (i k : Axis) :
    diagonal (linearJet i k) = fun x => planeCoefficient i k * x 3 := rfl

theorem linearJet_grad (a i k : Axis) (x : E4) :
    grad a (diagonal (linearJet i k)) x = planeCoefficient i k * (if a = 3 then 1 else 0) := by
  rw [linearJet_diagonal]
  have hd := ((compAxis 3).hasFDerivAt (x := x)).const_mul (planeCoefficient i k)
  unfold grad D
  rw [show (fun x : E4 => planeCoefficient i k * x 3) =
    (fun x : E4 => planeCoefficient i k * compAxis 3 x) from rfl, hd.fderiv]
  simp [compAxis, basis, eq_comm]

theorem linearJet_closed : ClosedJet linearJet := by
  refine ⟨?_, ?_, ?_⟩
  · intro i k v s
    have hs : s (0 : Fin 1) = 0 := Subsingleton.elim _ _
    simp [linearJet, Function.comp_def, hs]
  · intro i k
    ext v
    change planeCoefficient i k * v 0 3 = -(planeCoefficient k i * v 0 3)
    unfold planeCoefficient
    ring
  · intro a b c x
    rw [linearJet_grad, linearJet_grad, linearJet_grad]
    unfold planeCoefficient
    ring

theorem constantJet_reconstruction (x : Spacetime) :
    component (fieldTensor (potential constantJet) x) 0 1 = 1 := by
  rw [fieldTensor_potential constantJet_closed]
  norm_num [coefficient, constantJet, diagonal, planeCoefficient, axisSwap, Equiv.swap_apply_def]

theorem linearJet_reconstruction (x : Spacetime) :
    component (fieldTensor (potential linearJet) x) 0 1 = x 0 := by
  rw [fieldTensor_potential linearJet_closed]
  norm_num [coefficient, linearJet_diagonal, planeCoefficient, axisSwap, Equiv.swap_apply_def]

theorem constantJet_potential_coefficient (x : Spacetime) :
    potentialComponent (potential constantJet) 1 x = (1 / 2 : ℝ) * x 0 := by
  rw [radial_formula]
  norm_num [coefficient, constantJet, diagonal, planeCoefficient, axisSwap, Equiv.swap_apply_def, Fin.sum_univ_succ]

theorem linearJet_potential_coefficient (x : Spacetime) :
    potentialComponent (potential linearJet) 1 x = (1 / 3 : ℝ) * x 0 ^ 2 := by
  rw [radial_formula]
  norm_num [coefficient, linearJet_diagonal, planeCoefficient, axisSwap, Equiv.swap_apply_def, Fin.sum_univ_succ]
  ring

theorem constantJet_nonzero : constantJet ≠ 0 := by
  intro h
  have hz := congrArg (fun Q => diagonal (Q 3 1) (0 : E4)) h
  norm_num [constantJet, planeCoefficient, diagonal] at hz

theorem linearJet_nonzero : linearJet ≠ 0 := by
  intro h
  have hz := congrArg (fun Q => diagonal (Q 3 1) (basis 3)) h
  norm_num [linearJet_diagonal, planeCoefficient, diagonal, linearJet, basis] at hz

end ProjectAInos.Electrodynamics.Polynomial
