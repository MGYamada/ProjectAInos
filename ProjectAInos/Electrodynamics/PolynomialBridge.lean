module
public import ProjectAInos.Electrodynamics.PolynomialRadial
public import ProjectAInos.Electrodynamics.Components

/-! # Time-first scalar Maxwell jets

This adapter transports ordinary homogeneous polynomial forms through an
explicit continuous linear coordinate equivalence. Upstream time is at axis
3. The swap (0 3) sends (t,x,y,z) to (z,x,y,t); no metric is transported here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace ProjectAInos.Electrodynamics.Polynomial
open YM YM.Tensor YM.Analysis YM.Maxwell
open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

def axisSwap : Equiv.Perm (Fin 4) := Equiv.swap 0 3

def coordinatesLinear : Spacetime ≃ₗ[ℝ] E4 where
  toFun x := WithLp.toLp 2 (x ∘ axisSwap)
  invFun x := x.ofLp ∘ axisSwap
  left_inv x := by ext i; simp [axisSwap]
  right_inv x := by ext i; simp [axisSwap]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinates : Spacetime ≃L[ℝ] E4 := coordinatesLinear.toContinuousLinearEquiv

@[simp] theorem coordinates_apply (x : Spacetime) (i : Axis) :
    coordinates x i = x (axisSwap i) := rfl

@[simp] theorem coordinates_time (x : Spacetime) : coordinates x 3 = x 0 := by
  simp [axisSwap]

theorem coordinates_basis (i : Fin 4) : coordinates (Pi.single i 1) = basis (axisSwap i) := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [coordinates_apply, Pi.single_apply, basis, axisSwap, Equiv.swap_apply_def]

variable {j : ℕ}

def coefficient (Q : TwoJet ℝ j) (μ ν : Fin 4) (x : Spacetime) : ℝ :=
  diagonal (Q (axisSwap μ) (axisSwap ν)) (coordinates x)

def potential (Q : TwoJet ℝ j) : Potential := fun x =>
  oneCovector.symm (∑ ν : Fin 4, radial Q (axisSwap ν) (coordinates x) • ContinuousLinearMap.proj ν)

theorem potential_component (Q : TwoJet ℝ j) (ν : Fin 4) :
    potentialComponent (potential Q) ν = fun x => radial Q (axisSwap ν) (coordinates x) := by
  funext x
  simp [potentialComponent, potential, Pi.single_apply]

theorem potential_smooth (Q : TwoJet ℝ j) (n : ℕ∞ω) : ContDiff ℝ n (potential Q) := by
  apply oneCovector.symm.contDiff.comp
  exact ContDiff.sum fun ν _ => ((radial_smooth Q (axisSwap ν) n).comp coordinates.contDiff).smul contDiff_const

theorem grad_transport (f : E4 → ℝ) (hf : Differentiable ℝ f) (x : Spacetime) (μ : Fin 4) :
    fderiv ℝ (fun x => f (coordinates x)) x (Pi.single μ 1) =
      grad (axisSwap μ) f (coordinates x) := by
  have hd := ((hf (coordinates x)).hasFDerivAt.comp x coordinates.toContinuousLinearMap.hasFDerivAt).fderiv
  rw [show (fun x => f (coordinates x)) = f ∘ coordinates from rfl, hd]
  change fderiv ℝ f (coordinates x) (coordinates (Pi.single μ 1)) = _
  rw [coordinates_basis]
  rfl

/-- Evaluation and exterior differentiation agree with upstream radial recovery. -/
theorem fieldTensor_potential {Q : TwoJet ℝ j} (h : ClosedJet Q)
    (x : Spacetime) (μ ν : Fin 4) :
    component (fieldTensor (potential Q) x) μ ν = coefficient Q μ ν x := by
  rw [fieldTensor_component ((potential_smooth Q 1).differentiable one_ne_zero x),
    potential_component, potential_component,
    grad_transport _ ((radial_smooth Q _ 1).differentiable one_ne_zero),
    grad_transport _ ((radial_smooth Q _ 1).differentiable one_ne_zero)]
  exact radial_curl h _ _ _

theorem radial_formula (Q : TwoJet ℝ j) (ν : Fin 4) (x : Spacetime) :
    potentialComponent (potential Q) ν x =
      (↑(j + 2 : ℕ) : ℝ)⁻¹ * ∑ μ : Fin 4, x μ * coefficient Q μ ν x := by
  rw [potential_component]
  unfold radial coefficient
  simp only [smul_eq_mul]
  congr 1
  rw [← Equiv.sum_comp axisSwap]
  simp [coordinates_apply, axisSwap]

end ProjectAInos.Electrodynamics.Polynomial
