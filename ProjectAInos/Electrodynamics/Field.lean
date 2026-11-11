/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
-/
module
public import ProjectAInos.SpecialRelativity.Spacetime
public import ProjectAInos.SmoothGeometry.Minkowski.TwoForm
public import ProjectAInos.SmoothGeometry.Minkowski.HodgeNaturality

/-! # Local electromagnetic potentials and curvature

Time comes first, c = 1, and the physical signature is (-+++). A potential
only describes an exact curvature on its stated open domain. No global
potential, field equation with sources, or nontrivial bundle is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace ProjectAInos.Electrodynamics
open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

abbrev Potential := Form Spacetime 1
abbrev Field := Form Spacetime 2
abbrev OneForm := Spacetime [⋀^Fin 1]→L[ℝ] ℝ

def fieldTensor (A : Potential) : Field := exteriorDerivative A
def scalarForm (χ : Spacetime → ℝ) : Form Spacetime 0 :=
  fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ Spacetime (Fin 0) (χ x)
def gaugeShift (A : Potential) (χ : Spacetime → ℝ) : Potential :=
  A + exteriorDerivative (scalarForm χ)

def oneCovector : OneForm ≃L[ℝ] FourCovector :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Spacetime) (F := ℝ)
    (0 : Fin 1)).symm.toContinuousLinearEquiv

@[simp] theorem oneCovector_apply (a : OneForm) (v : Spacetime) :
    oneCovector a v = a (fun _ => v) := rfl

@[simp] theorem oneCovector_curryLeft (F : TwoForm) (v w : Spacetime) :
    oneCovector (F.curryLeft v) w = F ![v, w] := by
  rw [oneCovector_apply, ContinuousAlternatingMap.curryLeft_apply_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The curvature is the antisymmetrized differential of the potential. -/
theorem fieldTensor_apply (A : Potential) (x v w : Spacetime) :
    fieldTensor A x ![v, w] =
      oneCovector (fderiv ℝ A x v) w - oneCovector (fderiv ℝ A x w) v := by
  have h0 : Fin.removeNth (0 : Fin 2) ![v, w] = (fun _ : Fin 1 => w) := by
    ext i; fin_cases i; rfl
  have h1 : Fin.removeNth (1 : Fin 2) ![v, w] = (fun _ : Fin 1 => v) := by
    ext i; fin_cases i; rfl
  simp only [fieldTensor, exteriorDerivative, extDeriv,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  rw [Fin.sum_univ_two, h0, h1]
  simp [oneCovector_apply, sub_eq_add_neg]

theorem scalarForm_contDiff {n : ℕ∞ω} {χ : Spacetime → ℝ} (hχ : ContDiff ℝ n χ) :
    ContDiff ℝ n (scalarForm χ) :=
  (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ Spacetime ℝ (Fin 0)).contDiff.comp hχ

theorem scalarForm_contDiffAt {n : ℕ∞ω} {χ : Spacetime → ℝ} {x : Spacetime}
    (hχ : ContDiffAt ℝ n χ x) : ContDiffAt ℝ n (scalarForm χ) x :=
  (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ Spacetime ℝ (Fin 0)).contDiff.contDiffAt.comp x hχ

@[simp] theorem scalar_derivative (χ : Spacetime → ℝ) (x : Spacetime) :
    oneCovector (exteriorDerivative (scalarForm χ) x) = fderiv ℝ χ x := by
  change oneCovector (extDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty
    ℝ Spacetime (Fin 0) (χ y)) x) = _
  rw [extDeriv_constOfIsEmpty]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Spacetime) (F := ℝ)
    (0 : Fin 1)).symm_apply_apply _

theorem fieldTensor_gauge (A : Potential) (χ : Spacetime → ℝ)
    (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) :
    fieldTensor (gaugeShift A χ) = fieldTensor A :=
  gauge_exteriorDerivative A (scalarForm χ) hA (scalarForm_contDiff hχ)

theorem fieldTensor_gauge_on (A : Potential) (χ : Spacetime → ℝ)
    {U : Set Spacetime} (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U)
    (hχ : ContDiffOn ℝ 2 χ U) : Set.EqOn (fieldTensor (gaugeShift A χ)) (fieldTensor A) U := by
  intro x hx
  have hAx := ((hA x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hχx := scalarForm_contDiffAt ((hχ x hx).contDiffAt (hU.mem_nhds hx))
  have hd : DifferentiableAt ℝ (extDeriv (scalarForm χ)) x :=
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Spacetime ℝ).differentiableAt.comp x
      ((hχx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  change extDeriv (A + extDeriv (scalarForm χ)) x = extDeriv A x
  rw [extDeriv_add hAx hd, extDeriv_extDeriv_apply hχx (by norm_num), add_zero]

/-- The homogeneous Bianchi identity on the actual domain of a C² potential. -/
theorem bianchi_on (A : Potential) {U : Set Spacetime} (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) : Set.EqOn (exteriorDerivative (fieldTensor A)) 0 U :=
  exteriorDerivative_squared_on A hU hA

theorem fieldTensor_pullback (f : Spacetime → Spacetime) (A : Potential)
    (hf : ContDiff ℝ 2 f) (hA : Differentiable ℝ A) :
    fieldTensor (pullback f A) = pullback f (fieldTensor A) :=
  exteriorDerivative_pullback f A hf hA

theorem fieldTensor_pullback_on (f : Spacetime → Spacetime) (A : Potential)
    {U : Set Spacetime} (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x)
    (hA : ∀ x ∈ U, DifferentiableAt ℝ A (f x)) :
    Set.EqOn (fieldTensor (pullback f A)) (pullback f (fieldTensor A)) U :=
  exteriorDerivative_pullback_on f A hf hA

def star : TwoForm ≃L[ℝ] TwoForm := hodgeFiber .timeNegative .standard (by decide)
def electric (u : Observer 3) (F : TwoForm) : OneForm := -(F.curryLeft u.velocity)
def magnetic (u : Observer 3) (F : TwoForm) : OneForm := (star F).curryLeft u.velocity

theorem observer_reconstruction (u : Observer 3) (F : TwoForm) :
    reconstructTwoForm .timeNegative .standard u (-(electric u F)) (magnetic u F) = F := by
  simp only [electric, neg_neg, magnetic, star]
  exact reconstructTwoForm_contractions .timeNegative .standard u F

theorem electric_annihilates_observer (u : Observer 3) (F : TwoForm) :
    oneCovector (electric u F) u.velocity = 0 := by
  have hz : oneCovector (F.curryLeft u.velocity) u.velocity = 0 := by
    rw [oneCovector_apply, ContinuousAlternatingMap.curryLeft_apply_apply]
    have he : Matrix.vecCons u.velocity (fun _ : Fin 1 => u.velocity) =
        ![u.velocity, u.velocity] := by ext i; fin_cases i <;> rfl
    rw [he]
    have h := twoForm_swap F u.velocity u.velocity
    linarith
  simpa [electric] using congrArg Neg.neg hz

theorem magnetic_annihilates_observer (u : Observer 3) (F : TwoForm) :
    oneCovector (magnetic u F) u.velocity = 0 := by
  change star F ![u.velocity, u.velocity] = 0
  have h := twoForm_swap (star F) u.velocity u.velocity
  linarith

end ProjectAInos.Electrodynamics
