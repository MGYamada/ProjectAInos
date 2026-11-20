/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.SourceCovariance
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The field of a uniformly moving charge

A static solution is carried by the boost along the first axis to the solution of a charge in
uniform motion with the velocity `V` (Landau–Lifshitz, *The Classical Theory of Fields*, §38;
units with `c = 1` and `div E = ρ`). Time comes first and the four-potential is `A = −φ dt`.

* `StaticSolution`: a static solution on an open set of space, a `C²` potential `φ` with
  `−Δφ = ρ`. `StaticSolution.excitation`: its potential `staticScalar φ = −φ dt` solves
  `dH = −ι_k vol` with the static current `k = ρ ∂_t` over the domain.
* `movingScalar`: the pullback of `−φ dt` by the boost `t′ = γ (t − V x)`, `x′ = γ (x − V t)`
  to the rest frame (`restFrame`, proper and orthochronous by `boostProperOrthochronous`).
  `movingScalar_apply`: it is `−γ φ′ (dt − V dx)` with `φ′` at the comoving position.
* `excitation_movingScalar`, `maxwell_movingScalar`: the equations of Maxwell with the current
  `γ ρ (1, V, 0, 0)` at the comoving position (`movingCurrent`), by `excitation_pullback`.
* `electricField_movingScalar`: `E = (E′₁, γ E′₂, γ E′₃)` with the static field `E′ = −∇φ` at the
  comoving position; `magneticField_movingScalar`: `B = V × E`.
* `coulombSolution`: the point charge `q / 4π|x|`, a static solution on the complement of the
  origin, harmonic there (`spaceLaplacian_coulombPotential`). `uniformSolution`: the smooth
  static solution of a uniform density.
* `movingCoulomb_field`: off the world line `x = V t e₁` the boosted Coulomb potential solves the
  equation of the vacuum, its electric field is Landau–Lifshitz (38.8),
  `E = q (1 − V²) R / (4π R³ (1 − V² sin² θ)^{3/2})` with the vector `R` from the present position
  of the charge (`presentSeparation`) and the angle `θ` between `R` and the axis of the motion,
  and its magnetic field is `B = V × E`.
-/

@[expose] public section

noncomputable section

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.MovingCharge

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-! ### Static solutions -/

/-- The derivative `∂ᵢf` of a function on space along the axis `i`. -/
def spatialPartial (f : Space 3 → ℝ) (i : Fin 3) (p : Space 3) : ℝ :=
  fderiv ℝ f p (EuclideanSpace.single i 1)

/-- The Laplacian `Δf = Σᵢ ∂ᵢ∂ᵢf` of a function on space. -/
def spaceLaplacian (f : Space 3 → ℝ) (p : Space 3) : ℝ :=
  ∑ i : Fin 3, spatialPartial (spatialPartial f i) i p

/-- A static solution of the equations of the field: on an open set of space the scalar
potential `φ` is `C²` and solves the equation of Poisson `−Δφ = ρ` with the density `ρ`. -/
structure StaticSolution where
  /-- The open set of space on which the equation holds. -/
  domain : Set (Space 3)
  /-- The domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The scalar potential `φ`. -/
  potential : Space 3 → ℝ
  /-- The density of the charge `ρ`. -/
  density : Space 3 → ℝ
  /-- The potential is `C²` on the domain. -/
  contDiffOn_potential : ContDiffOn ℝ 2 potential domain
  /-- The equation of Poisson `−Δφ = ρ` on the domain. -/
  poisson : ∀ p ∈ domain, -spaceLaplacian potential p = density p

/-- The four-potential `A = −φ dt` of a scalar potential `φ` on space, that is `A^μ = (φ, 0)`. -/
def staticScalar (φ : Space 3 → ℝ) : Potential :=
  fun x => (-φ (space x)) • oneCovector.symm (ContinuousLinearMap.proj 0)

/-- The static electric field `E = −∇φ`. -/
def staticElectric (φ : Space 3 → ℝ) (p : Space 3) : Fin 3 → ℝ :=
  fun i => -spatialPartial φ i p

/-- The static current `ρ ∂_t`, with the density `k⁰ = ρ` and no current density. -/
def staticCurrent (ρ : Space 3 → ℝ) : Spacetime → Spacetime :=
  fun x => ρ (space x) • Pi.single 0 1

/-- The axis of the time has no part in space. -/
theorem space_single_zero : space (Pi.single 0 1 : Spacetime) = 0 := by
  ext j
  simp [space_apply, Fin.succ_ne_zero]

/-- The part in space of the axis `i + 1` of space-time is the axis `i` of space. -/
theorem space_single_succ (i : Fin 3) :
    space (Pi.single i.succ 1 : Spacetime) = EuclideanSpace.single i 1 := by
  ext j
  simp [space_apply, Pi.single_apply, PiLp.single_apply, Fin.succ_inj, eq_comm]

/-- The derivative of `−φ dt` at an event over a point where `φ` is differentiable. -/
theorem hasFDerivAt_staticScalar {φ : Space 3 → ℝ} {x : Spacetime}
    (hφ : DifferentiableAt ℝ φ (space x)) :
    HasFDerivAt (staticScalar φ)
      ((-(fderiv ℝ φ (space x)).comp (space : Spacetime →L[ℝ] Space 3)).smulRight
        (oneCovector.symm (ContinuousLinearMap.proj 0))) x :=
  ((hφ.hasFDerivAt.comp x space.hasFDerivAt).neg).smul_const
    (oneCovector.symm (ContinuousLinearMap.proj 0))

/-- The field of `−φ dt`: `F(v, w) = ∇φ · w⃗ v⁰ − ∇φ · v⃗ w⁰`. -/
theorem fieldTensor_staticScalar_apply {φ : Space 3 → ℝ} {x : Spacetime}
    (hφ : DifferentiableAt ℝ φ (space x)) (v w : Spacetime) :
    fieldTensor (staticScalar φ) x ![v, w] =
      fderiv ℝ φ (space x) (space w) * v 0 - fderiv ℝ φ (space x) (space v) * w 0 := by
  rw [fieldTensor_apply, (hasFDerivAt_staticScalar hφ).fderiv]
  simp
  ring

/-- The electric field of `−φ dt` is `−∇φ`. -/
theorem electricVector_staticScalar {φ : Space 3 → ℝ} {x : Spacetime}
    (hφ : DifferentiableAt ℝ φ (space x)) :
    electricVector (fieldTensor (staticScalar φ) x) = staticElectric φ (space x) := by
  funext i
  rw [electricVector_apply, component, fieldTensor_staticScalar_apply hφ, space_single_zero,
    space_single_succ]
  simp [staticElectric, spatialPartial, Fin.succ_ne_zero]

/-- The field of `−φ dt` has no magnetic part. -/
theorem magneticVector_staticScalar {φ : Space 3 → ℝ} {x : Spacetime}
    (hφ : DifferentiableAt ℝ φ (space x)) :
    magneticVector (fieldTensor (staticScalar φ) x) = 0 := by
  funext i
  fin_cases i <;>
    simp [magneticVector, component, fieldTensor_staticScalar_apply hφ]

/-- A function on space composed with the projection to space has the composed derivative. -/
theorem hasFDerivAt_comp_space {g : Space 3 → ℝ} {x : Spacetime}
    (hg : DifferentiableAt ℝ g (space x)) :
    HasFDerivAt (fun y => g (space y))
      ((fderiv ℝ g (space x)).comp (space : Spacetime →L[ℝ] Space 3)) x :=
  hg.hasFDerivAt.comp x space.hasFDerivAt

/-- The derivative of a `C²` function on an open set is differentiable there. -/
theorem differentiableAt_spatialPartial {f : Space 3 → ℝ} {D : Set (Space 3)} (hD : IsOpen D)
    (hf : ContDiffOn ℝ 2 f D) {p : Space 3} (hp : p ∈ D) (i : Fin 3) :
    DifferentiableAt ℝ (spatialPartial f i) p := by
  have hfp := (hf p hp).contDiffAt (hD.mem_nhds hp)
  exact ((hfp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const _)

/-- The potential `−φ dt` is `C²` where `φ` is. -/
theorem contDiffOn_staticScalar {φ : Space 3 → ℝ} {D : Set (Space 3)} (hφ : ContDiffOn ℝ 2 φ D) :
    ContDiffOn ℝ 2 (staticScalar φ) (space ⁻¹' D) :=
  ((hφ.comp space.contDiff.contDiffOn (fun _ hy => hy)).neg).smul contDiffOn_const

namespace StaticSolution

variable (S : StaticSolution)

/-- The set of space-time over the domain of a static solution. -/
def spacetimeDomain : Set Spacetime := space ⁻¹' S.domain

/-- The set of space-time over the domain is open. -/
theorem isOpen_spacetimeDomain : IsOpen S.spacetimeDomain :=
  S.isOpen_domain.preimage space.continuous

/-- The potential of a static solution is differentiable on the domain. -/
theorem differentiableAt_potential {p : Space 3} (hp : p ∈ S.domain) :
    DifferentiableAt ℝ S.potential p :=
  ((S.contDiffOn_potential p hp).contDiffAt (S.isOpen_domain.mem_nhds hp)).differentiableAt
    (by norm_num)

/-- Near an event over the domain the electric field is `−∇φ`. -/
theorem electricField_eventually {x : Spacetime} (hx : space x ∈ S.domain) (i : Fin 3) :
    electricField (fieldTensor (staticScalar S.potential)) i =ᶠ[𝓝 x]
      fun y => -spatialPartial S.potential i (space y) := by
  filter_upwards [S.isOpen_spacetimeDomain.mem_nhds hx] with y hy
  exact congrFun (electricVector_staticScalar (S.differentiableAt_potential hy)) i

/-- Near an event over the domain the magnetic field vanishes. -/
theorem magneticField_eventually {x : Spacetime} (hx : space x ∈ S.domain) (i : Fin 3) :
    magneticField (fieldTensor (staticScalar S.potential)) i =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [S.isOpen_spacetimeDomain.mem_nhds hx] with y hy
  exact congrFun (magneticVector_staticScalar (S.differentiableAt_potential hy)) i

/-- The derivatives `∂_μ Eᵢ = −∂_μ ∂ᵢ φ` of the electric field of a static solution. -/
theorem partialAt_electricField {x : Spacetime} (hx : space x ∈ S.domain) (i : Fin 3)
    (μ : Fin 4) :
    partialAt (electricField (fieldTensor (staticScalar S.potential)) i) μ x =
      -fderiv ℝ (spatialPartial S.potential i) (space x) (space (Pi.single μ 1)) := by
  have hd := differentiableAt_spatialPartial S.isOpen_domain S.contDiffOn_potential hx i
  rw [partialAt, (S.electricField_eventually hx i).fderiv_eq, fderiv_fun_neg,
    (hasFDerivAt_comp_space hd).fderiv]
  rfl

/-- The derivatives of the magnetic field of a static solution vanish. -/
theorem partialAt_magneticField {x : Spacetime} (hx : space x ∈ S.domain) (i : Fin 3)
    (μ : Fin 4) :
    partialAt (magneticField (fieldTensor (staticScalar S.potential)) i) μ x = 0 := by
  rw [partialAt, (S.magneticField_eventually hx i).fderiv_eq, fderiv_const_apply]
  rfl

/-- A static solution solves the equation `dH = −ι_k vol` of the excitation with the static
current `ρ ∂_t` over its domain. -/
theorem excitation {x : Spacetime} (hx : space x ∈ S.domain) :
    exteriorDerivative (fun y => -star (fieldTensor (staticScalar S.potential) y)) x =
      SourcedAction.matterCurrentForm (staticCurrent S.density) x := by
  have hF := differentiableAt_fieldTensor S.isOpen_spacetimeDomain
    (contDiffOn_staticScalar S.contDiffOn_potential) hx
  apply excitation_of_inhomogeneous hF
  · have hp := S.poisson _ hx
    simp only [divergence3, Fin.sum_univ_three, S.partialAt_electricField hx,
      space_single_succ] at hp ⊢
    simp only [spaceLaplacian, spatialPartial, Fin.sum_univ_three] at hp
    simp only [staticCurrent, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    linarith
  · intro i
    fin_cases i <;>
      simp [curl, S.partialAt_magneticField hx, S.partialAt_electricField hx, space_single_zero,
        staticCurrent]

end StaticSolution

/-! ### The boosted static solution -/

section Moving

variable (V : ℝ) (hV : |V| < 1)

/-- The boost `t′ = γ (t − V x)`, `x′ = γ (x − V t)` to the frame in which the charge is at rest,
as a proper Lorentz map. -/
def restFrame : properLorentzGroup 3 :=
  ⟨boost (axisVelocity V hV), (boostProperOrthochronous (axisVelocity V hV)).property.1⟩

/-- The position `(γ (x − V t), y, z)` of an event in the frame in which the charge is at
rest. -/
def comovingPosition (y : Spacetime) : Space 3 := space ((boost (axisVelocity V hV)).val y)

/-- The first component `γ (x − V t)` of the comoving position. -/
theorem comovingPosition_zero (y : Spacetime) :
    comovingPosition V hV y 0 = (axisVelocity V hV).gamma * (y 1 - V * y 0) := by
  rw [comovingPosition, space_apply, boost_axisVelocity_apply]
  rfl

/-- The second component `y` of the comoving position. -/
theorem comovingPosition_one (y : Spacetime) : comovingPosition V hV y 1 = y 2 := by
  rw [comovingPosition, space_apply, boost_axisVelocity_apply]
  rfl

/-- The third component `z` of the comoving position. -/
theorem comovingPosition_two (y : Spacetime) : comovingPosition V hV y 2 = y 3 := by
  rw [comovingPosition, space_apply, boost_axisVelocity_apply]
  rfl

/-- The potential of the static scalar potential `φ` carried by the charge moving with the
velocity `V` along the first axis: the pullback of `−φ dt` by the boost to the rest frame. -/
def movingScalar (φ : Space 3 → ℝ) : Potential :=
  pullback (boost (axisVelocity V hV)).val (staticScalar φ)

/-- The boosted potential is `A = −γ φ′ (dt − V dx)`, with `φ′` at the comoving position: the
scalar potential `γ φ′` and the vector potential `γ V φ′ e₁`. -/
theorem movingScalar_apply (φ : Space 3 → ℝ) (y v : Spacetime) :
    oneCovector (movingScalar V hV φ y) v =
      -((axisVelocity V hV).gamma * φ (comovingPosition V hV y)) * (v 0 - V * v 1) := by
  simp only [movingScalar, pullback, fderiv_lorentz]
  change oneCovector (staticScalar φ ((boost (axisVelocity V hV)).val y))
    ((boost (axisVelocity V hV)).val v) = _
  rw [staticScalar, map_smul, ContinuousLinearEquiv.apply_symm_apply,
    boost_axisVelocity_apply V hV v]
  simp only [comovingPosition, ContinuousLinearMap.proj_apply, smul_apply, Matrix.cons_val_zero,
    smul_eq_mul]
  ring

/-- The current `γ ρ (1, V, 0, 0)` of the moving charge, with the density `ρ` at the comoving
position. -/
def movingCurrent (ρ : Space 3 → ℝ) (y : Spacetime) : Spacetime :=
  ((axisVelocity V hV).gamma * ρ (comovingPosition V hV y)) • ![1, V, 0, 0]

/-- The inverse boost maps the axis of the time to the four-velocity `γ (1, V, 0, 0)`. -/
theorem boost_symm_single_zero :
    (boost (axisVelocity V hV)).val.symm (Pi.single 0 1) =
      ![(axisVelocity V hV).gamma, (axisVelocity V hV).gamma * V, 0, 0] := by
  have h : (boost (axisVelocity V hV)).val.symm (Pi.single 0 1) =
      (boost (axisVelocity V hV).neg).val (Pi.single 0 1) := by
    rw [boost_neg_inverse]
    rfl
  rw [h, axisVelocity_neg, boost_axisVelocity_single_zero, gamma_axisVelocity_neg V hV]
  simp

/-- The static current transported by the boost is the current of the moving charge. -/
theorem transport_staticCurrent (ρ : Space 3 → ℝ) :
    (fun y => (restFrame V hV).val.val.symm (staticCurrent ρ ((restFrame V hV).val.val y))) =
      movingCurrent V hV ρ := by
  funext y
  change (boost (axisVelocity V hV)).val.symm
      (ρ (comovingPosition V hV y) • Pi.single 0 1) = _
  rw [map_smul, boost_symm_single_zero, movingCurrent]
  ext μ
  fin_cases μ <;> simp [mul_comm, mul_left_comm]

/-- The boosted static solution solves the equation `dH = −ι_k vol` of the excitation with the
current `γ ρ (1, V, 0, 0)` at every event whose comoving position is in the domain. -/
theorem excitation_movingScalar (S : StaticSolution) {y : Spacetime}
    (hy : comovingPosition V hV y ∈ S.domain) :
    exteriorDerivative (fun z => -star (fieldTensor (movingScalar V hV S.potential) z)) y =
      SourcedAction.matterCurrentForm (movingCurrent V hV S.density) y := by
  have h := excitation_pullback (restFrame V hV) S.isOpen_spacetimeDomain
    (contDiffOn_staticScalar S.contDiffOn_potential) (fun x hx => S.excitation hx) y hy
  rwa [transport_staticCurrent] at h

/-- The boosted potential is `C²` over the domain. -/
theorem contDiffOn_movingScalar (S : StaticSolution) :
    ContDiffOn ℝ 2 (movingScalar V hV S.potential)
      {y | comovingPosition V hV y ∈ S.domain} :=
  contDiffOn_pullback_lorentz (boost (axisVelocity V hV))
    (contDiffOn_staticScalar S.contDiffOn_potential)

/-- The set of the events whose comoving position is in the domain is open. -/
theorem isOpen_comovingDomain (S : StaticSolution) :
    IsOpen {y | comovingPosition V hV y ∈ S.domain} :=
  S.isOpen_spacetimeDomain.preimage
    (LorentzGroup.toContinuousLinearEquiv (boost (axisVelocity V hV))).continuous

/-- The equations of Maxwell for the boosted static solution in the frame of the co-ordinates:
`div B = 0`, `∂_t B + curl E = 0`, `div E = γ ρ` and `curl B − ∂_t E = γ ρ V e₁`, with the
density `ρ` at the comoving position. -/
theorem maxwell_movingScalar (S : StaticSolution) {y : Spacetime}
    (hy : comovingPosition V hV y ∈ S.domain) :
    (divergence3 (magneticField (fieldTensor (movingScalar V hV S.potential))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (movingScalar V hV S.potential)) i) 0 y +
        curl (electricField (fieldTensor (movingScalar V hV S.potential))) y i = 0) ∧
    divergence3 (electricField (fieldTensor (movingScalar V hV S.potential))) y =
      (axisVelocity V hV).gamma * S.density (comovingPosition V hV y) ∧
    ∀ i, curl (magneticField (fieldTensor (movingScalar V hV S.potential))) y i -
        partialAt (electricField (fieldTensor (movingScalar V hV S.potential)) i) 0 y =
      (axisVelocity V hV).gamma * S.density (comovingPosition V hV y) * ![V, 0, 0] i := by
  have hF := differentiableAt_fieldTensor (isOpen_comovingDomain V hV S)
    (contDiffOn_movingScalar V hV S) hy
  obtain ⟨hdiv, hcurl⟩ := inhomogeneous_of_excitation hF (excitation_movingScalar V hV S hy)
  refine ⟨homogeneous_fieldTensor (isOpen_comovingDomain V hV S)
    (contDiffOn_movingScalar V hV S) hy, ?_, fun i => ?_⟩
  · rw [hdiv]
    simp [movingCurrent]
  · rw [hcurl i]
    fin_cases i <;> simp [movingCurrent]

/-- The field of the boosted potential is the pullback by the boost of the static field at the
boosted event. -/
theorem fieldTensor_movingScalar {φ : Space 3 → ℝ} {y : Spacetime}
    (hφ : DifferentiableAt ℝ φ (comovingPosition V hV y)) :
    fieldTensor (movingScalar V hV φ) y =
      lorentzPullback (boost (axisVelocity V hV))
        (fieldTensor (staticScalar φ) ((boost (axisVelocity V hV)).val y)) := by
  have hA : DifferentiableAt ℝ (staticScalar φ) ((boost (axisVelocity V hV)).val y) :=
    (hasFDerivAt_staticScalar hφ).differentiableAt
  have hL : ContDiff ℝ 2 (boost (axisVelocity V hV)).val :=
    (LorentzGroup.toContinuousLinearEquiv (boost (axisVelocity V hV))).contDiff
  rw [movingScalar, fieldTensor_pullback_on (boost (axisVelocity V hV)).val (staticScalar φ)
    (U := {y}) (fun _ _ => hL.contDiffAt) (fun _ hz => hz ▸ hA) rfl]
  simp only [pullback, fderiv_lorentz]
  rfl

/-- The electric field of the moving charge, `(E′₁, γ E′₂, γ E′₃)` with the static field
`E′ = −∇φ` at the comoving position. -/
theorem electricField_movingScalar {φ : Space 3 → ℝ} {y : Spacetime}
    (hφ : DifferentiableAt ℝ φ (comovingPosition V hV y)) :
    electricVector (fieldTensor (movingScalar V hV φ) y) =
      ![staticElectric φ (comovingPosition V hV y) 0,
        (axisVelocity V hV).gamma * staticElectric φ (comovingPosition V hV y) 1,
        (axisVelocity V hV).gamma * staticElectric φ (comovingPosition V hV y) 2] := by
  rw [fieldTensor_movingScalar V hV hφ, electricVector_boost,
    electricVector_staticScalar hφ, magneticVector_staticScalar hφ]
  simp [comovingPosition]

/-- The magnetic field of the moving charge is `B = V × E`. -/
theorem magneticField_movingScalar {φ : Space 3 → ℝ} {y : Spacetime}
    (hφ : DifferentiableAt ℝ φ (comovingPosition V hV y)) :
    magneticVector (fieldTensor (movingScalar V hV φ) y) =
      crossProduct ![V, 0, 0] (electricVector (fieldTensor (movingScalar V hV φ) y)) := by
  rw [electricField_movingScalar V hV hφ, fieldTensor_movingScalar V hV hφ, magneticVector_boost,
    electricVector_staticScalar hφ, magneticVector_staticScalar hφ, cross_apply]
  ext i
  fin_cases i <;> simp [comovingPosition] <;> ring

end Moving

/-! ### The point charge -/

/-- The Coulomb potential `q / 4π|x|` of the point charge `q` at the origin, in the units of the
project, in which `div E = ρ`. -/
def coulombPotential (q : ℝ) (p : Space 3) : ℝ := q / (4 * Real.pi * ‖p‖)

/-- The derivative of the Euclidean norm away from the origin. -/
theorem hasFDerivAt_norm_space {p : Space 3} (hp : p ≠ 0) :
    HasFDerivAt (fun r : Space 3 => ‖r‖) (‖p‖⁻¹ • innerSL ℝ p) p := by
  have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have h := (hasStrictFDerivAt_norm_sq p).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  refine h.congr_fderiv ?_
  ext v
  simp
  field_simp

/-- The gradient of the Coulomb potential, `∇(q / 4π|x|) = −q x / 4π|x|³`. -/
theorem hasFDerivAt_coulombPotential (q : ℝ) {p : Space 3} (hp : p ≠ 0) :
    HasFDerivAt (coulombPotential q)
      ((-(q / (4 * Real.pi)) * (‖p‖ ^ 3)⁻¹) • innerSL ℝ p) p := by
  have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have h : HasFDerivAt (fun r : Space 3 => q / (4 * Real.pi) * ‖r‖⁻¹) _ p :=
    ((hasDerivAt_inv hn).comp_hasFDerivAt p (hasFDerivAt_norm_space hp)).const_mul
      (q / (4 * Real.pi))
  have hfun : coulombPotential q = fun r : Space 3 => q / (4 * Real.pi) * ‖r‖⁻¹ := by
    funext r
    rw [coulombPotential]
    ring
  rw [hfun]
  refine h.congr_fderiv ?_
  ext v
  simp
  field_simp

/-- The derivatives `∂ᵢ (q / 4π|x|) = −q xᵢ / 4π|x|³` away from the origin. -/
theorem spatialPartial_coulombPotential (q : ℝ) {p : Space 3} (hp : p ≠ 0) (i : Fin 3) :
    spatialPartial (coulombPotential q) i p = -(q / (4 * Real.pi)) * (p i * (‖p‖ ^ 3)⁻¹) := by
  rw [spatialPartial, (hasFDerivAt_coulombPotential q hp).fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

/-- The Coulomb potential is harmonic away from the origin. -/
theorem spaceLaplacian_coulombPotential (q : ℝ) {p : Space 3} (hp : p ≠ 0) :
    spaceLaplacian (coulombPotential q) p = 0 := by
  have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have hev (i : Fin 3) : spatialPartial (coulombPotential q) i =ᶠ[𝓝 p]
      fun r => -(q / (4 * Real.pi)) * (r i * (‖r‖ ^ 3)⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hp] with r hr
    exact spatialPartial_coulombPotential q hr i
  have hd (i : Fin 3) : spatialPartial (spatialPartial (coulombPotential q) i) i p =
      -(q / (4 * Real.pi)) * ((‖p‖ ^ 3)⁻¹ - 3 * p i ^ 2 * (‖p‖ ^ 5)⁻¹) := by
    have h1 : HasFDerivAt (fun r : Space 3 => r i) (EuclideanSpace.proj i : Space 3 →L[ℝ] ℝ) p :=
      (EuclideanSpace.proj i : Space 3 →L[ℝ] ℝ).hasFDerivAt
    have h2 := (hasDerivAt_inv (pow_ne_zero 3 hn)).comp_hasFDerivAt p
      ((hasFDerivAt_norm_space hp).pow 3)
    have h : HasFDerivAt (fun r : Space 3 => -(q / (4 * Real.pi)) * (r i * (‖r‖ ^ 3)⁻¹)) _ p :=
      (h1.fun_mul h2).const_mul _
    rw [spatialPartial, (hev i).fderiv_eq, h.fderiv]
    simp [EuclideanSpace.inner_single_right]
    field_simp
    ring
  have hsum : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = ‖p‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  rw [spaceLaplacian, Fin.sum_univ_three, hd, hd, hd]
  field_simp
  linear_combination (3 * q) * hsum

/-- The point charge `q` at the origin is a static solution on the complement of the origin,
with no charge there. -/
def coulombSolution (q : ℝ) : StaticSolution where
  domain := {0}ᶜ
  isOpen_domain := isOpen_compl_singleton
  potential := coulombPotential q
  density := fun _ => 0
  contDiffOn_potential := fun _ hp =>
    (contDiffAt_const.div (contDiffAt_const.mul (contDiffAt_norm ℝ hp))
      (mul_ne_zero (by positivity) (norm_ne_zero_iff.mpr hp))).contDiffWithinAt
  poisson := fun _ hp => by
    rw [spaceLaplacian_coulombPotential q hp, neg_zero]

/-- The potential `−ρ₀ |x|² / 6` of the uniform density `ρ₀`. -/
def uniformPotential (ρ₀ : ℝ) (p : Space 3) : ℝ := -(ρ₀ / 6) * ‖p‖ ^ 2

/-- The derivatives `∂ᵢ (−ρ₀ |x|² / 6) = −ρ₀ xᵢ / 3`. -/
theorem spatialPartial_uniformPotential (ρ₀ : ℝ) (i : Fin 3) :
    spatialPartial (uniformPotential ρ₀) i = fun p => -(ρ₀ / 3) * p i := by
  funext p
  have h : HasFDerivAt (uniformPotential ρ₀) _ p :=
    (hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_mul (-(ρ₀ / 6))
  rw [spatialPartial, h.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

/-- The Laplacian of `−ρ₀ |x|² / 6` is `−ρ₀`. -/
theorem spaceLaplacian_uniformPotential (ρ₀ : ℝ) (p : Space 3) :
    spaceLaplacian (uniformPotential ρ₀) p = -ρ₀ := by
  have h (i : Fin 3) : HasFDerivAt (fun r : Space 3 => -(ρ₀ / 3) * r i) _ p :=
    (EuclideanSpace.proj i : Space 3 →L[ℝ] ℝ).hasFDerivAt.const_mul (-(ρ₀ / 3))
  simp only [spaceLaplacian, spatialPartial_uniformPotential]
  rw [Fin.sum_univ_three, spatialPartial, (h 0).fderiv, spatialPartial, (h 1).fderiv,
    spatialPartial, (h 2).fderiv]
  simp
  ring

/-- A smooth static solution: the uniform density `ρ₀` in all of space with the potential
`−ρ₀ |x|² / 6`. -/
def uniformSolution (ρ₀ : ℝ) : StaticSolution where
  domain := Set.univ
  isOpen_domain := isOpen_univ
  potential := uniformPotential ρ₀
  density := fun _ => ρ₀
  contDiffOn_potential := (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffOn
  poisson := fun p _ => by rw [spaceLaplacian_uniformPotential, neg_neg]

section MovingPointCharge

variable (V : ℝ) (hV : |V| < 1)

/-- The potential of the point charge `q` moving with the velocity `V` along the first axis,
which passes the origin at `t = 0`. -/
def movingCoulomb (q : ℝ) : Potential := movingScalar V hV (coulombPotential q)

/-- The vector `R = x − V t` from the present position of the charge to the point of
observation. -/
def presentSeparation (y : Spacetime) : Space 3 := space y - y 0 • (axisVelocity V hV).val

/-- The first component `x − V t` of the separation from the present position. -/
theorem presentSeparation_zero (y : Spacetime) : presentSeparation V hV y 0 = y 1 - y 0 * V := by
  simp [presentSeparation, axisVelocity, space_apply]

/-- The second component `y` of the separation from the present position. -/
theorem presentSeparation_one (y : Spacetime) : presentSeparation V hV y 1 = y 2 := by
  simp [presentSeparation, axisVelocity, space_apply]

/-- The third component `z` of the separation from the present position. -/
theorem presentSeparation_two (y : Spacetime) : presentSeparation V hV y 2 = y 3 := by
  simp [presentSeparation, axisVelocity, space_apply]

/-- The comoving position is `(γ R₁, R₂, R₃)`. -/
theorem comovingPosition_presentSeparation (y : Spacetime) :
    comovingPosition V hV y 0 = (axisVelocity V hV).gamma * presentSeparation V hV y 0 ∧
      comovingPosition V hV y 1 = presentSeparation V hV y 1 ∧
      comovingPosition V hV y 2 = presentSeparation V hV y 2 := by
  rw [comovingPosition_zero, comovingPosition_one, comovingPosition_two, presentSeparation_zero,
    presentSeparation_one, presentSeparation_two]
  exact ⟨by ring, rfl, rfl⟩

/-- Off the world line `R = 0` the comoving position is not the origin. -/
theorem comovingPosition_ne_zero {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) :
    comovingPosition V hV y ≠ 0 := by
  intro h0
  apply hy
  obtain ⟨h0', h1, h2⟩ := comovingPosition_presentSeparation V hV y
  have hg := (axisVelocity V hV).gamma_pos
  have e0 : comovingPosition V hV y 0 = 0 := by rw [h0]; rfl
  have e1 : comovingPosition V hV y 1 = 0 := by rw [h0]; rfl
  have e2 : comovingPosition V hV y 2 = 0 := by rw [h0]; rfl
  ext i
  fin_cases i
  · have h := h0'.symm.trans e0
    simpa [hg.ne'] using h
  · exact h1.symm.trans e1
  · exact h2.symm.trans e2

/-- The current form of the zero current vanishes. -/
theorem matterCurrentForm_zero (y : Spacetime) :
    SourcedAction.matterCurrentForm (fun _ => 0) y = 0 := by
  have h := interior_smul_vector (0 : ℝ) (0 : Spacetime) (coordinateForm (n := 4) id)
  rw [zero_smul, zero_smul] at h
  change -interior (0 : Spacetime) (coordinateForm (n := 4) id) = 0
  rw [h, neg_zero]

/-- Off the world line, the field of the moving point charge solves the equation of the vacuum
`d⋆F = 0`. -/
theorem movingCoulomb_vacuum (q : ℝ) {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) :
    exteriorDerivative (fun z => -star (fieldTensor (movingCoulomb V hV q) z)) y = 0 := by
  have h := excitation_movingScalar V hV (coulombSolution q)
    (comovingPosition_ne_zero V hV hy)
  have hk : movingCurrent V hV (coulombSolution q).density = fun _ => 0 := by
    funext z
    simp [movingCurrent, coulombSolution]
  rw [hk, matterCurrentForm_zero] at h
  exact h

/-- Off the world line, the field of the moving point charge satisfies the four equations of
Maxwell of the vacuum in the frame of the co-ordinates. -/
theorem maxwell_movingCoulomb (q : ℝ) {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) :
    (divergence3 (magneticField (fieldTensor (movingCoulomb V hV q))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (movingCoulomb V hV q)) i) 0 y +
        curl (electricField (fieldTensor (movingCoulomb V hV q))) y i = 0) ∧
    divergence3 (electricField (fieldTensor (movingCoulomb V hV q))) y = 0 ∧
    ∀ i, curl (magneticField (fieldTensor (movingCoulomb V hV q))) y i -
        partialAt (electricField (fieldTensor (movingCoulomb V hV q)) i) 0 y = 0 := by
  obtain ⟨hh, hdiv, hcurl⟩ := maxwell_movingScalar V hV (coulombSolution q)
    (comovingPosition_ne_zero V hV hy)
  refine ⟨hh, hdiv.trans (by simp [coulombSolution]), fun i => (hcurl i).trans ?_⟩
  simp [coulombSolution]

/-- `s^{3/2} = s √s` for `s > 0`. -/
theorem rpow_three_halves {s : ℝ} (hs : 0 < s) : s ^ (3 / 2 : ℝ) = s * √s := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- The electric field of the point charge `q` moving with the velocity `V` along the first
axis (Landau–Lifshitz (38.8) in the units with `div E = ρ`):
`E = q (1 − V²) R / (4π R³ (1 − V² sin² θ)^{3/2})`, with the vector `R` from the present
position of the charge and the angle `θ` between `R` and the axis of the motion. -/
theorem electricField_movingCoulomb (q : ℝ) {y : Spacetime} (hy : presentSeparation V hV y ≠ 0)
    (i : Fin 3) :
    electricVector (fieldTensor (movingCoulomb V hV q) y) i =
      q * (1 - V ^ 2) * presentSeparation V hV y i /
        (4 * Real.pi * ‖presentSeparation V hV y‖ ^ 3 *
          (1 - V ^ 2 * Real.sin (InnerProductGeometry.angle (presentSeparation V hV y)
            (EuclideanSpace.single 0 1)) ^ 2) ^ (3 / 2 : ℝ)) := by
  have hp := comovingPosition_ne_zero V hV hy
  have hφ : DifferentiableAt ℝ (coulombPotential q) (comovingPosition V hV y) :=
    (hasFDerivAt_coulombPotential q hp).differentiableAt
  have hE : electricVector (fieldTensor (movingCoulomb V hV q) y) = _ :=
    electricField_movingScalar V hV hφ
  have hγ := axisVelocity_gamma_identity V hV
  have hγpos := (axisVelocity V hV).gamma_pos
  obtain ⟨hp0, hp1, hp2⟩ := comovingPosition_presentSeparation V hV y
  rw [congrFun hE i]
  simp only [staticElectric, spatialPartial_coulombPotential q hp]
  generalize comovingPosition V hV y = p at hp hp0 hp1 hp2 ⊢
  generalize presentSeparation V hV y = R at hy hp0 hp1 hp2 ⊢
  generalize (axisVelocity V hV).gamma = γ at hγ hγpos hp0 ⊢
  have hV2 : V ^ 2 < 1 := by
    have := abs_lt.mp hV
    nlinarith
  have hRpos : 0 < ‖R‖ := norm_pos_iff.mpr hy
  have hRsq : ‖R‖ ^ 2 = R 0 ^ 2 + R 1 ^ 2 + R 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have hpsq : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have hsin : Real.sin (InnerProductGeometry.angle R (EuclideanSpace.single 0 1)) ^ 2 =
      1 - (R 0 / ‖R‖) ^ 2 := by
    rw [Real.sin_sq, InnerProductGeometry.cos_angle, EuclideanSpace.inner_single_right,
      PiLp.norm_single]
    simp
  rw [hsin]
  have hR0 : (R 0 / ‖R‖) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    nlinarith [sq_nonneg (R 1), sq_nonneg (R 2)]
  have hspos : 0 < 1 - V ^ 2 * (1 - (R 0 / ‖R‖) ^ 2) := by
    have h0 : 0 ≤ (R 0 / ‖R‖) ^ 2 := sq_nonneg _
    nlinarith
  have hkey : ‖p‖ ^ 2 = (γ * ‖R‖) ^ 2 * (1 - V ^ 2 * (1 - (R 0 / ‖R‖) ^ 2)) := by
    rw [hpsq, hp0, hp1, hp2]
    field_simp
    rw [hRsq]
    linear_combination (-(R 1 ^ 2 + R 2 ^ 2)) * hγ
  generalize 1 - V ^ 2 * (1 - (R 0 / ‖R‖) ^ 2) = s at hspos hkey ⊢
  have hpn : ‖p‖ = γ * ‖R‖ * √s := by
    rw [← Real.sqrt_sq (norm_nonneg p), hkey, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (by positivity)]
  have hsq : 0 < √s := Real.sqrt_pos.mpr hspos
  have hsqs : √s ^ 2 = s := Real.sq_sqrt hspos.le
  rw [rpow_three_halves hspos, hpn]
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, neg_mul, neg_neg, hp0]
    field_simp
    linear_combination (-q * R 0 * s) * hγ + (-q * R 0 * γ ^ 2 * (1 - V ^ 2)) * hsqs
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, neg_mul, neg_neg, hp1]
    field_simp
    linear_combination (-q * R 1 * s) * hγ + (-q * R 1 * γ ^ 2 * (1 - V ^ 2)) * hsqs
  · simp only [Fin.reduceFinMk, Matrix.cons_val, neg_mul, neg_neg, hp2]
    field_simp
    linear_combination (-q * R 2 * s) * hγ + (-q * R 2 * γ ^ 2 * (1 - V ^ 2)) * hsqs

/-- The magnetic field of the moving point charge is `B = V × E` (Landau–Lifshitz (38.7)). -/
theorem magneticField_movingCoulomb (q : ℝ) {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) :
    magneticVector (fieldTensor (movingCoulomb V hV q) y) =
      crossProduct ![V, 0, 0] (electricVector (fieldTensor (movingCoulomb V hV q) y)) :=
  magneticField_movingScalar V hV
    (hasFDerivAt_coulombPotential q (comovingPosition_ne_zero V hV hy)).differentiableAt

/-- The field of the point charge `q` in uniform motion with the velocity `V` along the first
axis. Off the world line `x = V t e₁` the boosted Coulomb potential solves the equation of the
vacuum `d⋆F = 0`, its electric field is Landau–Lifshitz (38.8),
`E = q (1 − V²) R / (4π R³ (1 − V² sin² θ)^{3/2})`, and its magnetic field is `B = V × E`. -/
theorem movingCoulomb_field (q : ℝ) {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) :
    exteriorDerivative (fun z => -star (fieldTensor (movingCoulomb V hV q) z)) y = 0 ∧
    (∀ i, electricVector (fieldTensor (movingCoulomb V hV q) y) i =
      q * (1 - V ^ 2) * presentSeparation V hV y i /
        (4 * Real.pi * ‖presentSeparation V hV y‖ ^ 3 *
          (1 - V ^ 2 * Real.sin (InnerProductGeometry.angle (presentSeparation V hV y)
            (EuclideanSpace.single 0 1)) ^ 2) ^ (3 / 2 : ℝ))) ∧
    magneticVector (fieldTensor (movingCoulomb V hV q) y) =
      crossProduct ![V, 0, 0] (electricVector (fieldTensor (movingCoulomb V hV q) y)) :=
  ⟨movingCoulomb_vacuum V hV q hy, electricField_movingCoulomb V hV q hy,
    magneticField_movingCoulomb V hV q hy⟩

end MovingPointCharge

end ProjectAinos.Electrodynamics.MovingCharge
