/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.LorentzForce
public import ProjectAinos.SmoothGeometry.ODE.LinearMotion
public import ProjectAinos.SpecialRelativity.OrbitalCharges
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The motion of a charge in a constant field

Let `F` be a constant field on space-time (Landau–Lifshitz, *The Classical Theory of Fields*,
§§20–22). In the proper time the four-velocity of a charge of mass `m` satisfies the linear
equation `m u′ = e F♯ u`.

* `ConstantField.potential F` is the potential `A(x) = ½ ι_x F`, with `dA = F`
  (`fieldTensor_potential`).
* `velocity m e F u₀` and `motion m e F x₀ u₀` are the solution for all values of the proper
  time. The interval of the velocity is constant (`intervalQuadratic_velocity`), a future
  timelike velocity stays future timelike (`futureTimelike_velocity`), and for a unit velocity
  the motion is a stationary curve of the action on every interval (`stationary_motion`).
  `deriv_eq_velocity_of_stationary`: every stationary curve in the proper time has this
  velocity.
* A field `F = α ∧ β` of two covectors (`IsSimple`) has the generator
  `−(e/m) (α ⊗ β♯ − β ⊗ α♯)`, whose cube is `κ` times itself with
  `κ = (e/m)² (⟨α, β⟩² − ⟨α, α⟩ ⟨β, β⟩)` (`generator_cube`). The motion is hyperbolic for
  `κ > 0` (`velocity_of_pos`, `motion_of_pos`: an electric field), circular for `κ < 0`
  (`velocity_of_neg`, `motion_of_neg`: a magnetic field) and a polynomial of degree three for
  `κ = 0` (`velocity_of_zero`, `motion_of_zero`: a null field).
* `velocity_add`: for two fields whose generators have zero products, the velocity is the
  sum of the two velocities minus the initial velocity. This is the case of parallel electric
  and magnetic fields.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ}

theorem lorentzGenerator_apply (σ : LorentzConvention) (α β : MinkowskiModel d →L[ℝ] ℝ)
    (v : MinkowskiModel d) :
    lorentzGenerator σ α β v = α v • sharp σ β - β v • sharp σ α := rfl

/-- The inverse metric is symmetric. -/
theorem covector_sharp_comm (σ : LorentzConvention) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    β (sharp σ α) = α (sharp σ β) := by
  rw [← minkowskiForm_sharp σ β (sharp σ α), ← minkowskiForm_sharp σ α (sharp σ β),
    minkowskiForm_symmetric]

/-- The invariant `⟨α, β⟩² − ⟨α, α⟩ ⟨β, β⟩` of two covectors. -/
def generatorInvariant (σ : LorentzConvention) (α β : MinkowskiModel d →L[ℝ] ℝ) : ℝ :=
  α (sharp σ β) ^ 2 - α (sharp σ α) * β (sharp σ β)

/-- The cube of the generator of two covectors is a multiple of the generator. -/
theorem lorentzGenerator_cube (σ : LorentzConvention) (α β : MinkowskiModel d →L[ℝ] ℝ)
    (v : MinkowskiModel d) :
    lorentzGenerator σ α β (lorentzGenerator σ α β (lorentzGenerator σ α β v)) =
      generatorInvariant σ α β • lorentzGenerator σ α β v := by
  have hc := covector_sharp_comm σ α β
  have h1 (w : MinkowskiModel d) : α (lorentzGenerator σ α β w) =
      α (sharp σ β) * α w - α (sharp σ α) * β w := by
    rw [lorentzGenerator_apply, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have h2 (w : MinkowskiModel d) : β (lorentzGenerator σ α β w) =
      β (sharp σ β) * α w - α (sharp σ β) * β w := by
    rw [lorentzGenerator_apply, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hc]
    ring
  rw [lorentzGenerator_apply σ α β (lorentzGenerator σ α β (lorentzGenerator σ α β v))]
  simp only [h1, h2]
  rw [lorentzGenerator_apply σ α β v, generatorInvariant]
  module

end ProjectAinos.SpecialRelativity

namespace ProjectAinos.Electrodynamics.ConstantField

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.LinearODE SpecialRelativity Mechanics

variable {m e : ℝ} (F : TwoForm)

/-! ### The potential and the generator -/

/-- The potential `A(x) = ½ ι_x F` of a constant field. -/
def potential (F : TwoForm) : Spacetime →L[ℝ] OneForm := (1 / 2 : ℝ) • F.curryLeft

/-- The field of the potential `½ ι_x F` is `F`. -/
theorem fieldTensor_potential (x : Spacetime) : fieldTensor (potential F) x = F := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, fieldTensor_apply, (potential F).fderiv]
  simp only [potential, smul_apply, map_smul, oneCovector_curryLeft, smul_eq_mul]
  have h := twoForm_swap F (v 1) (v 0)
  linarith

/-- The force `e F♯ v` as a linear map of the velocity. -/
def forceMap (e : ℝ) (F : TwoForm) : Spacetime →L[ℝ] Spacetime :=
  (sharp .timeNegative).toContinuousLinearMap.comp
    ((-e) • oneCovector.toContinuousLinearMap.comp F.curryLeft)

@[simp] theorem forceMap_apply (e : ℝ) (v : Spacetime) :
    forceMap e F v = lorentzForce e F v := rfl

/-- The generator `(e/m) F♯` of the motion in the proper time. -/
def generator (m e : ℝ) (F : TwoForm) : Spacetime →L[ℝ] Spacetime := m⁻¹ • forceMap e F

theorem generator_apply (m e : ℝ) (v : Spacetime) :
    generator m e F v = m⁻¹ • lorentzForce e F v := rfl

/-! ### The motion -/

/-- The four-velocity with the initial value `u₀`, as a function of the proper time. -/
def velocity (m e : ℝ) (F : TwoForm) (u₀ : Spacetime) : ℝ → Spacetime :=
  linearVelocity (generator m e F) u₀

/-- The world line with the initial event `x₀` and the initial four-velocity `u₀`. -/
def motion (m e : ℝ) (F : TwoForm) (x₀ u₀ : Spacetime) : ℝ → Spacetime :=
  linearMotion (generator m e F) x₀ u₀

@[simp] theorem velocity_zero (m e : ℝ) (u₀ : Spacetime) : velocity m e F u₀ 0 = u₀ :=
  linearVelocity_zero _ _

@[simp] theorem motion_zero (m e : ℝ) (x₀ u₀ : Spacetime) : motion m e F x₀ u₀ 0 = x₀ :=
  linearMotion_zero _ _ _

/-- The equation of motion `u′ = (e/m) F♯ u`. -/
theorem hasDerivAt_velocity (m e : ℝ) (u₀ : Spacetime) (τ : ℝ) :
    HasDerivAt (velocity m e F u₀) (m⁻¹ • lorentzForce e F (velocity m e F u₀ τ)) τ :=
  hasDerivAt_linearVelocity _ _ τ

theorem hasDerivAt_motion (m e : ℝ) (x₀ u₀ : Spacetime) (τ : ℝ) :
    HasDerivAt (motion m e F x₀ u₀) (velocity m e F u₀ τ) τ :=
  hasDerivAt_linearMotion _ _ _ τ

theorem deriv_motion (m e : ℝ) (x₀ u₀ : Spacetime) :
    deriv (motion m e F x₀ u₀) = velocity m e F u₀ :=
  deriv_linearMotion _ _ _

theorem contDiff_motion (m e : ℝ) (x₀ u₀ : Spacetime) : ContDiff ℝ ∞ (motion m e F x₀ u₀) :=
  contDiff_linearMotion _ _ _

theorem contDiff_velocity (m e : ℝ) (u₀ : Spacetime) : ContDiff ℝ ∞ (velocity m e F u₀) :=
  contDiff_linearVelocity _ _

/-- The force is orthogonal to the velocity for the indefinite pairing. -/
theorem pair_lorentzForce (e : ℝ) (v : Spacetime) : pair (lorentzForce e F v) v = 0 := by
  have h := lorentzForce_orthogonal e F v
  rw [metric_eq] at h
  exact (mul_eq_zero.mp h).resolve_left (LorentzConvention.timeSign_ne_zero _)

/-- The interval of the four-velocity is constant. -/
theorem intervalQuadratic_velocity (m e : ℝ) (u₀ : Spacetime) (τ : ℝ) :
    intervalQuadratic (velocity m e F u₀ τ) = intervalQuadratic u₀ := by
  have hd : ∀ t, HasDerivAt (fun t => intervalQuadratic (velocity m e F u₀ t)) 0 t := by
    intro t
    have h := (hasFDerivAt_intervalQuadratic (velocity m e F u₀ t)).comp_hasDerivAt t
      (hasDerivAt_velocity F m e u₀ t)
    have hz : ((2 : ℝ) • pair (velocity m e F u₀ t))
        (m⁻¹ • lorentzForce e F (velocity m e F u₀ t)) = 0 := by
      rw [smul_apply, map_smul, Minkowski.pair_comm, pair_lorentzForce, smul_zero, smul_zero]
    rw [hz] at h
    exact h
  have h := is_const_of_deriv_eq_zero (f := fun t => intervalQuadratic (velocity m e F u₀ t))
    (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) τ 0
  simpa using h

/-- A future timelike four-velocity stays future timelike. -/
theorem futureTimelike_velocity (m e : ℝ) {u₀ : Spacetime} (hu : FutureTimelike u₀) (τ : ℝ) :
    FutureTimelike (velocity m e F u₀ τ) := by
  have hu' := (futureTimelike_iff u₀).mp hu
  have hQ : ∀ t, Timelike (velocity m e F u₀ t) := fun t => by
    change 0 < intervalQuadratic (velocity m e F u₀ t)
    rw [intervalQuadratic_velocity]
    exact hu'.1
  have hne : ∀ t, time (velocity m e F u₀ t) ≠ 0 := fun t h0 => by
    have h := hQ t
    rw [Timelike, intervalQuadratic_coordinates, h0] at h
    nlinarith [sq_nonneg ‖space (velocity m e F u₀ t)‖]
  refine (futureTimelike_iff _).mpr ⟨hQ τ, ?_⟩
  by_contra hneg
  have hc : Continuous fun t => time (velocity m e F u₀ t) :=
    (time (d := 3)).continuous.comp (contDiff_velocity F m e u₀).continuous
  have hmem : (0 : ℝ) ∈ uIcc (time (velocity m e F u₀ 0)) (time (velocity m e F u₀ τ)) := by
    rw [velocity_zero]
    exact ⟨by rw [min_eq_right ((not_lt.mp hneg).trans hu'.2.le)]; exact not_lt.mp hneg,
      by rw [max_eq_left ((not_lt.mp hneg).trans hu'.2.le)]; exact hu'.2.le⟩
  obtain ⟨c, -, hc0⟩ := intermediate_value_uIcc (a := 0) (b := τ) hc.continuousOn hmem
  exact hne c hc0

/-- For a unit initial four-velocity the motion is a stationary curve of the action of the
charge, on every interval of the proper time. -/
theorem stationary_motion (hm : m ≠ 0) (e : ℝ) (x₀ : Spacetime) {u₀ : Spacetime}
    (hu : intervalQuadratic u₀ = 1) {a b : ℝ} (hab : a < b) :
    Stationary a b (chargedLagrangian m e (potential F)) (motion m e F x₀ u₀) := by
  have hγ : ContDiff ℝ 2 (motion m e F x₀ u₀) := (contDiff_motion F m e x₀ u₀).of_le (by simp)
  have hunit : ∀ t, intervalQuadratic (deriv (motion m e F x₀ u₀) t) = 1 := fun t => by
    rw [deriv_motion, intervalQuadratic_velocity, hu]
  have hv : ∀ t ∈ Icc a b, Timelike (deriv (motion m e F x₀ u₀) t) := fun t _ => by
    change 0 < intervalQuadratic (deriv (motion m e F x₀ u₀) t)
    rw [hunit t]
    norm_num
  refine (stationary_iff_lorentzForce m e hab hγ isOpen_univ
    (potential F).contDiff.contDiffOn (fun _ _ => mem_univ _) hv).mpr fun t _ => ?_
  have hfv : (fun s => fourVelocity (deriv (motion m e F x₀ u₀) s)) = velocity m e F u₀ := by
    funext s
    rw [fourVelocity, properSpeed, hunit s, Real.sqrt_one, inv_one, one_smul, deriv_motion]
  rw [hfv, (hasDerivAt_velocity F m e u₀ t).deriv, fieldTensor_potential, deriv_motion,
    smul_smul, mul_inv_cancel₀ hm, one_smul]

/-- Every stationary curve in the proper time has the four-velocity of the linear equation
with its initial value. -/
theorem deriv_eq_velocity_of_stationary (hm : m ≠ 0) (e : ℝ) {γ : ℝ → Spacetime} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hunit : ∀ t ∈ Icc a b, intervalQuadratic (deriv γ t) = 1)
    (hs : Stationary a b (chargedLagrangian m e (potential F)) γ) {t : ℝ} (ht : t ∈ Icc a b) :
    deriv γ t = velocity m e F (deriv γ a) (t - a) := by
  have hd : ∀ r ∈ Ioo a b, HasDerivAt (deriv γ) (generator m e F (deriv γ r)) r := by
    intro r hr
    have h := stationary_properTime m e hab hγ isOpen_univ (potential F).contDiff.contDiffOn
      (fun _ _ => mem_univ _) hunit hs hr
    rw [fieldTensor_potential] at h
    have hdd : HasDerivAt (deriv γ) (deriv (deriv γ) r) r :=
      (hγ.differentiable_deriv_two r).hasDerivAt
    have hval : deriv (deriv γ) r = generator m e F (deriv γ r) := by
      rw [generator_apply, ← h, smul_smul, inv_mul_cancel₀ hm, one_smul]
    rwa [hval] at hdd
  have hprop := eq_propagator_apply_of_hasDerivAt (ContinuousMap.const ℝ (generator m e F))
    (f := deriv γ) (s := a) (t := t)
    ((hγ.continuous_deriv (by norm_num)).continuousOn)
    (fun r hr => by
      rw [min_eq_left ht.1, max_eq_right ht.1] at hr
      exact hd r ⟨hr.1, hr.2.trans_le ht.2⟩)
  rw [hprop, velocity, linearVelocity, propagator_const, propagator_const, sub_zero]

/-! ### Fields of two covectors -/

/-- The field is the exterior product of the covectors `α` and `β`. -/
def IsSimple (F : TwoForm) (α β : FourCovector) : Prop :=
  ∀ v w, F ![v, w] = α v * β w - α w * β v

variable {F} {α β : FourCovector}

/-- The generator of a field of two covectors. -/
theorem generator_of_isSimple (h : IsSimple F α β) (m e : ℝ) (v : Spacetime) :
    generator m e F v = (-(e / m)) • lorentzGenerator .timeNegative α β v := by
  have hcov : oneCovector (F.curryLeft v) = α v • β - β v • α := by
    ext w
    rw [oneCovector_curryLeft, h v w]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    ring
  rw [generator_apply, lorentzForce, hcov, lorentzGenerator_apply, map_smul, map_sub, map_smul,
    map_smul]
  module

/-- The cube of the generator of a field of two covectors is a multiple of the generator. -/
theorem generator_cube (h : IsSimple F α β) (m e : ℝ) (v : Spacetime) :
    generator m e F (generator m e F (generator m e F v)) =
      ((e / m) ^ 2 * generatorInvariant .timeNegative α β) • generator m e F v := by
  simp only [generator_of_isSimple h, map_smul, lorentzGenerator_cube]
  module

/-! ### The three kinds of motion -/

theorem hasDerivAt_sinh_div {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => Real.sinh (Ω * t) / Ω)
      (1 + Ω ^ 2 * ((Real.cosh (Ω * τ) - 1) / Ω ^ 2)) τ := by
  have h : HasDerivAt (fun t => Real.sinh (Ω * t) / Ω) (Real.cosh (Ω * τ) * (Ω * 1) / Ω) τ :=
    ((Real.hasDerivAt_sinh (Ω * τ)).comp τ ((hasDerivAt_id τ).const_mul Ω)).div_const Ω
  refine h.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_cosh_sub_div {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => (Real.cosh (Ω * t) - 1) / Ω ^ 2) (Real.sinh (Ω * τ) / Ω) τ := by
  have h : HasDerivAt (fun t => (Real.cosh (Ω * t) - 1) / Ω ^ 2)
      (Real.sinh (Ω * τ) * (Ω * 1) / Ω ^ 2) τ :=
    (((Real.hasDerivAt_cosh (Ω * τ)).comp τ ((hasDerivAt_id τ).const_mul Ω)).sub_const
      1).div_const (Ω ^ 2)
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_sinh_sub_div {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => (Real.sinh (Ω * t) - Ω * t) / Ω ^ 3)
      ((Real.cosh (Ω * τ) - 1) / Ω ^ 2) τ := by
  have h : HasDerivAt (fun t => (Real.sinh (Ω * t) - Ω * t) / Ω ^ 3)
      ((Real.cosh (Ω * τ) * (Ω * 1) - Ω * 1) / Ω ^ 3) τ :=
    (((Real.hasDerivAt_sinh (Ω * τ)).comp τ ((hasDerivAt_id τ).const_mul Ω)).sub
      ((hasDerivAt_id τ).const_mul Ω)).div_const (Ω ^ 3)
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_sin_div {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => Real.sin (Ω * t) / Ω)
      (1 + -Ω ^ 2 * ((1 - Real.cos (Ω * τ)) / Ω ^ 2)) τ := by
  have h : HasDerivAt (fun t => Real.sin (Ω * t) / Ω) (Real.cos (Ω * τ) * (Ω * 1) / Ω) τ :=
    ((Real.hasDerivAt_sin (Ω * τ)).comp τ ((hasDerivAt_id τ).const_mul Ω)).div_const Ω
  refine h.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_one_sub_cos_div {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => (1 - Real.cos (Ω * t)) / Ω ^ 2) (Real.sin (Ω * τ) / Ω) τ := by
  have h : HasDerivAt (fun t => (1 - Real.cos (Ω * t)) / Ω ^ 2)
      (-(-Real.sin (Ω * τ) * (Ω * 1)) / Ω ^ 2) τ :=
    (((Real.hasDerivAt_cos (Ω * τ)).comp τ ((hasDerivAt_id τ).const_mul Ω)).const_sub
      1).div_const (Ω ^ 2)
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_sub_sin_div {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => (Ω * t - Real.sin (Ω * t)) / Ω ^ 3)
      ((1 - Real.cos (Ω * τ)) / Ω ^ 2) τ := by
  have h : HasDerivAt (fun t => (Ω * t - Real.sin (Ω * t)) / Ω ^ 3)
      ((Ω * 1 - Real.cos (Ω * τ) * (Ω * 1)) / Ω ^ 3) τ :=
    (((hasDerivAt_id τ).const_mul Ω).sub
      ((Real.hasDerivAt_sin (Ω * τ)).comp τ ((hasDerivAt_id τ).const_mul Ω))).div_const (Ω ^ 3)
  refine h.congr_deriv ?_
  field_simp

variable (h : IsSimple F α β) {Ω : ℝ}

include h in
/-- A field with `κ = Ω² > 0`, such as an electric field: the four-velocity is hyperbolic. -/
theorem velocity_of_pos (hΩ : Ω ≠ 0)
    (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = Ω ^ 2) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + (Real.sinh (Ω * τ) / Ω) • generator m e F u₀ +
      ((Real.cosh (Ω * τ) - 1) / Ω ^ 2) • generator m e F (generator m e F u₀) :=
  linearVelocity_eq_of_cube (fun v => by rw [generator_cube h, hκ]) (hasDerivAt_sinh_div hΩ)
    (hasDerivAt_cosh_sub_div hΩ) (by simp) (by simp) u₀ τ

include h in
/-- The world line in a field with `κ = Ω² > 0`. -/
theorem motion_of_pos (hΩ : Ω ≠ 0)
    (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = Ω ^ 2) (x₀ u₀ : Spacetime)
    (τ : ℝ) :
    motion m e F x₀ u₀ τ = x₀ + τ • u₀ +
      ((Real.cosh (Ω * τ) - 1) / Ω ^ 2) • generator m e F u₀ +
      ((Real.sinh (Ω * τ) - Ω * τ) / Ω ^ 3) • generator m e F (generator m e F u₀) :=
  linearMotion_eq_of_cube (fun v => by rw [generator_cube h, hκ]) (hasDerivAt_sinh_div hΩ)
    (hasDerivAt_cosh_sub_div hΩ) (by simp) (by simp) (hasDerivAt_sinh_sub_div hΩ) (by simp)
    x₀ u₀ τ

include h in
/-- A field with `κ = −Ω² < 0`, such as a magnetic field: the four-velocity turns. -/
theorem velocity_of_neg (hΩ : Ω ≠ 0)
    (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = -Ω ^ 2) (u₀ : Spacetime)
    (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + (Real.sin (Ω * τ) / Ω) • generator m e F u₀ +
      ((1 - Real.cos (Ω * τ)) / Ω ^ 2) • generator m e F (generator m e F u₀) :=
  linearVelocity_eq_of_cube (fun v => by rw [generator_cube h, hκ]) (hasDerivAt_sin_div hΩ)
    (hasDerivAt_one_sub_cos_div hΩ) (by simp) (by simp) u₀ τ

include h in
/-- The world line in a field with `κ = −Ω² < 0`: a helix. -/
theorem motion_of_neg (hΩ : Ω ≠ 0)
    (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = -Ω ^ 2) (x₀ u₀ : Spacetime)
    (τ : ℝ) :
    motion m e F x₀ u₀ τ = x₀ + τ • u₀ +
      ((1 - Real.cos (Ω * τ)) / Ω ^ 2) • generator m e F u₀ +
      ((Ω * τ - Real.sin (Ω * τ)) / Ω ^ 3) • generator m e F (generator m e F u₀) :=
  linearMotion_eq_of_cube (fun v => by rw [generator_cube h, hκ]) (hasDerivAt_sin_div hΩ)
    (hasDerivAt_one_sub_cos_div hΩ) (by simp) (by simp) (hasDerivAt_sub_sin_div hΩ) (by simp)
    x₀ u₀ τ

include h in
/-- A field with `κ = 0`, such as a null field: the four-velocity is a polynomial of degree
two in the proper time. -/
theorem velocity_of_zero (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = 0)
    (u₀ : Spacetime) (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + τ • generator m e F u₀ +
      (τ ^ 2 / 2) • generator m e F (generator m e F u₀) := by
  refine linearVelocity_eq_of_cube (κ := 0) (s := fun t => t) (c := fun t => t ^ 2 / 2)
    (fun v => by rw [generator_cube h, hκ]) (fun t => ?_) (fun t => ?_) rfl (by simp) u₀ τ
  · exact (hasDerivAt_id' t).congr_deriv (by simp)
  · have h2 := ((hasDerivAt_id t).pow 2).div_const 2
    refine h2.congr_deriv ?_
    simp

include h in
/-- The world line in a field with `κ = 0`: a polynomial of degree three. -/
theorem motion_of_zero (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = 0)
    (x₀ u₀ : Spacetime) (τ : ℝ) :
    motion m e F x₀ u₀ τ = x₀ + τ • u₀ + (τ ^ 2 / 2) • generator m e F u₀ +
      (τ ^ 3 / 6) • generator m e F (generator m e F u₀) := by
  refine linearMotion_eq_of_cube (κ := 0) (s := fun t => t) (c := fun t => t ^ 2 / 2)
    (C := fun t => t ^ 3 / 6) (fun v => by rw [generator_cube h, hκ]) (fun t => ?_)
    (fun t => ?_) rfl (by simp) (fun t => ?_) (by simp) x₀ u₀ τ
  · exact (hasDerivAt_id' t).congr_deriv (by simp)
  · have h2 := ((hasDerivAt_id t).pow 2).div_const 2
    refine h2.congr_deriv ?_
    simp
  · have h3 := ((hasDerivAt_id t).pow 3).div_const 6
    refine h3.congr_deriv ?_
    simp only [id_eq, mul_one]
    ring

/-! ### The sum of two fields -/

omit h in
theorem generator_add (m e : ℝ) (F₁ F₂ : TwoForm) :
    generator m e (F₁ + F₂) = generator m e F₁ + generator m e F₂ := by
  ext v : 1
  have hcov : oneCovector ((F₁ + F₂).curryLeft v) =
      oneCovector (F₁.curryLeft v) + oneCovector (F₂.curryLeft v) := by
    ext w
    rw [add_apply, oneCovector_curryLeft, oneCovector_curryLeft, oneCovector_curryLeft,
      ContinuousAlternatingMap.add_apply]
  rw [add_apply, generator_apply, generator_apply, generator_apply, lorentzForce, hcov,
    smul_add, map_add, smul_add]
  rfl

omit h in
/-- For two fields whose generators have zero products, the four-velocity is the sum of the
two four-velocities minus the initial value. -/
theorem velocity_add (m e : ℝ) {F₁ F₂ : TwoForm}
    (h12 : ∀ v, generator m e F₁ (generator m e F₂ v) = 0)
    (h21 : ∀ v, generator m e F₂ (generator m e F₁ v) = 0) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (F₁ + F₂) u₀ τ = velocity m e F₁ u₀ τ + velocity m e F₂ u₀ τ - u₀ := by
  rw [velocity, generator_add]
  exact linearVelocity_add h12 h21 u₀ τ

end ProjectAinos.Electrodynamics.ConstantField
