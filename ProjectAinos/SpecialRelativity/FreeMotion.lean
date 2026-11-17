/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.ParticleAction
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The motion of a free particle is inertial

Let `γ` be a `C²` curve in space-time whose velocity is timelike on `[a, b]`, with `a < b`
(Landau–Lifshitz, *The Classical Theory of Fields*, §8). For the action `−m ∫ ds`:

* `free_stationary_iff_deriv_kineticMomentum`: the action is stationary if and only if the
  derivative of the momentum covector `m U♭` vanishes on `(a, b)`;
* `free_stationary_iff_fourVelocity_const`: for `m ≠ 0`, if and only if the unit four-velocity
  `U` is constant on `[a, b]`;
* `free_stationary_iff_inertial`: for `m ≠ 0`, if and only if
  `γ t = γ a + τ(t) • U` on `[a, b]`, where `τ(t)` is the proper time from `a` to `t`. This is
  an inertial motion in the parameter `τ`; the given parameter is arbitrary.

The Lagrangian is homogeneous of degree one in the velocity, so its Hessian in the velocity is
degenerate. `hasFDerivAt_kineticMomentum` computes it,
`velocityHessian m v w = −(m/√Q(v)) (w♭ − (⟨v, w⟩/Q(v)) v♭)`, and for `m ≠ 0` its kernel is the
line of the velocity (`ker_velocityHessian`) and its rank is three
(`finrank_range_velocityHessian`).

`pair_fourVelocity_deriv` is the orthogonality of the four-acceleration to the four-velocity.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Topology

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski Mechanics

variable {m : ℝ} {γ : ℝ → Spacetime} {a b : ℝ}

/-- A function that is continuous on `[a, b]` and has zero derivative on `(a, b)` is constant on
`[a, b]`. -/
theorem eq_of_hasDerivAt_zero_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hcont : ContinuousOn f (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f 0 x)
    {x : ℝ} (hx : x ∈ Icc a b) : f x = f a := by
  rcases (hx.1.trans hx.2).eq_or_lt with hab | hab
  · have hxa : x = a := le_antisymm (hab ▸ hx.2) hx.1
    rw [hxa]
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hconst : EqOn f (fun _ => f ((a + b) / 2)) (Ioo a b) := by
    have key : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, s ≤ t → f t = f s := by
      intro s hs t ht hst
      refine constant_of_has_deriv_right_zero
        (hcont.mono (Icc_subset_Icc hs.1.le ht.2.le)) (fun y hy => ?_) t (right_mem_Icc.mpr hst)
      exact (hderiv y ⟨hs.1.trans_le hy.1, hy.2.trans ht.2⟩).hasDerivWithinAt
    intro t ht
    rcases le_total t ((a + b) / 2) with h | h
    · exact (key t ht _ hmid h).symm
    · exact key _ hmid t ht h
  have hall : EqOn f (fun _ => f ((a + b) / 2)) (Icc a b) :=
    hconst.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
      (closure_Ioo hab.ne).ge
  rw [hall hx, hall (left_mem_Icc.mpr hab.le)]

/-! ### The momentum along a curve -/

theorem isOpen_timelike : IsOpen {v : Spacetime | Timelike v} :=
  isOpen_lt continuous_const (contDiff_intervalQuadratic (n := 0)).continuous

/-- A timelike velocity stays timelike near the time `t`. -/
theorem eventually_timelike_deriv (hγ : ContDiff ℝ 2 γ) {t : ℝ} (hv : Timelike (deriv γ t)) :
    ∀ᶠ s in 𝓝 t, Timelike (deriv γ s) :=
  (hγ.continuous_deriv (by norm_num)).continuousAt.eventually (isOpen_timelike.mem_nhds hv)

theorem differentiableAt_kineticMomentum (m : ℝ) {v : Spacetime} (hv : Timelike v) :
    DifferentiableAt ℝ (kineticMomentum m) v :=
  ((flat .timeNegative).differentiableAt.comp v
    ((contDiffAt_fourVelocity hv (n := 1)).differentiableAt (by norm_num))).const_smul m

theorem differentiableAt_kineticMomentum_deriv (m : ℝ) (hγ : ContDiff ℝ 2 γ) {t : ℝ}
    (hv : Timelike (deriv γ t)) :
    DifferentiableAt ℝ (fun s => kineticMomentum m (deriv γ s)) t :=
  (differentiableAt_kineticMomentum m hv).comp t (hγ.differentiable_deriv_two t)

/-- The momentum determines the unit four-velocity, and conversely, for a nonzero mass. -/
theorem kineticMomentum_eq_iff (hm : m ≠ 0) (v w : Spacetime) :
    kineticMomentum m v = kineticMomentum m w ↔ fourVelocity v = fourVelocity w := by
  rw [kineticMomentum, kineticMomentum]
  constructor
  · intro h
    exact (flat .timeNegative).injective (smul_right_injective _ hm h)
  · intro h
    rw [h]

/-- Where the velocity is timelike, the Euler–Lagrange covector of the free action is minus the
derivative of the momentum. -/
theorem eulerLagrange_free (m : ℝ) (hγ : ContDiff ℝ 2 γ) {t : ℝ} (hv : Timelike (deriv γ t)) :
    eulerLagrange (freeLagrangian m) γ t =
      -deriv (fun s => kineticMomentum m (deriv γ s)) t := by
  have h : momentum (freeLagrangian m) γ =ᶠ[𝓝 t] fun s => kineticMomentum m (deriv γ s) :=
    (eventually_timelike_deriv hγ hv).mono fun s hs => free_momentum m hs
  rw [eulerLagrange, free_force m hv, zero_sub, h.deriv_eq]

/-! ### Stationary curves -/

/-- The free action is stationary if and only if the momentum has zero derivative. -/
theorem free_stationary_iff_deriv_kineticMomentum (m : ℝ) (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (freeLagrangian m) γ ↔
      ∀ t ∈ Ioo a b, deriv (fun s => kineticMomentum m (deriv γ s)) t = 0 := by
  rw [free_stationary_iff m hab hγ hv]
  refine forall₂_congr fun t ht => ?_
  rw [eulerLagrange_free m hγ (hv t (Ioo_subset_Icc_self ht)), neg_eq_zero]

/-- The free action is stationary if and only if the momentum is constant. -/
theorem free_stationary_iff_kineticMomentum_const (m : ℝ) (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (freeLagrangian m) γ ↔
      ∀ t ∈ Icc a b, kineticMomentum m (deriv γ t) = kineticMomentum m (deriv γ a) := by
  rw [free_stationary_iff_deriv_kineticMomentum m hab hγ hv]
  constructor
  · intro h t ht
    refine eq_of_hasDerivAt_zero_Ioo (f := fun s => kineticMomentum m (deriv γ s))
      (fun s hs => (differentiableAt_kineticMomentum_deriv m hγ (hv s hs)).continuousAt
        |>.continuousWithinAt) (fun s hs => ?_) ht
    have hd := (differentiableAt_kineticMomentum_deriv m hγ
      (hv s (Ioo_subset_Icc_self hs))).hasDerivAt
    rwa [h s hs] at hd
  · intro h t ht
    have heq : (fun s => kineticMomentum m (deriv γ s)) =ᶠ[𝓝 t]
        fun _ => kineticMomentum m (deriv γ a) :=
      Filter.eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2) fun s hs => h s hs
    rw [heq.deriv_eq, deriv_const]

/-- For a nonzero mass the free action is stationary if and only if the unit four-velocity is
constant. -/
theorem free_stationary_iff_fourVelocity_const (hm : m ≠ 0) (hab : a < b)
    (hγ : ContDiff ℝ 2 γ) (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (freeLagrangian m) γ ↔
      ∀ t ∈ Icc a b, fourVelocity (deriv γ t) = fourVelocity (deriv γ a) := by
  rw [free_stationary_iff_kineticMomentum_const m hab hγ hv]
  exact forall₂_congr fun t _ => kineticMomentum_eq_iff hm _ _

/-- A timelike vector is its proper speed times its unit four-velocity. -/
theorem properSpeed_smul_fourVelocity_of_timelike {v : Spacetime} (hv : Timelike v) :
    properSpeed v • fourVelocity v = v := by
  have hpos : 0 < properSpeed v := Real.sqrt_pos.mpr hv
  rw [fourVelocity, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- For a nonzero mass the free action is stationary if and only if the curve is an inertial
motion in its proper time: `γ t = γ a + τ(t) • U` with `τ(t)` the proper time from `a` to `t`
and `U` the unit four-velocity at `a`. -/
theorem free_stationary_iff_inertial (hm : m ≠ 0) (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (freeLagrangian m) γ ↔
      ∀ t ∈ Icc a b, γ t = γ a + properTime γ a t • fourVelocity (deriv γ a) := by
  have hderivc : Continuous (deriv γ) := hγ.continuous_deriv (by norm_num)
  have hspeedc : Continuous fun s => properSpeed (deriv γ s) :=
    properSpeed_continuous.comp hderivc
  constructor
  · intro hstat t ht
    have hU := (free_stationary_iff_fourVelocity_const hm hab hγ hv).mp hstat
    have hftc : ∫ s in a..t, deriv γ s = γ t - γ a :=
      intervalIntegral.integral_deriv_eq_sub
        (fun s _ => (hγ.differentiable (by norm_num)) s) (hderivc.intervalIntegrable a t)
    have hint : ∫ s in a..t, deriv γ s =
        ∫ s in a..t, properSpeed (deriv γ s) • fourVelocity (deriv γ a) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' : s ∈ Icc a b := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      change deriv γ s = properSpeed (deriv γ s) • fourVelocity (deriv γ a)
      rw [← hU s hs', properSpeed_smul_fourVelocity_of_timelike (hv s hs')]
    rw [hint, intervalIntegral.integral_smul_const] at hftc
    rw [properTime, hftc]
    abel
  · intro hline
    rw [free_stationary_iff_deriv_kineticMomentum m hab hγ hv]
    intro t ht
    have hderiv : ∀ᶠ s in 𝓝 t, fourVelocity (deriv γ s) = fourVelocity (deriv γ a) := by
      have hIoo : ∀ᶠ s in 𝓝 t, s ∈ Ioo a b := Ioo_mem_nhds ht.1 ht.2
      refine hIoo.mono fun s hs => ?_
      have hτs : HasDerivAt (fun r => properTime γ a r) (properSpeed (deriv γ s)) s :=
        (hspeedc.integral_hasStrictDerivAt a s).hasDerivAt
      have hlines : γ =ᶠ[𝓝 s] fun r => γ a + properTime γ a r • fourVelocity (deriv γ a) :=
        Filter.eventuallyEq_of_mem (Icc_mem_nhds hs.1 hs.2) fun r hr => hline r hr
      have hds : deriv γ s = properSpeed (deriv γ s) • fourVelocity (deriv γ a) :=
        hlines.deriv_eq.trans
          ((hτs.smul_const (fourVelocity (deriv γ a))).const_add (γ a)).deriv
      have hpos : 0 < properSpeed (deriv γ s) :=
        Real.sqrt_pos.mpr (hv s (Ioo_subset_Icc_self hs))
      calc fourVelocity (deriv γ s)
          = (properSpeed (deriv γ s))⁻¹ •
              (properSpeed (deriv γ s) • fourVelocity (deriv γ a)) :=
            congrArg (fun w : Spacetime => (properSpeed (deriv γ s))⁻¹ • w) hds
        _ = fourVelocity (deriv γ a) := by rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    have heq : (fun s => kineticMomentum m (deriv γ s)) =ᶠ[𝓝 t]
        fun _ => kineticMomentum m (deriv γ a) :=
      hderiv.mono fun s hs => (kineticMomentum_eq_iff hm _ _).mpr hs
    rw [heq.deriv_eq, deriv_const]

/-- The four-acceleration is orthogonal to the four-velocity. -/
theorem pair_fourVelocity_deriv (hγ : ContDiff ℝ 2 γ) {t : ℝ} (hv : Timelike (deriv γ t)) :
    pair (fourVelocity (deriv γ t)) (deriv (fun s => fourVelocity (deriv γ s)) t) = 0 := by
  have hU : HasDerivAt (fun s => fourVelocity (deriv γ s))
      (deriv (fun s => fourVelocity (deriv γ s)) t) t :=
    (((contDiffAt_fourVelocity hv (n := 1)).differentiableAt (by norm_num)).comp t
      (hγ.differentiable_deriv_two t)).hasDerivAt
  have hQ := (hasFDerivAt_intervalQuadratic (fourVelocity (deriv γ t))).comp_hasDerivAt t hU
  have hone : (fun s => intervalQuadratic (fourVelocity (deriv γ s))) =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
    (eventually_timelike_deriv hγ hv).mono fun s hs => fourVelocity_unit hs
  have hzero := hQ.unique (hone.hasDerivAt_iff.mpr (hasDerivAt_const t (1 : ℝ)))
  simp only [smul_apply, smul_eq_mul] at hzero
  linarith

/-! ### The Hessian in the velocity -/

/-- The derivative of the momentum in the velocity, which is the Hessian of the Lagrangian in
the velocity: `w ↦ −(m/√Q(v)) (w♭ − (⟨v, w⟩/Q(v)) v♭)`. -/
def velocityHessian (m : ℝ) (v : Spacetime) : Spacetime →L[ℝ] FourCovector :=
  (-m * (properSpeed v)⁻¹) •
    ((pair : Spacetime →L[ℝ] FourCovector) -
      (intervalQuadratic v)⁻¹ • ((pair v).smulRight (pair v) : Spacetime →L[ℝ] FourCovector))

theorem velocityHessian_apply (m : ℝ) (v w : Spacetime) :
    velocityHessian m v w =
      (-m * (properSpeed v)⁻¹) • (pair w - ((intervalQuadratic v)⁻¹ * pair v w) • pair v) := by
  simp only [velocityHessian, smul_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    smul_smul]

/-- The momentum is differentiable in the velocity, with the Hessian as its derivative. -/
theorem hasFDerivAt_kineticMomentum (m : ℝ) {v : Spacetime} (hv : Timelike v) :
    HasFDerivAt (kineticMomentum m) (velocityHessian m v) v := by
  have hpos : 0 < properSpeed v := Real.sqrt_pos.mpr hv
  have hQ : intervalQuadratic v = properSpeed v ^ 2 := (Real.sq_sqrt hv.le).symm
  have hc := ((hasDerivAt_inv hpos.ne').comp_hasFDerivAt v
    (hasFDerivAt_properSpeed hv)).const_mul (-m)
  have h := hc.smul (pair.hasFDerivAt (x := v))
  have hfun : kineticMomentum m = fun w => (-m * (properSpeed w)⁻¹) • pair w :=
    funext fun w => kineticMomentum_eq m w
  rw [hfun]
  refine h.congr_fderiv ?_
  ext w z
  simp only [velocityHessian, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    sub_apply, smul_eq_mul, hQ, Function.comp_apply]
  field_simp
  ring

/-- The velocity is in the kernel of the Hessian: the Lagrangian is homogeneous of degree one. -/
theorem velocityHessian_self (m : ℝ) {v : Spacetime} (hv : Timelike v) :
    velocityHessian m v v = 0 := by
  have hQ : pair v v = intervalQuadratic v := rfl
  rw [velocityHessian_apply, hQ, inv_mul_cancel₀ hv.ne', one_smul, sub_self, smul_zero]

/-- For a nonzero mass the kernel of the Hessian is the line of the velocity. -/
theorem velocityHessian_eq_zero_iff (hm : m ≠ 0) {v : Spacetime} (hv : Timelike v)
    (w : Spacetime) : velocityHessian m v w = 0 ↔ w ∈ Submodule.span ℝ {v} := by
  have hpos : 0 < properSpeed v := Real.sqrt_pos.mpr hv
  have hc : -m * (properSpeed v)⁻¹ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hm) (inv_ne_zero hpos.ne')
  rw [Submodule.mem_span_singleton]
  constructor
  · intro h
    rw [velocityHessian_apply, smul_eq_zero] at h
    have h0 := h.resolve_left hc
    refine ⟨(intervalQuadratic v)⁻¹ * pair v w, ?_⟩
    have hsub : pair (w - ((intervalQuadratic v)⁻¹ * pair v w) • v) = 0 := by
      rw [map_sub, map_smul]
      exact h0
    have hzero := minkowskiForm_nondegenerate .timePositive
      (w - ((intervalQuadratic v)⁻¹ * pair v w) • v) fun z => by
        change pair (w - ((intervalQuadratic v)⁻¹ * pair v w) • v) z = 0
        rw [hsub]
        rfl
    exact (sub_eq_zero.mp hzero).symm
  · rintro ⟨k, rfl⟩
    rw [map_smul, velocityHessian_self m hv, smul_zero]

theorem ker_velocityHessian (hm : m ≠ 0) {v : Spacetime} (hv : Timelike v) :
    LinearMap.ker (velocityHessian m v).toLinearMap = Submodule.span ℝ {v} :=
  Submodule.ext fun w => velocityHessian_eq_zero_iff hm hv w

/-- The rank of the Hessian is three: one less than the dimension of space-time, because the
action does not depend on the parameter of the curve. -/
theorem finrank_range_velocityHessian (hm : m ≠ 0) {v : Spacetime} (hv : Timelike v) :
    Module.finrank ℝ (LinearMap.range (velocityHessian m v).toLinearMap) = 3 := by
  have hne : v ≠ 0 := by
    rintro rfl
    rw [Timelike, map_zero] at hv
    exact lt_irrefl _ hv
  have h := LinearMap.finrank_range_add_finrank_ker (velocityHessian m v).toLinearMap
  rw [ker_velocityHessian hm hv, finrank_span_singleton hne, Module.finrank_fin_fun] at h
  omega

end ProjectAinos.SpecialRelativity
