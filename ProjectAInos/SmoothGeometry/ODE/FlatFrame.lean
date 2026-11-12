/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.RadialReparam
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Flat coordinate connections and radial frames

The defect of a frame is its covariant derivative. Flatness makes the
antisymmetric derivative of that defect homogeneous in the defect itself.
For a radial frame, a weighted restriction of the defect to each ray then
solves a linear ODE with zero initial value.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Filter Metric ContinuousLinearMap
open scoped ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LinearODE

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Zero curvature of coordinate connection coefficients, with convention
`R(u,v) = DᵤΓ(v) - DᵥΓ(u) + [Γ(u), Γ(v)]`. -/
def IsFlatConnectionOn (Γ : E → E →L[ℝ] E →L[ℝ] E) (U : Set E) : Prop :=
  ∀ x ∈ U, ∀ u v w : E,
    fderiv ℝ Γ x u v w - fderiv ℝ Γ x v u w +
      Γ x u (Γ x v w) - Γ x v (Γ x u w) = 0

/-- The covariant derivative of a coordinate frame, bundled in the direction
and the initial vector. -/
def frameDefect (Γ : E → E →L[ℝ] E →L[ℝ] E) (P : E → E →L[ℝ] E)
    (x : E) : E →L[ℝ] E →L[ℝ] E :=
  fderiv ℝ P x + ((compL ℝ E E E).flip (P x)).comp (Γ x)

@[simp] theorem frameDefect_apply (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (P : E → E →L[ℝ] E) (x u v : E) :
    frameDefect Γ P x u v = fderiv ℝ P x u v + Γ x u (P x v) := rfl

theorem frameDefect_contDiffOn {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {P : E → E →L[ℝ] E} {U : Set E} (hU : IsOpen U)
    (hΓ : ContDiffOn ℝ ∞ Γ U) (hP : ContDiffOn ℝ ∞ P U) :
    ContDiffOn ℝ ∞ (frameDefect Γ P) U := by
  exact (hP.fderiv_of_isOpen hU (by simp)).add
    ((contDiffOn_const.clm_apply hP).clm_comp hΓ)

/-- The ordinary derivative of the defect, evaluated in fixed directions. -/
theorem frameDefect_fderiv_apply {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {P : E → E →L[ℝ] E} {x : E} (hΓ : DifferentiableAt ℝ Γ x)
    (hP : ContDiffAt ℝ ∞ P x) (u v w : E) :
    fderiv ℝ (frameDefect Γ P) x u v w =
      fderiv ℝ (fderiv ℝ P) x u v w +
      fderiv ℝ Γ x u v (P x w) + Γ x v (fderiv ℝ P x u w) := by
  have hDP : DifferentiableAt ℝ (fderiv ℝ P) x :=
    (hP.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hP' := hP.differentiableAt (by simp)
  have heval := ((hDP.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply
    (hasFDerivAt_const w x)).add
    ((hΓ.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply
      (hP'.hasFDerivAt.clm_apply (hasFDerivAt_const w x)))
  have hQ : DifferentiableAt ℝ (frameDefect Γ P) x := by
    exact hDP.add ((((compL ℝ E E E).flip).differentiableAt.comp x hP').clm_comp hΓ)
  have heval' := (hQ.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply
    (hasFDerivAt_const w x)
  have h := congrArg (fun L : E →L[ℝ] E => L u) (heval'.unique heval)
  simpa [frameDefect, add_assoc, add_comm, add_left_comm] using h

/-- The Hessian terms cancel; zero curvature leaves only homogeneous defect
terms in the antisymmetric derivative. -/
theorem frameDefect_fderiv_sub {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {P : E → E →L[ℝ] E} {U : Set E} (hU : IsOpen U)
    (hΓ : ContDiffOn ℝ ∞ Γ U) (hP : ContDiffOn ℝ ∞ P U)
    (hflat : IsFlatConnectionOn Γ U) {x : E} (hx : x ∈ U) (u v w : E) :
    fderiv ℝ (frameDefect Γ P) x u v w -
      fderiv ℝ (frameDefect Γ P) x v u w =
      Γ x v (frameDefect Γ P x u w) - Γ x u (frameDefect Γ P x v w) := by
  have hΓx := ((hΓ x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hPx := (hP x hx).contDiffAt (hU.mem_nhds hx)
  rw [frameDefect_fderiv_apply hΓx hPx, frameDefect_fderiv_apply hΓx hPx,
    (hPx.isSymmSndFDerivAt (by simp)) u v]
  have hf := hflat x hx u v (P x w)
  simp only [frameDefect_apply, map_add]
  have he : fderiv ℝ Γ x u v (P x w) - fderiv ℝ Γ x v u (P x w) =
      Γ x v (Γ x u (P x w)) - Γ x u (Γ x v (P x w)) := by
    rw [sub_eq_zero] at hf
    calc
      _ = (fderiv ℝ Γ x u v (P x w) - fderiv ℝ Γ x v u (P x w) +
        Γ x u (Γ x v (P x w))) - Γ x u (Γ x v (P x w)) := by abel
      _ = _ := by rw [hf]
  calc
    _ = (fderiv ℝ Γ x u v (P x w) - fderiv ℝ Γ x v u (P x w)) +
      Γ x v (fderiv ℝ P x u w) - Γ x u (fderiv ℝ P x v w) := by abel
    _ = _ := by rw [he]; abel

/-- Differentiating the radial condition and using flatness gives a homogeneous
equation for the defect in its radial variable. -/
theorem frameDefect_fderiv_radial {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {P : E → E →L[ℝ] E} {U : Set E} (hU : IsOpen U)
    (hΓ : ContDiffOn ℝ ∞ Γ U) (hP : ContDiffOn ℝ ∞ P U)
    (hflat : IsFlatConnectionOn Γ U)
    (hrad : ∀ x ∈ U, frameDefect Γ P x x = 0)
    {x : E} (hx : x ∈ U) (u v : E) :
    fderiv ℝ (frameDefect Γ P) x x u v + frameDefect Γ P x u v =
      -(Γ x x (frameDefect Γ P x u v)) := by
  have hQ := (((frameDefect_contDiffOn hU hΓ hP) x hx).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  have hd := hQ.hasFDerivAt.clm_apply (hasFDerivAt_id x)
  have hz : HasFDerivAt (fun y => frameDefect Γ P y y)
      (0 : E →L[ℝ] E →L[ℝ] E) x := by
    apply (hasFDerivAt_const (0 : E →L[ℝ] E) x).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hrad y hy
  have hdu := congrArg (fun L : E →L[ℝ] E →L[ℝ] E => L u v) (hd.unique hz)
  have ha := frameDefect_fderiv_sub hU hΓ hP hflat hx x u v
  have hr : frameDefect Γ P x x v = 0 := by rw [hrad x hx]; rfl
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
    zero_apply] at hdu
  rw [hr, map_zero, zero_sub] at ha
  calc
    _ = fderiv ℝ (frameDefect Γ P) x x u v -
        fderiv ℝ (frameDefect Γ P) x u x v := by
      rw [← neg_eq_of_add_eq_zero_left hdu]
      abel
    _ = _ := ha

variable [CompleteSpace E]

/-- A smooth defect satisfying its homogeneous radial equation vanishes.
Multiplication by time gives a regular zero-initial-value ODE, including at
the center; no division by the radial parameter is used. -/
theorem eq_zero_of_radial_equation (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) {Q : E → E →L[ℝ] E →L[ℝ] E}
    {r : ℝ} (hr : 0 < r) (hQ : ContDiffOn ℝ ∞ Q (ball (0 : E) r))
    (hsmall : ∀ x ∈ ball (0 : E) r, ‖radialCoefficient Γ hΓ 0 x‖ < 1)
    (heq : ∀ x ∈ ball (0 : E) r, ∀ u v,
      fderiv ℝ Q x x u v + Q x u v = -(Γ x x (Q x u v)))
    {x : E} (hx : x ∈ ball (0 : E) r) : Q x = 0 := by
  ext u v
  have hxs (t : unitInterval) : (t : ℝ) • x ∈ ball (0 : E) r :=
    (convex_ball (0 : E) r).smul_mem_of_zero_mem (mem_ball_self hr) hx t.property
  have hpath : Continuous (fun t : unitInterval => (t : ℝ) • x) :=
    continuous_subtype_val.smul continuous_const
  have hQc : Continuous (fun t : unitInterval => Q ((t : ℝ) • x) u v) :=
    ((hQ.continuousOn.comp_continuous hpath hxs).clm_apply continuous_const).clm_apply
      continuous_const
  let f : Curve E := ⟨fun t => (t : ℝ) • Q ((t : ℝ) • x) u v,
    continuous_subtype_val.smul hQc⟩
  have h0 : f 0 = 0 := by simp [f]
  have hf : f = solutionOperator (radialCoefficient Γ hΓ 0 x) 0 := by
    apply eq_solution_of_hasDerivAt (hsmall x hx) 0 f h0
    intro t ht
    let s : unitInterval := ⟨t, mem_Icc_of_Ioo ht⟩
    have hQt := ((hQ _ (hxs s)).contDiffAt (isOpen_ball.mem_nhds (hxs s))).differentiableAt
      (by simp)
    have hdQ := (hQt.hasFDerivAt.clm_apply (hasFDerivAt_const u (t • x))).clm_apply
      (hasFDerivAt_const v (t • x))
    have hline : HasDerivAt (fun z : ℝ => z • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have hdQ' : HasDerivAt (fun z : ℝ => Q (z • x) u v)
        (fderiv ℝ Q (t • x) x u v) t := by
      simpa [s, Function.comp_def] using hdQ.comp_hasDerivAt t hline
    have hd := (hasDerivAt_id t).smul hdQ'
    have hdvalue : t • fderiv ℝ Q (t • x) x u v + Q (t • x) u v =
        -(Γ (t • x) x (t • Q (t • x) u v)) := by
      have he := heq (t • x) (hxs s) u v
      simpa only [map_smul, smul_apply] using he
    have hfeq : extend f =ᶠ[𝓝 t] fun z => z • Q (z • x) u v := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with z hz
      simp [extend, projIcc_of_mem zero_le_one (mem_Icc_of_Ioo hz), f]
    have hfval : extend f t = t • Q (t • x) u v := by
      change extend f (s : ℝ) = _
      rw [extend_coe]
      rfl
    have hAval : extend (radialCoefficient Γ hΓ 0 x) t = -(Γ (t • x) x) := by
      change extend (radialCoefficient Γ hΓ 0 x) (s : ℝ) = _
      rw [extend_coe, radialCoefficient_apply, zero_add]
    rw [hAval, hfval]
    simpa only [id_eq, one_smul, hdvalue, neg_apply] using hd.congr_of_eventuallyEq hfeq
  have hz := congrArg (fun c : Curve E => c 1) hf
  simpa [f] using hz

/-- A radial frame for a flat connection is parallel in every direction. -/
theorem frameDefect_eq_zero_of_flat (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) {P : E → E →L[ℝ] E} {r : ℝ} (hr : 0 < r)
    (hP : ContDiffOn ℝ ∞ P (ball (0 : E) r))
    (hsmall : ∀ x ∈ ball (0 : E) r, ‖radialCoefficient Γ hΓ 0 x‖ < 1)
    (hflat : IsFlatConnectionOn Γ (ball (0 : E) r))
    (hrad : ∀ x ∈ ball (0 : E) r, frameDefect Γ P x x = 0)
    {x : E} (hx : x ∈ ball (0 : E) r) : frameDefect Γ P x = 0 :=
  eq_zero_of_radial_equation Γ hΓ hr
    (frameDefect_contDiffOn isOpen_ball hΓ.contDiffOn hP) hsmall
    (fun _ hy => frameDefect_fderiv_radial isOpen_ball hΓ.contDiffOn hP hflat hrad hy) hx

/-- Full parallelness of the constructed radial endpoint family under the
coordinate zero-curvature condition. -/
theorem radialEndpoint_fderiv_of_flat (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ x ∈ ball (0 : E) r, ‖radialCoefficient Γ hΓ 0 x‖ < 1)
    (hflat : IsFlatConnectionOn Γ (ball (0 : E) r))
    {x : E} (hx : x ∈ ball (0 : E) r) (u v : E) :
    fderiv ℝ (radialEndpoint Γ hΓ 0) x u v =
      -(Γ x u (radialEndpoint Γ hΓ 0 x v)) := by
  have hP : ContDiffOn ℝ ∞ (radialEndpoint Γ hΓ 0) (ball (0 : E) r) :=
    fun y hy => (radialEndpoint_contDiffAt Γ hΓ 0 (hsmall y hy)).contDiffWithinAt
  have hrad : ∀ y ∈ ball (0 : E) r, frameDefect Γ (radialEndpoint Γ hΓ 0) y y = 0 := by
    intro y hy
    ext v
    simp [frameDefect_apply, radialEndpoint_fderiv_radial Γ hΓ 0 hr hsmall hy]
  have hz := congrArg (fun A : E →L[ℝ] E →L[ℝ] E => A u v)
    (frameDefect_eq_zero_of_flat Γ hΓ hr hP hsmall hflat hrad hx)
  exact eq_neg_of_add_eq_zero_left hz

/-- Inverting a parallel frame gives the corresponding parallel coframe. -/
theorem inverse_fderiv_of_parallel {P : E → E →L[ℝ] E} {x : E}
    (hP : ContDiffAt ℝ ∞ P x) (hinv : (P x).IsInvertible)
    (A : E →L[ℝ] E →L[ℝ] E)
    (hparallel : ∀ u v, fderiv ℝ P x u v = -(A u (P x v))) (u v : E) :
    fderiv ℝ (fun y => (P y).inverse) x u v = (P x).inverse (A u v) := by
  have hP' := hP.differentiableAt (by simp)
  have hi : ContDiffAt ℝ ∞ (fun y => (P y).inverse) x :=
    hinv.contDiffAt_map_inverse.comp x hP
  have hd := (hi.differentiableAt (by simp)).hasFDerivAt.clm_comp hP'.hasFDerivAt
  have hz : HasFDerivAt (fun y => (P y).inverse.comp (P y))
      (0 : E →L[ℝ] E →L[ℝ] E) x := by
    apply (hasFDerivAt_const (ContinuousLinearMap.id ℝ E) x).congr_of_eventuallyEq
    filter_upwards [hP.continuousAt hinv.eventually_nhds] with y hy
    ext w
    exact hy.inverse_apply_self w
  have h := congrArg (fun L : E →L[ℝ] E →L[ℝ] E => L u ((P x).inverse v)) (hd.unique hz)
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, zero_apply] at h
  rw [hparallel, hinv.self_apply_inverse, map_neg] at h
  exact eq_of_sub_eq_zero (by simpa only [neg_add_eq_sub] using h)

/-- The inverse radial frame satisfies the coframe equation in every
direction when curvature vanishes. -/
theorem radialCoframe_fderiv_of_flat (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ x ∈ ball (0 : E) r, ‖radialCoefficient Γ hΓ 0 x‖ < 1)
    (hflat : IsFlatConnectionOn Γ (ball (0 : E) r))
    {x : E} (hx : x ∈ ball (0 : E) r) (hinv : (radialEndpoint Γ hΓ 0 x).IsInvertible)
    (u v : E) :
    fderiv ℝ (radialCoframe Γ hΓ 0) x u v = radialCoframe Γ hΓ 0 x (Γ x u v) :=
  inverse_fderiv_of_parallel (radialEndpoint_contDiffAt Γ hΓ 0 (hsmall x hx)) hinv
    (Γ x) (radialEndpoint_fderiv_of_flat Γ hΓ hr hsmall hflat hx) u v

/-- A flat smooth connection on a neighborhood of the origin admits a smooth
invertible parallel coframe on a smaller ball, normalized to identity at the
origin. The neighborhood need not be the whole coordinate space. -/
theorem exists_parallel_radialCoframe (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) {U : Set E} (hU : U ∈ 𝓝 (0 : E))
    (hflat : IsFlatConnectionOn Γ U) :
    ∃ r : ℝ, 0 < r ∧ ball (0 : E) r ⊆ U ∧
      ContDiffOn ℝ ∞ (radialCoframe Γ hΓ 0) (ball 0 r) ∧
      (∀ x ∈ ball (0 : E) r, (radialCoframe Γ hΓ 0 x).IsInvertible) ∧
      radialCoframe Γ hΓ 0 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ x ∈ ball (0 : E) r, ∀ u v,
        fderiv ℝ (radialCoframe Γ hΓ 0) x u v = radialCoframe Γ hΓ 0 x (Γ x u v) := by
  obtain ⟨s, hs, hsmall, hinv, _, hθ, hθ0⟩ := exists_radial_ball Γ hΓ (0 : E)
  obtain ⟨a, ha, haU⟩ := Metric.mem_nhds_iff.mp hU
  let r := min s a
  have hrs : ball (0 : E) r ⊆ ball 0 s := ball_subset_ball (min_le_left _ _)
  have hrU : ball (0 : E) r ⊆ U := (ball_subset_ball (min_le_right _ _)).trans haU
  have hr : 0 < r := lt_min hs ha
  refine ⟨r, hr, hrU, hθ.mono hrs, ?_, hθ0, ?_⟩
  · intro x hx
    obtain ⟨e, he⟩ := hinv x (hrs hx)
    refine ⟨e.symm, ?_⟩
    simp [radialCoframe, ← he]
  · intro x hx u v
    exact radialCoframe_fderiv_of_flat Γ hΓ hr (fun y hy => hsmall y (hrs hy))
      (fun y hy => hflat y (hrU hy)) hx (hinv x (hrs hx)) u v

end ProjectAInos.SmoothGeometry.LinearODE
