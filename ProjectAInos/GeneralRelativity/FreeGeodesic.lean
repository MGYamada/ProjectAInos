/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.FreeLagrangian
public import ProjectAInos.GeneralRelativity.QuadraticGeodesic
public import ProjectAInos.GeneralRelativity.FiniteProperTime

/-! # Massive particle stationarity and native acceleration in model coordinates

The metric is an arbitrary smooth native Lorentz metric on the model
manifold. Positive mass and timelikeness are explicit hypotheses. The
proper-speed derivative supplies the non-affine acceleration term.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Bundle ContinuousLinearMap Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity

open SmoothGeometry LorentzMetric

variable {d : ℕ}
local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

theorem coordinateProperSpeed_model (g : LorentzMetric .timeNegative d E)
    (γ : ℝ → E) (t : ℝ) :
    coordinateProperSpeed (modelMetric g) (γ t, deriv γ t) = speedAlong g γ t := by
  simp only [coordinateProperSpeed, speedAlong, properSpeed, curveVelocity_model, modelMetric_apply]

theorem freeAction_eq_mechanics (g : LorentzMetric .timeNegative d E) (m : ℝ)
    (γ : ℝ → E) (a b : ℝ) :
    freeAction g m γ a b = Mechanics.action a b (freeLagrangian (modelMetric g) m) γ := by
  simp only [freeAction, properTime, Mechanics.action, freeLagrangian,
    coordinateProperSpeed_model, intervalIntegral.integral_const_mul]

/-- The Euler–Lagrange covector lowers acceleration minus its tangential,
non-affine part. The proper-speed factor is not assumed constant. -/
theorem free_eulerLagrange_native (g : LorentzMetric .timeNegative d E) (m : ℝ)
    {γ : ℝ → E} {t : ℝ} (hγ : ContDiffAt ℝ 2 γ t)
    (hv : Timelike g (curveVelocity γ t)) (w : E) :
    Mechanics.eulerLagrange (freeLagrangian (modelMetric g) m) γ t w =
      -(m / speedAlong g γ t) * g.form (γ t)
        (g.covariantAlong (curveVelocity γ) t -
          (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t)
        (modelField w (γ t)) := by
  have hB : ContDiffAt ℝ 2 (modelMetric g) (γ t) :=
    ((modelMetric_contDiff g).of_le (by simp)).contDiffAt
  have hv' : modelMetric g (γ t) (deriv γ t) (deriv γ t) < 0 := by
    simpa only [Timelike, curveVelocity_model, modelMetric_apply] using hv
  have hs : HasDerivAt (fun r => coordinateProperSpeed (modelMetric g) (γ r, deriv γ r))
      (deriv (speedAlong g γ) t) t := by
    simpa only [coordinateProperSpeed_model] using
      (hasDerivAt_speedAlong g hγ.contMDiffAt hv).differentiableAt.hasDerivAt
  rw [free_eulerLagrange (modelMetric g) m hB hγ (modelMetric_symmetric g) hv' hs,
    quadratic_eulerLagrange_native g hγ,
    quadratic_momentum (modelMetric g) γ t (hB.differentiableAt (by norm_num))
      (modelMetric_symmetric g (γ t)), coordinateProperSpeed_model]
  simp only [modelMetric_apply, curveVelocity_model, map_sub, sub_apply,
    map_smul, smul_apply, smul_eq_mul]
  ring

/-- Stationarity of the actual massive action gives precisely the non-affine
native acceleration equation. Variations are arbitrary smooth fixed-endpoint
coordinate variations; timelikeness of small variations follows from openness. -/
theorem freeAction_stationary_iff_acceleration (g : LorentzMetric .timeNegative d E)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → E} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t)) :
    (∀ η : ℝ → E, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction g m (Variational.perturb γ η ε) a b) 0 0) ↔
      ∀ t ∈ Ioo a b, g.covariantAlong (curveVelocity γ) t =
        (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t := by
  have hv' : ∀ t ∈ Icc a b, modelMetric g (γ t) (deriv γ t) (deriv γ t) < 0 := by
    intro t ht
    simpa only [Timelike, curveVelocity_model, modelMetric_apply] using hv t ht
  simp_rw [freeAction_eq_mechanics]
  change Mechanics.Stationary a b (freeLagrangian (modelMetric g) m) γ ↔ _
  rw [free_stationary_iff (modelMetric g) m isOpen_univ
    ((modelMetric_contDiff g).of_le (by simp)).contDiffOn hab hγ
    (fun _ _ => mem_univ _) hv']
  constructor
  · intro hel t ht
    apply sub_eq_zero.mp
    apply g.nondegenerate (γ t)
    intro v
    have he := congrArg (fun L : E →L[ℝ] ℝ => L (NormedSpace.fromTangentSpace (γ t) v))
      (hel t ht)
    rw [free_eulerLagrange_native g m hγ.contDiffAt (hv t ⟨ht.1.le, ht.2.le⟩)] at he
    have hp : 0 < speedAlong g γ t :=
      (properSpeed_pos_iff g _).mpr (hv t ⟨ht.1.le, ht.2.le⟩)
    have hn : -(m / speedAlong g γ t) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hm.ne' hp.ne')
    have hz := (mul_eq_zero.mp he).resolve_left hn
    simpa only [modelField, ContinuousLinearEquiv.symm_apply_apply] using hz
  · intro hacc t ht
    ext w
    rw [free_eulerLagrange_native g m hγ.contDiffAt (hv t ⟨ht.1.le, ht.2.le⟩), hacc t ht]
    simp

/-- In a parameter with unit proper-speed rate, massive stationarity is
equivalent to the affine geodesic equation. The parameter is supplied here;
its construction is a separate theorem. -/
theorem freeAction_stationary_iff_geodesic_of_unitSpeed
    (g : LorentzMetric .timeNegative d E) {m : ℝ} (hm : 0 < m)
    {γ : ℝ → E} {a b : ℝ} (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hunit : ∀ t ∈ Icc a b, speedAlong g γ t = 1) :
    (∀ η : ℝ → E, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction g m (Variational.perturb γ η ε) a b) 0 0) ↔
      g.IsGeodesicOn (Ioo a b) γ := by
  have hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t) := by
    intro t ht
    apply (properSpeed_pos_iff g _).mp
    change 0 < speedAlong g γ t
    rw [hunit t ht]
    norm_num
  rw [freeAction_stationary_iff_acceleration g hm hab hγ hv]
  have hd : ∀ t ∈ Ioo a b, deriv (speedAlong g γ) t = 0 := by
    intro t ht
    have he : speedAlong g γ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hunit s ⟨hs.1.le, hs.2.le⟩
    rw [he.deriv_eq, deriv_const]
  constructor
  · intro h t ht
    refine ⟨hγ.contMDiff.contMDiffAt, ?_⟩
    simpa only [hd t ht, zero_div, zero_smul] using h t ht
  · intro h t ht
    simpa only [hd t ht, zero_div, zero_smul] using (h t ht).2

/-- Massive stationarity is equivalent to tangential native acceleration;
the coefficient is derived from metric compatibility. -/
theorem freeAction_stationary_iff_tangential (g : LorentzMetric .timeNegative d E)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → E} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t)) :
    (∀ η : ℝ → E, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction g m (Variational.perturb γ η ε) a b) 0 0) ↔
      ∀ t ∈ Ioo a b, ∃ k : ℝ,
        g.covariantAlong (curveVelocity γ) t = k • curveVelocity γ t := by
  rw [freeAction_stationary_iff_acceleration g hm hab hγ hv]
  constructor
  · intro h t ht
    exact ⟨_, h t ht⟩
  · intro h t ht
    obtain ⟨k, hk⟩ := h t ht
    rw [acceleration_factor_eq g hγ.contMDiff.contMDiffAt (hv t ⟨ht.1.le, ht.2.le⟩) hk]
    exact hk

/-- The actual massive action is stationary iff the curve locally admits a
regular C² change of parameter making it an affine geodesic. The forward
direction constructs that change from proper time; the reverse direction
uses the full second-derivative parameter law. -/
theorem freeAction_stationary_iff_localGeodesic (g : LorentzMetric .timeNegative d E)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → E} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t)) :
    (∀ η : ℝ → E, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction g m (Variational.perturb γ η ε) a b) 0 0) ↔
      ∀ t₀ ∈ Ioo a b, ∃ e : OpenPartialHomeomorph ℝ ℝ,
        t₀ ∈ e.source ∧ e.source ⊆ Ioo a b ∧
        (∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧ 0 < deriv e.symm τ) ∧
        g.IsGeodesicOn e.target (γ ∘ e.symm) := by
  rw [freeAction_stationary_iff_tangential g hm hab hγ hv]
  constructor
  · intro ha t₀ ht₀
    obtain ⟨e, _, he₀, hsub, _, hi, hg⟩ := exists_properTime_geodesic_parameter g
      (fun _ _ => hγ.contMDiff.contMDiffAt) (fun s hs => hv s ⟨hs.1.le, hs.2.le⟩) ha ht₀
    refine ⟨e, he₀, hsub, ?_, hg⟩
    intro τ hτ
    refine ⟨(hi τ hτ).1, ?_⟩
    rw [(hi τ hτ).2.1.deriv]
    have hr := hsub (e.map_target hτ)
    exact inv_pos.mpr ((properSpeed_pos_iff g _).mpr (hv _ ⟨hr.1.le, hr.2.le⟩))
  · intro h t ht
    obtain ⟨e, he, _, hi, hg⟩ := h t ht
    have hτ := e.map_source he
    have ha := tangential_acceleration_of_reparam g hγ.contMDiff.contMDiffAt
      (hi _ hτ).1 (hi _ hτ).2.ne' (hg _ hτ).2
    have heq : e.symm (e t) = t := e.left_inv he
    exact heq ▸ ha

/-- A stationary massive worldline admits a single C² proper-time inverse
over its entire finite segment, with explicit endpoints and affine motion
throughout the proper-time interior. -/
theorem freeAction_stationary_finite_properTime (g : LorentzMetric .timeNegative d E)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → E} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t))
    (hs : ∀ η : ℝ → E, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction g m (Variational.perturb γ η ε) a b) 0 0) :
    ∃ r : ℝ → ℝ,
      r 0 = a ∧ r (properTime g γ a b) = b ∧
      MapsTo r (Icc 0 (properTime g γ a b)) (Icc a b) ∧
      (∀ τ ∈ Icc 0 (properTime g γ a b),
        ContDiffAt ℝ 2 r τ ∧ HasDerivAt r (speedAlong g γ (r τ))⁻¹ τ ∧
        properTime g γ a (r τ) = τ ∧ speedAlong g (γ ∘ r) τ = 1) ∧
      g.IsGeodesicOn (Ioo 0 (properTime g γ a b)) (γ ∘ r) := by
  have ha := (freeAction_stationary_iff_tangential g hm hab hγ hv).mp hs
  obtain ⟨e, he, hsource, himage, hinvimage, hleft, hright, hi, hg⟩ :=
    exists_finite_properTime_geodesic g hab.le (fun _ _ => hγ.contMDiff.contMDiffAt) hv ha
  have htarget : Icc 0 (properTime g γ a b) ⊆ e.target := by
    rw [← himage]
    rintro _ ⟨t, ht, rfl⟩
    exact e.map_source (hsource ht)
  refine ⟨e.symm, hleft, hright, ?_, ?_, hg⟩
  · intro τ hτ
    rw [← hinvimage]
    exact ⟨τ, hτ, rfl⟩
  · intro τ hτ
    refine ⟨(hi τ (htarget hτ)).1, (hi τ (htarget hτ)).2.1, ?_, (hi τ (htarget hτ)).2.2⟩
    rw [← he]
    exact e.right_inv (htarget hτ)

end ProjectAInos.GeneralRelativity
