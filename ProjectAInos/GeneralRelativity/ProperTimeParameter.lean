/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.ProperTime
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! # Constructing a proper-time parameter on a timelike curve

The parameter is the actual proper-time integral, and the inverse function
theorem constructs its local C² inverse. The curve lives on an arbitrary
smooth Lorentz manifold; no coordinate frame or global inverse is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity

open SmoothGeometry LorentzMetric

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- C² timelike curves have a C¹ proper-speed rate. -/
theorem contDiffAt_speedAlong (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : Timelike g (curveVelocity γ t)) : ContDiffAt ℝ 1 (speedAlong g γ) t := by
  have hV := curveVelocity_contMDiffAt (n := 1) hγ
  have hp : ContMDiffAt 𝓘(ℝ) ((I).prod 𝓘(ℝ)) 1
      (fun s => (⟨γ s, g.form (γ s) (curveVelocity γ s) (curveVelocity γ s)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ))) t :=
    (((g.smooth (γ t)).of_le (by simp)).comp t (hγ.of_le (by norm_num))).clm_bundle_apply₂ hV hV
  rw [contMDiffAt_totalSpace] at hp
  exact hp.2.contDiffAt.neg.sqrt (ne_of_gt (neg_pos.mpr hv))

/-- The derivative of the actual clock integral on an open regular interval. -/
theorem properTime_hasDerivAt_right (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b t₀ t : ℝ}
    (hγ : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ) I 1 γ s)
    (ht₀ : t₀ ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    HasDerivAt (properTime g γ t₀) (speedAlong g γ t) t := by
  have hc : ∀ s ∈ Ioo a b, ContinuousAt (speedAlong g γ) s :=
    fun s hs => speedAlong_continuousAt g (hγ s hs)
  exact intervalIntegral.integral_hasDerivAt_right
    (properTime_integrable g γ t₀ t (fun s hs =>
      hγ s (ordConnected_Ioo.uIcc_subset ht₀ ht hs)))
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hc t ht) (hc t ht)

/-- The proper-time integral is C² on any open C² timelike interval. -/
theorem properTime_contDiffOn (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b t₀ : ℝ}
    (hγ : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ) I 2 γ s)
    (hv : ∀ s ∈ Ioo a b, Timelike g (curveVelocity γ s)) (ht₀ : t₀ ∈ Ioo a b) :
    ContDiffOn ℝ 2 (properTime g γ t₀) (Ioo a b) := by
  have hd : ∀ s ∈ Ioo a b, HasDerivAt (properTime g γ t₀) (speedAlong g γ s) s :=
    fun s hs => properTime_hasDerivAt_right g (fun r hr => (hγ r hr).of_le (by norm_num)) ht₀ hs
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun s hs => (hd s hs).differentiableAt.differentiableWithinAt, by norm_num, ?_⟩
  apply ContDiffOn.congr (f := speedAlong g γ)
    (fun s hs => (contDiffAt_speedAlong g (hγ s hs) (hv s hs)).contDiffWithinAt)
  intro s hs
  exact (hd s hs).deriv

/-- A genuine local parameter change is constructed from the proper-time integral.
Its inverse has positive derivative and gives unit proper-speed rate throughout
its target. Neither the inverse nor these differential properties are premises. -/
theorem exists_properTime_parameter (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b t₀ : ℝ}
    (hγ : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ) I 2 γ s)
    (hv : ∀ s ∈ Ioo a b, Timelike g (curveVelocity γ s)) (ht₀ : t₀ ∈ Ioo a b) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = properTime g γ t₀ ∧ t₀ ∈ e.source ∧ e.source ⊆ Ioo a b ∧
      e t₀ = 0 ∧ ∀ τ ∈ e.target,
        ContDiffAt ℝ 2 e.symm τ ∧
        HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ ∧
        speedAlong g (γ ∘ e.symm) τ = 1 := by
  have hc := properTime_contDiffOn g hγ hv ht₀
  have hd : ∀ s ∈ Ioo a b, HasDerivAt (properTime g γ t₀) (speedAlong g γ s) s :=
    fun s hs => properTime_hasDerivAt_right g (fun r hr => (hγ r hr).of_le (by norm_num)) ht₀ hs
  have hp : ∀ s ∈ Ioo a b, 0 < speedAlong g γ s :=
    fun s hs => (properSpeed_pos_iff g _).mpr (hv s hs)
  let h := (hc.contDiffAt (isOpen_Ioo.mem_nhds ht₀)).toOpenPartialHomeomorph
    (properTime g γ t₀) ((hd t₀ ht₀).hasFDerivAt_equiv (hp t₀ ht₀).ne') (by norm_num)
  let e := h.restrOpen (Ioo a b) isOpen_Ioo
  have heq : (e : ℝ → ℝ) = properTime g γ t₀ := rfl
  have he₀ : t₀ ∈ e.source :=
    ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source .., ht₀⟩
  have hsub : e.source ⊆ Ioo a b := fun _ hx => hx.2
  refine ⟨e, heq, he₀, hsub, ?_, ?_⟩
  · change properTime g γ t₀ t₀ = 0
    exact properTime_self g γ t₀
  · intro τ hτ
    have hr := hsub (e.map_target hτ)
    have hde : HasDerivAt e (speedAlong g γ (e.symm τ)) (e.symm τ) := by
      rw [heq]
      exact hd _ hr
    have hi := e.hasDerivAt_symm hτ (hp _ hr).ne' hde
    refine ⟨e.contDiffAt_symm_deriv (hp _ hr).ne' hτ hde ?_, hi, ?_⟩
    · rw [heq]
      exact hc.contDiffAt (isOpen_Ioo.mem_nhds hr)
    · rw [speedAlong_comp g ((hγ _ hr).mdifferentiableAt (by norm_num)) hi.differentiableAt,
        hi.deriv, abs_of_pos (inv_pos.mpr (hp _ hr)), inv_mul_cancel₀ (hp _ hr).ne']

/-- The tangential acceleration coefficient of a timelike curve is forced by
metric compatibility; it is not extra reparametrization data. -/
theorem acceleration_factor_eq (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {t k : ℝ} (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : Timelike g (curveVelocity γ t))
    (ha : g.covariantAlong (curveVelocity γ) t = k • curveVelocity γ t) :
    deriv (speedAlong g γ) t / speedAlong g γ t = k := by
  have hp : speedAlong g γ t ≠ 0 := ne_of_gt ((properSpeed_pos_iff g _).mpr hv)
  have hs : speedAlong g γ t ^ 2 =
      -g.form (γ t) (curveVelocity γ t) (curveVelocity γ t) := properSpeed_sq g hv
  rw [(hasDerivAt_speedAlong g hγ hv).deriv, ha, map_smul, smul_apply, smul_eq_mul]
  field_simp
  rw [hs]
  ring

/-- A proper-time inverse eliminates precisely the tangential acceleration term. -/
theorem geodesic_properTime_inverse (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ}
    (hγ : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ) I 2 γ s)
    (hv : ∀ s ∈ Ioo a b, Timelike g (curveVelocity γ s))
    (ha : ∀ s ∈ Ioo a b, g.covariantAlong (curveVelocity γ) s =
      (deriv (speedAlong g γ) s / speedAlong g γ s) • curveVelocity γ s)
    (e : OpenPartialHomeomorph ℝ ℝ) (hsub : e.source ⊆ Ioo a b)
    (hi : ∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧
      HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ) :
    g.IsGeodesicOn e.target (γ ∘ e.symm) := by
  intro τ hτ
  have hr := hsub (e.map_target hτ)
  have hp : speedAlong g γ (e.symm τ) ≠ 0 :=
    ne_of_gt ((properSpeed_pos_iff g _).mpr (hv _ hr))
  have he : deriv e.symm =ᶠ[𝓝 τ] (fun u => (speedAlong g γ (e.symm u))⁻¹) := by
    filter_upwards [e.open_target.mem_nhds hτ] with u hu
    exact (hi u hu).2.deriv
  have hs := ((hasDerivAt_speedAlong g (hγ _ hr) (hv _ hr)).differentiableAt.hasDerivAt.comp τ
    (hi τ hτ).2).inv hp
  have hsecond : deriv (deriv e.symm) τ =
      -(deriv (speedAlong g γ) (e.symm τ) * (speedAlong g γ (e.symm τ))⁻¹) /
        speedAlong g γ (e.symm τ) ^ 2 := by
    rw [he.deriv_eq]
    exact hs.deriv
  refine ⟨(hγ _ hr).comp τ (hi τ hτ).1.contMDiffAt, ?_⟩
  rw [g.covariantAcceleration_reparam (hγ _ hr) (hi τ hτ).1,
    hsecond, (hi τ hτ).2.deriv, ha _ hr, smul_smul, ← add_smul]
  have hz : -(deriv (speedAlong g γ) (e.symm τ) * (speedAlong g γ (e.symm τ))⁻¹) /
        speedAlong g γ (e.symm τ) ^ 2 +
      ((speedAlong g γ (e.symm τ))⁻¹) ^ 2 *
        (deriv (speedAlong g γ) (e.symm τ) / speedAlong g γ (e.symm τ)) = 0 := by ring
  rw [hz, zero_smul]

/-- Native tangential acceleration yields an actual local affine geodesic in
the constructed proper-time parameter. This is a construction, not a
definition of pregeodesic motion that assumes a reparametrization exists. -/
theorem exists_properTime_geodesic_parameter (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b t₀ : ℝ}
    (hγ : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ) I 2 γ s)
    (hv : ∀ s ∈ Ioo a b, Timelike g (curveVelocity γ s))
    (ha : ∀ s ∈ Ioo a b, ∃ k : ℝ,
      g.covariantAlong (curveVelocity γ) s = k • curveVelocity γ s)
    (ht₀ : t₀ ∈ Ioo a b) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = properTime g γ t₀ ∧ t₀ ∈ e.source ∧ e.source ⊆ Ioo a b ∧
      e t₀ = 0 ∧
      (∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧
        HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ ∧
        speedAlong g (γ ∘ e.symm) τ = 1) ∧
      g.IsGeodesicOn e.target (γ ∘ e.symm) := by
  obtain ⟨e, he, he₀, hsub, hzero, hi⟩ := exists_properTime_parameter g hγ hv ht₀
  refine ⟨e, he, he₀, hsub, hzero, hi, geodesic_properTime_inverse g hγ hv ?_ e hsub ?_⟩
  · intro s hs
    obtain ⟨k, hk⟩ := ha s hs
    rw [acceleration_factor_eq g (hγ s hs) (hv s hs) hk]
    exact hk
  · intro τ hτ
    exact ⟨(hi τ hτ).1, (hi τ hτ).2.1⟩

/-- A regular parameter change taking the curve to an affine geodesic forces
the original acceleration to be tangential. -/
theorem tangential_acceleration_of_reparam (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {r : ℝ → ℝ} {τ : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (r τ)) (hr : ContDiffAt ℝ 2 r τ)
    (hn : deriv r τ ≠ 0)
    (ha : g.covariantAlong (curveVelocity (γ ∘ r)) τ = 0) :
    ∃ k : ℝ, g.covariantAlong (curveVelocity γ) (r τ) = k • curveVelocity γ (r τ) := by
  rw [g.covariantAcceleration_reparam hγ hr] at ha
  have h := congrArg (fun v => ((deriv r τ)^2)⁻¹ • v) ha
  simp only [smul_add, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hn), one_smul, smul_zero] at h
  refine ⟨-(((deriv r τ)^2)⁻¹ * deriv (deriv r) τ), ?_⟩
  simpa only [neg_smul] using eq_neg_of_add_eq_zero_right h

end ProjectAInos.GeneralRelativity
