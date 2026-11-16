/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.FlowVariation
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# A given local flow: uniqueness, determinant and volume

`IsLocalFlowOn X Φ Ω` states that `Φ(t, x)` is a family of solutions of
`ẋ = X(x)` on an open set `Ω` of times and initial points, twice continuously
differentiable, with `Φ(0, x) = x`, and such that the times of each initial
point form an interval that contains zero. The family is given; nothing is
constructed here.

For a continuously differentiable `X` on a finite-dimensional space:

* a solution through a point agrees with the family (`IsLocalFlowOn.eq_of_hasDerivAt`),
  and the map `Φ(t, ·)` is injective on its domain;
* `det D_x Φ(t, x) = exp (∫₀ᵗ tr DX(Φ(s, x)) ds)`;
* if `tr DX = 0`, the map `Φ(t, ·)` preserves the measure of every measurable
  set in its domain, and a family defined for all times and points preserves
  the measure (Liouville's theorem for a given flow).
-/

@[expose] public section
noncomputable section

open Set Filter ContinuousLinearMap MeasureTheory
open scoped Topology NNReal

namespace ProjectAInos.SmoothGeometry.NonlinearODE

open LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Uniqueness of solutions of an autonomous equation -/

/-- Two solutions on an interval that agree at its left end agree on it. -/
theorem eqOn_of_hasDerivAt_of_eq_left {X : E → E} (hX : ContDiff ℝ 1 X) {f g : ℝ → E}
    {a b : ℝ} (hf : ∀ r ∈ Icc a b, HasDerivAt f (X (f r)) r)
    (hg : ∀ r ∈ Icc a b, HasDerivAt g (X (g r)) r) (h : f a = g a) : EqOn f g (Icc a b) := by
  have hfc : ContinuousOn f (Icc a b) := fun r hr => (hf r hr).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun r hr => (hg r hr).continuousAt.continuousWithinAt
  have hK : IsCompact (f '' Icc a b ∪ g '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hfc).union (isCompact_Icc.image_of_continuousOn hgc)
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
    hX.locallyLipschitz.locallyLipschitzOn
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => X)
    (s := fun _ => f '' Icc a b ∪ g '' Icc a b) (K := C) (fun _ _ => hC) hfc
    (fun r hr => (hf r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt)
    (fun r hr => Or.inl ⟨r, ⟨hr.1, hr.2.le⟩, rfl⟩) hgc
    (fun r hr => (hg r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt)
    (fun r hr => Or.inr ⟨r, ⟨hr.1, hr.2.le⟩, rfl⟩) h

/-- Two solutions on an interval that agree at its right end agree on it. -/
theorem eqOn_of_hasDerivAt_of_eq_right {X : E → E} (hX : ContDiff ℝ 1 X) {f g : ℝ → E}
    {a b : ℝ} (hf : ∀ r ∈ Icc a b, HasDerivAt f (X (f r)) r)
    (hg : ∀ r ∈ Icc a b, HasDerivAt g (X (g r)) r) (h : f b = g b) : EqOn f g (Icc a b) := by
  have hfc : ContinuousOn f (Icc a b) := fun r hr => (hf r hr).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun r hr => (hg r hr).continuousAt.continuousWithinAt
  have hK : IsCompact (f '' Icc a b ∪ g '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hfc).union (isCompact_Icc.image_of_continuousOn hgc)
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
    hX.locallyLipschitz.locallyLipschitzOn
  exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => X)
    (s := fun _ => f '' Icc a b ∪ g '' Icc a b) (K := C) (fun _ _ => hC) hfc
    (fun r hr => (hf r ⟨hr.1.le, hr.2⟩).hasDerivWithinAt)
    (fun r hr => Or.inl ⟨r, ⟨hr.1.le, hr.2⟩, rfl⟩) hgc
    (fun r hr => (hg r ⟨hr.1.le, hr.2⟩).hasDerivWithinAt)
    (fun r hr => Or.inr ⟨r, ⟨hr.1.le, hr.2⟩, rfl⟩) h

/-- Two solutions between two times that agree at one of them agree at the other. -/
theorem eq_of_hasDerivAt_of_eq {X : E → E} (hX : ContDiff ℝ 1 X) {f g : ℝ → E} {s t : ℝ}
    (hf : ∀ r ∈ uIcc s t, HasDerivAt f (X (f r)) r)
    (hg : ∀ r ∈ uIcc s t, HasDerivAt g (X (g r)) r) (h : f s = g s) : f t = g t := by
  rcases le_total s t with hst | hst
  · rw [uIcc_of_le hst] at hf hg
    exact eqOn_of_hasDerivAt_of_eq_left hX hf hg h ⟨hst, le_rfl⟩
  · rw [uIcc_of_ge hst] at hf hg
    exact eqOn_of_hasDerivAt_of_eq_right hX hf hg h ⟨le_rfl, hst⟩

/-! ### A given local flow -/

/-- `Φ` is a family of solutions of `ẋ = X(x)` on the open set `Ω` of times and
initial points, with `Φ(0, x) = x`. -/
structure IsLocalFlowOn (X : E → E) (Φ : ℝ × E → E) (Ω : Set (ℝ × E)) : Prop where
  /-- The domain is open. -/
  isOpen : IsOpen Ω
  /-- The family is twice continuously differentiable in the time and the point. -/
  contDiffAt : ∀ p ∈ Ω, ContDiffAt ℝ 2 Φ p
  /-- The family solves the equation. -/
  hasDerivAt : ∀ p ∈ Ω, HasDerivAt (fun s => Φ (s, p.2)) (X (Φ p)) p.1
  /-- The times of an initial point form an interval that contains zero. -/
  segment : ∀ p ∈ Ω, ∀ s ∈ uIcc 0 p.1, (s, p.2) ∈ Ω
  /-- At time zero the family is the identity. -/
  initial : ∀ p ∈ Ω, Φ (0, p.2) = p.2

/-- A constant vector field: the translations `x ↦ x + t v` are a flow for all
times and points. -/
theorem isLocalFlowOn_translation (v : E) :
    IsLocalFlowOn (fun _ => v) (fun p : ℝ × E => p.2 + p.1 • v) univ where
  isOpen := isOpen_univ
  contDiffAt _ _ := (contDiff_snd.add (contDiff_fst.smul contDiff_const)).contDiffAt
  hasDerivAt p _ := by
    simpa using ((hasDerivAt_id p.1).smul_const v).const_add p.2
  segment _ _ _ _ := mem_univ _
  initial p _ := by simp

namespace IsLocalFlowOn

variable {X : E → E} {Φ : ℝ × E → E} {Ω : Set (ℝ × E)}

theorem zero_mem (h : IsLocalFlowOn X Φ Ω) {p : ℝ × E} (hp : p ∈ Ω) : (0, p.2) ∈ Ω :=
  h.segment p hp 0 left_mem_uIcc

theorem differentiableAt (h : IsLocalFlowOn X Φ Ω) {p : ℝ × E} (hp : p ∈ Ω) :
    DifferentiableAt ℝ Φ p := (h.contDiffAt p hp).differentiableAt (by simp)

theorem eventually_hasDerivAt (h : IsLocalFlowOn X Φ Ω) {p : ℝ × E} (hp : p ∈ Ω) :
    ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => Φ (s, q.2)) (X (Φ q)) q.1 :=
  Filter.eventually_of_mem (h.isOpen.mem_nhds hp) fun q hq => h.hasDerivAt q hq

/-- The derivative in the initial point. -/
theorem hasFDerivAt (h : IsLocalFlowOn X Φ Ω) {t : ℝ} {x : E} (hp : (t, x) ∈ Ω) :
    HasFDerivAt (fun y => Φ (t, y)) (fderiv ℝ (fun y => Φ (t, y)) x) x :=
  (hasFDerivAt_slice (h.differentiableAt hp)).differentiableAt.hasFDerivAt

/-- The variational equation along a solution of the family. -/
theorem hasDerivAt_fderiv (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) {t : ℝ} {x : E}
    (hp : (t, x) ∈ Ω) :
    HasDerivAt (fun s => fderiv ℝ (fun y => Φ (s, y)) x)
      (fderiv ℝ X (Φ (t, x)) ∘L fderiv ℝ (fun y => Φ (t, y)) x) t :=
  hasDerivAt_fderiv_of_isLocalFlow (h.contDiffAt _ hp)
    ((hX.differentiable one_ne_zero) _) (h.eventually_hasDerivAt hp)

/-- At time zero the derivative in the initial point is the identity. -/
theorem fderiv_zero (h : IsLocalFlowOn X Φ Ω) {x : E} (hx : (0, x) ∈ Ω) :
    fderiv ℝ (fun y => Φ (0, y)) x = ContinuousLinearMap.id ℝ E := by
  have hc : Tendsto (fun y : E => ((0 : ℝ), y)) (𝓝 x) (𝓝 (0, x)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : (fun y => Φ (0, y)) =ᶠ[𝓝 x] id := by
    filter_upwards [hc.eventually (h.isOpen.mem_nhds hx)] with y hy
    exact h.initial (0, y) hy
  rw [hev.fderiv_eq]
  exact fderiv_id

/-- A solution through a point of the domain is the solution of the family. -/
theorem eq_of_hasDerivAt (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) {t : ℝ} {x : E}
    (hp : (t, x) ∈ Ω) {y : ℝ → E} (hy : ∀ r ∈ uIcc 0 t, HasDerivAt y (X (y r)) r)
    (h0 : y 0 = x) : y t = Φ (t, x) :=
  eq_of_hasDerivAt_of_eq (g := fun s => Φ (s, x)) hX hy
    (fun r hr => h.hasDerivAt (r, x) (h.segment _ hp r hr)) (h0.trans (h.initial _ hp).symm)

/-- The map `Φ(t, ·)` is injective on its domain. -/
theorem injOn (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) {t : ℝ} {A : Set E}
    (hA : ∀ x ∈ A, (t, x) ∈ Ω) : InjOn (fun x => Φ (t, x)) A := by
  intro x hx y hy hxy
  have hfx : ∀ r ∈ uIcc t 0, HasDerivAt (fun s => Φ (s, x)) (X (Φ (r, x))) r := fun r hr =>
    h.hasDerivAt (r, x) (h.segment _ (hA x hx) r (by rwa [uIcc_comm]))
  have hfy : ∀ r ∈ uIcc t 0, HasDerivAt (fun s => Φ (s, y)) (X (Φ (r, y))) r := fun r hr =>
    h.hasDerivAt (r, y) (h.segment _ (hA y hy) r (by rwa [uIcc_comm]))
  have h0 := eq_of_hasDerivAt_of_eq hX hfx hfy hxy
  change Φ (0, x) = Φ (0, y) at h0
  rwa [h.initial _ (hA x hx), h.initial _ (hA y hy)] at h0

/-- A flow defined for all times and points is a group of maps. -/
theorem apply_add (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) (hΩ : Ω = univ) (s t : ℝ)
    (x : E) : Φ (s + t, x) = Φ (s, Φ (t, x)) := by
  have hmem : ∀ p : ℝ × E, p ∈ Ω := fun p => hΩ ▸ mem_univ p
  have hy : ∀ r ∈ uIcc 0 s, HasDerivAt (fun u => Φ (u + t, x)) (X (Φ (r + t, x))) r :=
    fun r _ => (h.hasDerivAt (r + t, x) (hmem _)).comp_add_const r t
  have h0 : (fun u => Φ (u + t, x)) 0 = Φ (t, x) := by simp
  exact h.eq_of_hasDerivAt hX (hmem (s, Φ (t, x))) hy h0

end IsLocalFlowOn

/-! ### Determinant and volume in finite dimension -/

section FiniteDimensional

variable [CompleteSpace E] [FiniteDimensional ℝ E] {X : E → E} {Φ : ℝ × E → E}
  {Ω : Set (ℝ × E)}

namespace IsLocalFlowOn

/-- The determinant of the derivative in the initial point:
`det D_x Φ(t, x) = exp (∫₀ᵗ tr DX(Φ(s, x)) ds)`. -/
theorem det_fderiv (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) {t : ℝ} {x : E}
    (hp : (t, x) ∈ Ω) :
    LinearMap.det (fderiv ℝ (fun y => Φ (t, y)) x : E →ₗ[ℝ] E) =
      Real.exp (∫ s in 0..t, traceCLM (fderiv ℝ X (Φ (s, x)))) := by
  have hcurve : ContinuousOn (fun s => Φ (s, x)) (uIcc 0 t) := fun s hs =>
    (h.hasDerivAt (s, x) (h.segment _ hp s hs)).continuousAt.continuousWithinAt
  -- the coefficient along the solution, continued by its values at the two ends
  let c : ℝ → ℝ := fun s => projIcc (min 0 t) (max 0 t) min_le_max s
  have hcmem : ∀ s, c s ∈ uIcc 0 t := fun s => (projIcc (min 0 t) (max 0 t) min_le_max s).2
  have hcid : ∀ s ∈ uIcc 0 t, c s = s := fun s hs => by
    change ((projIcc (min 0 t) (max 0 t) min_le_max s : Icc (min 0 t) (max 0 t)) : ℝ) = s
    rw [projIcc_of_mem min_le_max hs]
  have hccont : Continuous c := continuous_subtype_val.comp continuous_projIcc
  let A : C(ℝ, E →L[ℝ] E) := ⟨fun s => fderiv ℝ X (Φ (c s, x)),
    (hX.continuous_fderiv one_ne_zero).comp (hcurve.comp_continuous hccont hcmem)⟩
  have hdet := det_eq_det_mul_exp_integral_trace A
    (M := fun s => fderiv ℝ (fun y => Φ (s, y)) x) (s := 0) (t := t)
    (fun s hs =>
      (h.hasDerivAt_fderiv hX (h.segment _ hp s hs)).continuousAt.continuousWithinAt)
    (fun r hr => by
      have hr' : r ∈ uIcc 0 t := Ioo_subset_Icc_self hr
      have hv := h.hasDerivAt_fderiv hX (h.segment _ hp r hr')
      change HasDerivAt _ (fderiv ℝ X (Φ (c r, x)) ∘L _) r
      rw [hcid r hr']
      exact hv)
  rw [hdet, h.fderiv_zero (h.zero_mem hp)]
  have hid : LinearMap.det ((ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 :=
    LinearMap.det_id
  rw [hid, mul_one]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  change traceCLM (fderiv ℝ X (Φ (c s, x))) = _
  rw [hcid s hs]

/-- If the field has divergence zero the derivative in the initial point has
determinant one. -/
theorem det_fderiv_eq_one (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X)
    (hdiv : ∀ x, traceCLM (fderiv ℝ X x) = 0) {t : ℝ} {x : E} (hp : (t, x) ∈ Ω) :
    LinearMap.det (fderiv ℝ (fun y => Φ (t, y)) x : E →ₗ[ℝ] E) = 1 := by
  rw [h.det_fderiv hX hp]
  simp [hdiv]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Liouville's theorem for a given flow: if the field has divergence zero, the
map `Φ(t, ·)` preserves the measure of every measurable set in its domain. -/
theorem measure_image (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X)
    (hdiv : ∀ x, traceCLM (fderiv ℝ X x) = 0) {t : ℝ} {A : Set E} (hA : MeasurableSet A)
    (hAΩ : ∀ x ∈ A, (t, x) ∈ Ω) : μ ((fun x => Φ (t, x)) '' A) = μ A := by
  have h1 := lintegral_abs_det_fderiv_eq_addHaar_image μ hA (f := fun x => Φ (t, x))
    (f' := fun x => fderiv ℝ (fun y => Φ (t, y)) x)
    (fun x hx => (h.hasFDerivAt (hAΩ x hx)).hasFDerivWithinAt) (h.injOn hX hAΩ)
  rw [← h1]
  have hone : ∀ x ∈ A, ENNReal.ofReal |(fderiv ℝ (fun y => Φ (t, y)) x).det| = 1 := by
    intro x hx
    have hd : (fderiv ℝ (fun y => Φ (t, y)) x).det = 1 :=
      h.det_fderiv_eq_one hX hdiv (hAΩ x hx)
    rw [hd]
    simp
  rw [setLIntegral_congr_fun hA hone, setLIntegral_one]

/-- Liouville's theorem: a flow of a field of divergence zero, defined for all
times and points, preserves the measure. -/
theorem measurePreserving (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X)
    (hdiv : ∀ x, traceCLM (fderiv ℝ X x) = 0) (hΩ : Ω = univ) (t : ℝ) :
    MeasurePreserving (fun x => Φ (t, x)) μ μ := by
  have hmem : ∀ p : ℝ × E, p ∈ Ω := fun p => hΩ ▸ mem_univ p
  have hfwd : Function.LeftInverse (fun x => Φ (t, x)) (fun x => Φ (-t, x)) := fun x => by
    have e := h.apply_add hX hΩ t (-t) x
    rw [add_neg_cancel] at e
    exact e.symm.trans (h.initial (-t, x) (hmem _))
  have hbwd : Function.RightInverse (fun x => Φ (t, x)) (fun x => Φ (-t, x)) := fun x => by
    have e := h.apply_add hX hΩ (-t) t x
    rw [neg_add_cancel] at e
    exact e.symm.trans (h.initial (t, x) (hmem _))
  have hcont : Continuous fun x => Φ (t, x) :=
    continuous_iff_continuousAt.mpr fun x => (h.hasFDerivAt (hmem (t, x))).continuousAt
  refine ⟨hcont.measurable, ?_⟩
  ext B hB
  rw [Measure.map_apply hcont.measurable hB,
    ← congrFun (image_eq_preimage_of_inverse hfwd hbwd) B]
  exact h.measure_image μ hX hdiv hB fun x _ => hmem _

end IsLocalFlowOn

end FiniteDimensional

/-! ### The flow of a linear field -/

section Linear

variable [CompleteSpace E]

theorem contDiff_propagator_const (A₀ : E →L[ℝ] E) :
    ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E => propagator (ContinuousMap.const ℝ A₀) p.1 0 := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (ContinuousMap.const ℝ A₀ : ℝ → E →L[ℝ] E) := by
    rw [ContinuousMap.coe_const]
    exact contDiff_const
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E => (p.1, (0 : ℝ)) :=
    contDiff_fst.prodMk contDiff_const
  exact ContDiff.comp (g := fun q : ℝ × ℝ => propagator (ContinuousMap.const ℝ A₀) q.1 q.2)
    (f := fun p : ℝ × E => (p.1, (0 : ℝ))) (propagator_contDiff_of_contDiff hA) h2

theorem contDiff_propagator_const_apply (A₀ : E →L[ℝ] E) :
    ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E => propagator (ContinuousMap.const ℝ A₀) p.1 0 p.2 :=
  ContDiff.clm_apply (f := fun p : ℝ × E => propagator (ContinuousMap.const ℝ A₀) p.1 0)
    (g := fun p : ℝ × E => p.2) (contDiff_propagator_const A₀) contDiff_snd

theorem hasDerivAt_propagator_const_apply (A₀ : E →L[ℝ] E) (t : ℝ) (x : E) :
    HasDerivAt (fun s => propagator (ContinuousMap.const ℝ A₀) s 0 x)
      (A₀ (propagator (ContinuousMap.const ℝ A₀) t 0 x)) t := by
  have h := hasDerivAt_propagator_apply (ContinuousMap.const ℝ A₀) t 0 x
  rwa [ContinuousMap.const_apply] at h

/-- The propagator of a constant coefficient is the flow of the linear field. -/
theorem isLocalFlowOn_linear (A₀ : E →L[ℝ] E) :
    IsLocalFlowOn (fun x => A₀ x)
      (fun p : ℝ × E => propagator (ContinuousMap.const ℝ A₀) p.1 0 p.2) univ where
  isOpen := isOpen_univ
  contDiffAt _ _ := ((contDiff_propagator_const_apply A₀).of_le (by simp)).contDiffAt
  hasDerivAt p _ := hasDerivAt_propagator_const_apply A₀ p.1 p.2
  segment _ _ _ _ := mem_univ _
  initial p _ := by
    change propagator (ContinuousMap.const ℝ A₀) 0 0 p.2 = p.2
    rw [propagator_self]
    rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- The flow of a linear field of trace zero preserves the volume. -/
theorem measurePreserving_propagator_const (A₀ : E →L[ℝ] E) (hA : traceCLM A₀ = 0)
    (t : ℝ) :
    MeasurePreserving (fun x => propagator (ContinuousMap.const ℝ A₀) t 0 x) μ μ :=
  (isLocalFlowOn_linear A₀).measurePreserving μ A₀.contDiff
    (fun x => by rw [A₀.fderiv]; exact hA) rfl t

end Linear

end ProjectAInos.SmoothGeometry.NonlinearODE
