/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Optics.Basic
public import ProjectAinos.Mechanics.EndpointAction
public import ProjectAinos.SmoothGeometry.Euclidean.Similarity
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Image formation with broad bundles of rays

Landau–Lifshitz, *The Classical Theory of Fields*, §57. A ray of a medium `n` is a path with
nonvanishing velocity that solves the Euler–Lagrange equation of the optical Lagrangian
`n(q) |v|`, whose action is `Optics.opticalLength`. The Lagrangian is smooth only away from
`v = 0`, so the families of rays are smooth on an open set of the jet space with `v ≠ 0`. Smooth
families of rays are data, and stigmatic imaging is a hypothesis.

* `hasDerivAt_opticalLength`: the first variation of the optical length along a smooth family of
  rays with moving end points is the boundary term `n(r′) ⟨t̂′, δr′⟩ − n(r) ⟨t̂, δr⟩`, from
  `Mechanics.hasDerivAt_action_movingEndpoints_on`; the energy of the optical Lagrangian is `0`.
* `opticalLength_eq`: a smooth family of rays from a point `P` to its image `P′` has a constant
  optical length. `opticalLength_segmentFamily` is the instance of the reparametrized segments of
  a homogeneous medium.
* `eikonal_variation_eq` and `sine_condition`: for stigmatic imaging of an object element the
  boundary term is the same for every ray of the bundle; comparison with the axial ray gives
  Abbe's sine condition `n ⟨t̂, δr⟩ = n′ ⟨t̂′, δr′⟩`, that is `n y sin θ = n′ y′ sin θ′`.
  `sine_condition_shiftedSegment` is a degenerate instance of their hypotheses.
* `IsAbsoluteInstrument`: stigmatic imaging of an object region `Ω` by a map `φ` with the eikonal
  `ψ`, recorded through the rays along every direction at every object point (Maxwell's tangent
  rays). `IsAbsoluteInstrument.norm_fderiv_eq` gives `n′ |Dφ(x) v| = n |v|` and
  `IsAbsoluteInstrument.opticalLength_curve_eq` the equality of the optical lengths of an object
  curve and its image (Maxwell's theorem). `isAbsoluteInstrument_id` is the trivial instance.
* `isSimilarity_of_absolute`: Carathéodory's theorem, from `SmoothGeometry.Similarity`. A `C²`
  map with `n′ |Dφ(x) v| = n |v|` on a connected open set is `x ↦ (n/n′) L x + c` with a linear
  isometry `L`. `IsAbsoluteInstrument.isSimilarity` applies it to an absolute instrument;
  `isSimilarity_reflection` is the plane mirror, with `n = n′`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace ProjectAinos.Electrodynamics.Optics.Imaging

section Similarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Carathéodory's theorem** (§57), from `SmoothGeometry.Similarity`. A twice continuously
differentiable map whose derivative multiplies every length by `n/n′` on a connected open set,
`n′ |Dφ(x) v| = n |v|`, is a similarity of ratio `n/n′` there: `φ(x) = (n/n′) L x + c` with a
linear isometry `L`. -/
theorem isSimilarity_of_absolute {n n' : ℝ} (hn : 0 < n) (hn' : 0 < n') {φ : E → E}
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hφ : ContDiffOn ℝ 2 φ Ω)
    (hiso : ∀ x ∈ Ω, ∀ v, n' * ‖fderiv ℝ φ x v‖ = n * ‖v‖) :
    ∃ (L : E ≃ₗᵢ[ℝ] E) (c : E), ∀ x ∈ Ω, φ x = (n / n') • L x + c :=
  SmoothGeometry.Similarity.exists_linearIsometryEquiv_of_norm_fderiv hn hn' hΩ hΩc hφ hiso

/-- The plane mirror, the reflection in a subspace `K`, as an instance of
`isSimilarity_of_absolute` with `n = n′` on the whole space. -/
theorem isSimilarity_reflection (K : Submodule ℝ E) [K.HasOrthogonalProjection] {n : ℝ}
    (hn : 0 < n) : ∃ (L : E ≃ₗᵢ[ℝ] E) (c : E), ∀ x, K.reflection x = (n / n) • L x + c := by
  obtain ⟨L, c, h⟩ := isSimilarity_of_absolute hn hn isOpen_univ isPreconnected_univ
    (SmoothGeometry.Similarity.contDiff_reflection K).contDiffOn fun x _ v =>
      SmoothGeometry.Similarity.norm_fderiv_reflection K n x v
  exact ⟨L, c, fun x => h x (mem_univ x)⟩

end Similarity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Rays

/-- The Lagrangian `n(q) |v|` of Fermat's principle, whose action is the optical length. -/
def opticalLagrangian (n : E3 → ℝ) : Mechanics.Lagrangian E3 := fun _ z => n z.1 * ‖z.2‖

/-- The action of `opticalLagrangian n` is the optical length. -/
theorem action_opticalLagrangian (n : E3 → ℝ) (γ : ℝ → E3) (a b : ℝ) :
    Mechanics.action a b (opticalLagrangian n) γ = opticalLength n γ a b := rfl

/-- The unit tangent `γ′/|γ′|` of a path. -/
def unitTangent (γ : ℝ → E3) (t : ℝ) : E3 := ‖deriv γ t‖⁻¹ • deriv γ t

/-- A ray of the medium `n` on `[a, b]`: a path with nonvanishing velocity that solves the
Euler–Lagrange equation of the optical length. -/
structure IsRay (n : E3 → ℝ) (γ : ℝ → E3) (a b : ℝ) : Prop where
  deriv_ne_zero : ∀ t ∈ uIcc a b, deriv γ t ≠ 0
  eulerLagrange_eq_zero : ∀ t ∈ uIcc a b,
    Mechanics.eulerLagrange (opticalLagrangian n) γ t = 0

/-- The derivative of the norm away from the origin, `D|·|(v) = ⟨v, ·⟩/|v|`. -/
theorem hasFDerivAt_norm {v : E3} (hv : v ≠ 0) :
    HasFDerivAt (fun z : E3 => ‖z‖) (‖v‖⁻¹ • innerSL ℝ v) v := by
  have h := (hasStrictFDerivAt_norm_sq v).hasFDerivAt.sqrt
    (by simpa using norm_ne_zero_iff.mpr hv)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  refine h.congr_fderiv ?_
  ext w
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, two_smul, add_apply]
  field_simp
  ring

/-- The derivative of the optical Lagrangian at a point `(q, v)` with `v ≠ 0`. -/
theorem hasFDerivAt_opticalLagrangian {n : E3 → ℝ} {q v : E3} (hn : DifferentiableAt ℝ n q)
    (hv : v ≠ 0) (t : ℝ) :
    HasFDerivAt (opticalLagrangian n t)
      (n q • (‖v‖⁻¹ • innerSL ℝ v).comp (ContinuousLinearMap.snd ℝ E3 E3) +
        ‖v‖ • (fderiv ℝ n q).comp (ContinuousLinearMap.fst ℝ E3 E3)) (q, v) := by
  have h1 : HasFDerivAt (fun z : E3 × E3 => n z.1)
      ((fderiv ℝ n q).comp (ContinuousLinearMap.fst ℝ E3 E3)) (q, v) :=
    hn.hasFDerivAt.comp (q, v) (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun z : E3 × E3 => ‖z.2‖)
      ((‖v‖⁻¹ • innerSL ℝ v).comp (ContinuousLinearMap.snd ℝ E3 E3)) (q, v) :=
    (hasFDerivAt_norm hv).comp (q, v) (hasFDerivAt_snd)
  exact h1.mul h2

/-- The momentum of the optical Lagrangian is `n ⟨t̂, ·⟩`, with the unit tangent `t̂`. -/
theorem momentum_opticalLagrangian {n : E3 → ℝ} {γ : ℝ → E3} {t : ℝ}
    (hn : DifferentiableAt ℝ n (γ t)) (hγ : deriv γ t ≠ 0) :
    Mechanics.momentum (opticalLagrangian n) γ t = n (γ t) • innerSL ℝ (unitTangent γ t) := by
  rw [Mechanics.momentum, (hasFDerivAt_opticalLagrangian hn hγ t).fderiv]
  ext w
  simp [unitTangent]

/-- The force of the optical Lagrangian is `|γ′| Dn`. -/
theorem force_opticalLagrangian {n : E3 → ℝ} {γ : ℝ → E3} {t : ℝ}
    (hn : DifferentiableAt ℝ n (γ t)) (hγ : deriv γ t ≠ 0) :
    Mechanics.force (opticalLagrangian n) γ t = ‖deriv γ t‖ • fderiv ℝ n (γ t) := by
  rw [Mechanics.force, (hasFDerivAt_opticalLagrangian hn hγ t).fderiv]
  ext w
  simp

/-- The jets `(t, q, v)` with `q ∈ V` and `v ≠ 0` form an open set. -/
theorem isOpen_rayJets {V : Set E3} (hV : IsOpen V) :
    IsOpen {p : ℝ × (E3 × E3) | p.2.1 ∈ V ∧ p.2.2 ≠ 0} :=
  (hV.prod isOpen_compl_singleton).preimage continuous_snd

/-- The optical Lagrangian is smooth at the jets `(t, q, v)` with `q ∈ V` and `v ≠ 0`, for a
medium that is smooth on the open set `V`. -/
theorem contDiffOn_opticalLagrangian {n : E3 → ℝ} {V : Set E3} (hV : IsOpen V)
    (hn : ContDiffOn ℝ ∞ n V) :
    ContDiffOn ℝ ∞ (Function.uncurry (opticalLagrangian n))
      {p : ℝ × (E3 × E3) | p.2.1 ∈ V ∧ p.2.2 ≠ 0} := by
  intro p hp
  have h1 : ContDiffAt ℝ ∞ (fun p : ℝ × (E3 × E3) => n p.2.1) p :=
    (hn.contDiffAt (hV.mem_nhds hp.1)).comp p (contDiff_fst.comp contDiff_snd).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun p : ℝ × (E3 × E3) => ‖p.2.2‖) p :=
    (contDiffAt_norm ℝ hp.2).comp p (contDiff_snd.comp contDiff_snd).contDiffAt
  exact (h1.mul h2).contDiffWithinAt

/-- A smooth family of paths `γ(s, t)` whose path `γ(s₀, ·)` is a ray on `[a, b]` of the medium
`n` inside the set `V`: the family is smooth on an open set that contains the segment
`{s₀} × [a, b]`. -/
structure IsRayFamily (n : E3 → ℝ) (V : Set E3) (γ : ℝ × ℝ → E3) (a b s₀ : ℝ) : Prop where
  smooth : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ ContDiffOn ℝ ∞ γ U ∧ ∀ t ∈ uIcc a b, (s₀, t) ∈ U
  mem : ∀ t ∈ uIcc a b, γ (s₀, t) ∈ V
  isRay : IsRay n (fun t => γ (s₀, t)) a b

/-- **The first variation of the optical length with moving end points.** Let `γ(s, t)` be a
smooth family of paths whose path `γ(s₀, ·)` is a ray on `[a, b]` of a medium `n` that is smooth
on an open set `V`. The derivative of the optical length in `s` is the boundary term
`n(r′) ⟨t̂′, δr′⟩ − n(r) ⟨t̂, δr⟩`, with the end points `r = γ(s₀, a)`, `r′ = γ(s₀, b)`, their
displacements `δr = ∂ₛγ(s₀, a)`, `δr′ = ∂ₛγ(s₀, b)` and the unit tangents `t̂`, `t̂′` of the ray
there. The energy `p · γ′ − n |γ′|` of the optical Lagrangian vanishes, so the formula holds for
every parametrization of the rays. -/
theorem hasDerivAt_opticalLength {n : E3 → ℝ} {V : Set E3} (hV : IsOpen V)
    (hn : ContDiffOn ℝ ∞ n V) {γ : ℝ × ℝ → E3} {a b s₀ : ℝ} (hγ : IsRayFamily n V γ a b s₀) :
    HasDerivAt (fun s => opticalLength n (fun t => γ (s, t)) a b)
      (n (γ (s₀, b)) * ⟪unitTangent (fun t => γ (s₀, t)) b, deriv (fun s => γ (s, b)) s₀⟫ -
        n (γ (s₀, a)) * ⟪unitTangent (fun t => γ (s₀, t)) a, deriv (fun s => γ (s, a)) s₀⟫)
      s₀ := by
  obtain ⟨U, hU, hγU, hsU⟩ := hγ.smooth
  have h := Mechanics.hasDerivAt_action_movingEndpoints_on (isOpen_rayJets hV)
    (contDiffOn_opticalLagrangian hV hn) hU hγU (a := fun _ => a) (b := fun _ => b)
    (hasDerivAt_const s₀ a) (hasDerivAt_const s₀ b) hsU
    (fun t ht => ⟨hγ.mem t ht, hγ.isRay.deriv_ne_zero t ht⟩) hγ.isRay.eulerLagrange_eq_zero
  have hnd : ∀ t ∈ uIcc a b, DifferentiableAt ℝ n (γ (s₀, t)) := fun t ht =>
    (hn.contDiffAt (hV.mem_nhds (hγ.mem t ht))).differentiableAt (by simp)
  rw [momentum_opticalLagrangian (hnd b right_mem_uIcc)
      (hγ.isRay.deriv_ne_zero b right_mem_uIcc),
    momentum_opticalLagrangian (hnd a left_mem_uIcc)
      (hγ.isRay.deriv_ne_zero a left_mem_uIcc)] at h
  simp only [mul_zero, sub_zero, FunLike.coe_smul, Pi.smul_apply,
    innerSL_apply_apply, smul_eq_mul, action_opticalLagrangian] at h
  exact h

/-- **The optical length of the rays between a point and its image** (§57). If a smooth family
of rays `γ(ε, ·)` of a smooth medium joins a point `P` to its image `P′` for every parameter `ε`
of a connected open set `I`, all these rays have the same optical length: its derivative in `ε`
is the boundary term of the first variation, which vanishes for fixed end points. -/
theorem opticalLength_eq {n : E3 → ℝ} {V : Set E3} (hV : IsOpen V) (hn : ContDiffOn ℝ ∞ n V)
    {γ : ℝ × ℝ → E3} {I : Set ℝ} (hIo : IsOpen I) (hIc : IsPreconnected I) {a b : ℝ}
    (hγ : ∀ ε ∈ I, IsRayFamily n V γ a b ε) {P P' : E3}
    (hP : ∀ ε ∈ I, γ (ε, a) = P) (hP' : ∀ ε ∈ I, γ (ε, b) = P') {ε₁ ε₂ : ℝ} (h₁ : ε₁ ∈ I)
    (h₂ : ε₂ ∈ I) :
    opticalLength n (fun t => γ (ε₁, t)) a b = opticalLength n (fun t => γ (ε₂, t)) a b := by
  have hd : ∀ ε ∈ I, HasDerivAt (fun s => opticalLength n (fun t => γ (s, t)) a b) 0 ε := by
    intro ε hε
    have h := hasDerivAt_opticalLength hV hn (hγ ε hε)
    have hc : ∀ (c : ℝ) (Q : E3), (∀ s ∈ I, γ (s, c) = Q) →
        deriv (fun s => γ (s, c)) ε = 0 := by
      intro c Q hQ
      rw [Filter.EventuallyEq.deriv_eq (f := fun _ => Q)
        (Filter.eventually_of_mem (hIo.mem_nhds hε) hQ)]
      exact deriv_const ε Q
    rw [hc a P hP, hc b P' hP'] at h
    simpa using h
  exact hIo.is_const_of_deriv_eq_zero hIc
    (fun ε hε => (hd ε hε).differentiableAt.differentiableWithinAt)
    (fun ε hε => (hd ε hε).deriv) h₁ h₂

/-- **The variation of the eikonal is the same for all rays of a stigmatic bundle** (§57). Two
smooth families of rays `γ₁`, `γ₂` of a smooth medium `N` join the points `r(s)` of an object
element to the points `r′(s)` of its image. If the imaging is stigmatic, so that the two rays have
the same optical length for every `s` near `s₀`, the boundary terms of their first variations
agree: `N(r′) ⟨t̂′₁, δr′⟩ − N(r) ⟨t̂₁, δr⟩ = N(r′) ⟨t̂′₂, δr′⟩ − N(r) ⟨t̂₂, δr⟩`. -/
theorem eikonal_variation_eq {N : E3 → ℝ} {V : Set E3} (hV : IsOpen V)
    (hN : ContDiffOn ℝ ∞ N V) {γ₁ γ₂ : ℝ × ℝ → E3} {a b s₀ : ℝ}
    (hγ₁ : IsRayFamily N V γ₁ a b s₀) (hγ₂ : IsRayFamily N V γ₂ a b s₀) {r r' : ℝ → E3}
    (hr₁ : (fun s => γ₁ (s, a)) =ᶠ[𝓝 s₀] r) (hr₁' : (fun s => γ₁ (s, b)) =ᶠ[𝓝 s₀] r')
    (hr₂ : (fun s => γ₂ (s, a)) =ᶠ[𝓝 s₀] r) (hr₂' : (fun s => γ₂ (s, b)) =ᶠ[𝓝 s₀] r')
    (hstig : ∀ᶠ s in 𝓝 s₀, opticalLength N (fun t => γ₁ (s, t)) a b =
      opticalLength N (fun t => γ₂ (s, t)) a b) :
    N (r' s₀) * ⟪unitTangent (fun t => γ₁ (s₀, t)) b, deriv r' s₀⟫ -
        N (r s₀) * ⟪unitTangent (fun t => γ₁ (s₀, t)) a, deriv r s₀⟫ =
      N (r' s₀) * ⟪unitTangent (fun t => γ₂ (s₀, t)) b, deriv r' s₀⟫ -
        N (r s₀) * ⟪unitTangent (fun t => γ₂ (s₀, t)) a, deriv r s₀⟫ := by
  have h₁ := hasDerivAt_opticalLength hV hN hγ₁
  have h₂ := hasDerivAt_opticalLength hV hN hγ₂
  have h := (h₁.congr_of_eventuallyEq (hstig.mono fun s hs => hs.symm)).unique h₂
  rw [hr₁.deriv_eq, hr₁'.deriv_eq, hr₂.deriv_eq, hr₂'.deriv_eq, hr₁.eq_of_nhds,
    hr₁'.eq_of_nhds, hr₂.eq_of_nhds, hr₂'.eq_of_nhds] at h
  exact h

/-- **Abbe's sine condition** (§57). Let the imaging of an object element by a smooth medium `N`
be stigmatic, as in `eikonal_variation_eq`, with a ray `γ₁` of the broad bundle and the axial ray
`γ₂`, which is normal to the object element at `r` and to its image at `r′`. If the index is `n`
at the object point and `n′` at the image point, then `n ⟨t̂₁, δr⟩ = n′ ⟨t̂′₁, δr′⟩`. For a
displacement `δr = y e` across the axis and a ray in the plane of the axis and `e` that makes the
angle `θ` with the axis, `⟨t̂₁, δr⟩ = y sin θ`, and the identity is `n y sin θ = n′ y′ sin θ′`. -/
theorem sine_condition {N : E3 → ℝ} {V : Set E3} (hV : IsOpen V)
    (hN : ContDiffOn ℝ ∞ N V) {γ₁ γ₂ : ℝ × ℝ → E3} {a b s₀ : ℝ}
    (hγ₁ : IsRayFamily N V γ₁ a b s₀) (hγ₂ : IsRayFamily N V γ₂ a b s₀) {r r' : ℝ → E3}
    (hr₁ : (fun s => γ₁ (s, a)) =ᶠ[𝓝 s₀] r) (hr₁' : (fun s => γ₁ (s, b)) =ᶠ[𝓝 s₀] r')
    (hr₂ : (fun s => γ₂ (s, a)) =ᶠ[𝓝 s₀] r) (hr₂' : (fun s => γ₂ (s, b)) =ᶠ[𝓝 s₀] r')
    (hstig : ∀ᶠ s in 𝓝 s₀, opticalLength N (fun t => γ₁ (s, t)) a b =
      opticalLength N (fun t => γ₂ (s, t)) a b)
    (haxis : ⟪unitTangent (fun t => γ₂ (s₀, t)) a, deriv r s₀⟫ = 0)
    (haxis' : ⟪unitTangent (fun t => γ₂ (s₀, t)) b, deriv r' s₀⟫ = 0) {n n' : ℝ}
    (hn : N (r s₀) = n) (hn' : N (r' s₀) = n') :
    n * ⟪unitTangent (fun t => γ₁ (s₀, t)) a, deriv r s₀⟫ =
      n' * ⟪unitTangent (fun t => γ₁ (s₀, t)) b, deriv r' s₀⟫ := by
  have h := eikonal_variation_eq hV hN hγ₁ hγ₂ hr₁ hr₁' hr₂ hr₂' hstig
  rw [haxis, haxis', hn, hn'] at h
  linarith

/-- In a homogeneous medium a straight path `P + h(t) w` that moves forward, `h′ > 0`, is a ray. -/
theorem isRay_const {n₀ : ℝ} {P w : E3} (hw : w ≠ 0) {h h' : ℝ → ℝ}
    (hh : ∀ t, HasDerivAt h (h' t) t) (hh' : Continuous h') {a b : ℝ}
    (hpos : ∀ t ∈ uIcc a b, 0 < h' t) : IsRay (fun _ => n₀) (fun t => P + h t • w) a b := by
  have hd : ∀ t, deriv (fun t => P + h t • w) t = h' t • w := fun t =>
    (((hh t).smul_const w).const_add P).deriv
  have hne : ∀ t, 0 < h' t → deriv (fun t => P + h t • w) t ≠ 0 := fun t ht => by
    rw [hd t]
    exact smul_ne_zero ht.ne' hw
  refine ⟨fun t ht => hne t (hpos t ht), fun t ht => ?_⟩
  have hmom : Mechanics.momentum (opticalLagrangian fun _ => n₀) (fun t => P + h t • w)
      =ᶠ[𝓝 t] fun _ => n₀ • innerSL ℝ (‖w‖⁻¹ • w) := by
    filter_upwards [hh'.continuousAt.eventually (lt_mem_nhds (hpos t ht))] with t' ht'
    rw [momentum_opticalLagrangian (differentiableAt_const n₀) (hne t' ht'), unitTangent,
      hd t', norm_smul, Real.norm_of_nonneg ht'.le, smul_smul, mul_inv_rev, mul_assoc,
      inv_mul_cancel₀ ht'.ne', mul_one]
  rw [Mechanics.eulerLagrange, force_opticalLagrangian (differentiableAt_const n₀)
    (hne t (hpos t ht)), hmom.deriv_eq, deriv_const, fderiv_fun_const, Pi.zero_apply,
    smul_zero, sub_zero]

/-- The parametrizations `P + (t + ε t (1 − t)) (P′ − P)` of the segment from `P` to `P′`. -/
def segmentFamily (P P' : E3) (p : ℝ × ℝ) : E3 :=
  P + (p.2 + p.1 * (p.2 * (1 - p.2))) • (P' - P)

/-- The speed `1 + ε (1 − 2t)` of the parametrization `t + ε t (1 − t)`. -/
theorem hasDerivAt_segmentParam (ε t : ℝ) :
    HasDerivAt (fun t => t + ε * (t * (1 - t))) (1 + ε * (1 - 2 * t)) t := by
  have h1 := ((hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub
    (hasDerivAt_id t))).const_mul ε
  refine ((hasDerivAt_id t).add h1).congr_deriv ?_
  simp only [id, Pi.sub_apply]
  ring

/-- For `|ε| < 1` the parametrization `t + ε t (1 − t)` moves forward on `[0, 1]`. -/
theorem segmentParam_speed_pos {ε t : ℝ} (hε : ε ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 + ε * (1 - 2 * t) := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hε0, hε1⟩ := hε
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) (by linarith : (0 : ℝ) ≤ 1 - t),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) ht0]

/-- For `|ε| < 1` the unit tangent of the segment family is the direction of `P′ − P`. -/
theorem unitTangent_segmentFamily (P P' : E3) {ε t : ℝ} (hε : ε ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    unitTangent (fun t => segmentFamily P P' (ε, t)) t = ‖P' - P‖⁻¹ • (P' - P) := by
  have hd : deriv (fun t => segmentFamily P P' (ε, t)) t =
      (1 + ε * (1 - 2 * t)) • (P' - P) :=
    (((hasDerivAt_segmentParam ε t).smul_const (P' - P)).const_add P).deriv
  have hc := segmentParam_speed_pos hε ht
  rw [unitTangent, hd, norm_smul, Real.norm_of_nonneg hc.le, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hc.ne', mul_one]

/-- For `|ε| < 1` the segment family is a smooth family of rays of a homogeneous medium on
`[0, 1]`, from `P` to `P′`: the hypotheses of `opticalLength_eq` hold with `I = (−1, 1)`. -/
theorem isRayFamily_segmentFamily (n₀ : ℝ) {P P' : E3} (hPP' : P ≠ P') {ε : ℝ}
    (hε : ε ∈ Ioo (-1 : ℝ) 1) :
    IsRayFamily (fun _ => n₀) univ (segmentFamily P P') 0 1 ε := by
  refine ⟨⟨univ, isOpen_univ, ?_, fun _ _ => mem_univ _⟩, fun _ _ => mem_univ _, ?_⟩
  · exact (contDiff_const.add ((contDiff_snd.add (contDiff_fst.mul (contDiff_snd.mul
      (contDiff_const.sub contDiff_snd)))).smul contDiff_const)).contDiffOn
  · refine isRay_const (sub_ne_zero.mpr hPP'.symm) (hasDerivAt_segmentParam ε) (by fun_prop)
      fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    exact segmentParam_speed_pos hε ht

theorem segmentFamily_zero (P P' : E3) (ε : ℝ) : segmentFamily P P' (ε, 0) = P := by
  simp [segmentFamily]

theorem segmentFamily_one (P P' : E3) (ε : ℝ) : segmentFamily P P' (ε, 1) = P' := by
  simp [segmentFamily]

/-- The parametrizations of a segment in a homogeneous medium all have the same optical length,
by `opticalLength_eq`. -/
theorem opticalLength_segmentFamily (n₀ : ℝ) {P P' : E3} (hPP' : P ≠ P') {ε₁ ε₂ : ℝ}
    (h₁ : ε₁ ∈ Ioo (-1 : ℝ) 1) (h₂ : ε₂ ∈ Ioo (-1 : ℝ) 1) :
    opticalLength (fun _ => n₀) (fun t => segmentFamily P P' (ε₁, t)) 0 1 =
      opticalLength (fun _ => n₀) (fun t => segmentFamily P P' (ε₂, t)) 0 1 :=
  opticalLength_eq isOpen_univ contDiffOn_const isOpen_Ioo isPreconnected_Ioo
    (fun _ hε => isRayFamily_segmentFamily n₀ hPP' hε) (fun ε _ => segmentFamily_zero P P' ε)
    (fun ε _ => segmentFamily_one P P' ε) h₁ h₂

/-- The segment from `s e` to `s e + d` in the parametrization `ε` of `segmentFamily`, as a family
in the position `s` of its end points. -/
def shiftedSegmentFamily (d e : E3) (ε : ℝ) (p : ℝ × ℝ) : E3 :=
  segmentFamily (p.1 • e) (p.1 • e + d) (ε, p.2)

/-- For `d ≠ 0` and `|ε| < 1` the shifted segments are a smooth family of rays of a homogeneous
medium at every position `s₀`. -/
theorem isRayFamily_shiftedSegmentFamily (n₀ : ℝ) {d : E3} (hd : d ≠ 0) (e : E3) {ε : ℝ}
    (hε : ε ∈ Ioo (-1 : ℝ) 1) (s₀ : ℝ) :
    IsRayFamily (fun _ => n₀) univ (shiftedSegmentFamily d e ε) 0 1 s₀ := by
  refine ⟨⟨univ, isOpen_univ, ?_, fun _ _ => mem_univ _⟩, fun _ _ => mem_univ _, ?_⟩
  · refine ContDiff.contDiffOn ?_
    unfold shiftedSegmentFamily segmentFamily
    fun_prop
  · have hPP' : s₀ • e ≠ s₀ • e + d := fun h => hd (by simpa using h)
    exact (isRayFamily_segmentFamily n₀ hPP' hε).isRay

/-- **A degenerate instance of the sine condition.** In a homogeneous medium of index `n₀` the
object point `r(s) = s e` moves across the axis `d`, `⟨d, e⟩ = 0`, and its image is
`r′(s) = s e + d`. The ray `γ₁` of the bundle is the axial segment in the parametrization
`ε = 1/2` and the axial ray `γ₂` is the same segment in the parametrization `ε = 0`; the two have
the same optical length by `opticalLength_segmentFamily`. All the hypotheses of
`eikonal_variation_eq` and `sine_condition` hold together, and the conclusion, obtained from
`sine_condition`, is the identity `0 = 0`: the instance shows that the hypotheses are
satisfiable, not a non-trivial imaging. -/
theorem sine_condition_shiftedSegment (n₀ : ℝ) {d e : E3} (hd : d ≠ 0) (hde : ⟪d, e⟫ = 0)
    (s₀ : ℝ) :
    n₀ * ⟪unitTangent (fun t => shiftedSegmentFamily d e (1 / 2) (s₀, t)) 0,
        deriv (fun s : ℝ => s • e) s₀⟫ =
      n₀ * ⟪unitTangent (fun t => shiftedSegmentFamily d e (1 / 2) (s₀, t)) 1,
        deriv (fun s : ℝ => s • e + d) s₀⟫ := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hr : ∀ ε, (fun s => shiftedSegmentFamily d e ε (s, 0)) =ᶠ[𝓝 s₀] fun s : ℝ => s • e :=
    fun ε => Filter.Eventually.of_forall fun s => segmentFamily_zero _ _ ε
  have hr' : ∀ ε,
      (fun s => shiftedSegmentFamily d e ε (s, 1)) =ᶠ[𝓝 s₀] fun s : ℝ => s • e + d :=
    fun ε => Filter.Eventually.of_forall fun s => segmentFamily_one _ _ ε
  have hPP' : ∀ s : ℝ, s • e ≠ s • e + d := fun s h => hd (by simpa using h)
  have hstig : ∀ᶠ s in 𝓝 s₀,
      opticalLength (fun _ => n₀) (fun t => shiftedSegmentFamily d e (1 / 2) (s, t)) 0 1 =
        opticalLength (fun _ => n₀) (fun t => shiftedSegmentFamily d e 0 (s, t)) 0 1 :=
    Filter.Eventually.of_forall fun s => opticalLength_segmentFamily n₀ (hPP' s) hhalf h0
  have hde_e : deriv (fun s : ℝ => s • e) s₀ = e := by
    simpa using ((hasDerivAt_id s₀).smul_const e).deriv
  have hde_e' : deriv (fun s : ℝ => s • e + d) s₀ = e := by
    simpa using (((hasDerivAt_id s₀).smul_const e).add_const d).deriv
  have haxis : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : E3, w = e →
      ⟪unitTangent (fun t => shiftedSegmentFamily d e 0 (s₀, t)) t, w⟫ = 0 := by
    intro t ht w hw
    rw [hw, show (fun t => shiftedSegmentFamily d e 0 (s₀, t)) =
      fun t => segmentFamily (s₀ • e) (s₀ • e + d) (0, t) from rfl,
      unitTangent_segmentFamily _ _ h0 ht, add_sub_cancel_left, real_inner_smul_left, hde,
      mul_zero]
  exact sine_condition isOpen_univ contDiffOn_const
    (isRayFamily_shiftedSegmentFamily n₀ hd e hhalf s₀)
    (isRayFamily_shiftedSegmentFamily n₀ hd e h0 s₀) (hr _) (hr' _) (hr _) (hr' _) hstig
    (haxis 0 (left_mem_Icc.mpr zero_le_one) _ hde_e)
    (haxis 1 (right_mem_Icc.mpr zero_le_one) _ hde_e') rfl rfl

end Rays

section Absolute

/-- **An absolute instrument** (§57): a medium `N` that has the index `n` at the points of an
object region `Ω` and the index `n′` at their images, and images every point `x ∈ Ω`
stigmatically at `φ x`. The eikonal `ψ x` is the optical length from `x` to `φ x`, the same
along every ray through `x`. Of these rays the structure records the rays along the directions
`v ≠ 0` (the tangent rays of Maxwell's argument): such a ray `σ` with `σ 0 = x` and `σ′ 0 = v`
also passes through its own points `σ s` near `x`, so it passes through their images, at the
times `τ s`, and the optical length from `σ s` to `φ (σ s)` along it is `ψ (σ s)`.

The rays through `x` are required in every direction, as for Maxwell's fish-eye; the proofs use
the directions `v` and `−v`. The ray equation of `σ` is part of the definition but is not used
by the proofs, and the differentiability of `φ` and `ψ` is a hypothesis of each theorem. -/
structure IsAbsoluteInstrument (N : E3 → ℝ) (n n' : ℝ) (Ω : Set E3) (φ : E3 → E3)
    (ψ : E3 → ℝ) : Prop where
  index_object : ∀ x ∈ Ω, N x = n
  index_image : ∀ x ∈ Ω, N (φ x) = n'
  tangentRay : ∀ x ∈ Ω, ∀ v : E3, v ≠ 0 → ∃ (σ : ℝ → E3) (τ : ℝ → ℝ),
    ContDiff ℝ 1 σ ∧ σ 0 = x ∧ deriv σ 0 = v ∧ DifferentiableAt ℝ τ 0 ∧
      (∀ᶠ s in 𝓝 0, IsRay N σ s (τ s)) ∧ (∀ᶠ s in 𝓝 0, σ (τ s) = φ (σ s)) ∧
      ∀ᶠ s in 𝓝 0, opticalLength N σ s (τ s) = ψ (σ s)

/-- Along a path `σ` that passes through the images of its points, at the times `τ s`, with the
optical length `ψ (σ s)` between them, the derivatives of the eikonal and of the image map in the
direction `v = σ′ 0` are `Dψ v = N(φ x) a − N(x) |v|` and `|Dφ v| = |a|`, with
`a = |σ′(τ 0)| τ′(0)`. -/
theorem fderiv_eikonal_of_carries {N : E3 → ℝ} (hN : Continuous N) {φ : E3 → E3}
    {ψ : E3 → ℝ} {σ : ℝ → E3} {τ : ℝ → ℝ} {x v : E3} (hσ : ContDiff ℝ 1 σ) (h0 : σ 0 = x)
    (hv : deriv σ 0 = v) (hτ : DifferentiableAt ℝ τ 0)
    (him : ∀ᶠ s in 𝓝 0, σ (τ s) = φ (σ s))
    (heik : ∀ᶠ s in 𝓝 0, opticalLength N σ s (τ s) = ψ (σ s))
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    fderiv ℝ ψ x v = N (φ x) * (‖deriv σ (τ 0)‖ * deriv τ 0) - N x * ‖v‖ ∧
      ‖fderiv ℝ φ x v‖ = |‖deriv σ (τ 0)‖ * deriv τ 0| := by
  have hσd : ∀ t, HasDerivAt σ (deriv σ t) t := fun t =>
    ((hσ.differentiable one_ne_zero) t).hasDerivAt
  set g : ℝ → ℝ := fun t => N (σ t) * ‖deriv σ t‖ with hg_def
  have hg : Continuous g := (hN.comp hσ.continuous).mul (hσ.continuous_deriv le_rfl).norm
  have hG : ∀ u, HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, g t) (g u) u := fun u =>
    (hg.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hf : HasDerivAt (fun s => (∫ t in (0 : ℝ)..τ s, g t) - ∫ t in (0 : ℝ)..s, g t)
      (g (τ 0) * deriv τ 0 - g 0) 0 :=
    ((hG (τ 0)).comp 0 hτ.hasDerivAt).sub (hG 0)
  have hfeq : (fun s => opticalLength N σ s (τ s)) =
      fun s => (∫ t in (0 : ℝ)..τ s, g t) - ∫ t in (0 : ℝ)..s, g t := by
    funext s
    exact (intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)).symm
  have hτ0 : σ (τ 0) = φ x := by rw [him.self_of_nhds, h0]
  -- the eikonal along the path
  have hψσ : HasDerivAt (fun s => ψ (σ s)) (fderiv ℝ ψ x v) 0 := by
    have h := (h0 ▸ hψ).hasFDerivAt.comp_hasDerivAt 0 (hσd 0)
    rw [hv, h0] at h
    exact h
  rw [← hfeq] at hf
  have h1 := hf.congr_of_eventuallyEq (heik.mono fun s hs => hs.symm) |>.unique hψσ
  -- the image along the path
  have hφσ : HasDerivAt (fun s => φ (σ s)) (fderiv ℝ φ x v) 0 := by
    have h := (h0 ▸ hφ).hasFDerivAt.comp_hasDerivAt 0 (hσd 0)
    rw [hv, h0] at h
    exact h
  have h2 := ((hσd (τ 0)).scomp 0 hτ.hasDerivAt).congr_of_eventuallyEq
    (him.mono fun s hs => hs.symm) |>.unique hφσ
  refine ⟨?_, ?_⟩
  · rw [← h1]
    simp only [hg_def, hτ0, h0, hv]
    ring
  · rw [← h2, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
    ring

/-- **Maxwell's theorem on absolute instruments**, infinitesimal form (§57). If the image map
and the eikonal are differentiable at `x ∈ Ω`, the image map multiplies the lengths at `x` by
`n/n′`, `n′ |Dφ(x) v| = n |v|`, and the eikonal is stationary, `Dψ(x) = 0`. The rays along `v`
and along `−v` give `Dψ v = n′ a₁ − n |v|` and `−Dψ v = n′ a₂ − n |v|` with `|a₁| = |a₂| =
|Dφ v|`, which forces `a₁ = a₂ = |Dφ v|`. -/
theorem IsAbsoluteInstrument.norm_fderiv_eq_and_fderiv_eikonal {N : E3 → ℝ} {n n' : ℝ}
    {Ω : Set E3} {φ : E3 → E3} {ψ : E3 → ℝ} (hI : IsAbsoluteInstrument N n n' Ω φ ψ)
    (hN : Continuous N) (hn : 0 < n) (hn' : 0 < n') {x : E3} (hx : x ∈ Ω)
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) (v : E3) :
    n' * ‖fderiv ℝ φ x v‖ = n * ‖v‖ ∧ fderiv ℝ ψ x v = 0 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  obtain ⟨σ₁, τ₁, hσ₁, h₁0, h₁v, hτ₁, -, him₁, heik₁⟩ := hI.tangentRay x hx v hv
  obtain ⟨σ₂, τ₂, hσ₂, h₂0, h₂v, hτ₂, -, him₂, heik₂⟩ :=
    hI.tangentRay x hx (-v) (neg_ne_zero.mpr hv)
  obtain ⟨e₁, n₁⟩ := fderiv_eikonal_of_carries hN hσ₁ h₁0 h₁v hτ₁ him₁ heik₁ hφ hψ
  obtain ⟨e₂, n₂⟩ := fderiv_eikonal_of_carries hN hσ₂ h₂0 h₂v hτ₂ him₂ heik₂ hφ hψ
  rw [map_neg, norm_neg] at e₂
  rw [map_neg, norm_neg] at n₂
  rw [hI.index_object x hx, hI.index_image x hx] at e₁ e₂
  set m := ‖fderiv ℝ φ x v‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  have hv0 : 0 < n * ‖v‖ := mul_pos hn (norm_pos_iff.mpr hv)
  have hnm : 0 ≤ n' * m := mul_nonneg hn'.le hm0
  rcases (abs_eq hm0).mp n₁.symm with h₁ | h₁ <;> rcases (abs_eq hm0).mp n₂.symm with h₂ | h₂ <;>
    rw [h₁] at e₁ <;> rw [h₂] at e₂ <;> constructor <;> nlinarith

/-- **Maxwell's theorem** (§57): an absolute instrument multiplies the lengths of its object
region by `n/n′`, `n′ |Dφ(x) v| = n |v|`. -/
theorem IsAbsoluteInstrument.norm_fderiv_eq {N : E3 → ℝ} {n n' : ℝ} {Ω : Set E3}
    {φ : E3 → E3} {ψ : E3 → ℝ} (hI : IsAbsoluteInstrument N n n' Ω φ ψ) (hN : Continuous N)
    (hn : 0 < n) (hn' : 0 < n') {x : E3} (hx : x ∈ Ω) (hφ : DifferentiableAt ℝ φ x)
    (hψ : DifferentiableAt ℝ ψ x) (v : E3) : n' * ‖fderiv ℝ φ x v‖ = n * ‖v‖ :=
  (hI.norm_fderiv_eq_and_fderiv_eikonal hN hn hn' hx hφ hψ v).1

/-- The eikonal of an absolute instrument is stationary on the object region. -/
theorem IsAbsoluteInstrument.fderiv_eikonal_eq_zero {N : E3 → ℝ} {n n' : ℝ} {Ω : Set E3}
    {φ : E3 → E3} {ψ : E3 → ℝ} (hI : IsAbsoluteInstrument N n n' Ω φ ψ) (hN : Continuous N)
    (hn : 0 < n) (hn' : 0 < n') {x : E3} (hx : x ∈ Ω) (hφ : DifferentiableAt ℝ φ x)
    (hψ : DifferentiableAt ℝ ψ x) : fderiv ℝ ψ x = 0 := by
  ext v
  exact (hI.norm_fderiv_eq_and_fderiv_eikonal hN hn hn' hx hφ hψ v).2

/-- **The optical length of an object curve equals that of its image** (§57). For an absolute
instrument whose image map and eikonal are differentiable on the object region, every
differentiable curve `c` in the object region and its image `φ ∘ c` have the same optical
length. -/
theorem IsAbsoluteInstrument.opticalLength_curve_eq {N : E3 → ℝ} {n n' : ℝ} {Ω : Set E3}
    {φ : E3 → E3} {ψ : E3 → ℝ} (hI : IsAbsoluteInstrument N n n' Ω φ ψ) (hN : Continuous N)
    (hn : 0 < n) (hn' : 0 < n') (hφ : ∀ x ∈ Ω, DifferentiableAt ℝ φ x)
    (hψ : ∀ x ∈ Ω, DifferentiableAt ℝ ψ x) {c : ℝ → E3} {a b : ℝ}
    (hcΩ : ∀ t ∈ uIcc a b, c t ∈ Ω) (hc : ∀ t ∈ uIcc a b, DifferentiableAt ℝ c t) :
    opticalLength N (φ ∘ c) a b = opticalLength N c a b := by
  refine intervalIntegral.integral_congr fun t ht => ?_
  have hx := hcΩ t ht
  simp only [Function.comp_apply]
  rw [fderiv_comp_deriv t (hφ _ hx) (hc t ht), hI.index_image _ hx, hI.index_object _ hx,
    hI.norm_fderiv_eq hN hn hn' hx (hφ _ hx) (hψ _ hx)]

/-- **Carathéodory's theorem for absolute instruments** (§57): on a connected open object region
an absolute instrument with a twice continuously differentiable image map and a differentiable
eikonal is a similarity of ratio `n/n′`. -/
theorem IsAbsoluteInstrument.isSimilarity {N : E3 → ℝ} {n n' : ℝ} {Ω : Set E3}
    {φ : E3 → E3} {ψ : E3 → ℝ} (hI : IsAbsoluteInstrument N n n' Ω φ ψ) (hN : Continuous N)
    (hn : 0 < n) (hn' : 0 < n') (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hφ : ContDiffOn ℝ 2 φ Ω) (hψ : ∀ x ∈ Ω, DifferentiableAt ℝ ψ x) :
    ∃ (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3), ∀ x ∈ Ω, φ x = (n / n') • L x + c :=
  isSimilarity_of_absolute hn hn' hΩ hΩc hφ fun x hx =>
    hI.norm_fderiv_eq hN hn hn' hx
      ((hφ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)) (hψ x hx)

/-- The trivial instrument, a homogeneous medium that images every point on itself with the
eikonal `0`, is absolute: the tangent rays are the straight lines `x + t v`. -/
theorem isAbsoluteInstrument_id (n₀ : ℝ) (Ω : Set E3) :
    IsAbsoluteInstrument (fun _ => n₀) n₀ n₀ Ω id fun _ => 0 := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun x _ v hv => ⟨fun t => x + t • v, id, ?_, ?_, ?_,
    differentiableAt_id, ?_, ?_, ?_⟩⟩
  · fun_prop
  · simp
  · exact ((hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add x).deriv.trans (one_smul ℝ v)
  · refine Filter.Eventually.of_forall fun s => ?_
    exact isRay_const hv (fun t => hasDerivAt_id t) continuous_const fun _ _ => one_pos
  · exact Filter.Eventually.of_forall fun s => rfl
  · exact Filter.Eventually.of_forall fun s => intervalIntegral.integral_same

end Absolute

end ProjectAinos.Electrodynamics.Optics.Imaging
