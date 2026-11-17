/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.JointFlowSmooth
public import ProjectAInos.SmoothGeometry.ODE.PeriodLattice
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Commuting flows on a level set of a submersion

Let `F : E → ℝ^κ` be smooth on a space `E` of finite dimension, and let `Xᵢ`,
`i ∈ ι`, be smooth fields with `DF(y) Xᵢ(y) = 0`: the fields are tangent to the
level sets of `F`. Suppose `dim E = |ι| + |κ|`.

* `flow_jointField_levelSet`: `F` is constant along the flow of `Σᵢ tᵢ Xᵢ`.
* `isInvariantSet_levelSet`: a compact level set is invariant, with complete
  flows.
* `isLocallyFree_levelSet`: on a level set at whose points `DF` is onto and the
  `Xᵢ` are linearly independent, the joint flow is locally free. The proof is
  the inverse function theorem for `(t, s) ↦ g^t (x + L s)`, with `L` a right
  inverse of `DF(x)`.
* `exists_torus_chart_levelSet`: if moreover the fields commute and the level
  set is compact and connected, it carries angles in which the flows are
  uniform motions.
-/

@[expose] public section
noncomputable section

open Set Filter Module
open scoped Topology ContDiff

namespace ProjectAInos.SmoothGeometry.NonlinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {X : ι → E → E} {F : E → κ → ℝ} {c : κ → ℝ}

omit [CompleteSpace E] [Fintype κ] in
theorem fderiv_apply_jointField (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) (t : ι → ℝ) (y : E) :
    fderiv ℝ F y (jointField X t y) = 0 := by
  simp [jointField, htan]

/-- `F` is constant along the flow of `Σᵢ tᵢ Xᵢ`. -/
theorem flow_jointField_levelSet (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hF : ContDiff ℝ ∞ F)
    (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) (t : ι → ℝ) {r : ℝ} {x : E}
    (h : (r, x) ∈ flowDomain (jointField X t)) :
    F (flow (jointField X t) (r, x)) = F x := by
  refine flow_invariant (contDiff_jointField hX t) (f := F) (fun {y} {u} hy => ?_) h
  have h1 : HasDerivAt (fun s => F (y s)) (fderiv ℝ F (y u) (jointField X t (y u))) u :=
    (hF.differentiable (by simp) (y u)).hasFDerivAt.comp_hasDerivAt u hy
  rwa [fderiv_apply_jointField htan] at h1

/-- A compact level set is invariant, with complete flows. -/
theorem isInvariantSet_levelSet (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hF : ContDiff ℝ ∞ F)
    (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) (hcomp : IsCompact (F ⁻¹' {c})) :
    IsInvariantSet X (F ⁻¹' {c}) :=
  isInvariantSet_of_isCompact hX hcomp fun t r x hx h => by
    have hx' : F x = c := hx
    change F (flow (jointField X t) (r, x)) = c
    rw [flow_jointField_levelSet hX hF htan t h, hx']

variable [FiniteDimensional ℝ E]

/-- A chart at a point of a regular level set: `(t, s) ↦ g^t (x + L s)` is a
homeomorphism near zero, and its points with `s ≠ 0` are not on the level
set. -/
theorem exists_levelSet_chart (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hF : ContDiff ℝ ∞ F)
    (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) {x : E} (hx : F x = c)
    (hind : LinearIndependent ℝ fun i => X i x) (hsurj : Function.Surjective (fderiv ℝ F x))
    (hdim : finrank ℝ E = Fintype.card ι + Fintype.card κ) :
    ∃ (e : OpenPartialHomeomorph ((ι → ℝ) × (κ → ℝ)) E) (L : (κ → ℝ) →L[ℝ] E),
      ((0 : ι → ℝ), (0 : κ → ℝ)) ∈ e.source ∧
      (∀ p, e p = jointFlow X p.1 (x + L p.2)) ∧
      ∀ p ∈ e.source, F (e p) = c → p.2 = 0 := by
  -- a right inverse of the derivative of `F`
  obtain ⟨L₀, hL₀⟩ := (fderiv ℝ F x : E →ₗ[ℝ] κ → ℝ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  obtain ⟨L, hL⟩ : ∃ L : (κ → ℝ) →L[ℝ] E, ∀ s, L s = L₀ s :=
    ⟨LinearMap.toContinuousLinearMap L₀, fun s => rfl⟩
  have hFL : ∀ s, fderiv ℝ F x (L s) = s := fun s => by
    rw [hL]
    exact LinearMap.congr_fun hL₀ s
  -- the derivative of `(t, s) ↦ g^t (x + L s)` at zero
  obtain ⟨D, hD, hDstrict⟩ := hasFDerivAt_jointFlow_zero hX x
  obtain ⟨A, hA⟩ : ∃ A : (ι → ℝ) × (κ → ℝ) →L[ℝ] (ι → ℝ) × E, ∀ p, A p = (p.1, L p.2) :=
    ⟨(ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ)).prod
      (L.comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))), fun p => rfl⟩
  have hinner : HasStrictFDerivAt
      (fun p : (ι → ℝ) × (κ → ℝ) => ((p.1, x + L p.2) : (ι → ℝ) × E)) A (0, 0) := by
    have h1 : (fun p : (ι → ℝ) × (κ → ℝ) => ((p.1, x + L p.2) : (ι → ℝ) × E)) =
        fun p => ((0 : ι → ℝ), x) + A p := by
      funext p
      rw [hA]
      simp
    rw [h1]
    exact A.hasStrictFDerivAt.const_add _
  have hΘ : HasStrictFDerivAt (fun p : (ι → ℝ) × (κ → ℝ) => jointFlow X p.1 (x + L p.2))
      (D.comp A) (0, 0) := by
    have hD' : HasStrictFDerivAt (fun q : (ι → ℝ) × E => jointFlow X q.1 q.2) D
        ((fun p : (ι → ℝ) × (κ → ℝ) => ((p.1, x + L p.2) : (ι → ℝ) × E)) (0, 0)) := by
      simp only [map_zero, add_zero]
      exact hDstrict
    exact hD'.comp (0, 0) hinner
  have hDA : ∀ p : (ι → ℝ) × (κ → ℝ), (D.comp A) p = jointField X p.1 x + L p.2 := fun p => by
    rw [ContinuousLinearMap.comp_apply, hA, hD]
  have hinj : Function.Injective (D.comp A) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    rw [hDA] at hp
    have h1 := congrArg (fderiv ℝ F x) hp
    rw [map_add, hFL, map_zero, fderiv_apply_jointField htan, zero_add] at h1
    rw [h1, map_zero, add_zero] at hp
    have h3 : p.1 = 0 := funext fun i => Fintype.linearIndependent_iff.mp hind p.1 hp i
    exact Prod.ext h3 h1
  have hfin : finrank ℝ ((ι → ℝ) × (κ → ℝ)) = finrank ℝ E := by
    rw [finrank_prod, finrank_fintype_fun_eq_card, finrank_fintype_fun_eq_card, hdim]
  obtain ⟨eq, heq⟩ : ∃ eq : ((ι → ℝ) × (κ → ℝ)) ≃L[ℝ] E,
      (eq : (ι → ℝ) × (κ → ℝ) →L[ℝ] E) = D.comp A :=
    ⟨(LinearEquiv.ofInjectiveOfFinrankEq (D.comp A : (ι → ℝ) × (κ → ℝ) →ₗ[ℝ] E) hinj
      hfin).toContinuousLinearEquiv, by ext p <;> rfl⟩
  rw [← heq] at hΘ
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : OpenPartialHomeomorph ((ι → ℝ) × (κ → ℝ)) E,
      e₀ = hΘ.toOpenPartialHomeomorph _ := ⟨_, rfl⟩
  have h0src : ((0 : ι → ℝ), (0 : κ → ℝ)) ∈ e₀.source := by
    rw [he₀]
    exact hΘ.mem_toOpenPartialHomeomorph_source
  have he₀coe : ∀ p, e₀ p = jointFlow X p.1 (x + L p.2) := fun p => by
    rw [he₀]
    rfl
  -- `s ↦ F (x + L s)` is injective near zero
  have hG : HasStrictFDerivAt (fun s : κ → ℝ => F (x + L s))
      ((ContinuousLinearEquiv.refl ℝ (κ → ℝ) : (κ → ℝ) ≃L[ℝ] κ → ℝ) :
        (κ → ℝ) →L[ℝ] κ → ℝ) 0 := by
    have hFs : HasStrictFDerivAt F (fderiv ℝ F x) (x + L 0) := by
      rw [map_zero, add_zero]
      exact hF.contDiffAt.hasStrictFDerivAt (by simp)
    have hLs : HasStrictFDerivAt (fun s : κ → ℝ => x + L s) L 0 :=
      L.hasStrictFDerivAt.const_add x
    have h1 := hFs.comp 0 hLs
    have e : (fderiv ℝ F x).comp L =
        ((ContinuousLinearEquiv.refl ℝ (κ → ℝ) : (κ → ℝ) ≃L[ℝ] κ → ℝ) :
          (κ → ℝ) →L[ℝ] κ → ℝ) := ContinuousLinearMap.ext fun s => hFL s
    rw [e] at h1
    exact h1
  obtain ⟨eG, heG⟩ : ∃ eG : OpenPartialHomeomorph (κ → ℝ) (κ → ℝ),
      eG = hG.toOpenPartialHomeomorph _ := ⟨_, rfl⟩
  have h0G : (0 : κ → ℝ) ∈ eG.source := by
    rw [heG]
    exact hG.mem_toOpenPartialHomeomorph_source
  have heGcoe : ∀ s, eG s = F (x + L s) := fun s => by
    rw [heG]
    rfl
  -- the open set on which the flow is defined and `F` is injective in `s`
  have hYopen : IsOpen {q : (ι → ℝ) × E | ((1 : ℝ), q) ∈ flowDomain (extendedJointField X)} :=
    (isOpen_flowDomain (contDiff_extendedJointField hX)).preimage
      (continuous_const.prodMk continuous_id)
  have hinnerc : Continuous fun p : (ι → ℝ) × (κ → ℝ) => ((p.1, x + L p.2) : (ι → ℝ) × E) :=
    continuous_fst.prodMk (continuous_const.add (L.continuous.comp continuous_snd))
  obtain ⟨V, hV⟩ : ∃ V : Set ((ι → ℝ) × (κ → ℝ)), V =
      ((fun p : (ι → ℝ) × (κ → ℝ) => ((p.1, x + L p.2) : (ι → ℝ) × E)) ⁻¹'
        {q : (ι → ℝ) × E | ((1 : ℝ), q) ∈ flowDomain (extendedJointField X)}) ∩
      (Prod.snd ⁻¹' eG.source) := ⟨_, rfl⟩
  have hVopen : IsOpen V := by
    rw [hV]
    exact (hYopen.preimage hinnerc).inter (eG.open_source.preimage continuous_snd)
  have h0V : ((0 : ι → ℝ), (0 : κ → ℝ)) ∈ V := by
    rw [hV]
    refine ⟨?_, h0G⟩
    change ((1 : ℝ), ((0 : ι → ℝ), x + L 0)) ∈ flowDomain (extendedJointField X)
    rw [map_zero, add_zero]
    exact (flow_extendedJointField hX (one_mem_flowDomain_jointField_zero X x).1).1
  refine ⟨e₀.restrOpen V hVopen, L, ⟨h0src, h0V⟩, he₀coe, fun p hp hFp => ?_⟩
  have hpV : p ∈ V := hp.2
  rw [hV] at hpV
  have hdom : ((1 : ℝ), x + L p.2) ∈ flowDomain (jointField X p.1) :=
    mem_flowDomain_jointField_of_extended hX hpV.1
  have h1 : F (jointFlow X p.1 (x + L p.2)) = F (x + L p.2) :=
    flow_jointField_levelSet hX hF htan p.1 hdom
  have h2 : F (e₀ p) = c := hFp
  rw [he₀coe, h1, ← heGcoe] at h2
  have h3 : eG 0 = c := by
    rw [heGcoe, map_zero, add_zero, hx]
  exact eG.injOn hpV.2 h0G (h2.trans h3.symm)

/-- On a regular level set the joint flow is locally free. -/
theorem isLocallyFree_levelSet (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hF : ContDiff ℝ ∞ F)
    (htan : ∀ i y, fderiv ℝ F y (X i y) = 0)
    (hind : ∀ x ∈ F ⁻¹' {c}, LinearIndependent ℝ fun i => X i x)
    (hsurj : ∀ x ∈ F ⁻¹' {c}, Function.Surjective (fderiv ℝ F x))
    (hdim : finrank ℝ E = Fintype.card ι + Fintype.card κ) :
    IsLocallyFree X (F ⁻¹' {c}) := by
  constructor
  · intro x hx
    obtain ⟨e, L, h0, he, -⟩ := exists_levelSet_chart hX hF htan hx (hind x hx) (hsurj x hx) hdim
    have hcont : Continuous fun t : ι → ℝ => ((t, 0) : (ι → ℝ) × (κ → ℝ)) :=
      continuous_id.prodMk continuous_const
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (e.open_source.preimage hcont) 0 h0
    refine ⟨δ, hδ, fun t ht htx => ?_⟩
    have hmem : ((t, 0) : (ι → ℝ) × (κ → ℝ)) ∈ e.source :=
      hball (by rwa [Metric.mem_ball, dist_zero_right])
    have h1 : e (t, 0) = e (0, 0) := by
      rw [he, he]
      simp only [map_zero, add_zero]
      rw [htx, jointFlow_zero_apply]
    exact (Prod.mk.inj (e.injOn hmem h0 h1)).1
  · intro x hx ε hε
    obtain ⟨e, L, h0, he, hF0⟩ :=
      exists_levelSet_chart hX hF htan hx (hind x hx) (hsurj x hx) hdim
    obtain ⟨N, hN⟩ : ∃ N : Set ((ι → ℝ) × (κ → ℝ)), N = e.source ∩ {p | ‖p.1‖ < ε} := ⟨_, rfl⟩
    have hNopen : IsOpen N := by
      rw [hN]
      exact e.open_source.inter (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const)
    have hNsub : N ⊆ e.source := by
      rw [hN]
      exact inter_subset_left
    refine ⟨e '' N, e.isOpen_image_of_subset_source hNopen hNsub, ⟨(0, 0), ?_, ?_⟩, ?_⟩
    · rw [hN]
      exact ⟨h0, by simpa using hε⟩
    · rw [he]
      simp only [map_zero, add_zero]
      exact jointFlow_zero_apply X x
    · rintro y ⟨hy, p, hp, rfl⟩
      rw [hN] at hp
      have hp2 := hF0 p hp.1 hy
      refine ⟨p.1, hp.2, ?_⟩
      rw [he p, hp2, map_zero, add_zero]

/-- Angles on a compact connected regular level set of the integrals of
commuting fields: the level set is the image of `θ ↦ g^{Σ θᵢ bᵢ} x`, two angles
give the same point exactly when they differ by integers, and the flows of the
fields are uniform motions of the angles. -/
theorem exists_torus_chart_levelSet (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X)
    (hF : ContDiff ℝ ∞ F) (htan : ∀ i y, fderiv ℝ F y (X i y) = 0)
    (hind : ∀ x ∈ F ⁻¹' {c}, LinearIndependent ℝ fun i => X i x)
    (hsurj : ∀ x ∈ F ⁻¹' {c}, Function.Surjective (fderiv ℝ F x))
    (hdim : finrank ℝ E = Fintype.card ι + Fintype.card κ) (hcomp : IsCompact (F ⁻¹' {c}))
    (hconn : IsPreconnected (F ⁻¹' {c})) :
    ∃ b : Basis ι ℝ (ι → ℝ), ∀ x ∈ F ⁻¹' {c},
      (∀ y ∈ F ⁻¹' {c}, ∃ θ : ι → ℝ, jointFlow X (∑ i, θ i • b i) x = y) ∧
      (∀ θ θ' : ι → ℝ, jointFlow X (∑ i, θ i • b i) x = jointFlow X (∑ i, θ' i • b i) x ↔
        ∀ i, ∃ n : ℤ, θ i - θ' i = n) ∧
      ∀ (s : ι → ℝ) (r : ℝ) (θ : ι → ℝ),
        flow (jointField X s) (r, jointFlow X (∑ i, θ i • b i) x) =
          jointFlow X (∑ i, (θ i + r * b.repr s i) • b i) x :=
  exists_torus_chart hX hc (isInvariantSet_levelSet hX hF htan hcomp)
    (isLocallyFree_levelSet hX hF htan hind hsurj hdim) hconn hcomp

end ProjectAInos.SmoothGeometry.NonlinearODE
