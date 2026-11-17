/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.LevelSetTube

/-!
# The derivative of the joint flow and the smooth family of periods

* `hasFDerivAt_jointFlow`: at a point `y` of an invariant set the derivative of
  `(t, y) ↦ g^t y` is `(τ, v) ↦ Σᵢ τᵢ Xᵢ(g^t y) + D_y g^t(y) v`.
* `exists_period_family`: let `x` be a point of an open invariant set, `L` a
  transversal to the level set of `F` through `x`, and `b` a period of `x`,
  `g^b x = x`. Then there is a function `e` of `s`, smooth at zero with
  `e(0) = b`, such that `g^{e(s)} (x + L s) = x + L s` for small `s`: the period
  extends to the neighbouring level sets.
-/

@[expose] public section
noncomputable section

open Set Filter Module
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.NonlinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {X : ι → E → E} {M : Set E}

/-- The derivative of the joint flow in the times and the point, at a point of
an invariant set. -/
theorem hasFDerivAt_jointFlow (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X)
    (hM : IsInvariantSet X M) (t : ι → ℝ) {y : E} (hy : y ∈ M) :
    ∃ D : (ι → ℝ) × E →L[ℝ] E,
      (∀ (τ : ι → ℝ) (v : E), D (τ, v) =
        jointField X τ (jointFlow X t y) + fderiv ℝ (fun z => jointFlow X t z) y v) ∧
      HasFDerivAt (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) D (t, y) := by
  have hsm := contDiffAt_jointFlow hX (hM.mem_flowDomain t 1 y hy)
  have hd : HasFDerivAt (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2)
      (fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (t, y)) (t, y) :=
    (hsm.differentiableAt (by simp)).hasFDerivAt
  refine ⟨fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (t, y), fun τ v => ?_, hd⟩
  -- the derivative along the point
  have hv : fderiv ℝ (fun z => jointFlow X t z) y v =
      fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (t, y) (0, v) := by
    have h1 : HasFDerivAt (fun z : E => jointFlow X t z)
        ((fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (t, y)).comp
          (ContinuousLinearMap.inr ℝ (ι → ℝ) E)) y :=
      HasFDerivAt.comp y (g := fun p : (ι → ℝ) × E => jointFlow X p.1 p.2)
        (f := fun z : E => ((t, z) : (ι → ℝ) × E)) hd (hasFDerivAt_prodMk_right t y)
    rw [h1.fderiv]
    rfl
  -- the derivative along the times
  have hτ : fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (t, y) (τ, 0) =
      jointField X τ (jointFlow X t y) := by
    have hline : HasDerivAt (fun r : ℝ => ((t + r • τ, y) : (ι → ℝ) × E)) (τ, 0) 0 := by
      have h1 : HasDerivAt (fun r : ℝ => t + r • τ) ((1 : ℝ) • τ) 0 :=
        ((hasDerivAt_id (0 : ℝ)).smul_const τ).const_add t
      rw [one_smul] at h1
      exact h1.prodMk (hasDerivAt_const (0 : ℝ) y)
    have hcomp : HasDerivAt (fun r : ℝ => jointFlow X (t + r • τ) y)
        (fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (t, y) (τ, 0)) 0 := by
      have h0 : HasFDerivAt (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2)
          (fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (t, y))
          (t + (0 : ℝ) • τ, y) := by
        rw [zero_smul, add_zero]
        exact hd
      exact HasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (l := fun p : (ι → ℝ) × E => jointFlow X p.1 p.2)
        (f := fun r : ℝ => ((t + r • τ, y) : (ι → ℝ) × E)) h0 hline
    have hmem : jointFlow X t y ∈ M := jointFlow_mem hM t hy
    have hflow := hasDerivAt_jointFlow_smul hX hM τ hmem 0
    rw [zero_smul, jointFlow_zero hX hM hmem] at hflow
    have e : (fun r : ℝ => jointFlow X (t + r • τ) y) =
        fun r : ℝ => jointFlow X (r • τ) (jointFlow X t y) :=
      funext fun r => by rw [add_comm, jointFlow_add hX hc hM (r • τ) t hy]
    rw [e] at hcomp
    exact hcomp.unique hflow
  have e : ((τ, v) : (ι → ℝ) × E) = (τ, 0) + (0, v) := by simp
  rw [e, map_add, hτ, hv]

variable [FiniteDimensional ℝ E] {F : E → κ → ℝ}

/-- A period of a point extends to a smooth family of periods of the points of
a transversal. -/
theorem exists_period_family (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X)
    (hF : ContDiff ℝ ∞ F) (htan : ∀ i y, fderiv ℝ F y (X i y) = 0)
    (hM : IsInvariantSet X M) (hMo : IsOpen M) {x : E} (hx : x ∈ M)
    (hind : LinearIndependent ℝ fun i => X i x)
    (hdim : finrank ℝ E = Fintype.card ι + Fintype.card κ) (L : (κ → ℝ) →L[ℝ] E)
    (N : (κ → ℝ) ≃L[ℝ] (κ → ℝ)) (hFL : ∀ s, fderiv ℝ F x (L s) = N s) {b : ι → ℝ}
    (hb : jointFlow X b x = x) :
    ∃ (S : Set (κ → ℝ)) (e : (κ → ℝ) → ι → ℝ), IsOpen S ∧ (0 : κ → ℝ) ∈ S ∧ e 0 = b ∧
      ContDiffAt ℝ ∞ e 0 ∧
      ∀ s ∈ S, x + L s ∈ M ∧ jointFlow X (e s) (x + L s) = x + L s := by
  obtain ⟨ec, S₀, h0src, hec, hS₀o, h0S₀, hinj, hsrc, hsymm⟩ :=
    exists_levelSet_chart_of_transversal hX hF htan hind hdim L N hFL
  have hx0 : ec (0, 0) = x := by
    rw [hec]
    simp only [map_zero, add_zero]
    exact jointFlow_zero_apply X x
  have hs0 : ec.symm x = (0, 0) := by
    have h := ec.left_inv h0src
    rwa [hx0] at h
  have haff : Continuous fun s : κ → ℝ => x + L s := continuous_const.add L.continuous
  -- the points of the transversal in the invariant set
  have hOo : IsOpen {s : κ → ℝ | x + L s ∈ M} := hMo.preimage haff
  have hRsm : ∀ s ∈ {s : κ → ℝ | x + L s ∈ M},
      ContDiffAt ℝ ∞ (fun s : κ → ℝ => jointFlow X b (x + L s)) s := by
    intro s hs
    have h1 := contDiffAt_jointFlow hX (hM.mem_flowDomain b 1 _ hs)
    exact ContDiffAt.comp s (g := fun p : (ι → ℝ) × E => jointFlow X p.1 p.2)
      (f := fun s : κ → ℝ => ((b, x + L s) : (ι → ℝ) × E)) h1
      (contDiffAt_const.prodMk (contDiffAt_const.add L.contDiff.contDiffAt))
  have hRc : ContinuousOn (fun s : κ → ℝ => jointFlow X b (x + L s))
      {s : κ → ℝ | x + L s ∈ M} := fun s hs => (hRsm s hs).continuousAt.continuousWithinAt
  obtain ⟨S, hSdef⟩ : ∃ S : Set (κ → ℝ), S = ({s : κ → ℝ | x + L s ∈ M} ∩
      (fun s : κ → ℝ => jointFlow X b (x + L s)) ⁻¹' ec.target) ∩ S₀ := ⟨_, rfl⟩
  have hSo : IsOpen S := by
    rw [hSdef]
    exact (hRc.isOpen_inter_preimage hOo ec.open_target).inter hS₀o
  have hxt : x ∈ ec.target := by
    have h := ec.map_source h0src
    rwa [hx0] at h
  have h0S : (0 : κ → ℝ) ∈ S := by
    rw [hSdef]
    refine ⟨⟨?_, ?_⟩, h0S₀⟩
    · change x + L 0 ∈ M
      rw [map_zero, add_zero]
      exact hx
    · change jointFlow X b (x + L 0) ∈ ec.target
      rw [map_zero, add_zero, hb]
      exact hxt
  refine ⟨S, fun s => b - (ec.symm (jointFlow X b (x + L s))).1, hSo, h0S, ?_, ?_, ?_⟩
  · change b - (ec.symm (jointFlow X b (x + L 0))).1 = b
    rw [map_zero, add_zero, hb, hs0, sub_zero]
  · have hR0 : ContDiffAt ℝ ∞ (fun s : κ → ℝ => jointFlow X b (x + L s)) 0 :=
      hRsm 0 (by
        change x + L 0 ∈ M
        rw [map_zero, add_zero]
        exact hx)
    have hsymm' : ContDiffAt ℝ ∞ ec.symm
        ((fun s : κ → ℝ => jointFlow X b (x + L s)) 0) := by
      simp only [map_zero, add_zero]
      rw [hb]
      exact hsymm
    have hcomp : ContDiffAt ℝ ∞ (fun s : κ → ℝ => ec.symm (jointFlow X b (x + L s))) 0 :=
      ContDiffAt.comp 0 (g := ec.symm) (f := fun s : κ → ℝ => jointFlow X b (x + L s))
        hsymm' hR0
    exact contDiffAt_const.sub (contDiffAt_fst.comp 0 hcomp)
  · intro s hs
    rw [hSdef] at hs
    have hsM : x + L s ∈ M := hs.1.1
    have hRt : jointFlow X b (x + L s) ∈ ec.target := hs.1.2
    obtain ⟨p, hp⟩ : ∃ p, p = ec.symm (jointFlow X b (x + L s)) := ⟨_, rfl⟩
    have hpsrc : p ∈ ec.source := by
      rw [hp]
      exact ec.map_target hRt
    have hep : ec p = jointFlow X b (x + L s) := by
      rw [hp]
      exact ec.right_inv hRt
    have hps : p.2 = s := by
      refine hinj (hsrc p hpsrc).1 hs.2 ?_
      change F (x + L p.2) = F (x + L s)
      rw [← (hsrc p hpsrc).2, hep]
      exact flow_jointField_levelSet hX hF htan b (hM.mem_flowDomain b 1 _ hsM)
    refine ⟨hsM, ?_⟩
    change jointFlow X (b - (ec.symm (jointFlow X b (x + L s))).1) (x + L s) = x + L s
    rw [← hp, sub_eq_neg_add, jointFlow_add hX hc hM (-p.1) b hsM, ← hep, hec, hps]
    exact jointFlow_neg hX hc hM p.1 hsM

end ProjectAinos.SmoothGeometry.NonlinearODE
