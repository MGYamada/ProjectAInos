/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Quadratic coordinate corrections

A symmetric bilinear second derivative and an invertible first derivative
determine a quadratic local coordinate change. The analytic regularity used
here belongs to the polynomial map, not to charts on a smooth manifold.
-/

@[expose] public section
noncomputable section

open ContinuousLinearMap Set Filter
open scoped ContDiff Topology Manifold

namespace ProjectAInos.SmoothGeometry.QuadraticChart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A translated quadratic polynomial with prescribed linear part. -/
def correction (L : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (a x : E) : E :=
  L (x - a) + (1 / 2 : ℝ) • B (x - a) (x - a)

@[simp] theorem correction_self (L : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (a : E) :
    correction L B a a = 0 := by simp [correction]

theorem correction_contDiff (L : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (a : E) :
    ContDiff ℝ ω (correction L B a) := by
  unfold correction
  fun_prop

/-- Symmetry gives the affine derivative `L + B(x-a,·)`. -/
theorem correction_hasFDerivAt (L : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u) (a x : E) :
    HasFDerivAt (correction L B a) ((L : E →L[ℝ] E) + B (x - a)) x := by
  have hx := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const a
  have h := (L.hasFDerivAt.comp x hx).add ((B.hasFDerivAt_of_bilinear hx hx).const_smul (1 / 2 : ℝ))
  convert h using 1
  · rfl
  · ext v
    simp only [add_apply, comp_apply, id_apply, smul_apply, precompR_apply, precompL_apply,
      compL_apply, id_eq]
    rw [hB v (x - a), ← two_smul ℝ, smul_smul]
    norm_num

theorem correction_fderiv (L : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u) (a x : E) :
    fderiv ℝ (correction L B a) x = (L : E →L[ℝ] E) + B (x - a) :=
  (correction_hasFDerivAt L B hB a x).fderiv

/-- The second derivative, in either ordered pair of directions, is `B`. -/
theorem correction_second (L : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u) (a x u v : E) :
    fderiv ℝ (fun y => fderiv ℝ (correction L B a) y v) x u = B u v := by
  simp_rw [correction_fderiv L B hB a]
  have h := ((B.flip v).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)).const_add (L v)
  simpa only [add_apply, comp_id, flip_apply, Function.comp_apply, id_eq,
    ContinuousLinearEquiv.coe_coe] using
    congrArg (fun A : E →L[ℝ] E => A u) h.fderiv

/-- A globally analytic map with invertible derivative has a local
homeomorphism whose forward and inverse maps are smooth on their domains.
Shrinking the inverse's source supplies a single smooth neighborhood. -/
theorem exists_smoothLocalInverse [CompleteSpace E] {f : E → E} {a : E}
    (hf : ContDiff ℝ ω f) (L : E ≃L[ℝ] E) (hd : HasFDerivAt f (L : E →L[ℝ] E) a) :
    ∃ e : OpenPartialHomeomorph E E, a ∈ e.source ∧ (⇑e = f) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let e₀ := hf.contDiffAt.toOpenPartialHomeomorph f hd (by simp)
  have ha : a ∈ e₀.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hi : ContDiffAt ℝ ω e₀.symm (f a) := hf.contDiffAt.to_localInverse hd (by simp)
  obtain ⟨U, hUsub, hUopen, hUa⟩ := mem_nhds_iff.mp (hi.eventually (by simp))
  let r := e₀.symm.restrOpen U hUopen
  have hra : f a ∈ r.source := ⟨e₀.map_source ha, hUa⟩
  have hri : r (f a) = a := e₀.left_inv ha
  refine ⟨r.symm, ?_, rfl, (hf.of_le (by simp)).contDiffOn, ?_⟩
  · rw [← hri]
    exact r.map_source hra
  · intro y hy
    have hyi : ContDiffAt ℝ ω e₀.symm y := hUsub hy.2
    exact (hyi.of_le (by simp)).contDiffWithinAt

/-- The quadratic polynomial is a genuine smooth local coordinate change,
with the prescribed first and second derivatives at its center. -/
theorem exists_chart [CompleteSpace E] (L : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u) (a : E) :
    ∃ e : OpenPartialHomeomorph E E, a ∈ e.source ∧ e a = 0 ∧
      (⇑e = correction L B a) ∧ ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ fderiv ℝ e a = (L : E →L[ℝ] E) ∧
      ∀ u v, fderiv ℝ (fun y => fderiv ℝ e y v) a u = B u v := by
  have hd : HasFDerivAt (correction L B a) (L : E →L[ℝ] E) a := by
    simpa only [sub_self, map_zero, add_zero] using correction_hasFDerivAt L B hB a a
  obtain ⟨e, ha, he, hf, hi⟩ := exists_smoothLocalInverse (correction_contDiff L B a) L hd
  refine ⟨e, ha, ?_, he, hf, hi, ?_, ?_⟩
  · rw [he, correction_self]
  · rw [he]
    exact hd.fderiv
  · intro u v
    rw [he]
    exact correction_second L B hB a a u v

/-- On any smooth manifold, a prescribed invertible first derivative and
symmetric second derivative can be realized by an actual smooth chart
transition. Only the coordinate correction is analytic. -/
theorem exists_manifoldChart [CompleteSpace E] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {p : M} (hp : p ∈ e.source)
    (L : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u) :
    ∃ e' : OpenPartialHomeomorph M E, e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      p ∈ e'.source ∧ e' p = 0 ∧ fderiv ℝ (e' ∘ e.symm) (e p) = (L : E →L[ℝ] E) ∧
      ∀ u v, fderiv ℝ (fun y => fderiv ℝ (e' ∘ e.symm) y v) (e p) u = B u v := by
  obtain ⟨c, hc, hc0, hec, hf, hi, hd, hdd⟩ := exists_chart L B hB (e p)
  let e' := e.trans c
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := by
    apply e'.mem_maximalAtlas_of_contMDiffOn
    · intro x hx
      exact (((hf.contDiffAt (c.open_source.mem_nhds hx.2)).contMDiffAt).comp x
        (contMDiffAt_of_mem_maximalAtlas he hx.1)).contMDiffWithinAt
    · intro y hy
      exact ((contMDiffAt_symm_of_mem_maximalAtlas he hy.2).comp y
        (hi.contDiffAt (c.open_target.mem_nhds hy.1)).contMDiffAt).contMDiffWithinAt
  have heq : e' ∘ e.symm =ᶠ[𝓝 (e p)] c := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hp)] with y hy
    change c (e (e.symm y)) = c y
    rw [e.right_inv hy]
  refine ⟨e', he', ⟨hp, hc⟩, hc0, heq.fderiv_eq.trans hd, ?_⟩
  intro u v
  have hder : (fun y => fderiv ℝ (e' ∘ e.symm) y v) =ᶠ[𝓝 (e p)]
      (fun y => fderiv ℝ c y v) :=
    heq.eventuallyEq_nhds.mono fun y hy => congrArg (fun A : E →L[ℝ] E => A v) hy.fderiv_eq
  rw [hder.fderiv_eq]
  exact hdd u v

end ProjectAInos.SmoothGeometry.QuadraticChart
