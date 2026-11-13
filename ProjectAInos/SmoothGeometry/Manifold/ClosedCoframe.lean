/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Integrating a closed coframe to local coordinates

A smooth vector-valued closed one-form on an open convex coordinate domain
has a smooth primitive. If its values are invertible, that primitive gives
actual smooth local coordinate maps. This is the integration step for a
parallel coframe; construction of the coframe is a separate obligation.
-/

@[expose] public section
noncomputable section

open ContinuousLinearMap Set
open scoped ContDiff Topology Manifold

namespace ProjectAInos.SmoothGeometry.ClosedCoframe

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Poincaré's primitive is smooth because its derivative is the given smooth
one-form. The closedness hypothesis uses the ordinary Fréchet derivative. -/
theorem exists_smooth_primitive {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {θ : E → E →L[ℝ] F} (hθ : ContDiffOn ℝ ∞ θ U)
    (hclosed : ∀ x ∈ U, ∀ u v, fderiv ℝ θ x u v = fderiv ℝ θ x v u) :
    ∃ f : E → F, ContDiffOn ℝ ∞ f U ∧ ∀ x ∈ U, HasFDerivAt f (θ x) x := by
  obtain ⟨f, hf⟩ := hconv.exists_forall_hasFDerivAt_of_fderiv_symmetric hU
    (hθ.differentiableOn (by simp)) hclosed
  refine ⟨f, (contDiffOn_infty_iff_fderiv_of_isOpen hU).mpr ⟨?_, ?_⟩, hf⟩
  · exact fun x hx => (hf x hx).differentiableAt.differentiableWithinAt
  · exact hθ.congr (fun x hx => (hf x hx).fderiv)

/-- An invertible smooth closed coframe integrates to a centered smooth local
chart with exactly the prescribed derivative throughout its source. -/
theorem exists_chart [CompleteSpace E] {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {θ : E → E →L[ℝ] E} (hθ : ContDiffOn ℝ ∞ θ U)
    (hclosed : ∀ x ∈ U, ∀ u v, fderiv ℝ θ x u v = fderiv ℝ θ x v u)
    (hinv : ∀ x ∈ U, (θ x).IsInvertible) {p : E} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph E E, p ∈ e.source ∧ e.source ⊆ U ∧ e p = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x ∈ e.source, HasFDerivAt e (θ x) x := by
  obtain ⟨f, hf, hdf⟩ := exists_smooth_primitive hU hconv hθ hclosed
  let q : E → E := fun x => f x - f p
  have hq : ContDiffOn ℝ ∞ q U := hf.sub contDiffOn_const
  have hdq (x) (hx : x ∈ U) : HasFDerivAt q (θ x) x := (hdf x hx).sub_const (f p)
  obtain ⟨L, hL⟩ := hinv p hp
  have hd : HasFDerivAt q (L : E →L[ℝ] E) p := by rw [hL]; exact hdq p hp
  let e₀ := (hq.contDiffAt (hU.mem_nhds hp)).toOpenPartialHomeomorph q hd (by simp)
  let e := e₀.restrOpen U hU
  have hep : p ∈ e.source :=
    ⟨(hq.contDiffAt (hU.mem_nhds hp)).mem_toOpenPartialHomeomorph_source hd (by simp), hp⟩
  have heq : (⇑e : E → E) = q := rfl
  refine ⟨e, hep, fun _ hx => hx.2, ?_, ?_, ?_, ?_⟩
  · change f p - f p = 0
    exact sub_self _
  · rw [heq]
    exact hq.mono (fun _ hx => hx.2)
  · intro y hy
    have hx : e.symm y ∈ U := (e.map_target hy).2
    obtain ⟨A, hA⟩ := hinv (e.symm y) hx
    have hde : HasFDerivAt e (A : E →L[ℝ] E) (e.symm y) := by
      rw [heq, hA]
      exact hdq _ hx
    have hce : ContDiffAt ℝ ∞ e (e.symm y) := by
      rw [heq]
      exact hq.contDiffAt (hU.mem_nhds hx)
    exact (e.contDiffAt_symm hy hde hce).contDiffWithinAt
  · intro x hx
    rw [heq]
    exact hdq x hx.2

/-- Integration of a coordinate coframe gives a chart in the manifold's
smooth maximal atlas. Its transition derivative equals the coframe on the
whole new chart source, not merely at its center. -/
theorem exists_manifoldChart [CompleteSpace E] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {θ : E → E →L[ℝ] E} (hθ : ContDiffOn ℝ ∞ θ U)
    (hclosed : ∀ x ∈ U, ∀ u v, fderiv ℝ θ x u v = fderiv ℝ θ x v u)
    (hinv : ∀ x ∈ U, (θ x).IsInvertible) {p : M} (hp : p ∈ e.source) (hpU : e p ∈ U) :
    ∃ e' : OpenPartialHomeomorph M E, e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      p ∈ e'.source ∧ e' p = 0 ∧ e'.source ⊆ e.source ∧
      ∀ x ∈ e'.source, e x ∈ U ∧ HasFDerivAt (e' ∘ e.symm) (θ (e x)) (e x) := by
  obtain ⟨c, hc, hcU, hc0, hf, hi, hd⟩ := exists_chart hU hconv hθ hclosed hinv hpU
  let e' := e.trans c
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := by
    apply e'.mem_maximalAtlas_of_contMDiffOn
    · intro x hx
      exact (((hf.contDiffAt (c.open_source.mem_nhds hx.2)).contMDiffAt).comp x
        (contMDiffAt_of_mem_maximalAtlas he hx.1)).contMDiffWithinAt
    · intro y hy
      exact ((contMDiffAt_symm_of_mem_maximalAtlas he hy.2).comp y
        (hi.contDiffAt (c.open_target.mem_nhds hy.1)).contMDiffAt).contMDiffWithinAt
  refine ⟨e', he', ⟨hp, hc⟩, hc0, fun _ hx => hx.1, ?_⟩
  intro x hx
  refine ⟨hcU hx.2, (hd _ hx.2).congr_of_eventuallyEq ?_⟩
  filter_upwards [e.open_target.mem_nhds (e.map_source hx.1)] with y hy
  change c (e (e.symm y)) = c y
  rw [e.right_inv hy]

end ProjectAInos.SmoothGeometry.ClosedCoframe
