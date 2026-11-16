/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.PropagatorDet
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The variational equation of a given family of solutions

Let `Φ(t, x)` be a family of solutions of `ẋ = X(x)` near a point, twice
continuously differentiable in `(t, x)`. The derivative `M(t) = D_x Φ(t, x)`
with respect to the initial point satisfies the variational equation

`M' = DX(Φ(t, x)) M`.

The proof exchanges the derivatives in `t` and in `x`, by the symmetry of the
second derivative. No family is constructed here: `Φ` is given.
-/

@[expose] public section
noncomputable section

open Set Filter ContinuousLinearMap
open scoped Topology

namespace ProjectAInos.SmoothGeometry.NonlinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative in the initial point of a differentiable family, as a
restriction of the full derivative. -/
theorem hasFDerivAt_slice {Φ : ℝ × E → E} {p : ℝ × E} (hp : DifferentiableAt ℝ Φ p) :
    HasFDerivAt (fun y => Φ (p.1, y)) (fderiv ℝ Φ p ∘L ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
  hp.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)

/-- The derivative in the time of a differentiable family. -/
theorem hasDerivAt_slice_time {Φ : ℝ × E → E} {p : ℝ × E} (hp : DifferentiableAt ℝ Φ p) :
    HasDerivAt (fun s => Φ (s, p.2)) (fderiv ℝ Φ p (1, 0)) p.1 :=
  hp.hasFDerivAt.comp_hasDerivAt p.1 ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))

/-- The variational equation: the derivative in the initial point of a family of
solutions solves the linearized equation along the solution. -/
theorem hasDerivAt_fderiv_of_isLocalFlow {Φ : ℝ × E → E} {X : E → E} {t : ℝ} {x : E}
    (hΦ : ContDiffAt ℝ 2 Φ (t, x)) (hX : DifferentiableAt ℝ X (Φ (t, x)))
    (hsol : ∀ᶠ p in 𝓝 (t, x), HasDerivAt (fun s => Φ (s, p.2)) (X (Φ p)) p.1) :
    HasDerivAt (fun s => fderiv ℝ (fun y => Φ (s, y)) x)
      (fderiv ℝ X (Φ (t, x)) ∘L fderiv ℝ (fun y => Φ (t, y)) x) t := by
  have hdiff : ∀ᶠ p in 𝓝 (t, x), DifferentiableAt ℝ Φ p :=
    (hΦ.eventually (by simp)).mono fun p hp => hp.differentiableAt (by simp)
  have hΦ' : DifferentiableAt ℝ (fderiv ℝ Φ) (t, x) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsymm := hΦ.isSymmSndFDerivAt (by simp)
  have hΦ0 : DifferentiableAt ℝ Φ (t, x) := hΦ.differentiableAt (by simp)
  -- the derivative in the time of `s ↦ DΦ(s, x)` restricted to the initial point
  have hG : HasDerivAt (fun s => fderiv ℝ Φ (s, x) ∘L ContinuousLinearMap.inr ℝ ℝ E)
      (fderiv ℝ (fderiv ℝ Φ) (t, x) (1, 0) ∘L ContinuousLinearMap.inr ℝ ℝ E) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : E)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have h2 := hΦ'.hasFDerivAt.comp_hasDerivAt t h1
    have h3 := h2.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ E))
    simpa using h3
  have hev : (fun s => fderiv ℝ (fun y => Φ (s, y)) x) =ᶠ[𝓝 t]
      fun s => fderiv ℝ Φ (s, x) ∘L ContinuousLinearMap.inr ℝ ℝ E := by
    have hc : Tendsto (fun s : ℝ => (s, x)) (𝓝 t) (𝓝 (t, x)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    filter_upwards [hc.eventually hdiff] with s hs
    exact (hasFDerivAt_slice hs).fderiv
  refine (hG.congr_of_eventuallyEq hev).congr_deriv ?_
  have hslice0 := hasFDerivAt_slice hΦ0
  -- the two functions of the initial point that agree near `x`
  have hh : HasFDerivAt (fun y : E => fderiv ℝ Φ (t, y) (1, 0))
      ((fderiv ℝ (fderiv ℝ Φ) (t, x) ∘L ContinuousLinearMap.inr ℝ ℝ E).flip (1, 0)) x := by
    have h2 := hΦ'.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    have h3 := h2.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : E)) x)
    simpa using h3
  have hk : HasFDerivAt (fun y : E => X (Φ (t, y)))
      (fderiv ℝ X (Φ (t, x)) ∘L (fderiv ℝ Φ (t, x) ∘L ContinuousLinearMap.inr ℝ ℝ E)) x :=
    hX.hasFDerivAt.comp x hslice0
  have hev' : (fun y : E => fderiv ℝ Φ (t, y) (1, 0)) =ᶠ[𝓝 x] fun y => X (Φ (t, y)) := by
    have hc : Tendsto (fun y : E => (t, y)) (𝓝 x) (𝓝 (t, x)) :=
      (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [hc.eventually hdiff, hc.eventually hsol] with y hy hsy
    exact (hasDerivAt_slice_time hy).unique hsy
  have hD := (hk.congr_of_eventuallyEq hev').unique hh
  ext v
  rw [hslice0.fderiv]
  have hv := congrArg (fun L : E →L[ℝ] E => L v) hD
  change fderiv ℝ X (Φ (t, x)) (fderiv ℝ Φ (t, x) (0, v)) =
    fderiv ℝ (fderiv ℝ Φ) (t, x) (0, v) (1, 0) at hv
  change fderiv ℝ (fderiv ℝ Φ) (t, x) (1, 0) (0, v) =
    fderiv ℝ X (Φ (t, x)) (fderiv ℝ Φ (t, x) (0, v))
  rw [hv]
  exact hsymm _ _

end ProjectAInos.SmoothGeometry.NonlinearODE
