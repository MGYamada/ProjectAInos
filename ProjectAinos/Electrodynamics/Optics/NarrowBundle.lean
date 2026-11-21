/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.Riccati
public import ProjectAinos.SmoothGeometry.ODE.Flow
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Narrow bundles of rays

Landau–Lifshitz, *The Classical Theory of Fields*, §56, and the loss of the estimate of geometrical
optics at a focal point (§58).

Let `ψ` be a `C³` solution of the static eikonal equation `|∇ψ|² = 1` on an open set `U ⊆ ℝ³`
(a homogeneous medium). Its second derivative is written as the operator `hessian ψ x = D(∇ψ)(x)`.

* `hessian_apply_gradient`: `D²ψ ∇ψ = 0`; hence `gradient_ray`: the line
  `ray ψ x₀ l = x₀ + l ∇ψ(x₀)` is a ray, `∇ψ(x(l)) = ∇ψ(x₀)` while the segment stays in `U`.
* `hessian_hasDerivAt`: along the ray, `d/dl D²ψ(x(l)) = −(D²ψ(x(l)))²`, and `hessian_ray`:
  `D²ψ(x(l)) = H₀ (1 + l H₀)⁻¹` with `H₀ = D²ψ(x₀)`; `1 + l H₀` is invertible.
* `principalRadius_add`: a principal radius `R` of the wave front becomes `R + l`;
  `focal_iff`: `det(1 + l H₀) = 0` exactly when `l = −R` for a principal radius `R`, and
  `exists_not_mem_of_det_eq_zero`: no segment of a ray in `U` reaches a focal point.
* `laplacian_eq_traceCLM_hessian`: `Δψ = tr D²ψ`. `amplitude_ray`: a solution `a` of the transport
  equation `2⟨∇a, ∇ψ⟩ + a Δψ = 0` is `a(x(l)) = a(x₀) / √det(1 + l H₀)` along the ray, and
  `amplitude_tendsto_focal`: at a focal point `|a(x(l))| → ∞`.

For the rays of a smooth index `n` on all of `ℝ³`:

* `rayField n (q, p) = (p, ∇(n²/2)(q))` on the phase space `ℝ³ × ℝ³`, whose flow
  `NonlinearODE.flow (rayField n)` gives the rays.
* `transverseMap_hasDerivAt`: the linearized ray map `transverseMap n t z` solves the variational
  equation; `norm_beam_sub_linear_le`: a narrow beam of width `δ` about a ray deviates from the
  linearized map by `O(δ²)` uniformly on a compact set of times.

Instances: the front `convergingFront P c x = −‖P(x − c)‖` of an orthogonal projection `P`
(spherical for `P = 1`, cylindrical for the projection orthogonal to an axis), with its focal
points (`focal_sphericalFront_iff`, `focal_cylindricalFront_iff`) and the amplitude `1/r` of a
spherical wave (`amplitude_tendsto_sphericalFront`); for the ray field, the homogeneous medium,
in which the linearized map is exact (`beam_sub_linear_const`).
-/

@[expose] public section

noncomputable section

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace ContDiff Laplacian

namespace ProjectAinos.Electrodynamics.Optics.NarrowBundle

open SmoothGeometry LinearODE NonlinearODE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Gradient and second derivative -/

/-- The second derivative `D²ψ(x)` of a function on `ℝ³`, as the operator `D(∇ψ)(x)`. -/
def hessian (ψ : E3 → ℝ) (x : E3) : E3 →L[ℝ] E3 := fderiv ℝ (∇ ψ) x

/-- The straight line `x₀ + l ∇ψ(x₀)` from `x₀` in the direction of the gradient: the ray through
`x₀` of a solution of the eikonal equation in a homogeneous medium (`gradient_ray`). -/
def ray (ψ : E3 → ℝ) (x₀ : E3) (l : ℝ) : E3 := x₀ + l • ∇ ψ x₀

variable {ψ : E3 → ℝ} {U : Set E3}

theorem ray_zero (ψ : E3 → ℝ) (x₀ : E3) : ray ψ x₀ 0 = x₀ := by
  simp [ray]

theorem hasDerivAt_ray (ψ : E3 → ℝ) (x₀ : E3) (l : ℝ) :
    HasDerivAt (ray ψ x₀) (∇ ψ x₀) l :=
  (((hasDerivAt_id l).smul_const (∇ ψ x₀)).const_add x₀).congr_deriv (one_smul ℝ _)

theorem continuous_ray (ψ : E3 → ℝ) (x₀ : E3) : Continuous (ray ψ x₀) :=
  continuous_const.add (continuous_id.smul continuous_const)

/-- The derivative of a function is the inner product with its gradient. -/
theorem fderiv_eq_innerSL_gradient (ψ : E3 → ℝ) :
    fderiv ℝ ψ = fun x => innerSL ℝ (∇ ψ x) := by
  funext x
  ext v
  rw [innerSL_apply_apply, gradient, toDual_symm_apply]

/-- The gradient of a `Cⁿ` function is `Cᵐ` for `m + 1 ≤ n`. -/
theorem contDiffAt_gradient {m n : WithTop ℕ∞} {x : E3} (hψ : ContDiffAt ℝ n ψ x)
    (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (∇ ψ) x :=
  ((toDual ℝ E3).symm.toContinuousLinearEquiv.contDiff.contDiffAt).comp x (hψ.fderiv_right hmn)

theorem contDiff_gradient {m n : WithTop ℕ∞} (hψ : ContDiff ℝ n ψ) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (∇ ψ) :=
  (toDual ℝ E3).symm.toContinuousLinearEquiv.contDiff.comp (hψ.fderiv_right hmn)

theorem contDiffOn_gradient {m n : WithTop ℕ∞} (hU : IsOpen U) (hψ : ContDiffOn ℝ n ψ U)
    (hmn : m + 1 ≤ n) : ContDiffOn ℝ m (∇ ψ) U := fun _ hx =>
  (contDiffAt_gradient (hψ.contDiffAt (hU.mem_nhds hx)) hmn).contDiffWithinAt

theorem differentiableAt_gradient {x : E3} (hψ : ContDiffAt ℝ 2 ψ x) :
    DifferentiableAt ℝ (∇ ψ) x :=
  (contDiffAt_gradient (m := 1) hψ (by norm_num)).differentiableAt one_ne_zero

/-- The second derivative is the inner product with the Hessian:
`D²ψ(x)(u, v) = ⟨D²ψ(x) u, v⟩`. -/
theorem fderiv_fderiv_apply {x : E3} (hx : DifferentiableAt ℝ (∇ ψ) x) (u v : E3) :
    fderiv ℝ (fderiv ℝ ψ) x u v = ⟪hessian ψ x u, v⟫ := by
  have h : HasFDerivAt (fderiv ℝ ψ)
      ((innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ).comp (hessian ψ x)) x := by
    rw [fderiv_eq_innerSL_gradient ψ]
    exact (innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ).hasFDerivAt.comp x hx.hasFDerivAt
  rw [h.fderiv]
  simp [innerSL_apply_apply]

/-- The Hessian of a `C²` function is symmetric. -/
theorem inner_hessian_comm {x : E3} (hψ : ContDiffAt ℝ 2 ψ x) (u v : E3) :
    ⟪hessian ψ x u, v⟫ = ⟪u, hessian ψ x v⟫ := by
  have hd := differentiableAt_gradient hψ
  have hs := hψ.isSymmSndFDerivAt (by simp)
  rw [← fderiv_fderiv_apply hd, hs u v, fderiv_fderiv_apply hd, real_inner_comm]

/-- The Laplacian is the trace of the Hessian. -/
theorem laplacian_eq_traceCLM_hessian {x : E3} (hψ : ContDiffAt ℝ 2 ψ x) :
    Δ ψ x = traceCLM (hessian ψ x) := by
  have hd := differentiableAt_gradient hψ
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis ψ b) x, traceCLM_apply,
    LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_apply hd, real_inner_comm]
  rfl

/-! ### The eikonal equation along a ray -/

/-- Differentiating the eikonal equation: `⟨∇ψ, D²ψ v⟩ = 0`. -/
theorem inner_gradient_hessian_eq_zero (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x : E3} (hx : x ∈ U) (v : E3) :
    ⟪∇ ψ x, hessian ψ x v⟫ = 0 := by
  have hd := differentiableAt_gradient (hψ.contDiffAt (hU.mem_nhds hx))
  have h1 := hd.hasFDerivAt.norm_sq
  have h2 : HasFDerivAt (fun y => ‖∇ ψ y‖ ^ 2) (0 : E3 →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => heik y hy)
  have h3 := congrArg (fun L : E3 →L[ℝ] ℝ => L v) (h1.unique h2)
  simp only [smul_apply, comp_apply, innerSL_apply_apply, zero_apply, nsmul_eq_mul,
    Nat.cast_ofNat] at h3
  change 2 * ⟪∇ ψ x, hessian ψ x v⟫ = 0 at h3
  linarith

/-- **The rays are straight (§56)**: for a solution of the eikonal equation, `D²ψ ∇ψ = 0`. -/
theorem hessian_apply_gradient (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x : E3} (hx : x ∈ U) :
    hessian ψ x (∇ ψ x) = 0 := by
  have h := inner_gradient_hessian_eq_zero hU hψ heik hx (hessian ψ x (∇ ψ x))
  rw [← inner_hessian_comm (hψ.contDiffAt (hU.mem_nhds hx))] at h
  exact inner_self_eq_zero.mp h

/-- The derivative of the Hessian along the gradient: `D³ψ(∇ψ) = −(D²ψ)²`, obtained by
differentiating `D²ψ ∇ψ = 0`. -/
theorem fderiv_hessian_apply_gradient (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x : E3} (hx : x ∈ U) :
    fderiv ℝ (hessian ψ) x (∇ ψ x) = -(hessian ψ x * hessian ψ x) := by
  have hψx := hψ.contDiffAt (hU.mem_nhds hx)
  have hg : ContDiffAt ℝ 2 (∇ ψ) x := contDiffAt_gradient hψx (by norm_num)
  have hHd : DifferentiableAt ℝ (hessian ψ) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hgd : DifferentiableAt ℝ (∇ ψ) x := hg.differentiableAt (by norm_num)
  have hψ2 : ContDiffOn ℝ 2 ψ U := hψ.of_le (by norm_num)
  have h1 := hHd.hasFDerivAt.clm_apply hgd.hasFDerivAt
  have h2 : HasFDerivAt (fun y => hessian ψ y (∇ ψ y)) (0 : E3 →L[ℝ] E3) x :=
    (hasFDerivAt_const (0 : E3) x).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy =>
        hessian_apply_gradient hU hψ2 heik hy)
  have h3 := h1.unique h2
  have hsymm := hg.isSymmSndFDerivAt (by simp)
  ext1 v
  have h4 := congrArg (fun L : E3 →L[ℝ] E3 => L v) h3
  simp only [add_apply, comp_apply, flip_apply, zero_apply] at h4
  have h5 : fderiv ℝ (hessian ψ) x v (∇ ψ x) = fderiv ℝ (hessian ψ) x (∇ ψ x) v :=
    hsymm v (∇ ψ x)
  rw [neg_apply, mul_apply_eq_comp, ← h5]
  exact eq_neg_of_add_eq_zero_right h4

/-- **The ray stays a ray (§56)**: while the segment `x₀ + s ∇ψ(x₀)`, `s` between `0` and `l`,
stays in `U`, the gradient is constant along it, `∇ψ(x(l)) = ∇ψ(x₀)`. -/
theorem gradient_ray (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l : ℝ}
    (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) : ∇ ψ (ray ψ x₀ l) = ∇ ψ x₀ := by
  have hgd : ∀ s ∈ uIcc 0 l,
      HasFDerivAt (∇ ψ) (hessian ψ (ray ψ x₀ s)) (ray ψ x₀ s) := fun s hs =>
    (differentiableAt_gradient (hψ.contDiffAt (hU.mem_nhds (hseg s hs)))).hasFDerivAt
  have hcont : ContinuousOn (fun s => hessian ψ (ray ψ x₀ s)) (uIcc 0 l) := by
    have hc := (contDiffOn_gradient (m := 1) hU hψ (by norm_num)).continuousOn_fderiv_of_isOpen
      hU le_rfl
    exact hc.comp (continuous_ray ψ x₀).continuousOn fun s hs => hseg s hs
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hcont
  have hw := Riccati.eqOn_zero_of_hasDerivAt (A := fun s => -hessian ψ (ray ψ x₀ s))
    (w := fun s => ∇ ψ (ray ψ x₀ s) - ∇ ψ x₀) (fun s hs => by rw [norm_neg]; exact hC s hs)
    (fun s hs => by
      have h := ((hgd s hs).comp_hasDerivAt s (hasDerivAt_ray ψ x₀ s)).sub_const (∇ ψ x₀)
      refine h.congr_deriv ?_
      simp only [neg_apply, map_sub, hessian_apply_gradient hU hψ heik (hseg s hs)]
      simp)
    (by simp [ray_zero])
  have := hw right_mem_uIcc
  simpa [sub_eq_zero] using this

/-- **The Hessian along a ray (§56)**: `d/dl D²ψ(x(l)) = −(D²ψ(x(l)))²` while the segment of the
ray stays in `U`. -/
theorem hessian_hasDerivAt (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l : ℝ}
    (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) :
    HasDerivAt (fun s => hessian ψ (ray ψ x₀ s))
      (-(hessian ψ (ray ψ x₀ l) * hessian ψ (ray ψ x₀ l))) l := by
  have hx := hseg l right_mem_uIcc
  have hψx := hψ.contDiffAt (hU.mem_nhds hx)
  have hHd : DifferentiableAt ℝ (hessian ψ) (ray ψ x₀ l) :=
    ((contDiffAt_gradient (m := 2) hψx (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt one_ne_zero
  refine (hHd.hasFDerivAt.comp_hasDerivAt l (hasDerivAt_ray ψ x₀ l)).congr_deriv ?_
  rw [← fderiv_hessian_apply_gradient hU hψ heik hx,
    gradient_ray hU (hψ.of_le (by norm_num)) heik hseg]

theorem hessian_hasDerivAt_of_mem (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l : ℝ}
    (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) :
    ∀ s ∈ uIcc 0 l, HasDerivAt (fun r => hessian ψ (ray ψ x₀ r))
      (-(hessian ψ (ray ψ x₀ s) * hessian ψ (ray ψ x₀ s))) s := fun _ hs =>
  hessian_hasDerivAt hU hψ heik fun t ht => hseg t (uIcc_subset_uIcc left_mem_uIcc hs ht)

/-- **The Hessian along a ray (§56)**: `D²ψ(x(l)) = H₀ (1 + l H₀)⁻¹` with `H₀ = D²ψ(x₀)`, while
the segment of the ray stays in `U`. -/
theorem hessian_ray (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l : ℝ}
    (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) :
    hessian ψ (ray ψ x₀ l) = hessian ψ x₀ * Ring.inverse (1 + l • hessian ψ x₀) :=
  Riccati.matrix_eq_of_hasDerivAt (hessian_hasDerivAt_of_mem hU hψ heik hseg)
    (by simp only [ray_zero])

/-- While the segment of the ray stays in `U`, `1 + l D²ψ(x₀)` is invertible. -/
theorem isUnit_one_add_smul_hessian (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l : ℝ}
    (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) : IsUnit (1 + l • hessian ψ x₀) :=
  (Riccati.isUnit_one_add_smul (hessian_hasDerivAt_of_mem hU hψ heik hseg)
    (by simp only [ray_zero])).1

/-! ### Principal radii of curvature and focal points -/

/-- **The principal radii of curvature (§56)**: if `v` is an eigenvector of `D²ψ(x₀)` with
eigenvalue `1/R`, a principal direction of the wave front with radius of curvature `R`, then it
is an eigenvector of `D²ψ(x(l))` with eigenvalue `1/(R + l)`: the radius becomes `R + l`. By
`gradient_ray`, `v` stays orthogonal to the ray. -/
theorem principalRadius_add (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l : ℝ}
    (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) {R : ℝ} (hR : R ≠ 0) {v : E3}
    (hv : hessian ψ x₀ v = R⁻¹ • v) :
    hessian ψ (ray ψ x₀ l) v = (R + l)⁻¹ • v := by
  obtain ⟨-, h2⟩ := Riccati.one_add_smul_mul_eq (H₀ := hessian ψ x₀)
    (hessian_hasDerivAt_of_mem hU hψ heik hseg) (by simp only [ray_zero])
  have h3 := congrArg (fun L : E3 →L[ℝ] E3 => L v) h2
  simp only [mul_apply_eq_comp, add_apply, one_apply_eq_self, smul_apply, hv, map_add,
    map_smul] at h3
  have h4 : (1 + l * R⁻¹) • hessian ψ (ray ψ x₀ l) v = R⁻¹ • v := by
    rw [add_smul, one_smul, mul_smul]
    exact h3
  by_cases hRl : R + l = 0
  · have hc : 1 + l * R⁻¹ = 0 := by
      field_simp
      linarith
    rw [hc, zero_smul] at h4
    have hv0 : v = 0 := (smul_eq_zero.mp h4.symm).resolve_left (inv_ne_zero hR)
    simp [hv0]
  · have hc : 1 + l * R⁻¹ ≠ 0 := by
      have : 1 + l * R⁻¹ = (R + l) * R⁻¹ := by field_simp
      rw [this]
      exact mul_ne_zero hRl (inv_ne_zero hR)
    calc hessian ψ (ray ψ x₀ l) v
        = (1 + l * R⁻¹)⁻¹ • ((1 + l * R⁻¹) • hessian ψ (ray ψ x₀ l) v) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = (R + l)⁻¹ • v := by
          rw [h4, smul_smul]
          congr 1
          field_simp

/-- **The focal points (§56)**: `det(1 + l D²ψ(x₀)) = 0` exactly when `l = −R` for a principal
radius of curvature `R` of the wave front at `x₀`, that is, an eigenvalue `1/R ≠ 0` of
`D²ψ(x₀)` with an eigenvector orthogonal to `∇ψ(x₀)`. -/
theorem focal_iff (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} (hx₀ : x₀ ∈ U) (l : ℝ) :
    LinearMap.det ((1 + l • hessian ψ x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0 ↔
      ∃ R : ℝ, R ≠ 0 ∧ l = -R ∧
        ∃ v : E3, v ≠ 0 ∧ ⟪v, ∇ ψ x₀⟫ = 0 ∧ hessian ψ x₀ v = R⁻¹ • v := by
  have hψx := hψ.contDiffAt (hU.mem_nhds hx₀)
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨v, hv, hv0⟩
    rw [LinearMap.mem_ker] at hv
    have hv' : v + l • hessian ψ x₀ v = 0 := by simpa using hv
    have hl : l ≠ 0 := by
      rintro rfl
      simp only [zero_smul, add_zero] at hv'
      exact hv0 hv'
    refine ⟨-l, neg_ne_zero.mpr hl, (neg_neg l).symm, v, hv0, ?_, ?_⟩
    · have h1 : v = -(l • hessian ψ x₀ v) := eq_neg_of_add_eq_zero_left hv'
      rw [h1, inner_neg_left, real_inner_smul_left, inner_hessian_comm hψx,
        hessian_apply_gradient hU hψ heik hx₀]
      simp
    · have h1 : l • hessian ψ x₀ v = -v := eq_neg_of_add_eq_zero_right hv'
      calc hessian ψ x₀ v = l⁻¹ • (l • hessian ψ x₀ v) := by
            rw [smul_smul, inv_mul_cancel₀ hl, one_smul]
        _ = (-l)⁻¹ • v := by rw [h1, inv_neg, neg_smul, smul_neg]
  · rintro ⟨R, hR, rfl, v, hv0, -, hv⟩
    refine ⟨v, ?_, hv0⟩
    rw [LinearMap.mem_ker]
    simp [hv, smul_smul, hR]

/-- **No ray of `U` reaches a focal point**: if `det(1 + l D²ψ(x₀)) = 0`, the segment of the ray
between `0` and `l` leaves `U`. -/
theorem exists_not_mem_of_det_eq_zero (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l : ℝ}
    (hdet : LinearMap.det ((1 + l • hessian ψ x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0) :
    ∃ s ∈ uIcc 0 l, ray ψ x₀ s ∉ U := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact Riccati.det_ne_zero_of_isUnit (isUnit_one_add_smul_hessian hU hψ heik h) hdet

/-! ### The amplitude -/

/-- **The amplitude along a ray (§56)**: if `α′ = −α Δψ / 2` along the segment of the ray between
`0` and `l` (the transport equation `2⟨∇a, ∇ψ⟩ + a Δψ = 0` for `α(s) = a(x(s))`), then
`α(l) = α(0) / √det(1 + l D²ψ(x₀))`. -/
theorem amplitude_eq (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l : ℝ}
    (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) {α : ℝ → ℝ}
    (hα : ∀ s ∈ uIcc 0 l, HasDerivAt α (-(α s * Δ ψ (ray ψ x₀ s)) / 2) s) :
    α l = α 0 /
      Real.sqrt (LinearMap.det ((1 + l • hessian ψ x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3)) := by
  refine Riccati.eq_div_sqrt_det (hessian_hasDerivAt_of_mem hU hψ heik hseg)
    (by simp only [ray_zero]) fun s hs => ?_
  rw [← laplacian_eq_traceCLM_hessian ((hψ.contDiffAt (hU.mem_nhds (hseg s hs))).of_le
    (by norm_num))]
  exact hα s hs

/-- The derivative of a function along the ray is its inner product with `∇ψ` on the ray. -/
theorem hasDerivAt_comp_ray (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l : ℝ}
    (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) {a : E3 → ℝ}
    (ha : DifferentiableAt ℝ a (ray ψ x₀ l)) :
    HasDerivAt (fun s => a (ray ψ x₀ s)) ⟪∇ a (ray ψ x₀ l), ∇ ψ (ray ψ x₀ l)⟫ l := by
  refine (ha.hasFDerivAt.comp_hasDerivAt l (hasDerivAt_ray ψ x₀ l)).congr_deriv ?_
  rw [gradient_ray hU hψ heik hseg, fderiv_eq_innerSL_gradient a, innerSL_apply_apply]

/-- **The amplitude along a ray (§56)**: a solution `a` of the transport equation
`2⟨∇a, ∇ψ⟩ + a Δψ = 0` on `U` is `a(x(l)) = a(x₀) / √det(1 + l D²ψ(x₀))` while the segment of
the ray stays in `U`. -/
theorem amplitude_ray (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l : ℝ}
    (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) {a : E3 → ℝ}
    (ha : ∀ x ∈ U, DifferentiableAt ℝ a x)
    (htr : ∀ x ∈ U, 2 * ⟪∇ a x, ∇ ψ x⟫ + a x * Δ ψ x = 0) :
    a (ray ψ x₀ l) = a x₀ /
      Real.sqrt (LinearMap.det ((1 + l • hessian ψ x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3)) := by
  have h := amplitude_eq hU hψ heik hseg (α := fun s => a (ray ψ x₀ s)) fun s hs => by
    have hsub : ∀ t ∈ uIcc 0 s, ray ψ x₀ t ∈ U := fun t ht =>
      hseg t (uIcc_subset_uIcc left_mem_uIcc hs ht)
    refine (hasDerivAt_comp_ray hU (hψ.of_le (by norm_num)) heik hsub
      (ha _ (hseg s hs))).congr_deriv ?_
    have := htr _ (hseg s hs)
    linarith
  simpa only [ray_zero] using h

/-- **The amplitude at a focal point (§§56, 58)**: if the ray from `x₀` stays in `U` on `[0, l₀)`
and `l₀ > 0` is a focal point, `det(1 + l₀ D²ψ(x₀)) = 0`, a solution `a` of the transport
equation with `a(x₀) ≠ 0` tends to infinity along the ray: `|a(x(l))| → ∞` as `l → l₀⁻`. The
estimate of geometrical optics, which needs a bounded amplitude, is lost at a caustic. -/
theorem amplitude_tendsto_focal (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U)
    (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3} {l₀ : ℝ} (hl₀ : 0 < l₀)
    (hseg : ∀ s ∈ Ico 0 l₀, ray ψ x₀ s ∈ U) {a : E3 → ℝ}
    (ha : ∀ x ∈ U, DifferentiableAt ℝ a x)
    (htr : ∀ x ∈ U, 2 * ⟪∇ a x, ∇ ψ x⟫ + a x * Δ ψ x = 0)
    (hdet : LinearMap.det ((1 + l₀ • hessian ψ x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0)
    (h0 : a x₀ ≠ 0) :
    Tendsto (fun s => |a (ray ψ x₀ s)|) (𝓝[<] l₀) atTop := by
  have hsub : ∀ s ∈ Ico 0 l₀, ∀ t ∈ uIcc 0 s, ray ψ x₀ t ∈ U := by
    intro s hs t ht
    rw [uIcc_of_le hs.1] at ht
    exact hseg t ⟨ht.1, ht.2.trans_lt hs.2⟩
  refine Riccati.tendsto_abs_div_sqrt_det (α := fun s => a (ray ψ x₀ s)) hl₀
    (fun s hs => ?_) (fun s hs => ?_) hdet (by simpa only [ray_zero] using h0)
  · simpa only [ray_zero] using amplitude_ray hU hψ heik (hsub s hs) ha htr
  · exact Riccati.det_pos (hessian_hasDerivAt_of_mem hU hψ heik (hsub s hs))
      (by simp only [ray_zero]) s right_mem_uIcc

/-! ### The rays of a general medium: the linearized ray map -/

/-- The ray field `(q, p) ↦ (p, ∇(n²/2)(q))` on the phase space `ℝ³ × ℝ³`. Its integral curves are
the rays `d²q/dτ² = ∇(n²/2)(q)` of the medium of index `n`, in the parameter `dτ = dl/n`, with
`p = dq/dτ = n t` for the unit tangent `t` (§53). -/
def rayField (n : E3 → ℝ) (z : E3 × E3) : E3 × E3 := (z.2, ∇ (fun q => n q ^ 2 / 2) z.1)

theorem contDiff_rayField {n : E3 → ℝ} (hn : ContDiff ℝ ∞ n) : ContDiff ℝ ∞ (rayField n) :=
  contDiff_snd.prodMk ((contDiff_gradient ((hn.pow 2).div_const 2) (by simp)).comp contDiff_fst)

/-- The linearized ray map: the derivative of the ray flow in the initial point of phase space.
It maps the initial deviation of a neighbouring ray to its deviation at the time `t`. -/
def transverseMap (n : E3 → ℝ) (t : ℝ) (z : E3 × E3) : E3 × E3 →L[ℝ] E3 × E3 :=
  fderiv ℝ (fun y => flow (rayField n) (t, y)) z

theorem transverseMap_zero {n : E3 → ℝ} (hn : ContDiff ℝ ∞ n) (z : E3 × E3) :
    transverseMap n 0 z = ContinuousLinearMap.id ℝ (E3 × E3) :=
  (isLocalFlowOn_flow (contDiff_rayField hn)).fderiv_zero (zero_mem_flowDomain _ z)

/-- **The variational equation (§56)**: along a ray of the flow domain, the linearized ray map
solves `M′ = DX(Φ(t, z)) M` for the ray field `X`, with `M(0) = 1` (`transverseMap_zero`). -/
theorem transverseMap_hasDerivAt {n : E3 → ℝ} (hn : ContDiff ℝ ∞ n) {t : ℝ} {z : E3 × E3}
    (h : (t, z) ∈ flowDomain (rayField n)) :
    HasDerivAt (fun s => transverseMap n s z)
      (fderiv ℝ (rayField n) (flow (rayField n) (t, z)) ∘L transverseMap n t z) t :=
  (isLocalFlowOn_flow (contDiff_rayField hn)).hasDerivAt_fderiv
    ((contDiff_rayField hn).of_le (by simp)) h

/-- The derivative of the ray field, `DX(q, p)(δq, δp) = (δp, D∇(n²/2)(q) δq)`: the variational
equation of `transverseMap_hasDerivAt` is `δq′ = δp`, `δp′ = D²(n²/2)(q) δq`. -/
theorem fderiv_rayField_apply {n : E3 → ℝ} (hn : ContDiff ℝ ∞ n) (z w : E3 × E3) :
    fderiv ℝ (rayField n) z w = (w.2, fderiv ℝ (∇ fun q => n q ^ 2 / 2) z.1 w.1) := by
  have hg : Differentiable ℝ (∇ fun q => n q ^ 2 / 2) :=
    (contDiff_gradient (m := 1) ((hn.pow 2).div_const 2) (by simp)).differentiable one_ne_zero
  have h : HasFDerivAt (rayField n)
      ((ContinuousLinearMap.snd ℝ E3 E3).prod ((fderiv ℝ (∇ fun q => n q ^ 2 / 2) z.1).comp
        (ContinuousLinearMap.fst ℝ E3 E3))) z :=
    hasFDerivAt_snd.prodMk ((hg z.1).hasFDerivAt.comp z hasFDerivAt_fst)
  rw [h.fderiv]
  rfl

/-- **A narrow beam (§56)**: on a compact set `K` of times for which the ray from `z₀` is in the
flow domain, the rays of a narrow beam of initial width `δ` about it deviate from the linearized
ray map by `O(δ²)`: `‖Φ(t, z₀ + w) − Φ(t, z₀) − M(t) w‖ ≤ C ‖w‖²` for `t ∈ K` and `‖w‖ ≤ δ`
(the Taylor bound `NonlinearODE.exists_norm_sub_sub_fderiv_le` of the smooth flow). -/
theorem norm_beam_sub_linear_le {n : E3 → ℝ} (hn : ContDiff ℝ ∞ n) {K : Set ℝ}
    (hK : IsCompact K) {z₀ : E3 × E3} (hKz : ∀ t ∈ K, (t, z₀) ∈ flowDomain (rayField n)) :
    ∃ δ > 0, ∃ C : ℝ, ∀ t ∈ K, ∀ w : E3 × E3, ‖w‖ ≤ δ →
      ‖flow (rayField n) (t, z₀ + w) - flow (rayField n) (t, z₀) - transverseMap n t z₀ w‖ ≤
        C * ‖w‖ ^ 2 :=
  NonlinearODE.exists_norm_sub_sub_fderiv_le (isOpen_flowDomain (contDiff_rayField hn))
    (fun _ hp => (contDiffAt_flow (contDiff_rayField hn) hp).of_le (by simp)) hK hKz

/-! ### Instance: the homogeneous medium -/

theorem rayField_const (n₀ : ℝ) : rayField (fun _ : E3 => n₀) = fun z => (z.2, 0) := by
  funext z
  simp [rayField]

theorem contDiff_rayField_const (n₀ : ℝ) : ContDiff ℝ 1 (rayField fun _ : E3 => n₀) := by
  rw [rayField_const]
  exact contDiff_snd.prodMk contDiff_const

private theorem hasDerivWithinAt_line (z : E3 × E3) (s : Set ℝ) (r : ℝ) :
    HasDerivWithinAt (fun r : ℝ => (z.1 + r • z.2, z.2))
      ((fun z : E3 × E3 => (z.2, (0 : E3))) (z.1 + r • z.2, z.2)) s r :=
  ((((hasDerivAt_id r).smul_const z.2).const_add z.1).prodMk
    (hasDerivAt_const r z.2)).hasDerivWithinAt.congr_deriv (by simp)

/-- In a homogeneous medium the rays are straight: `Φ(t, (q, p)) = (q + t p, p)`. -/
theorem flow_rayField_const (n₀ t : ℝ) (z : E3 × E3) :
    flow (rayField fun _ : E3 => n₀) (t, z) = (z.1 + t • z.2, z.2) := by
  refine flow_eq_of_hasDerivWithinAt (y := fun r => (z.1 + r • z.2, z.2))
    (contDiff_rayField_const n₀) (by simp) fun r _ => ?_
  rw [rayField_const]
  exact hasDerivWithinAt_line z _ r

/-- In a homogeneous medium every ray exists for all times. -/
theorem flowDomain_rayField_const (n₀ : ℝ) : flowDomain (rayField fun _ : E3 => n₀) = univ := by
  refine eq_univ_of_forall fun p => ?_
  refine mem_flowDomain_of_hasDerivWithinAt (y := fun r => (p.2.1 + r • p.2.2, p.2.2))
    (contDiff_rayField_const n₀).continuous (by simp) fun r _ => ?_
  rw [rayField_const]
  exact hasDerivWithinAt_line p.2 _ r

/-- In a homogeneous medium the linearized ray map is `(δq, δp) ↦ (δq + t δp, δp)`. -/
theorem transverseMap_const (n₀ t : ℝ) (z w : E3 × E3) :
    transverseMap (fun _ : E3 => n₀) t z w = (w.1 + t • w.2, w.2) := by
  have hfun : (fun y : E3 × E3 => flow (rayField fun _ : E3 => n₀) (t, y)) =
      ⇑((ContinuousLinearMap.fst ℝ E3 E3 + t • ContinuousLinearMap.snd ℝ E3 E3).prod
        (ContinuousLinearMap.snd ℝ E3 E3)) := by
    funext y
    rw [flow_rayField_const]
    rfl
  rw [transverseMap, hfun, ContinuousLinearMap.fderiv]
  rfl

/-- **The homogeneous medium**: the linearized ray map is exact, the beam deviation vanishes. -/
theorem beam_sub_linear_const (n₀ t : ℝ) (z₀ w : E3 × E3) :
    flow (rayField fun _ : E3 => n₀) (t, z₀ + w) - flow (rayField fun _ : E3 => n₀) (t, z₀) -
      transverseMap (fun _ : E3 => n₀) t z₀ w = 0 := by
  rw [flow_rayField_const, flow_rayField_const, transverseMap_const]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.fst_zero, smul_add]
    abel
  · simp

/-! ### Instances: converging spherical and cylindrical fronts -/

/-- In `ℝ³` two vectors have a common nonzero orthogonal vector. -/
theorem exists_ne_zero_inner_eq_zero (u w : E3) : ∃ v : E3, v ≠ 0 ∧ ⟪u, v⟫ = 0 ∧ ⟪w, v⟫ = 0 := by
  let K : Submodule ℝ E3 := Submodule.span ℝ (Set.range ![u, w])
  have hK : Module.finrank ℝ K ≤ 2 :=
    le_of_le_of_eq (finrank_range_le_card (R := ℝ) ![u, w]) (Fintype.card_fin 2)
  have hsum := Submodule.finrank_add_finrank_orthogonal K
  rw [finrank_euclideanSpace_fin] at hsum
  have hne : Kᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hu : u ∈ K := Submodule.subset_span (⟨0, rfl⟩ : u ∈ Set.range ![u, w])
  have hw : w ∈ K := Submodule.subset_span (⟨1, by simp⟩ : w ∈ Set.range ![u, w])
  exact ⟨v, hv0, Submodule.inner_right_of_mem_orthogonal hu hv,
    Submodule.inner_right_of_mem_orthogonal hw hv⟩

private theorem hasFDerivAt_norm' {y : E3} (hy : y ≠ 0) :
    HasFDerivAt (fun z : E3 => ‖z‖) (‖y‖⁻¹ • innerSL ℝ y) y := by
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.sqrt (by positivity)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  refine h.congr_fderiv ?_
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, two_smul, add_apply]
  field_simp
  ring

/-- The front `ψ(x) = −‖P(x − c)‖` of an operator `P`. For an orthogonal projection `P` it is
minus the distance to the affine subspace `c + ker P`, a front converging to it: spherical for
`P = 1`, cylindrical for the projection `axisProj e` orthogonal to an axis. -/
def convergingFront (P : E3 →L[ℝ] E3) (c x : E3) : ℝ := -‖P (x - c)‖

variable {P : E3 →L[ℝ] E3} {c : E3}

/-- The domain `P(x − c) ≠ 0` of the front is open. -/
theorem isOpen_frontDomain (P : E3 →L[ℝ] E3) (c : E3) : IsOpen {x : E3 | P (x - c) ≠ 0} :=
  isOpen_ne_fun (P.continuous.comp (continuous_id.sub continuous_const)) continuous_const

theorem contDiffOn_convergingFront (P : E3 →L[ℝ] E3) (c : E3) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (convergingFront P c) {x | P (x - c) ≠ 0} := fun x hx =>
  ((contDiffAt_norm ℝ hx).comp x
    (P.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt).neg.contDiffWithinAt

theorem hasFDerivAt_sub_apply (P : E3 →L[ℝ] E3) (c x : E3) :
    HasFDerivAt (fun y => P (y - c)) P x :=
  (P.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)).congr_fderiv (P.comp_id)

theorem hasFDerivAt_convergingFront {x : E3} (hx : P (x - c) ≠ 0) :
    HasFDerivAt (convergingFront P c)
      (-((‖P (x - c)‖⁻¹ • innerSL ℝ (P (x - c))).comp P)) x :=
  ((hasFDerivAt_norm' hx).comp x (hasFDerivAt_sub_apply P c x)).neg

/-- The gradient of the front of an orthogonal projection, `∇ψ = −P(x − c)/‖P(x − c)‖`. The
hypothesis `⟨P u, v⟩ = ⟨P u, P v⟩` states that `P` is an orthogonal projection. -/
theorem gradient_convergingFront (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x : E3}
    (hx : P (x - c) ≠ 0) : ∇ (convergingFront P c) x = -‖P (x - c)‖⁻¹ • P (x - c) := by
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hasFDerivAt_convergingFront hx).congr_fderiv ?_
  ext v
  simp only [neg_apply, comp_apply, smul_apply, innerSL_apply_apply, toDual_apply_apply,
    real_inner_smul_left, smul_eq_mul]
  rw [hP (x - c) v]
  ring

/-- The front of an orthogonal projection solves the eikonal equation `|∇ψ|² = 1`. -/
theorem eikonal_convergingFront (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x : E3}
    (hx : P (x - c) ≠ 0) : ‖∇ (convergingFront P c) x‖ ^ 2 = 1 := by
  rw [gradient_convergingFront hP hx, norm_smul, norm_neg, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_pow]

/-- The Hessian of the front: `D²ψ v = −(P v − ⟨n, v⟩ n)/‖P(x − c)‖` with
`n = P(x − c)/‖P(x − c)‖`. -/
theorem hessian_convergingFront_apply (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x : E3}
    (hx : P (x - c) ≠ 0) (v : E3) :
    hessian (convergingFront P c) x v =
      -‖P (x - c)‖⁻¹ • (P v - (‖P (x - c)‖⁻¹ ^ 2 * ⟪P (x - c), v⟫) • P (x - c)) := by
  have hρ : ‖P (x - c)‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hev : ∇ (convergingFront P c) =ᶠ[𝓝 x] fun y => -‖P (y - c)‖⁻¹ • P (y - c) :=
    Filter.eventually_of_mem ((isOpen_frontDomain P c).mem_nhds hx) fun y hy =>
      gradient_convergingFront hP hy
  have hn : HasFDerivAt (fun y => ‖P (y - c)‖)
      ((‖P (x - c)‖⁻¹ • innerSL ℝ (P (x - c))).comp P) x :=
    (hasFDerivAt_norm' hx).comp x (hasFDerivAt_sub_apply P c x)
  have hi := ((hasDerivAt_inv hρ).comp_hasFDerivAt x hn).neg
  have hG : HasFDerivAt (fun y => -‖P (y - c)‖⁻¹ • P (y - c)) _ x :=
    hi.smul (hasFDerivAt_sub_apply P c x)
  rw [hessian, hev.fderiv_eq, hG.fderiv]
  simp only [add_apply, smul_apply, smulRight_apply, neg_apply, comp_apply,
    innerSL_apply_apply, smul_eq_mul, Function.comp_apply, Pi.neg_apply]
  rw [← hP (x - c) v]
  module

/-- An orthogonal projection is idempotent. -/
theorem apply_apply_of_inner (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) (u : E3) : P (P u) = P u := by
  have hsymm : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫ := fun a b => by
    calc ⟪P a, b⟫ = ⟪P a, P b⟫ := hP a b
      _ = ⟪P b, P a⟫ := real_inner_comm _ _
      _ = ⟪P b, a⟫ := (hP b a).symm
      _ = ⟪a, P b⟫ := real_inner_comm _ _
  refine ext_inner_right ℝ fun w => ?_
  rw [hsymm (P u) w, ← hP u w]

/-- **The focal points of the front of an orthogonal projection**: if the range of `P` has a
nonzero vector orthogonal to `P(x₀ − c)`, then `det(1 + l D²ψ(x₀)) = 0` exactly at
`l = ‖P(x₀ − c)‖`, where the ray reaches `c + ker P`. -/
theorem focal_convergingFront_iff (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x₀ : E3}
    (hx₀ : P (x₀ - c) ≠ 0) (hex : ∃ v : E3, v ≠ 0 ∧ P v = v ∧ ⟪P (x₀ - c), v⟫ = 0) (l : ℝ) :
    LinearMap.det
        ((1 + l • hessian (convergingFront P c) x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0 ↔
      l = ‖P (x₀ - c)‖ := by
  rw [focal_iff (isOpen_frontDomain P c) (contDiffOn_convergingFront P c)
    (fun x hx => eikonal_convergingFront hP hx) hx₀]
  simp only [gradient_convergingFront hP hx₀, hessian_convergingFront_apply hP hx₀]
  set ρ := ‖P (x₀ - c)‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.mpr hx₀
  constructor
  · rintro ⟨R, hR, rfl, v, hv0, hvg, hv⟩
    have hvy : ⟪P (x₀ - c), v⟫ = 0 := by
      rw [real_inner_smul_right, mul_eq_zero] at hvg
      rw [real_inner_comm]
      exact hvg.resolve_left (neg_ne_zero.mpr (inv_ne_zero hρ.ne'))
    rw [hvy, mul_zero, zero_smul, sub_zero] at hv
    have h1 : v = (-(R * ρ⁻¹)) • P v := by
      calc v = R • (R⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hR, one_smul]
        _ = (-(R * ρ⁻¹)) • P v := by
          rw [← hv, smul_smul]
          congr 1
          ring
    have hPv : P v = v := by
      calc P v = P ((-(R * ρ⁻¹)) • P v) := by rw [← h1]
        _ = (-(R * ρ⁻¹)) • P (P v) := map_smul _ _ _
        _ = v := by rw [apply_apply_of_inner hP, ← h1]
    rw [hPv] at hv
    have h2 : (R⁻¹ + ρ⁻¹) • v = 0 := by rw [add_smul, ← hv, neg_smul, neg_add_cancel]
    have h3 : R⁻¹ + ρ⁻¹ = 0 := (smul_eq_zero.mp h2).resolve_right hv0
    have h4 : R = -ρ := by
      have : R⁻¹ = (-ρ)⁻¹ := by
        rw [inv_neg]
        linarith
      exact inv_injective this
    rw [h4, neg_neg]
  · rintro rfl
    obtain ⟨v, hv0, hPv, hvy⟩ := hex
    refine ⟨-ρ, neg_ne_zero.mpr hρ.ne', (neg_neg ρ).symm, v, hv0, ?_, ?_⟩
    · rw [real_inner_smul_right, real_inner_comm, hvy, mul_zero]
    · rw [hPv, hvy, mul_zero, zero_smul, sub_zero, inv_neg]

/-- The ray from `x₀` reaches `c + ker P` at `l = ‖P(x₀ − c)‖`. -/
theorem apply_ray_convergingFront (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x₀ : E3}
    (hx₀ : P (x₀ - c) ≠ 0) : P (ray (convergingFront P c) x₀ ‖P (x₀ - c)‖ - c) = 0 := by
  have hρ : ‖P (x₀ - c)‖ ≠ 0 := norm_ne_zero_iff.mpr hx₀
  rw [ray, gradient_convergingFront hP hx₀, smul_smul, mul_neg, mul_inv_cancel₀ hρ, neg_smul,
    one_smul, show x₀ + -P (x₀ - c) - c = (x₀ - c) - P (x₀ - c) by abel, map_sub,
    apply_apply_of_inner hP, sub_self]

/-! #### The spherical front -/

/-- The spherical front `ψ(x) = −‖x − c‖` converging to `c`. -/
theorem convergingFront_id_apply (c x : E3) :
    convergingFront (ContinuousLinearMap.id ℝ E3) c x = -‖x - c‖ := rfl

/-- **The spherical front**: every direction orthogonal to the ray is principal, with the radius of
curvature `−‖x₀ − c‖` (the front converges). -/
theorem hessian_sphericalFront_apply {x₀ : E3} (hx₀ : x₀ ≠ c) {v : E3} (hv : ⟪x₀ - c, v⟫ = 0) :
    hessian (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ v = (-‖x₀ - c‖)⁻¹ • v := by
  rw [hessian_convergingFront_apply (fun _ _ => rfl) (sub_ne_zero.mpr hx₀)]
  simp only [ContinuousLinearMap.id_apply, hv, mul_zero, zero_smul, sub_zero, inv_neg, neg_smul]

/-- **The focal point of a spherical front is its centre**: `det(1 + l D²ψ(x₀)) = 0` exactly at
`l = ‖x₀ − c‖`, where the ray reaches `c` (`ray_sphericalFront`). -/
theorem focal_sphericalFront_iff {x₀ : E3} (hx₀ : x₀ ≠ c) (l : ℝ) :
    LinearMap.det ((1 + l • hessian (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ :
        E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0 ↔ l = ‖x₀ - c‖ := by
  obtain ⟨v, hv0, hv, -⟩ := exists_ne_zero_inner_eq_zero (x₀ - c) (x₀ - c)
  exact focal_convergingFront_iff (fun _ _ => rfl) (sub_ne_zero.mpr hx₀) ⟨v, hv0, rfl, hv⟩ l

theorem ray_sphericalFront {x₀ : E3} (hx₀ : x₀ ≠ c) :
    ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ ‖x₀ - c‖ = c := by
  have h := apply_ray_convergingFront (P := ContinuousLinearMap.id ℝ E3) (fun _ _ => rfl)
    (sub_ne_zero.mpr hx₀)
  simpa [sub_eq_zero] using h

theorem sub_ray_sphericalFront {x₀ : E3} (hx₀ : x₀ ≠ c) (s : ℝ) :
    ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ s - c =
      (1 - s * ‖x₀ - c‖⁻¹) • (x₀ - c) := by
  rw [ray, gradient_convergingFront (P := ContinuousLinearMap.id ℝ E3) (fun _ _ => rfl)
    (sub_ne_zero.mpr hx₀)]
  simp only [ContinuousLinearMap.id_apply]
  module

/-- The ray of the spherical front stays off the centre except at `l = ‖x₀ − c‖`. -/
theorem ray_mem_sphericalFront {x₀ : E3} (hx₀ : x₀ ≠ c) {s : ℝ} (hs : s ≠ ‖x₀ - c‖) :
    ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ s ∈
      {x : E3 | ContinuousLinearMap.id ℝ E3 (x - c) ≠ 0} := by
  have hρ : ‖x₀ - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx₀)
  have hc : 1 - s * ‖x₀ - c‖⁻¹ ≠ 0 := by
    intro h
    apply hs
    field_simp at h
    linarith
  show ContinuousLinearMap.id ℝ E3 _ ≠ 0
  rw [ContinuousLinearMap.id_apply, sub_ray_sphericalFront hx₀]
  exact smul_ne_zero hc (sub_ne_zero.mpr hx₀)

/-- **The spherical front along a ray**: in front of the centre the principal radius
`−‖x₀ − c‖` becomes `l − ‖x₀ − c‖`, by `principalRadius_add`. -/
theorem principalRadius_sphericalFront {x₀ : E3} (hx₀ : x₀ ≠ c) {l : ℝ} (hl : l < ‖x₀ - c‖)
    {v : E3} (hv : ⟪x₀ - c, v⟫ = 0) :
    hessian (convergingFront (ContinuousLinearMap.id ℝ E3) c)
        (ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ l) v =
      (-‖x₀ - c‖ + l)⁻¹ • v := by
  have hρ : 0 < ‖x₀ - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx₀)
  refine principalRadius_add (isOpen_frontDomain _ c) (contDiffOn_convergingFront _ c)
    (fun x hx => eikonal_convergingFront (fun _ _ => rfl) hx) (fun s hs => ?_)
    (neg_ne_zero.mpr hρ.ne') (hessian_sphericalFront_apply hx₀ hv)
  exact ray_mem_sphericalFront hx₀ (ne_of_lt (lt_of_le_of_lt hs.2 (max_lt hρ hl)))

/-! #### The cylindrical front -/

/-- The orthogonal projection `v ↦ v − ⟨e, v⟩ e` onto the plane orthogonal to a unit vector `e`. -/
def axisProj (e : E3) : E3 →L[ℝ] E3 :=
  ContinuousLinearMap.id ℝ E3 - (innerSL ℝ e).smulRight e

theorem axisProj_apply (e v : E3) : axisProj e v = v - ⟪e, v⟫ • e := rfl

theorem inner_axisProj_self {e : E3} (he : ‖e‖ = 1) (u : E3) : ⟪axisProj e u, e⟫ = 0 := by
  rw [axisProj_apply, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he,
    real_inner_comm]
  ring

/-- `axisProj e` is an orthogonal projection. -/
theorem inner_axisProj {e : E3} (he : ‖e‖ = 1) (u v : E3) :
    ⟪axisProj e u, v⟫ = ⟪axisProj e u, axisProj e v⟫ := by
  conv_rhs => rw [axisProj_apply e v]
  rw [inner_sub_right, real_inner_smul_right, inner_axisProj_self he, mul_zero, sub_zero]

/-- **The cylindrical front**: the axis `e` is a principal direction with zero curvature (an
infinite radius), orthogonal to the ray. -/
theorem hessian_cylindricalFront_axis {e : E3} (he : ‖e‖ = 1) {x₀ : E3}
    (hx₀ : axisProj e (x₀ - c) ≠ 0) :
    hessian (convergingFront (axisProj e) c) x₀ e = 0 ∧
      ⟪e, ∇ (convergingFront (axisProj e) c) x₀⟫ = 0 := by
  have hPe : axisProj e e = 0 := by
    rw [axisProj_apply, real_inner_self_eq_norm_sq, he]
    simp
  constructor
  · rw [hessian_convergingFront_apply (inner_axisProj he) hx₀, hPe, inner_axisProj_self he]
    simp
  · rw [gradient_convergingFront (inner_axisProj he) hx₀, real_inner_smul_right,
      real_inner_comm, inner_axisProj_self he, mul_zero]

/-- **The cylindrical front**: the direction orthogonal to the axis and to the ray is principal,
with the radius of curvature `−ρ`, `ρ = ‖axisProj e (x₀ − c)‖` the distance to the axis. -/
theorem hessian_cylindricalFront_apply {e : E3} (he : ‖e‖ = 1) {x₀ : E3}
    (hx₀ : axisProj e (x₀ - c) ≠ 0) {v : E3} (hve : ⟪e, v⟫ = 0)
    (hv : ⟪axisProj e (x₀ - c), v⟫ = 0) :
    hessian (convergingFront (axisProj e) c) x₀ v = (-‖axisProj e (x₀ - c)‖)⁻¹ • v := by
  have hPv : axisProj e v = v := by rw [axisProj_apply, hve, zero_smul, sub_zero]
  rw [hessian_convergingFront_apply (inner_axisProj he) hx₀, hPv, hv, mul_zero, zero_smul,
    sub_zero, inv_neg, neg_smul]

/-- **The focal line of a cylindrical front is its axis**: `det(1 + l D²ψ(x₀)) = 0` exactly at the
distance `l = ‖axisProj e (x₀ − c)‖` to the axis, where the ray meets it
(`apply_ray_convergingFront`). -/
theorem focal_cylindricalFront_iff {e : E3} (he : ‖e‖ = 1) {x₀ : E3}
    (hx₀ : axisProj e (x₀ - c) ≠ 0) (l : ℝ) :
    LinearMap.det ((1 + l • hessian (convergingFront (axisProj e) c) x₀ :
        E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0 ↔ l = ‖axisProj e (x₀ - c)‖ := by
  obtain ⟨v, hv0, hve, hv⟩ := exists_ne_zero_inner_eq_zero e (axisProj e (x₀ - c))
  refine focal_convergingFront_iff (inner_axisProj he) hx₀ ⟨v, hv0, ?_, hv⟩ l
  rw [axisProj_apply, hve, zero_smul, sub_zero]

/-! #### The amplitude of a spherical wave -/

/-- The trace of the Hessian of the front: `Δψ = −(tr P − 1)/‖P(x − c)‖`. -/
theorem traceCLM_hessian_convergingFront (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x : E3}
    (hx : P (x - c) ≠ 0) :
    traceCLM (hessian (convergingFront P c) x) = -‖P (x - c)‖⁻¹ * (traceCLM P - 1) := by
  have hρ : ‖P (x - c)‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hH : hessian (convergingFront P c) x = -‖P (x - c)‖⁻¹ •
      (P - (‖P (x - c)‖⁻¹ ^ 2) • (innerSL ℝ (P (x - c))).smulRight (P (x - c))) := by
    ext1 v
    rw [hessian_convergingFront_apply hP hx]
    simp only [smul_apply, sub_apply, smulRight_apply, innerSL_apply_apply, smul_smul]
  have htr : traceCLM ((innerSL ℝ (P (x - c))).smulRight (P (x - c))) = ‖P (x - c)‖ ^ 2 := by
    rw [traceCLM_apply, ← real_inner_self_eq_norm_sq]
    exact LinearMap.trace_smulRight (innerSL ℝ (E := E3) (P (x - c)) : E3 →ₗ[ℝ] ℝ) (P (x - c))
  rw [hH, map_smul traceCLM, map_sub traceCLM, map_smul traceCLM, htr, smul_eq_mul, smul_eq_mul,
    inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hρ)]

theorem traceCLM_id : traceCLM (ContinuousLinearMap.id ℝ E3) = 3 := by
  rw [traceCLM_apply, ContinuousLinearMap.coe_id, LinearMap.trace_id, finrank_euclideanSpace_fin]
  norm_num

/-- The Laplacian of the spherical front, `Δψ = −2/‖x − c‖`. -/
theorem laplacian_sphericalFront {x : E3} (hx : x ≠ c) :
    Δ (convergingFront (ContinuousLinearMap.id ℝ E3) c) x = -2 * ‖x - c‖⁻¹ := by
  rw [laplacian_eq_traceCLM_hessian ((contDiffOn_convergingFront _ c).contDiffAt
    ((isOpen_frontDomain _ c).mem_nhds (sub_ne_zero.mpr hx))),
    traceCLM_hessian_convergingFront (fun _ _ => rfl) (sub_ne_zero.mpr hx), traceCLM_id]
  simp only [ContinuousLinearMap.id_apply]
  ring

theorem hasFDerivAt_inv_norm_sub {x : E3} (hx : x ≠ c) :
    HasFDerivAt (fun y => ‖y - c‖⁻¹)
      ((-(‖x - c‖ ^ 2)⁻¹) • (‖x - c‖⁻¹ • innerSL ℝ (x - c))) x := by
  have hn := (hasFDerivAt_norm' (sub_ne_zero.mpr hx)).comp x
    (hasFDerivAt_sub_apply (ContinuousLinearMap.id ℝ E3) c x)
  have h := (hasDerivAt_inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))).comp_hasFDerivAt x hn
  exact h.congr_fderiv (by simp)

/-- **The amplitude of a spherical wave**: `a = 1/‖x − c‖` solves the transport equation
`2⟨∇a, ∇ψ⟩ + a Δψ = 0` of the spherical front off its centre. -/
theorem transport_sphericalFront {x : E3} (hx : x ≠ c) :
    2 * ⟪∇ (fun y => ‖y - c‖⁻¹) x, ∇ (convergingFront (ContinuousLinearMap.id ℝ E3) c) x⟫ +
      ‖x - c‖⁻¹ * Δ (convergingFront (ContinuousLinearMap.id ℝ E3) c) x = 0 := by
  have hρ : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hinner : ∀ w : E3, ⟪∇ (fun y => ‖y - c‖⁻¹) x, w⟫ =
      -(‖x - c‖ ^ 2)⁻¹ * (‖x - c‖⁻¹ * ⟪x - c, w⟫) := by
    intro w
    have hd := congrFun (fderiv_eq_innerSL_gradient (fun y : E3 => ‖y - c‖⁻¹)) x
    rw [← innerSL_apply_apply ℝ, ← hd, (hasFDerivAt_inv_norm_sub hx).fderiv]
    simp [innerSL_apply_apply, inner_sub_left]
  rw [hinner, laplacian_sphericalFront hx,
    gradient_convergingFront (P := ContinuousLinearMap.id ℝ E3) (fun _ _ => rfl)
      (sub_ne_zero.mpr hx)]
  simp only [ContinuousLinearMap.id_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- **The amplitude of a converging spherical wave blows up at the centre (§58)**: along the ray
from `x₀ ≠ c`, `|a(x(l))| = 1/‖x(l) − c‖ → ∞` as `l → ‖x₀ − c‖⁻`, by `amplitude_tendsto_focal`. -/
theorem amplitude_tendsto_sphericalFront {x₀ : E3} (hx₀ : x₀ ≠ c) :
    Tendsto (fun s => |‖ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ s - c‖⁻¹|)
      (𝓝[<] ‖x₀ - c‖) atTop := by
  have hρ : 0 < ‖x₀ - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx₀)
  have hseg : ∀ s ∈ Ico 0 ‖x₀ - c‖,
      ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ s ∈
        {x : E3 | ContinuousLinearMap.id ℝ E3 (x - c) ≠ 0} := fun s hs =>
    ray_mem_sphericalFront hx₀ (ne_of_lt hs.2)
  refine amplitude_tendsto_focal (isOpen_frontDomain _ c) (contDiffOn_convergingFront _ c)
    (fun x hx => eikonal_convergingFront (fun _ _ => rfl) hx) hρ hseg
    (a := fun y => ‖y - c‖⁻¹) (fun x hx => ?_) (fun x hx => ?_)
    ((focal_sphericalFront_iff hx₀ _).mpr rfl) (inv_ne_zero hρ.ne')
  · exact (hasFDerivAt_inv_norm_sub (sub_ne_zero.mp hx)).differentiableAt
  · exact transport_sphericalFront (sub_ne_zero.mp hx)

end ProjectAinos.Electrodynamics.Optics.NarrowBundle
