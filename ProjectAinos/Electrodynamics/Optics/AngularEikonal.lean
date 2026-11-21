/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import ProjectAinos.Mechanics.Poisson.GeneratingFunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The angular eikonal

Landau–Lifshitz, *The Classical Theory of Fields*, §55. An optical system lies between two
homogeneous media. A ray is described by its points `r`, `r′` in two transverse planes, one in each
medium, and by the transverse components `p`, `p′` of `n n̂` and `n′ n̂′`, where `n̂`, `n̂′` are the
unit vectors along the ray; the longitudinal components follow from `|n n̂| = n`. The transverse
plane is a real inner product space `E` (physically `ℝ²`). In `ℝ³` the point eikonal of a
homogeneous medium does not change when a point moves along the ray, so its mixed Hessian is
singular; the statements below therefore use the transverse planes.

The point eikonal `ψ(r, r′)` is the optical length of the ray from `r` to `r′`, with
`∂ψ/∂r = −p` and `∂ψ/∂r′ = p′`.

* `entryMomentum`, `exitMomentum`, `momentumMap`: `p = −∂ψ/∂r`, `p′ = ∂ψ/∂r′` and the map
  `(r, r′) ↦ (p, p′)`; `entryMomentum_eq_neg_gradient` and `exitMomentum_eq_gradient` identify
  them with the partial gradients.
* `angularEikonal ψ g`: `f(p, p′) = ψ(r, r′) − p′·r′ + p·r` with `(r, r′) = g(p, p′)` for a right
  inverse `g` of the momentum map. `fderiv_angularEikonal`, `gradient_angularEikonal_fst` and
  `gradient_angularEikonal_snd`: `df = r·dp − r′·dp′`, that is `∂f/∂p = r`, `∂f/∂p′ = −r′`.
* `exists_localInverse_momentumMap`, `exists_angularEikonal`: for a point eikonal of class `C²`
  whose momentum map has an invertible derivative (the Hessian of `ψ` with the sign of the first
  row reversed), the inverse function theorem gives a `C¹` local inverse and the angular eikonal.
  An invertible mixed Hessian does not suffice: for free propagation it is invertible, but the
  momentum map is not a local diffeomorphism
  (`not_isInvertible_fderiv_momentumMap_freePropagation`).
* `canonicalForm`, `IsRayMapOn`, `rayMap_symplectic`: a differentiable ray map
  `(r, p) ↦ (r′, p′)` of a `C²` point eikonal preserves `dp ∧ dr`, by the symmetry of the second
  derivative of `ψ`.
* `mixedHessian`, `exists_rayMap`, `exists_rayMap_symplectic`: if the mixed Hessian `∂²ψ/∂r∂r′` is
  invertible, the implicit function theorem gives a `C¹` ray map near the given ray.
* `paraxialEikonal ψ₀ a b c = ψ₀ + (a r² − 2b r·r′ + c r′²)/2`, the paraxial point eikonal of a
  centred system: its momenta, the linear inverse `paraxialInverse` for `b² ≠ ac`, the angular
  eikonal `ψ₀ + (c p² − 2b p·p′ + a p′²)/2(b² − ac)` (`angularEikonal_paraxialEikonal`), and the
  ray map `paraxialRayMap` for `b ≠ 0`. Free propagation over `L` is `a = b = c = 1/L`; a thin
  lens of focal length `F` followed by a gap `L` is `a = 1/L − 1/F`, `b = c = 1/L`, with the
  angular eikonal `ψ₀ + (F |p − p′|² − L p′²)/2` (`angularEikonal_thinLens`).
* `freeEikonal`, `freeRayMap`, `freeRayMap_symplectic`: free propagation without the paraxial
  approximation, `ψ = √(L² + |r′ − r|²)`, whose ray map `r′ = r + L p/√(1 − p²)`, `p′ = p` is
  defined on the open set `|p| < 1`.
* `Free.rayMap`, `Free.rayMap_isPoissonHom`: in the free C∞-ring of the positions, the point
  eikonal `ψ` is the generating function `−ψ` of §45, and the ray map of a free generating function
  preserves the canonical bracket. `Free.isFree_paraxialEikonal`: the paraxial eikonal with
  `b ≠ 0` is free, with a linear inverse; `Free.rayMap_thinLens_isPoissonHom` is the instance of
  the thin lens.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics.Optics.AngularEikonal

open InnerProductSpace ContinuousLinearMap Set Filter
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The momenta of a point eikonal -/

/-- The vector of the restriction `u ↦ φ(u, 0)` of a covector `φ` on `E × E` to the first
factor. -/
def firstVector : ((E × E) →L[ℝ] ℝ) →L[ℝ] E :=
  (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((compL ℝ E (E × E) ℝ).flip (inl ℝ E E))

/-- The vector of the restriction `u′ ↦ φ(0, u′)` of a covector `φ` on `E × E` to the second
factor. -/
def secondVector : ((E × E) →L[ℝ] ℝ) →L[ℝ] E :=
  (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((compL ℝ E (E × E) ℝ).flip (inr ℝ E E))

theorem inner_firstVector (φ : (E × E) →L[ℝ] ℝ) (a : E) : ⟪firstVector φ, a⟫ = φ (a, 0) := by
  simp [firstVector]

theorem inner_secondVector (φ : (E × E) →L[ℝ] ℝ) (b : E) : ⟪secondVector φ, b⟫ = φ (0, b) := by
  simp [secondVector]

/-- The momentum `p = −∂ψ/∂r` of the ray at entry: the transverse part of `n n̂`. -/
def entryMomentum (ψ : E × E → ℝ) (x : E × E) : E :=
  -firstVector (fderiv ℝ ψ x)

/-- The momentum `p′ = ∂ψ/∂r′` of the ray at exit: the transverse part of `n′ n̂′`. -/
def exitMomentum (ψ : E × E → ℝ) (x : E × E) : E :=
  secondVector (fderiv ℝ ψ x)

/-- The momentum map `(r, r′) ↦ (p, p′) = (−∂ψ/∂r, ∂ψ/∂r′)` of a point eikonal. -/
def momentumMap (ψ : E × E → ℝ) (x : E × E) : E × E :=
  (entryMomentum ψ x, exitMomentum ψ x)

theorem inner_entryMomentum (ψ : E × E → ℝ) (x : E × E) (a : E) :
    ⟪entryMomentum ψ x, a⟫ = -fderiv ℝ ψ x (a, 0) := by
  rw [entryMomentum, inner_neg_left, inner_firstVector]

theorem inner_exitMomentum (ψ : E × E → ℝ) (x : E × E) (b : E) :
    ⟪exitMomentum ψ x, b⟫ = fderiv ℝ ψ x (0, b) :=
  inner_secondVector _ b

/-- `dψ = −p dr + p′ dr′`. -/
theorem fderiv_apply_eq_inner (ψ : E × E → ℝ) (x u : E × E) :
    fderiv ℝ ψ x u = -⟪entryMomentum ψ x, u.1⟫ + ⟪exitMomentum ψ x, u.2⟫ := by
  rw [inner_entryMomentum, inner_exitMomentum, neg_neg, ← map_add, Prod.mk_add_mk, add_zero,
    zero_add]

/-- The entry momentum is minus the gradient of `ψ` in the entry point (`∂ψ/∂r = −n n̂`). -/
theorem entryMomentum_eq_neg_gradient {ψ : E × E → ℝ} {x : E × E}
    (hψ : DifferentiableAt ℝ ψ x) : entryMomentum ψ x = -gradient (fun r => ψ (r, x.2)) x.1 := by
  have h : HasFDerivAt (fun r => ψ (r, x.2)) ((fderiv ℝ ψ x).comp (inl ℝ E E)) x.1 :=
    hψ.hasFDerivAt.comp x.1 (hasFDerivAt_prodMk_left x.1 x.2)
  rw [gradient, h.fderiv, entryMomentum]
  rfl

/-- The exit momentum is the gradient of `ψ` in the exit point (`∂ψ/∂r′ = n′ n̂′`). -/
theorem exitMomentum_eq_gradient {ψ : E × E → ℝ} {x : E × E}
    (hψ : DifferentiableAt ℝ ψ x) : exitMomentum ψ x = gradient (fun r' => ψ (x.1, r')) x.2 := by
  have h : HasFDerivAt (fun r' => ψ (x.1, r')) ((fderiv ℝ ψ x).comp (inr ℝ E E)) x.2 :=
    hψ.hasFDerivAt.comp x.2 (hasFDerivAt_prodMk_right x.1 x.2)
  rw [gradient, h.fderiv, exitMomentum]
  rfl

theorem contDiffOn_entryMomentum {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ 2 ψ U) : ContDiffOn ℝ 1 (entryMomentum ψ) U :=
  (firstVector.contDiff.comp_contDiffOn (hψ.fderiv_of_isOpen hU le_rfl)).neg

theorem contDiffOn_exitMomentum {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ 2 ψ U) : ContDiffOn ℝ 1 (exitMomentum ψ) U :=
  secondVector.contDiff.comp_contDiffOn (hψ.fderiv_of_isOpen hU le_rfl)

theorem contDiffOn_momentumMap {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ 2 ψ U) : ContDiffOn ℝ 1 (momentumMap ψ) U :=
  (contDiffOn_entryMomentum hU hψ).prodMk (contDiffOn_exitMomentum hU hψ)

theorem hasFDerivAt_entryMomentum {ψ : E × E → ℝ} {x : E × E} (hψ : ContDiffAt ℝ 2 ψ x) :
    HasFDerivAt (entryMomentum ψ) (-(firstVector.comp (fderiv ℝ (fderiv ℝ ψ) x))) x := by
  have h := ((hψ.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  exact ((firstVector (E := E)).hasFDerivAt.comp x h).fun_neg

theorem hasFDerivAt_exitMomentum {ψ : E × E → ℝ} {x : E × E} (hψ : ContDiffAt ℝ 2 ψ x) :
    HasFDerivAt (exitMomentum ψ) (secondVector.comp (fderiv ℝ (fderiv ℝ ψ) x)) x := by
  have h := ((hψ.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  exact (secondVector (E := E)).hasFDerivAt.comp x h

/-- The mixed second derivative `∂²ψ/∂r∂r′ = −∂p/∂r′` of a point eikonal, as the linear map
`δr′ ↦ ∂(∂ψ/∂r)/∂r′ · δr′`. -/
def mixedHessian (ψ : E × E → ℝ) (x : E × E) : E →L[ℝ] E :=
  -(fderiv ℝ (entryMomentum ψ) x).comp (inr ℝ E E)

theorem inner_mixedHessian {ψ : E × E → ℝ} {x : E × E} (hψ : ContDiffAt ℝ 2 ψ x) (a b : E) :
    ⟪mixedHessian ψ x b, a⟫ = fderiv ℝ (fderiv ℝ ψ) x (0, b) (a, 0) := by
  rw [mixedHessian, (hasFDerivAt_entryMomentum hψ).fderiv]
  simp [inner_firstVector]

/-! ### The angular eikonal -/

/-- The angular eikonal `f(p, p′) = ψ(r, r′) − p′·r′ + p·r` of Landau–Lifshitz §55, where
`(r, r′) = g(p, p′)` and `g` is a right inverse of the momentum map of the point eikonal `ψ` on the
set where `f` is used. -/
def angularEikonal (ψ : E × E → ℝ) (g : E × E → E × E) (y : E × E) : ℝ :=
  ψ (g y) - ⟪y.2, (g y).2⟫ + ⟪y.1, (g y).1⟫

/-- `df = r·dp − r′·dp′` (Landau–Lifshitz §55) at a point where `g` is differentiable and a right
inverse of the momentum map. -/
theorem hasFDerivAt_angularEikonal {ψ : E × E → ℝ} {g : E × E → E × E} {y : E × E}
    (hψ : DifferentiableAt ℝ ψ (g y)) (hg : DifferentiableAt ℝ g y)
    (hy : momentumMap ψ (g y) = y) :
    HasFDerivAt (angularEikonal ψ g)
      ((innerSL ℝ (g y).1).comp (fst ℝ E E) - (innerSL ℝ (g y).2).comp (snd ℝ E E)) y := by
  have hg' := hg.hasFDerivAt
  have h1 := hψ.hasFDerivAt.comp y hg'
  have h2 := (hasFDerivAt_snd (p := y)).inner ℝ (hasFDerivAt_snd.comp y hg')
  have h3 := (hasFDerivAt_fst (p := y)).inner ℝ (hasFDerivAt_fst.comp y hg')
  have h := (h1.sub h2).add h3
  refine h.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
  have hp : entryMomentum ψ (g y) = y.1 := congrArg Prod.fst hy
  have hp' : exitMomentum ψ (g y) = y.2 := congrArg Prod.snd hy
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, coe_fst', coe_snd', innerSL_apply_apply, Function.comp_apply,
    fderiv_apply_eq_inner, hp, hp']
  rw [real_inner_comm u.1, real_inner_comm u.2]
  ring

/-- `df = r·dp − r′·dp′` on a set `V` on which `g` is a differentiable right inverse of the
momentum map. -/
theorem fderiv_angularEikonal {ψ : E × E → ℝ} {g : E × E → E × E} {V : Set (E × E)}
    (hψ : ∀ y ∈ V, DifferentiableAt ℝ ψ (g y)) (hg : ∀ y ∈ V, DifferentiableAt ℝ g y)
    (hinv : ∀ y ∈ V, momentumMap ψ (g y) = y) {y : E × E} (hy : y ∈ V) :
    fderiv ℝ (angularEikonal ψ g) y =
      (innerSL ℝ (g y).1).comp (fst ℝ E E) - (innerSL ℝ (g y).2).comp (snd ℝ E E) :=
  (hasFDerivAt_angularEikonal (hψ y hy) (hg y hy) (hinv y hy)).fderiv

/-- `∂f/∂p = r`. -/
theorem gradient_angularEikonal_fst {ψ : E × E → ℝ} {g : E × E → E × E} {y : E × E}
    (hψ : DifferentiableAt ℝ ψ (g y)) (hg : DifferentiableAt ℝ g y)
    (hy : momentumMap ψ (g y) = y) :
    gradient (fun p => angularEikonal ψ g (p, y.2)) y.1 = (g y).1 := by
  have h0 := hasFDerivAt_angularEikonal hψ hg hy
  have h := h0.comp y.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) y.1 y.2)
  refine HasGradientAt.gradient ((hasGradientAt_iff_hasFDerivAt).mpr ?_)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
  simp

/-- `∂f/∂p′ = −r′`. -/
theorem gradient_angularEikonal_snd {ψ : E × E → ℝ} {g : E × E → E × E} {y : E × E}
    (hψ : DifferentiableAt ℝ ψ (g y)) (hg : DifferentiableAt ℝ g y)
    (hy : momentumMap ψ (g y) = y) :
    gradient (fun p' => angularEikonal ψ g (y.1, p')) y.2 = -(g y).2 := by
  have h0 := hasFDerivAt_angularEikonal hψ hg hy
  have h := h0.comp y.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) y.1 y.2)
  refine HasGradientAt.gradient ((hasGradientAt_iff_hasFDerivAt).mpr ?_)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
  simp

/-! ### The ray map and the canonical two-form -/

/-- The canonical two-form `dp ∧ dr` on the phase space `E × E` of the pairs `(r, p)`:
`ω((δr₁, δp₁), (δr₂, δp₂)) = δp₁·δr₂ − δr₁·δp₂`. -/
def canonicalForm (v w : E × E) : ℝ :=
  ⟪v.2, w.1⟫ - ⟪v.1, w.2⟫

/-- `Φ : (r, p) ↦ (r′, p′)` is a ray map of the point eikonal `ψ` on `W`: for every `(r, p) ∈ W`
the momenta of `ψ` at `(r, r′)` are `p = −∂ψ/∂r` and `p′ = ∂ψ/∂r′`. -/
def IsRayMapOn (ψ : E × E → ℝ) (Φ : E × E → E × E) (W : Set (E × E)) : Prop :=
  ∀ z ∈ W, momentumMap ψ (z.1, (Φ z).1) = (z.2, (Φ z).2)

/-- A ray map of a point eikonal preserves the canonical two-form `dp ∧ dr`: the derivative of
the map `(r, p) ↦ (r′, p′)` is symplectic (Landau–Lifshitz §55; the proof uses only the symmetry
of the second derivative of `ψ`). -/
theorem rayMap_symplectic {ψ : E × E → ℝ} {Φ : E × E → E × E} {W : Set (E × E)}
    (hW : IsOpen W) (hray : IsRayMapOn ψ Φ W) {z : E × E} (hz : z ∈ W)
    (hΦ : DifferentiableAt ℝ Φ z) (hψ : ContDiffAt ℝ 2 ψ (z.1, (Φ z).1)) (v w : E × E) :
    canonicalForm (fderiv ℝ Φ z v) (fderiv ℝ Φ z w) = canonicalForm v w := by
  set x : E × E := (z.1, (Φ z).1)
  set D := fderiv ℝ Φ z
  set H := fderiv ℝ (fderiv ℝ ψ) x
  have hd := ((hψ.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have hsymm : IsSymmSndFDerivAt ℝ ψ x := hψ.isSymmSndFDerivAt (by simp)
  have hσ : HasFDerivAt (fun z' : E × E => (z'.1, (Φ z').1))
      ((fst ℝ E E).prod ((fst ℝ E E).comp D)) z :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_fst.comp z hΦ.hasFDerivAt)
  have hev : ∀ᶠ z' in 𝓝 z, momentumMap ψ (z'.1, (Φ z').1) = (z'.2, (Φ z').2) :=
    eventually_of_mem (hW.mem_nhds hz) hray
  set s : E × E → E × E := fun v => (v.1, (D v).1)
  have hA : ∀ (v : E × E) (a : E), ⟪a, v.2⟫ = -H (s v) (a, 0) := by
    intro v a
    have h1 := ((apply ℝ ℝ ((a, 0) : E × E)).hasFDerivAt.comp x hd).comp z hσ
    have h2 := ((innerSL ℝ a).comp (snd ℝ E E)).hasFDerivAt (x := z)
    have heq : (fun z' : E × E => ⟪a, z'.2⟫) =ᶠ[𝓝 z]
        fun z' => -(apply ℝ ℝ ((a, 0) : E × E) (fderiv ℝ ψ (z'.1, (Φ z').1))) := by
      filter_upwards [hev] with z' hz'
      have hp : entryMomentum ψ (z'.1, (Φ z').1) = z'.2 := congrArg Prod.fst hz'
      rw [apply_apply, ← inner_entryMomentum, hp, real_inner_comm]
    have h3 := (h1.fun_neg.congr_of_eventuallyEq heq).unique h2
    have h4 := congrArg (fun L : (E × E) →L[ℝ] ℝ => L v) h3
    simp only [neg_apply, ContinuousLinearMap.comp_apply, apply_apply, prod_apply, coe_fst',
      innerSL_apply_apply, coe_snd'] at h4
    exact h4.symm
  have hB : ∀ (v : E × E) (b : E), ⟪b, (D v).2⟫ = H (s v) (0, b) := by
    intro v b
    have h1 := ((apply ℝ ℝ ((0, b) : E × E)).hasFDerivAt.comp x hd).comp z hσ
    have heq : (fun z' : E × E => ⟪b, (Φ z').2⟫) =ᶠ[𝓝 z]
        fun z' => apply ℝ ℝ ((0, b) : E × E) (fderiv ℝ ψ (z'.1, (Φ z').1)) := by
      filter_upwards [hev] with z' hz'
      have hp : exitMomentum ψ (z'.1, (Φ z').1) = (Φ z').2 := congrArg Prod.snd hz'
      rw [apply_apply, ← inner_exitMomentum, hp, real_inner_comm]
    have h2 : HasFDerivAt (fun z' : E × E => ⟪b, (Φ z').2⟫)
        ((innerSL ℝ b).comp ((snd ℝ E E).comp D)) z :=
      ((innerSL ℝ b).hasFDerivAt.comp z (hasFDerivAt_snd.comp z hΦ.hasFDerivAt))
    have h3 := (h1.congr_of_eventuallyEq heq).unique h2
    have h4 := congrArg (fun L : (E × E) →L[ℝ] ℝ => L v) h3
    simp only [ContinuousLinearMap.comp_apply, apply_apply, prod_apply, coe_fst',
      innerSL_apply_apply, coe_snd'] at h4
    exact h4.symm
  have hsplit : ∀ (u v : E × E), H u (s v) = H u (v.1, 0) + H u (0, (D v).1) := by
    intro u v
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have e1 := hB v (D w).1
  have e2 := hB w (D v).1
  have e3 := hA v w.1
  have e4 := hA w v.1
  have e5 := hsplit (s v) w
  have e6 := hsplit (s w) v
  have e7 : H (s v) (s w) = H (s w) (s v) := hsymm (s v) (s w)
  rw [real_inner_comm] at e1 e3
  unfold canonicalForm
  linarith

/-! ### Existence by the inverse and implicit function theorems -/

/-- The local inverse of the momentum map: if the point eikonal is `C²` on an open set and the
derivative of its momentum map (the Hessian of `ψ`, with the sign of the first row reversed) is
invertible at `x₀`, the momentum map has a `C¹` inverse `g` on an open neighbourhood `V` of its
value, with values in the open set, which inverts it near `x₀`. -/
theorem exists_localInverse_momentumMap {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ 2 ψ U) {x₀ : E × E} (hx₀ : x₀ ∈ U)
    (hinv : (fderiv ℝ (momentumMap ψ) x₀).IsInvertible) :
    ∃ (V : Set (E × E)) (g : E × E → E × E), IsOpen V ∧ momentumMap ψ x₀ ∈ V ∧
      g (momentumMap ψ x₀) = x₀ ∧ ContDiffOn ℝ 1 g V ∧
      (∀ y ∈ V, g y ∈ U ∧ momentumMap ψ (g y) = y) ∧
      ∀ᶠ x in 𝓝 x₀, g (momentumMap ψ x) = x := by
  have hc : ContDiffAt ℝ 1 (momentumMap ψ) x₀ :=
    (contDiffOn_momentumMap hU hψ).contDiffAt (hU.mem_nhds hx₀)
  obtain ⟨H, hH⟩ := hinv
  have hd : HasFDerivAt (momentumMap ψ) (H : (E × E) →L[ℝ] E × E) x₀ := by
    rw [hH]
    exact (hc.differentiableAt one_ne_zero).hasFDerivAt
  let e := hc.toOpenPartialHomeomorph (momentumMap ψ) hd one_ne_zero
  have hsrc : x₀ ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd one_ne_zero
  have he : ∀ x, e x = momentumMap ψ x := fun _ => rfl
  have hg : ContDiffAt ℝ 1 e.symm (momentumMap ψ x₀) := hc.to_localInverse hd one_ne_zero
  obtain ⟨V₁, hV₁sub, hV₁open, hV₁mem⟩ := mem_nhds_iff.mp (hg.eventually (by simp))
  have hleft : e.symm (momentumMap ψ x₀) = x₀ := by
    rw [← he]
    exact e.left_inv hsrc
  have hV₁ : ∀ y ∈ V₁, ContDiffAt ℝ 1 e.symm y := fun y hy => hV₁sub hy
  refine ⟨V₁ ∩ (e.target ∩ e.symm ⁻¹' U), e.symm,
    hV₁open.inter (e.isOpen_inter_preimage_symm hU), ⟨hV₁mem, ?_, ?_⟩, hleft,
    fun y hy => (hV₁ y hy.1).contDiffWithinAt, fun y hy => ⟨hy.2.2, e.right_inv hy.2.1⟩,
    e.eventually_left_inverse hsrc⟩
  · rw [← he]
    exact e.map_source hsrc
  · rw [mem_preimage, hleft]
    exact hx₀

/-- The angular eikonal of a point eikonal with invertible Hessian (Landau–Lifshitz §55): on an
open neighbourhood `V` of the momenta of `x₀` the local inverse `g` of the momentum map defines
the angular eikonal, with `df = r·dp − r′·dp′`. -/
theorem exists_angularEikonal {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ 2 ψ U) {x₀ : E × E} (hx₀ : x₀ ∈ U)
    (hinv : (fderiv ℝ (momentumMap ψ) x₀).IsInvertible) :
    ∃ (V : Set (E × E)) (g : E × E → E × E), IsOpen V ∧ momentumMap ψ x₀ ∈ V ∧
      g (momentumMap ψ x₀) = x₀ ∧ ContDiffOn ℝ 1 g V ∧
      (∀ y ∈ V, g y ∈ U ∧ momentumMap ψ (g y) = y) ∧
      ∀ y ∈ V, fderiv ℝ (angularEikonal ψ g) y =
        (innerSL ℝ (g y).1).comp (fst ℝ E E) - (innerSL ℝ (g y).2).comp (snd ℝ E E) := by
  obtain ⟨V, g, hV, hmem, hg₀, hg, hinvV, -⟩ := exists_localInverse_momentumMap hU hψ hx₀ hinv
  refine ⟨V, g, hV, hmem, hg₀, hg, hinvV, fun y hy => ?_⟩
  refine fderiv_angularEikonal (V := V) (fun y hy => ?_) (fun y hy => ?_)
    (fun y hy => (hinvV y hy).2) hy
  · exact (hψ.contDiffAt (hU.mem_nhds (hinvV y hy).1)).differentiableAt (by simp)
  · exact (hg.contDiffAt (hV.mem_nhds hy)).differentiableAt one_ne_zero

/-- The ray map of a point eikonal with invertible mixed Hessian `∂²ψ/∂r∂r′` (Landau–Lifshitz §55):
the equation `p = −∂ψ/∂r(r, r′)` has, near `x₀`, a `C¹` solution `r′(r, p)` by the implicit
function theorem, and `Φ(r, p) = (r′, ∂ψ/∂r′(r, r′))` is a ray map on an open neighbourhood `W`
of `(r₀, p₀)`. -/
theorem exists_rayMap {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ 2 ψ U) {x₀ : E × E} (hx₀ : x₀ ∈ U)
    (hinv : (mixedHessian ψ x₀).IsInvertible) :
    ∃ (W : Set (E × E)) (Φ : E × E → E × E), IsOpen W ∧ (x₀.1, entryMomentum ψ x₀) ∈ W ∧
      Φ (x₀.1, entryMomentum ψ x₀) = (x₀.2, exitMomentum ψ x₀) ∧ ContDiffOn ℝ 1 Φ W ∧
      (∀ z ∈ W, (z.1, (Φ z).1) ∈ U) ∧ IsRayMapOn ψ Φ W := by
  set z₀ : E × E := (x₀.1, entryMomentum ψ x₀)
  set u : (E × E) × E := (z₀, x₀.2)
  let κ : ((E × E) × E) →L[ℝ] E × E :=
    ((fst ℝ E E).comp (fst ℝ (E × E) E)).prod (snd ℝ (E × E) E)
  let f : (E × E) × E → E := fun w => entryMomentum ψ (κ w) - w.1.2
  have hκu : κ u = x₀ := rfl
  have hentry : ContDiffAt ℝ 1 (entryMomentum ψ) x₀ :=
    (contDiffOn_entryMomentum hU hψ).contDiffAt (hU.mem_nhds hx₀)
  have hentry' : HasFDerivAt (entryMomentum ψ) (fderiv ℝ (entryMomentum ψ) x₀) (κ u) :=
    (hentry.differentiableAt one_ne_zero).hasFDerivAt
  have hfd : HasFDerivAt f ((fderiv ℝ (entryMomentum ψ) x₀).comp κ -
      (snd ℝ E E).comp (fst ℝ (E × E) E)) u :=
    (hentry'.comp u κ.hasFDerivAt).sub ((snd ℝ E E).comp (fst ℝ (E × E) E)).hasFDerivAt
  have hf : ContDiffAt ℝ 1 f u :=
    (hentry.comp u κ.contDiff.contDiffAt).sub
      ((snd ℝ E E).comp (fst ℝ (E × E) E)).contDiff.contDiffAt
  have hfinr : fderiv ℝ f u ∘L inr ℝ (E × E) E = -mixedHessian ψ x₀ := by
    rw [hfd.fderiv]
    refine ContinuousLinearMap.ext fun b => ?_
    simp [mixedHessian, κ]
  have hfinv : (fderiv ℝ f u ∘L inr ℝ (E × E) E).IsInvertible := by
    rw [hfinr]
    have hn : (-ContinuousLinearMap.id ℝ E).IsInvertible :=
      IsInvertible.of_inverse (g := -ContinuousLinearMap.id ℝ E)
        (ContinuousLinearMap.ext fun _ => by simp) (ContinuousLinearMap.ext fun _ => by simp)
    have h := hn.comp hinv
    rwa [neg_comp, ContinuousLinearMap.id_comp] at h
  set φ := hf.implicitFunction one_ne_zero hfinv
  have hφ₀ : φ z₀ = x₀.2 := hf.implicitFunction_apply_self one_ne_zero hfinv
  have hφeq : ∀ᶠ z in 𝓝 z₀, f (z, φ z) = f u :=
    hf.eventually_apply_implicitFunction one_ne_zero hfinv
  have hfu : f u = 0 := sub_self _
  have hφc : ContDiffAt ℝ 1 φ z₀ := hf.contDiffAt_implicitFunction one_ne_zero hfinv
  have hmem : ∀ᶠ z in 𝓝 z₀, (z.1, φ z) ∈ U := by
    have ht : Tendsto (fun z : E × E => (z.1, φ z)) (𝓝 z₀) (𝓝 (z₀.1, φ z₀)) :=
      (continuousAt_fst (p := z₀)).prodMk hφc.continuousAt
    have hz₀ : (z₀.1, φ z₀) = x₀ := by rw [hφ₀]
    rw [hz₀] at ht
    exact ht.eventually (hU.mem_nhds hx₀)
  obtain ⟨W, hWsub, hWopen, hW₀⟩ :=
    mem_nhds_iff.mp ((hφc.eventually (by simp)).and (hφeq.and hmem))
  refine ⟨W, fun z => (φ z, exitMomentum ψ (z.1, φ z)), hWopen, hW₀, ?_, ?_,
    fun z hz => (hWsub hz).2.2, fun z hz => ?_⟩
  · show (φ z₀, exitMomentum ψ (z₀.1, φ z₀)) = _
    rw [hφ₀]
  · intro z hz
    have hzU := (hWsub hz).2.2
    have hexit : ContDiffAt ℝ 1 (exitMomentum ψ) (z.1, φ z) :=
      (contDiffOn_exitMomentum hU hψ).contDiffAt (hU.mem_nhds hzU)
    exact ((hWsub hz).1.prodMk (hexit.comp z (contDiffAt_fst.prodMk (hWsub hz).1))).contDiffWithinAt
  · have h := (hWsub hz).2.1
    rw [hfu] at h
    exact Prod.ext (sub_eq_zero.mp h) rfl

/-- The ray map of a point eikonal with invertible mixed Hessian preserves `dp ∧ dr`. -/
theorem exists_rayMap_symplectic {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ 2 ψ U) {x₀ : E × E} (hx₀ : x₀ ∈ U)
    (hinv : (mixedHessian ψ x₀).IsInvertible) :
    ∃ (W : Set (E × E)) (Φ : E × E → E × E), IsOpen W ∧ (x₀.1, entryMomentum ψ x₀) ∈ W ∧
      ContDiffOn ℝ 1 Φ W ∧ IsRayMapOn ψ Φ W ∧ ∀ z ∈ W, ∀ v w : E × E,
        canonicalForm (fderiv ℝ Φ z v) (fderiv ℝ Φ z w) = canonicalForm v w := by
  obtain ⟨W, Φ, hW, hW₀, -, hΦ, hWU, hray⟩ := exists_rayMap hU hψ hx₀ hinv
  refine ⟨W, Φ, hW, hW₀, hΦ, hray, fun z hz v w => ?_⟩
  exact rayMap_symplectic hW hray hz ((hΦ.contDiffAt (hW.mem_nhds hz)).differentiableAt
    one_ne_zero) (hψ.contDiffAt (hU.mem_nhds (hWU z hz))) v w

/-! ### The paraxial point eikonal -/

/-- The paraxial point eikonal `ψ₀ + (a r² − 2b r·r′ + c r′²)/2` of a centred optical system
between two transverse planes. -/
def paraxialEikonal (ψ₀ a b c : ℝ) (x : E × E) : ℝ :=
  ψ₀ + (a * ‖x.1‖ ^ 2 - 2 * b * ⟪x.1, x.2⟫ + c * ‖x.2‖ ^ 2) / 2

omit [CompleteSpace E] in
theorem hasFDerivAt_paraxialEikonal (ψ₀ a b c : ℝ) (x : E × E) :
    HasFDerivAt (paraxialEikonal ψ₀ a b c)
      ((innerSL ℝ (a • x.1 - b • x.2)).comp (fst ℝ E E) +
        (innerSL ℝ (c • x.2 - b • x.1)).comp (snd ℝ E E)) x := by
  have h1 := (hasFDerivAt_fst (p := x) (𝕜 := ℝ)).norm_sq
  have h2 := (hasFDerivAt_fst (p := x) (𝕜 := ℝ)).inner ℝ (hasFDerivAt_snd (p := x))
  have h3 := (hasFDerivAt_snd (p := x) (𝕜 := ℝ)).norm_sq
  have h := ((((h1.const_mul a).fun_sub (h2.const_mul (2 * b))).fun_add
    (h3.const_mul c)).mul_const (1 / 2 : ℝ)).const_add ψ₀
  have hfun : paraxialEikonal ψ₀ a b c = fun y : E × E =>
      ψ₀ + (a * ‖y.1‖ ^ 2 - 2 * b * ⟪y.1, y.2⟫ + c * ‖y.2‖ ^ 2) * (1 / 2) := by
    funext y
    simp only [paraxialEikonal]
    ring
  rw [hfun]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply, coe_fst', coe_snd',
    innerSL_apply_apply, smul_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    inner_sub_left, inner_smul_left, smul_eq_mul, RCLike.conj_to_real]
  rw [real_inner_comm u.1 x.2, real_inner_comm u.2 x.1]
  ring

omit [CompleteSpace E] in
theorem contDiff_paraxialEikonal (ψ₀ a b c : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (paraxialEikonal (E := E) ψ₀ a b c) := by
  unfold paraxialEikonal
  have h1 : ContDiff ℝ n fun x : E × E => ‖x.1‖ ^ 2 := (contDiff_norm_sq ℝ).comp contDiff_fst
  have h2 : ContDiff ℝ n fun x : E × E => ‖x.2‖ ^ 2 := (contDiff_norm_sq ℝ).comp contDiff_snd
  have h3 : ContDiff ℝ n fun x : E × E => ⟪x.1, x.2⟫ := contDiff_fst.inner ℝ contDiff_snd
  exact contDiff_const.add ((((contDiff_const.mul h1).sub (contDiff_const.mul h3)).add
    (contDiff_const.mul h2)).div_const 2)

/-- The momenta of the paraxial eikonal: `p = b r′ − a r`, `p′ = c r′ − b r`. -/
theorem momentumMap_paraxialEikonal (ψ₀ a b c : ℝ) (x : E × E) :
    momentumMap (paraxialEikonal ψ₀ a b c) x = (b • x.2 - a • x.1, c • x.2 - b • x.1) := by
  have hd := (hasFDerivAt_paraxialEikonal ψ₀ a b c x).fderiv
  refine Prod.ext (ext_inner_right ℝ fun v => ?_) (ext_inner_right ℝ fun v => ?_)
  · change ⟪entryMomentum _ x, v⟫ = _
    rw [inner_entryMomentum, hd]
    simp only [add_apply, ContinuousLinearMap.comp_apply, coe_fst', coe_snd',
      innerSL_apply_apply, inner_zero_right, add_zero, inner_sub_left, inner_smul_left,
      RCLike.conj_to_real]
    ring
  · change ⟪exitMomentum _ x, v⟫ = _
    rw [inner_exitMomentum, hd]
    simp only [add_apply, ContinuousLinearMap.comp_apply, coe_fst', coe_snd',
      innerSL_apply_apply, inner_zero_right, zero_add, inner_sub_left, inner_smul_left,
      RCLike.conj_to_real]

/-- The momentum map `(r, r′) ↦ (b r′ − a r, c r′ − b r)` of the paraxial eikonal, as a linear
map. -/
def paraxialMomentum (a b c : ℝ) : (E × E) →L[ℝ] E × E :=
  (b • snd ℝ E E - a • fst ℝ E E).prod (c • snd ℝ E E - b • fst ℝ E E)

theorem momentumMap_paraxialEikonal_eq (ψ₀ a b c : ℝ) :
    momentumMap (paraxialEikonal ψ₀ a b c) = paraxialMomentum (E := E) a b c :=
  funext fun x => by
    rw [momentumMap_paraxialEikonal]
    rfl

/-- The inverse `(p, p′) ↦ ((c p − b p′)/D, (b p − a p′)/D)`, `D = b² − ac`, of the momentum map
of the paraxial eikonal. -/
def paraxialInverse (a b c : ℝ) : (E × E) →L[ℝ] E × E :=
  (b ^ 2 - a * c)⁻¹ • ((c • fst ℝ E E - b • snd ℝ E E).prod (b • fst ℝ E E - a • snd ℝ E E))

omit [CompleteSpace E] in
theorem paraxialMomentum_paraxialInverse {a b c : ℝ} (hD : b ^ 2 - a * c ≠ 0) (y : E × E) :
    paraxialMomentum a b c (paraxialInverse a b c y) = y := by
  have h : (b ^ 2 - a * c)⁻¹ * (b ^ 2 - a * c) = 1 := inv_mul_cancel₀ hD
  refine Prod.ext ?_ ?_
  · simp only [paraxialMomentum, paraxialInverse, ContinuousLinearMap.prod_apply, sub_apply,
      smul_apply, coe_fst', coe_snd', Prod.smul_mk]
    calc _ = ((b ^ 2 - a * c)⁻¹ * (b ^ 2 - a * c)) • y.1 := by module
      _ = y.1 := by rw [h, one_smul]
  · simp only [paraxialMomentum, paraxialInverse, ContinuousLinearMap.prod_apply, sub_apply,
      smul_apply, coe_fst', coe_snd', Prod.smul_mk]
    calc _ = ((b ^ 2 - a * c)⁻¹ * (b ^ 2 - a * c)) • y.2 := by module
      _ = y.2 := by rw [h, one_smul]

omit [CompleteSpace E] in
theorem paraxialInverse_paraxialMomentum {a b c : ℝ} (hD : b ^ 2 - a * c ≠ 0) (x : E × E) :
    paraxialInverse a b c (paraxialMomentum a b c x) = x := by
  have h : (b ^ 2 - a * c)⁻¹ * (b ^ 2 - a * c) = 1 := inv_mul_cancel₀ hD
  refine Prod.ext ?_ ?_
  · simp only [paraxialMomentum, paraxialInverse, ContinuousLinearMap.prod_apply, sub_apply,
      smul_apply, coe_fst', coe_snd', Prod.smul_mk]
    calc _ = ((b ^ 2 - a * c)⁻¹ * (b ^ 2 - a * c)) • x.1 := by module
      _ = x.1 := by rw [h, one_smul]
  · simp only [paraxialMomentum, paraxialInverse, ContinuousLinearMap.prod_apply, sub_apply,
      smul_apply, coe_fst', coe_snd', Prod.smul_mk]
    calc _ = ((b ^ 2 - a * c)⁻¹ * (b ^ 2 - a * c)) • x.2 := by module
      _ = x.2 := by rw [h, one_smul]

/-- The hypothesis of `exists_angularEikonal` for the paraxial eikonal: the derivative of the
momentum map is invertible when `b² ≠ ac`. -/
theorem isInvertible_fderiv_momentumMap_paraxialEikonal {ψ₀ a b c : ℝ}
    (hD : b ^ 2 - a * c ≠ 0) (x : E × E) :
    (fderiv ℝ (momentumMap (paraxialEikonal ψ₀ a b c)) x).IsInvertible := by
  rw [momentumMap_paraxialEikonal_eq, ContinuousLinearMap.fderiv]
  exact IsInvertible.of_inverse (g := paraxialInverse a b c)
    (ContinuousLinearMap.ext fun y => paraxialMomentum_paraxialInverse hD y)
    (ContinuousLinearMap.ext fun x => paraxialInverse_paraxialMomentum hD x)

/-- The hypotheses of `fderiv_angularEikonal` for the paraxial eikonal, with `V` the whole
space. -/
theorem momentumMap_paraxialInverse {ψ₀ a b c : ℝ} (hD : b ^ 2 - a * c ≠ 0) (y : E × E) :
    momentumMap (paraxialEikonal ψ₀ a b c) (paraxialInverse a b c y) = y := by
  rw [momentumMap_paraxialEikonal_eq]
  exact paraxialMomentum_paraxialInverse hD y

omit [CompleteSpace E] in
/-- The angular eikonal of the paraxial eikonal:
`f(p, p′) = ψ₀ + (c p² − 2b p·p′ + a p′²)/2(b² − ac)`. -/
theorem angularEikonal_paraxialEikonal {ψ₀ a b c : ℝ} (hD : b ^ 2 - a * c ≠ 0) (y : E × E) :
    angularEikonal (paraxialEikonal ψ₀ a b c) (paraxialInverse a b c) y =
      ψ₀ + (c * ‖y.1‖ ^ 2 - 2 * b * ⟪y.1, y.2⟫ + a * ‖y.2‖ ^ 2) / (2 * (b ^ 2 - a * c)) := by
  simp only [angularEikonal, paraxialEikonal, paraxialInverse, smul_apply,
    ContinuousLinearMap.prod_apply, sub_apply, coe_fst', coe_snd', Prod.smul_mk]
  simp only [← real_inner_self_eq_norm_sq, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, RCLike.conj_to_real, real_inner_comm y.1 y.2]
  field_simp
  ring

theorem entryMomentum_paraxialEikonal (ψ₀ a b c : ℝ) :
    entryMomentum (paraxialEikonal ψ₀ a b c) = ⇑(b • snd ℝ E E - a • fst ℝ E E) :=
  funext fun x => (congrArg Prod.fst (momentumMap_paraxialEikonal ψ₀ a b c x)).trans rfl

/-- The mixed Hessian of the paraxial eikonal is `∂²ψ/∂r∂r′ = −b`. -/
theorem mixedHessian_paraxialEikonal (ψ₀ a b c : ℝ) (x : E × E) :
    mixedHessian (paraxialEikonal ψ₀ a b c) x = -b • ContinuousLinearMap.id ℝ E := by
  rw [mixedHessian, entryMomentum_paraxialEikonal, ContinuousLinearMap.fderiv]
  refine ContinuousLinearMap.ext fun v => ?_
  simp

/-- The hypothesis of `exists_rayMap` for the paraxial eikonal: the mixed Hessian is invertible
when `b ≠ 0`. -/
theorem isInvertible_mixedHessian_paraxialEikonal {ψ₀ a b c : ℝ} (hb : b ≠ 0) (x : E × E) :
    (mixedHessian (paraxialEikonal ψ₀ a b c) x).IsInvertible := by
  rw [mixedHessian_paraxialEikonal]
  refine IsInvertible.of_inverse (g := -b⁻¹ • ContinuousLinearMap.id ℝ E)
    (ContinuousLinearMap.ext fun v => ?_) (ContinuousLinearMap.ext fun v => ?_) <;>
  simp [smul_smul, hb]

/-- The ray map of the paraxial eikonal (its ray-transfer matrix):
`r′ = (p + a r)/b`, `p′ = c r′ − b r`. -/
def paraxialRayMap (a b c : ℝ) : (E × E) →L[ℝ] E × E :=
  (b⁻¹ • (snd ℝ E E + a • fst ℝ E E)).prod
    (c • (b⁻¹ • (snd ℝ E E + a • fst ℝ E E)) - b • fst ℝ E E)

/-- The hypothesis of `rayMap_symplectic` for the paraxial eikonal with `b ≠ 0`, on the whole
phase space. -/
theorem isRayMapOn_paraxialRayMap {ψ₀ a b c : ℝ} (hb : b ≠ 0) :
    IsRayMapOn (paraxialEikonal ψ₀ a b c) (paraxialRayMap (E := E) a b c) univ := by
  intro z _
  rw [momentumMap_paraxialEikonal]
  refine Prod.ext ?_ rfl
  simp only [paraxialRayMap, ContinuousLinearMap.prod_apply, smul_apply, add_apply, coe_fst',
    coe_snd', smul_smul, mul_inv_cancel₀ hb, one_smul, add_sub_cancel_right]

/-- The paraxial ray map preserves `dp ∧ dr`, by `rayMap_symplectic`. -/
theorem paraxialRayMap_symplectic {a b c : ℝ} (hb : b ≠ 0) (v w : E × E) :
    canonicalForm (paraxialRayMap a b c v) (paraxialRayMap a b c w) = canonicalForm v w := by
  have hΦ : DifferentiableAt ℝ (paraxialRayMap (E := E) a b c) 0 :=
    (paraxialRayMap (E := E) a b c).hasFDerivAt.differentiableAt
  have h := rayMap_symplectic isOpen_univ (isRayMapOn_paraxialRayMap (ψ₀ := 0) hb)
    (mem_univ 0) hΦ ((contDiff_paraxialEikonal 0 a b c).contDiffAt) v w
  rwa [ContinuousLinearMap.fderiv] at h

/-! #### Free propagation and the thin lens -/

omit [CompleteSpace E] in
/-- The paraxial eikonal of free propagation over a distance `L` in a medium of index `1`:
`L + |r′ − r|²/2L`, the expansion of `√(L² + |r′ − r|²)`. -/
theorem paraxialEikonal_freePropagation (L : ℝ) (x : E × E) :
    paraxialEikonal L L⁻¹ L⁻¹ L⁻¹ x = L + ‖x.2 - x.1‖ ^ 2 / (2 * L) := by
  rw [paraxialEikonal, norm_sub_sq_real, real_inner_comm]
  ring

omit [CompleteSpace E] in
/-- The ray map of free propagation: `r′ = r + L p`, `p′ = p`. -/
theorem paraxialRayMap_freePropagation {L : ℝ} (hL : L ≠ 0) (z : E × E) :
    paraxialRayMap L⁻¹ L⁻¹ L⁻¹ z = (z.1 + L • z.2, z.2) := by
  have h : L * L⁻¹ = 1 := mul_inv_cancel₀ hL
  simp only [paraxialRayMap, ContinuousLinearMap.prod_apply, smul_apply, add_apply, sub_apply,
    coe_fst', coe_snd', inv_inv, smul_add, smul_smul, h, one_smul]
  refine Prod.ext (add_comm _ _) ?_
  simp only [inv_mul_cancel₀ hL, one_smul]
  abel

/-- For free propagation (`a = b = c`) the momentum map is not a local diffeomorphism: the
momenta `p = p′ = a (r′ − r)` do not change when both points move by the same vector. The
angular eikonal does not exist, although the mixed Hessian `−a` is invertible for `a ≠ 0`. -/
theorem not_isInvertible_fderiv_momentumMap_freePropagation [Nontrivial E] (ψ₀ a : ℝ)
    (x : E × E) : ¬(fderiv ℝ (momentumMap (paraxialEikonal ψ₀ a a a)) x).IsInvertible := by
  rw [momentumMap_paraxialEikonal_eq, ContinuousLinearMap.fderiv]
  rintro ⟨e, he⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have h : e (v, v) = e 0 := by
    rw [map_zero, ← ContinuousLinearEquiv.coe_coe, he]
    simp [paraxialMomentum]
  exact hv (congrArg Prod.fst (e.injective h))

omit [CompleteSpace E] in
/-- The thin lens of focal length `F` followed by a gap `L`: the point eikonal
`ψ₀ − r²/2F + |r′ − r|²/2L` is the paraxial eikonal with `a = 1/L − 1/F`, `b = c = 1/L`, and its
angular eikonal is `ψ₀ + (F |p − p′|² − L p′²)/2`. -/
theorem angularEikonal_thinLens {ψ₀ F L : ℝ} (hF : F ≠ 0) (hL : L ≠ 0) (y : E × E) :
    angularEikonal (paraxialEikonal ψ₀ (L⁻¹ - F⁻¹) L⁻¹ L⁻¹)
        (paraxialInverse (L⁻¹ - F⁻¹) L⁻¹ L⁻¹) y =
      ψ₀ + (F * ‖y.1 - y.2‖ ^ 2 - L * ‖y.2‖ ^ 2) / 2 := by
  have hD : L⁻¹ ^ 2 - (L⁻¹ - F⁻¹) * L⁻¹ = (F * L)⁻¹ := by
    field_simp
    ring
  have hD' : L⁻¹ ^ 2 - (L⁻¹ - F⁻¹) * L⁻¹ ≠ 0 := by
    rw [hD]
    exact inv_ne_zero (mul_ne_zero hF hL)
  rw [angularEikonal_paraxialEikonal hD', hD, norm_sub_sq_real]
  field_simp
  ring

omit [CompleteSpace E] in
/-- The ray map of the thin lens followed by a gap `L`: the lens turns `p` into `p − r/F`, and the
ray then travels the distance `L`. -/
theorem paraxialRayMap_thinLens {F L : ℝ} (hL : L ≠ 0) (z : E × E) :
    paraxialRayMap (L⁻¹ - F⁻¹) L⁻¹ L⁻¹ z = (z.1 + L • (z.2 - F⁻¹ • z.1), z.2 - F⁻¹ • z.1) := by
  have h : L * L⁻¹ = 1 := mul_inv_cancel₀ hL
  have h' : L⁻¹ * L = 1 := inv_mul_cancel₀ hL
  simp only [paraxialRayMap, ContinuousLinearMap.prod_apply, smul_apply, add_apply, sub_apply,
    coe_fst', coe_snd', inv_inv]
  refine Prod.ext ?_ ?_
  · calc _ = (L * L⁻¹) • z.1 + L • (z.2 - F⁻¹ • z.1) := by module
      _ = _ := by rw [h, one_smul]
  · calc _ = (L⁻¹ * L) • (z.2 - F⁻¹ • z.1) + (L⁻¹ * L - 1) • (L⁻¹ • z.1) := by module
      _ = _ := by rw [h', sub_self, zero_smul, add_zero, one_smul]

/-! #### Free propagation without the paraxial approximation -/

/-- The point eikonal `√(L² + |r′ − r|²)` of free propagation over a distance `L` between two
transverse planes in a medium of index `1`. -/
def freeEikonal (L : ℝ) (x : E × E) : ℝ :=
  √(L ^ 2 + ‖x.2 - x.1‖ ^ 2)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem freeEikonal_pos {L : ℝ} (hL : L ≠ 0) (x : E × E) : 0 < freeEikonal L x :=
  Real.sqrt_pos.mpr (by positivity)

omit [CompleteSpace E] in
theorem contDiff_freeEikonal {L : ℝ} (hL : L ≠ 0) {n : WithTop ℕ∞} :
    ContDiff ℝ n (freeEikonal (E := E) L) := by
  have h : ContDiff ℝ n fun x : E × E => L ^ 2 + ‖x.2 - x.1‖ ^ 2 :=
    contDiff_const.add ((contDiff_norm_sq ℝ).comp (contDiff_snd.sub contDiff_fst))
  exact h.sqrt fun x => (by positivity : (0 : ℝ) < L ^ 2 + ‖x.2 - x.1‖ ^ 2).ne'

omit [CompleteSpace E] in
theorem hasFDerivAt_freeEikonal {L : ℝ} (hL : L ≠ 0) (x : E × E) :
    HasFDerivAt (freeEikonal L)
      ((freeEikonal L x)⁻¹ • (innerSL ℝ (x.2 - x.1)).comp (snd ℝ E E - fst ℝ E E)) x := by
  have hd : HasFDerivAt (fun y : E × E => y.2 - y.1) (snd ℝ E E - fst ℝ E E) x :=
    (snd ℝ E E - fst ℝ E E).hasFDerivAt
  have hg := (hd.norm_sq.const_add (L ^ 2)).sqrt
    (by positivity : (0 : ℝ) < L ^ 2 + ‖x.2 - x.1‖ ^ 2).ne'
  refine hg.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
  have hs := (freeEikonal_pos hL x).ne'
  rw [freeEikonal] at hs ⊢
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  field_simp

/-- The momenta of free propagation: `p = p′ = (r′ − r)/√(L² + |r′ − r|²)`, the transverse part
of the unit vector along the ray. -/
theorem momentumMap_freeEikonal {L : ℝ} (hL : L ≠ 0) (x : E × E) :
    momentumMap (freeEikonal L) x =
      ((freeEikonal L x)⁻¹ • (x.2 - x.1), (freeEikonal L x)⁻¹ • (x.2 - x.1)) := by
  have hd := (hasFDerivAt_freeEikonal hL x).fderiv
  refine Prod.ext (ext_inner_right ℝ fun v => ?_) (ext_inner_right ℝ fun v => ?_)
  · change ⟪entryMomentum _ x, v⟫ = _
    rw [inner_entryMomentum, hd]
    simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul,
      sub_apply, coe_fst', coe_snd', zero_sub, inner_neg_right, inner_smul_left,
      RCLike.conj_to_real]
    ring
  · change ⟪exitMomentum _ x, v⟫ = _
    rw [inner_exitMomentum, hd]
    simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul,
      sub_apply, coe_fst', coe_snd', sub_zero, inner_smul_left, RCLike.conj_to_real]

/-- The ray map of free propagation over `L > 0`: a ray with transverse direction `p`, `|p| < 1`,
reaches `r′ = r + L p/√(1 − p²)` and keeps its direction. -/
def freeRayMap (L : ℝ) (z : E × E) : E × E :=
  (z.1 + (L / √(1 - ‖z.2‖ ^ 2)) • z.2, z.2)

omit [CompleteSpace E] in
theorem differentiableAt_freeRayMap (L : ℝ) {z : E × E} (hz : ‖z.2‖ < 1) :
    DifferentiableAt ℝ (freeRayMap L) z := by
  have hpos : 0 < 1 - ‖z.2‖ ^ 2 := by nlinarith [norm_nonneg z.2]
  have h1 : DifferentiableAt ℝ (fun y : E × E => 1 - ‖y.2‖ ^ 2) z :=
    (differentiableAt_const _).sub (differentiableAt_snd.norm_sq ℝ)
  have h2 : DifferentiableAt ℝ (fun y : E × E => L / √(1 - ‖y.2‖ ^ 2)) z := by
    simp only [div_eq_mul_inv]
    exact ((h1.sqrt hpos.ne').fun_inv (Real.sqrt_pos.mpr hpos).ne').const_mul L
  exact (differentiableAt_fst.add (h2.smul differentiableAt_snd)).prodMk differentiableAt_snd

/-- The ray map of free propagation is a ray map of `√(L² + |r′ − r|²)` on the open set
`|p| < 1`. -/
theorem isRayMapOn_freeRayMap {L : ℝ} (hL : 0 < L) :
    IsRayMapOn (freeEikonal L) (freeRayMap L) {z : E × E | ‖z.2‖ < 1} := by
  intro z hz
  have hz' : ‖z.2‖ < 1 := hz
  have hpos : 0 < 1 - ‖z.2‖ ^ 2 := by nlinarith [norm_nonneg z.2]
  have hs : 0 < √(1 - ‖z.2‖ ^ 2) := Real.sqrt_pos.mpr hpos
  have hs0 : √(1 - ‖z.2‖ ^ 2) ≠ 0 := hs.ne'
  have hs2 : √(1 - ‖z.2‖ ^ 2) ^ 2 = 1 - ‖z.2‖ ^ 2 := Real.sq_sqrt hpos.le
  have ht : 0 < L / √(1 - ‖z.2‖ ^ 2) := div_pos hL hs
  have hψ : freeEikonal L (z.1, (freeRayMap L z).1) = L / √(1 - ‖z.2‖ ^ 2) := by
    rw [freeEikonal, Real.sqrt_eq_iff_mul_self_eq_of_pos ht]
    simp only [freeRayMap, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      mul_pow, div_pow]
    field_simp
    linarith
  rw [momentumMap_freeEikonal hL.ne', hψ]
  simp only [freeRayMap, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

/-- The ray map of free propagation preserves `dp ∧ dr`, by `rayMap_symplectic`. -/
theorem freeRayMap_symplectic {L : ℝ} (hL : 0 < L) {z : E × E} (hz : ‖z.2‖ < 1)
    (v w : E × E) :
    canonicalForm (fderiv ℝ (freeRayMap L) z v) (fderiv ℝ (freeRayMap L) z w) =
      canonicalForm v w := by
  have hW : IsOpen {z : E × E | ‖z.2‖ < 1} := isOpen_lt continuous_snd.norm continuous_const
  have hψ : ContDiffAt ℝ 2 (freeEikonal (E := E) L) (z.1, (freeRayMap L z).1) :=
    (contDiff_freeEikonal hL.ne').contDiffAt
  exact rayMap_symplectic hW (isRayMapOn_freeRayMap hL) hz (differentiableAt_freeRayMap L hz)
    hψ v w

/-! ### The ray map of a point eikonal in the free C∞-ring -/

namespace Free

open SmoothAlgebra SmoothRing FreeSmoothRing Mechanics.GeneratingFunction

variable {ι : Type*} [DecidableEq ι]

/-- The ray map of a point eikonal `ψ(q, Q)` of the entry positions `q = r` and the exit
positions `Q = r′`, with an inverse `G` of `oldMap (−ψ)`: the generating function of
Landau–Lifshitz §45 is `F = −ψ`, so that `p = ∂F/∂q = −∂ψ/∂r` and `P = −∂F/∂Q = ∂ψ/∂r′`. -/
def rayMap (ψ : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)) :
    SmoothRingHom (PhaseSpace ι) (PhaseSpace ι) :=
  transformation (-ψ) G

theorem rayMap_q (ψ : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι))
    (i : ι) : rayMap ψ G (PhaseSpace.q i) = G (newPosition i) :=
  transformation_q _ _ _

theorem rayMap_p (ψ : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι))
    (i : ι) : rayMap ψ G (PhaseSpace.p i) = G (gradNew ψ i) := by
  rw [rayMap, transformation_p, gradNew_neg, Pi.neg_apply, SmoothRingHom.map_neg, neg_neg]

/-- The ray map of a point eikonal that is a free generating function preserves the canonical
bracket (Landau–Lifshitz §55, by §45). -/
theorem rayMap_isPoissonHom [Fintype ι] {ψ : PositionPair ι}
    {G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)} (h : IsFree (-ψ) G) :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (PhaseSpace.canonical ι).toAlmostPoissonStructure (rayMap ψ G) :=
  h.isPoissonHom_transformation

variable (ι) in
/-- The paraxial point eikonal `Σᵢ (a qᵢ² − 2b qᵢQᵢ + c Qᵢ²)/2` in the free C∞-ring. -/
def paraxialEikonal [Fintype ι] (a b c : ℝ) : PositionPair ι :=
  ∑ k, (algebraMap ℝ (PositionPair ι) (a / 2) * (oldPosition k * oldPosition k) -
    algebraMap ℝ (PositionPair ι) b * (oldPosition k * newPosition k) +
    algebraMap ℝ (PositionPair ι) (c / 2) * (newPosition k * newPosition k))

omit [DecidableEq ι] in
private theorem algebraMap_half (a : ℝ) :
    algebraMap ℝ (PositionPair ι) a = algebraMap ℝ (PositionPair ι) (a / 2) * 2 := by
  rw [← map_ofNat (algebraMap ℝ (PositionPair ι)) 2, ← map_mul]
  congr 1
  ring

/-- `∂ψ/∂qᵢ = a qᵢ − b Qᵢ`. -/
theorem gradOld_paraxialEikonal [Fintype ι] (a b c : ℝ) (i : ι) :
    gradOld (paraxialEikonal ι a b c) i =
      algebraMap ℝ (PositionPair ι) a * oldPosition i -
        algebraMap ℝ (PositionPair ι) b * newPosition i := by
  have hterm (k : ι) : partialDerivation (Sum.inl i)
      (algebraMap ℝ (PositionPair ι) (a / 2) * (oldPosition k * oldPosition k) -
        algebraMap ℝ (PositionPair ι) b * (oldPosition k * newPosition k) +
        algebraMap ℝ (PositionPair ι) (c / 2) * (newPosition k * newPosition k)) =
      if k = i then algebraMap ℝ (PositionPair ι) a * oldPosition i -
        algebraMap ℝ (PositionPair ι) b * newPosition i else 0 := by
    simp only [SmoothDerivation.map_add, map_sub, SmoothDerivation.map_mul,
      SmoothDerivation.map_algebraMap, oldPosition, newPosition, partialDerivation_generator,
      Sum.inl.injEq, reduceCtorEq, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
    split_ifs with h
    · subst h
      rw [algebraMap_half a]
      ring
    · ring
  rw [gradOld, paraxialEikonal, map_sum]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- `∂ψ/∂Qᵢ = c Qᵢ − b qᵢ`. -/
theorem gradNew_paraxialEikonal [Fintype ι] (a b c : ℝ) (i : ι) :
    gradNew (paraxialEikonal ι a b c) i =
      algebraMap ℝ (PositionPair ι) c * newPosition i -
        algebraMap ℝ (PositionPair ι) b * oldPosition i := by
  have hterm (k : ι) : partialDerivation (Sum.inr i)
      (algebraMap ℝ (PositionPair ι) (a / 2) * (oldPosition k * oldPosition k) -
        algebraMap ℝ (PositionPair ι) b * (oldPosition k * newPosition k) +
        algebraMap ℝ (PositionPair ι) (c / 2) * (newPosition k * newPosition k)) =
      if k = i then algebraMap ℝ (PositionPair ι) c * newPosition i -
        algebraMap ℝ (PositionPair ι) b * oldPosition i else 0 := by
    simp only [SmoothDerivation.map_add, map_sub, SmoothDerivation.map_mul,
      SmoothDerivation.map_algebraMap, oldPosition, newPosition, partialDerivation_generator,
      Sum.inr.injEq, reduceCtorEq, ↓reduceIte, smul_eq_mul, mul_zero, zero_add]
    split_ifs with h
    · subst h
      rw [algebraMap_half c]
      ring
    · ring
  rw [gradNew, paraxialEikonal, map_sum]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

variable (ι) in
/-- The inverse of `oldMap (−ψ)` for the paraxial eikonal: `q ↦ q`, `Q ↦ (p + a q)/b`. -/
def paraxialInverse (a b : ℝ) : SmoothRingHom (PositionPair ι) (PhaseSpace ι) :=
  FreeSmoothRing.lift (Sum.elim PhaseSpace.q fun i => algebraMap ℝ (PhaseSpace ι) b⁻¹ *
    (PhaseSpace.p i + algebraMap ℝ (PhaseSpace ι) a * PhaseSpace.q i))

omit [DecidableEq ι] in
theorem paraxialInverse_oldPosition (a b : ℝ) (i : ι) :
    paraxialInverse ι a b (oldPosition i) = PhaseSpace.q i := by
  rw [paraxialInverse, oldPosition, lift_generator, Sum.elim_inl]

omit [DecidableEq ι] in
theorem paraxialInverse_newPosition (a b : ℝ) (i : ι) :
    paraxialInverse ι a b (newPosition i) = algebraMap ℝ (PhaseSpace ι) b⁻¹ *
      (PhaseSpace.p i + algebraMap ℝ (PhaseSpace ι) a * PhaseSpace.q i) := by
  rw [paraxialInverse, newPosition, lift_generator, Sum.elim_inr]

/-- The paraxial point eikonal with `b ≠ 0` is a free generating function: `(q, p)` and `(q, Q)`
are co-ordinates of the same space, by the linear inverse `Q = (p + a q)/b`. -/
theorem isFree_paraxialEikonal [Fintype ι] {a b : ℝ} (c : ℝ) (hb : b ≠ 0) :
    IsFree (-paraxialEikonal ι a b c) (paraxialInverse ι a b) where
  left_inv := by
    have hbb : algebraMap ℝ (PhaseSpace ι) b * algebraMap ℝ (PhaseSpace ι) b⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hb, map_one]
    refine FreeSmoothRing.hom_ext fun s => ?_
    rcases s with i | i
    · rw [SmoothRingHom.comp_apply, SmoothRingHom.id_apply,
        show (generator (Sum.inl i) : PhaseSpace ι) = PhaseSpace.q i from rfl, oldMap_q,
        paraxialInverse_oldPosition]
    · rw [SmoothRingHom.comp_apply, SmoothRingHom.id_apply,
        show (generator (Sum.inr i) : PhaseSpace ι) = PhaseSpace.p i from rfl, oldMap_p,
        gradOld_neg, Pi.neg_apply, gradOld_paraxialEikonal, SmoothRingHom.map_neg,
        SmoothRingHom.map_sub, SmoothRingHom.map_mul, SmoothRingHom.map_mul,
        SmoothRingHom.map_algebraMap, SmoothRingHom.map_algebraMap, paraxialInverse_oldPosition,
        paraxialInverse_newPosition]
      linear_combination
        (PhaseSpace.p i + algebraMap ℝ (PhaseSpace ι) a * PhaseSpace.q i) * hbb
  right_inv := by
    have hbb : algebraMap ℝ (PositionPair ι) b⁻¹ * algebraMap ℝ (PositionPair ι) b = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hb, map_one]
    refine FreeSmoothRing.hom_ext fun s => ?_
    rcases s with i | i
    · rw [SmoothRingHom.comp_apply, SmoothRingHom.id_apply,
        show (generator (Sum.inl i) : PositionPair ι) = oldPosition i from rfl,
        paraxialInverse_oldPosition, oldMap_q]
    · rw [SmoothRingHom.comp_apply, SmoothRingHom.id_apply,
        show (generator (Sum.inr i) : PositionPair ι) = newPosition i from rfl,
        paraxialInverse_newPosition, SmoothRingHom.map_mul, SmoothRingHom.map_add,
        SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_algebraMap,
        oldMap_q, oldMap_p, gradOld_neg, Pi.neg_apply, gradOld_paraxialEikonal]
      rw [neg_sub, sub_add_cancel, ← mul_assoc, hbb, one_mul]

/-- The paraxial ray map `r′ = (p + a r)/b`, `p′ = c r′ − b r`. -/
theorem rayMap_paraxialEikonal_q [Fintype ι] (a b c : ℝ) (i : ι) :
    rayMap (paraxialEikonal ι a b c) (paraxialInverse ι a b) (PhaseSpace.q i) =
      algebraMap ℝ (PhaseSpace ι) b⁻¹ *
        (PhaseSpace.p i + algebraMap ℝ (PhaseSpace ι) a * PhaseSpace.q i) := by
  rw [rayMap_q, paraxialInverse_newPosition]

theorem rayMap_paraxialEikonal_p [Fintype ι] (a b c : ℝ) (i : ι) :
    rayMap (paraxialEikonal ι a b c) (paraxialInverse ι a b) (PhaseSpace.p i) =
      algebraMap ℝ (PhaseSpace ι) c * (algebraMap ℝ (PhaseSpace ι) b⁻¹ *
        (PhaseSpace.p i + algebraMap ℝ (PhaseSpace ι) a * PhaseSpace.q i)) -
        algebraMap ℝ (PhaseSpace ι) b * PhaseSpace.q i := by
  rw [rayMap_p, gradNew_paraxialEikonal, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
    SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_algebraMap,
    paraxialInverse_oldPosition, paraxialInverse_newPosition]

/-- The paraxial ray map with `b ≠ 0` is canonical. -/
theorem rayMap_paraxialEikonal_isPoissonHom [Fintype ι] {a b : ℝ} (c : ℝ) (hb : b ≠ 0) :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (rayMap (paraxialEikonal ι a b c) (paraxialInverse ι a b)) :=
  rayMap_isPoissonHom (isFree_paraxialEikonal c hb)

variable (ι) in
/-- The point eikonal `−q²/2F + |Q − q|²/2L` of a thin lens of focal length `F` followed by a gap
`L` (without the constant `L`). -/
def thinLens [Fintype ι] (F L : ℝ) : PositionPair ι :=
  paraxialEikonal ι (L⁻¹ - F⁻¹) L⁻¹ L⁻¹

/-- The ray map of the thin lens is canonical: the proved instance of `rayMap_isPoissonHom`. -/
theorem rayMap_thinLens_isPoissonHom [Fintype ι] (F : ℝ) {L : ℝ} (hL : L ≠ 0) :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (rayMap (thinLens ι F L) (paraxialInverse ι (L⁻¹ - F⁻¹) L⁻¹)) :=
  rayMap_isPoissonHom (isFree_paraxialEikonal L⁻¹ (inv_ne_zero hL))

/-- The ray map of the thin lens: `r′ = r + L (p − r/F)`. -/
theorem rayMap_thinLens_q [Fintype ι] (F : ℝ) {L : ℝ} (hL : L ≠ 0) (i : ι) :
    rayMap (thinLens ι F L) (paraxialInverse ι (L⁻¹ - F⁻¹) L⁻¹) (PhaseSpace.q i) =
      PhaseSpace.q i + algebraMap ℝ (PhaseSpace ι) L *
        (PhaseSpace.p i - algebraMap ℝ (PhaseSpace ι) F⁻¹ * PhaseSpace.q i) := by
  have h : algebraMap ℝ (PhaseSpace ι) L * algebraMap ℝ (PhaseSpace ι) L⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hL, map_one]
  rw [thinLens, rayMap_paraxialEikonal_q, inv_inv, map_sub]
  linear_combination PhaseSpace.q i * h

/-- The ray map of the thin lens: `p′ = p − r/F`. -/
theorem rayMap_thinLens_p [Fintype ι] (F : ℝ) {L : ℝ} (hL : L ≠ 0) (i : ι) :
    rayMap (thinLens ι F L) (paraxialInverse ι (L⁻¹ - F⁻¹) L⁻¹) (PhaseSpace.p i) =
      PhaseSpace.p i - algebraMap ℝ (PhaseSpace ι) F⁻¹ * PhaseSpace.q i := by
  have h : algebraMap ℝ (PhaseSpace ι) L⁻¹ * algebraMap ℝ (PhaseSpace ι) L = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hL, map_one]
  rw [thinLens, rayMap_paraxialEikonal_p, inv_inv, map_sub]
  linear_combination (PhaseSpace.p i + (algebraMap ℝ (PhaseSpace ι) L⁻¹ -
    algebraMap ℝ (PhaseSpace ι) F⁻¹) * PhaseSpace.q i) * h

end Free

end ProjectAinos.Electrodynamics.Optics.AngularEikonal
