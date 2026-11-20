/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# The Laplacian in Euclidean co-ordinates

Space is the Euclidean space `EuclideanSpace ℝ (Fin n)`, with its norm `‖x‖ = √(Σ xᵢ²)` and its
Lebesgue measure `volume`. `coordLaplacian f x = Σᵢ ∂ᵢ∂ᵢ f(x)` is the Laplacian in the
co-ordinates, written with iterated derivatives along the unit vectors `EuclideanSpace.single i 1`.

* `coordLaplacian_eq_laplacian`: for a function that is `C²` at `x` it is Mathlib's
  Laplacian `Δ f x`, computed in the orthonormal basis `EuclideanSpace.basisFun`.
* `coordLaplacian_comp_normSq`: the Laplacian of a radial function `g(‖x‖²)` is
  `2n g'(‖x‖²) + 4‖x‖² g''(‖x‖²)`.
* `coordLaplacian_comp_sub`, `coordLaplacian_comp_add_left`: translations commute with the
  Laplacian; `coordLaplacian_normSq_sub`: `Δ ‖x − c‖² = 2n`.
* `integral_mul_coordLaplacian`: Green's identity `∫ f Δg = ∫ (Δf) g` on all of space, for `C²`
  functions of which `g` has a compact support.
* `integral_mul_coordLaplacian_eq_neg_sum`: Green's first identity `∫ w Δφ = −∫ Σᵢ ∂ᵢw ∂ᵢφ` for
  a `C²` function `φ` and a `C¹` function `w` of compact support.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Laplacian ContDiff

namespace ProjectAinos.SmoothGeometry.Potential

variable {n : ℕ}

/-- The Laplacian `Σᵢ ∂ᵢ∂ᵢ f` in the co-ordinates of `EuclideanSpace ℝ (Fin n)`. -/
def coordLaplacian (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single i 1)

/-- For a function that is `C²` at `x`, the derivative along `v` of the derivative along `w` is
the second derivative on `(v, w)`. -/
theorem fderiv_fderiv_apply {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f x) (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- For a function that is `C²` at `x`, the Laplacian in the co-ordinates is Mathlib's
Laplacian. -/
theorem coordLaplacian_eq_laplacian {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x) :
    coordLaplacian f x = Δ f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [coordLaplacian, iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_fderiv_apply hf]
  simp

/-- A function that is `C²` on all of space has the Laplacian `coordLaplacian f`. -/
theorem laplacian_eq_coordLaplacian {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) :
    Δ f = coordLaplacian f := by
  funext x
  exact (coordLaplacian_eq_laplacian hf.contDiffAt).symm

/-- The Laplacian of a `C²` function is continuous. -/
theorem continuous_coordLaplacian {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (coordLaplacian f) := by
  show Continuous fun x => ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single i 1)
  refine continuous_finsetSum _ fun i _ => ?_
  exact (((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
    (by norm_num)).clm_apply continuous_const

/-- The Laplacian vanishes outside the closed support. -/
theorem coordLaplacian_eq_zero_of_notMem_tsupport {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ tsupport f) : coordLaplacian f x = 0 := by
  have hf : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have h1 (v : EuclideanSpace ℝ (Fin n)) : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hf.eventuallyEq_nhds] with y hy
    rw [hy.fderiv_eq]
    simp
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [(h1 _).fderiv_eq]
  simp

/-- The Laplacian of a function of compact support has a compact support. -/
theorem hasCompactSupport_coordLaplacian {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (coordLaplacian f) :=
  hf.mono' fun _ hx => by_contra fun h => hx (coordLaplacian_eq_zero_of_notMem_tsupport h)

/-! ### Radial functions -/

/-- The derivative of a radial function `g(‖y‖²)` along `v` is `2 g'(‖y‖²) ⟨v, y⟩`. -/
theorem hasFDerivAt_comp_normSq {g : ℝ → ℝ} {g' : ℝ} {y : EuclideanSpace ℝ (Fin n)}
    (hg : HasDerivAt g g' (‖y‖ ^ 2)) :
    HasFDerivAt (fun z => g (‖z‖ ^ 2)) ((2 * g') • innerSL ℝ y) y := by
  refine (hg.comp_hasFDerivAt y (hasStrictFDerivAt_norm_sq y).hasFDerivAt).congr_fderiv ?_
  ext v
  simp
  ring

/-- The Laplacian of a radial function `g(‖x‖²)` is `2n g'(‖x‖²) + 4‖x‖² g''(‖x‖²)`. -/
theorem coordLaplacian_comp_normSq {g g' : ℝ → ℝ} {g'' : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hg : ∀ᶠ s in 𝓝 (‖x‖ ^ 2), HasDerivAt g (g' s) s) (hg' : HasDerivAt g' g'' (‖x‖ ^ 2)) :
    coordLaplacian (fun y => g (‖y‖ ^ 2)) x = 2 * n * g' (‖x‖ ^ 2) + 4 * ‖x‖ ^ 2 * g'' := by
  have hc : ContinuousAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x := by fun_prop
  have hev : ∀ᶠ y in 𝓝 x, HasDerivAt g (g' (‖y‖ ^ 2)) (‖y‖ ^ 2) := hc.eventually hg
  have hi (v : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => g (‖z‖ ^ 2)) y v) x v =
        2 * g' (‖x‖ ^ 2) * inner ℝ v v + 4 * g'' * inner ℝ x v ^ 2 := by
    have heq : (fun y => fderiv ℝ (fun z => g (‖z‖ ^ 2)) y v) =ᶠ[𝓝 x]
        fun y => 2 * g' (‖y‖ ^ 2) * innerSL ℝ v y := by
      filter_upwards [hev] with y hy
      rw [(hasFDerivAt_comp_normSq hy).fderiv]
      simp [real_inner_comm]
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => 2 * g' (‖y‖ ^ 2))
        ((2 : ℝ) • ((2 * g'') • innerSL ℝ x)) x :=
      (hasFDerivAt_comp_normSq hg').const_mul 2
    have h2 : HasFDerivAt (fun y => 2 * g' (‖y‖ ^ 2) * innerSL ℝ v y) _ x :=
      h1.mul (innerSL ℝ v).hasFDerivAt
    rw [heq.fderiv_eq, h2.fderiv]
    simp [smul_eq_mul, real_inner_comm]
    ring
  have hs : ∑ i : Fin n, inner ℝ x (EuclideanSpace.single i (1 : ℝ)) ^ 2 = ‖x‖ ^ 2 := by
    simpa [EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_left x
  have h1 (i : Fin n) : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
    simp
  simp only [coordLaplacian, hi, real_inner_self_eq_norm_sq, h1, Finset.sum_add_distrib,
    ← Finset.mul_sum, hs]
  simp
  ring

/-! ### Translations -/

/-- The Laplacian commutes with the translation `y ↦ y − a`. -/
theorem coordLaplacian_comp_sub (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (a x : EuclideanSpace ℝ (Fin n)) :
    coordLaplacian (fun y => f (y - a)) x = coordLaplacian f (x - a) := by
  unfold coordLaplacian
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (fun y => fderiv ℝ (fun y => f (y - a)) y (EuclideanSpace.single i 1)) =
      fun y => fderiv ℝ f (y - a) (EuclideanSpace.single i 1) := by
    funext y
    rw [fderiv_comp_sub (𝕜 := ℝ) (f := f) a]
  rw [h, fderiv_comp_sub (𝕜 := ℝ) (f := fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) a]

/-- The Laplacian commutes with the translation `y ↦ a + y`. -/
theorem coordLaplacian_comp_add_left (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (a x : EuclideanSpace ℝ (Fin n)) :
    coordLaplacian (fun y => f (a + y)) x = coordLaplacian f (a + x) := by
  unfold coordLaplacian
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (fun y => fderiv ℝ (fun y => f (a + y)) y (EuclideanSpace.single i 1)) =
      fun y => fderiv ℝ f (a + y) (EuclideanSpace.single i 1) := by
    funext y
    rw [fderiv_comp_add_left (𝕜 := ℝ) (f := f) a]
  rw [h, fderiv_comp_add_left (𝕜 := ℝ)
    (f := fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) a]

/-- The Laplacian of `‖x − c‖²` is `2n`. -/
theorem coordLaplacian_normSq_sub (c x : EuclideanSpace ℝ (Fin n)) :
    coordLaplacian (fun y => ‖y - c‖ ^ 2) x = 2 * n := by
  rw [coordLaplacian_comp_sub (fun y => ‖y‖ ^ 2) c x,
    coordLaplacian_comp_normSq (g := fun s => s) (g' := fun _ => 1) (g'' := 0)
      (Eventually.of_forall fun s => hasDerivAt_id' s) (hasDerivAt_const _ _)]
  ring

/-! ### Green's identity -/

/-- Integration by parts twice along `v`: `∫ f ∂ᵥ∂ᵥg = ∫ (∂ᵥ∂ᵥf) g` for `C²` functions, of
which `g` has a compact support. -/
theorem integral_mul_fderiv_fderiv {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, f x * fderiv ℝ (fun y => fderiv ℝ g y v) x v =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x v * g x := by
  set G : EuclideanSpace ℝ (Fin n) → ℝ := fun y => fderiv ℝ g y v with hG
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun y => fderiv ℝ f y v with hF
  have hG1 : ContDiff ℝ 1 G :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hF1 : ContDiff ℝ 1 F :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hcG : HasCompactSupport G := hcg.fderiv_apply (𝕜 := ℝ) v
  have hcG' : HasCompactSupport (fun y => fderiv ℝ G y v) := hcG.fderiv_apply (𝕜 := ℝ) v
  have hcg' : HasCompactSupport (fun y => fderiv ℝ g y v) := hcg.fderiv_apply (𝕜 := ℝ) v
  have hfc : Continuous f := hf.continuous
  have hFc : Continuous F := hF1.continuous
  have hf'c : Continuous fun y => fderiv ℝ f y v :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hGc : Continuous G := hG1.continuous
  have hG'c : Continuous fun y => fderiv ℝ G y v :=
    (hG1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hF'c : Continuous fun y => fderiv ℝ F y v :=
    (hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have step1 : ∫ x, f x * fderiv ℝ G x v = -∫ x, fderiv ℝ f x v * G x := by
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
      (fun x _ => (hf.differentiable (by norm_num)).differentiableAt)
      (fun x _ => (hG1.differentiable (by norm_num)).differentiableAt)
    · exact (hf'c.mul hGc).integrable_of_hasCompactSupport hcG.mul_left
    · exact (hfc.mul hG'c).integrable_of_hasCompactSupport hcG'.mul_left
    · exact (hfc.mul hGc).integrable_of_hasCompactSupport hcG.mul_left
  have step2 : ∫ x, F x * fderiv ℝ g x v = -∫ x, fderiv ℝ F x v * g x := by
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
      (fun x _ => (hF1.differentiable (by norm_num)).differentiableAt)
      (fun x _ => (hg.differentiable (by norm_num)).differentiableAt)
    · exact (hF'c.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left
    · exact (hFc.mul hGc).integrable_of_hasCompactSupport hcg'.mul_left
    · exact (hFc.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left
  change ∫ x, f x * fderiv ℝ G x v = ∫ x, fderiv ℝ F x v * g x
  rw [step1]
  change -∫ x, F x * fderiv ℝ g x v = _
  rw [step2, neg_neg]

/-- Green's identity on all of space: `∫ f Δg = ∫ (Δf) g` for `C²` functions, of which `g` has
a compact support. -/
theorem integral_mul_coordLaplacian {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    ∫ x, f x * coordLaplacian g x = ∫ x, coordLaplacian f x * g x := by
  have hd (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ 2 h)
      (v : EuclideanSpace ℝ (Fin n)) : Continuous fun x => fderiv ℝ (fun y => fderiv ℝ h y v) x v :=
    (((hh.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      (by norm_num)).clm_apply continuous_const
  simp only [coordLaplacian, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum, integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ =>
      integral_mul_fderiv_fderiv hf hg hcg (EuclideanSpace.single i 1)
  · intro i _
    exact ((hd f hf _).mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left
  · intro i _
    have hc : HasCompactSupport fun x =>
        fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) :=
      (hcg.fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _
    exact (hf.continuous.mul (hd g hg _)).integrable_of_hasCompactSupport hc.mul_left

/-- **Green's first identity** on all of space: `∫ w Δφ = −∫ Σᵢ ∂ᵢw ∂ᵢφ` for a `C²` function `φ`
and a `C¹` function `w` of compact support. -/
theorem integral_mul_coordLaplacian_eq_neg_sum {w φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hw : ContDiff ℝ 1 w) (hcw : HasCompactSupport w) (hφ : ContDiff ℝ 2 φ) :
    ∫ x, w x * coordLaplacian φ x = -∫ x, ∑ i, fderiv ℝ w x (EuclideanSpace.single i 1) *
      fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  have hφ1 (v : EuclideanSpace ℝ (Fin n)) : ContDiff ℝ 1 fun y => fderiv ℝ φ y v :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hw' (v : EuclideanSpace ℝ (Fin n)) : Continuous fun x => fderiv ℝ w x v :=
    (hw.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hφ' (v : EuclideanSpace ℝ (Fin n)) :
      Continuous fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x v :=
    ((hφ1 v).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hstep (v : EuclideanSpace ℝ (Fin n)) :
      ∫ x, w x * fderiv ℝ (fun y => fderiv ℝ φ y v) x v =
        -∫ x, fderiv ℝ w x v * fderiv ℝ φ x v := by
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
      (fun x _ => (hw.differentiable (by norm_num)).differentiableAt)
      (fun x _ => ((hφ1 v).differentiable (by norm_num)).differentiableAt)
    · exact ((hw' v).mul (hφ1 v).continuous).integrable_of_hasCompactSupport
        (hcw.fderiv_apply (𝕜 := ℝ) v).mul_right
    · exact (hw.continuous.mul (hφ' v)).integrable_of_hasCompactSupport hcw.mul_right
    · exact (hw.continuous.mul (hφ1 v).continuous).integrable_of_hasCompactSupport hcw.mul_right
  simp only [coordLaplacian, Finset.mul_sum]
  rw [integral_finsetSum, integral_finsetSum, ← Finset.sum_neg_distrib]
  · exact Finset.sum_congr rfl fun i _ => hstep _
  · intro i _
    exact ((hw' _).mul (hφ1 _).continuous).integrable_of_hasCompactSupport
      (hcw.fderiv_apply (𝕜 := ℝ) _).mul_right
  · intro i _
    exact (hw.continuous.mul (hφ' _)).integrable_of_hasCompactSupport hcw.mul_right

end ProjectAinos.SmoothGeometry.Potential
