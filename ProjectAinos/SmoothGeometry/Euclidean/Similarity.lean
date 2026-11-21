/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Maps that multiply all lengths by the same factor

Let `E` be a finite-dimensional real inner product space. A twice continuously differentiable
map `φ` whose derivative multiplies every length by the same factor `k = n/n′ > 0` on a connected
open set, `n′ |Dφ(x) v| = n |v|`, is a similarity there (Carathéodory's theorem on absolute
instruments, Landau–Lifshitz, *The Classical Theory of Fields*, §57).

* `inner_map_map_of_norm`: a linear map that multiplies the lengths by `k` multiplies the inner
  products by `k²`.
* `eq_zero_of_symm_of_antisymm`: a trilinear expression that is symmetric in its first two
  arguments and antisymmetric in its last two vanishes.
* `fderiv_fderiv_eq_zero_of_norm`: the second derivative of such a map vanishes, since
  `⟨D²φ(w, u), Dφ v⟩` is symmetric in `w, u` and antisymmetric in `u, v`, and `Dφ` is onto.
* `exists_linearIsometryEquiv_of_norm_fderiv`: `φ(x) = (n/n′) L x + c` on the set, with a linear
  isometry `L`.
* `norm_fderiv_reflection`, `contDiff_reflection`: a reflection (a plane mirror) satisfies the
  hypotheses with `n = n′`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology RealInnerProductSpace

namespace ProjectAinos.SmoothGeometry.Similarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A linear map that multiplies every length by `k` multiplies every inner product by `k²`. -/
theorem inner_map_map_of_norm {A : E →L[ℝ] E} {k : ℝ} (hA : ∀ v, ‖A v‖ = k * ‖v‖) (u v : E) :
    ⟪A u, A v⟫ = k ^ 2 * ⟪u, v⟫ := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two u v,
    ← map_add, hA, hA, hA]
  ring

/-- A trilinear expression that is symmetric in its first two arguments and antisymmetric in its
last two vanishes. -/
theorem eq_zero_of_symm_of_antisymm {F : Type*} (T : F → F → F → ℝ)
    (hs : ∀ a b c, T a b c = T b a c) (ha : ∀ a b c, T a b c = -T a c b) (a b c : F) :
    T a b c = 0 := by
  have h1 := ha a b c
  have h2 := hs a c b
  have h3 := ha c a b
  have h4 := hs c b a
  have h5 := ha b c a
  have h6 := hs b a c
  linarith

/-- A reflection in a subspace `K` (a plane mirror) multiplies no length:
`n |Dφ(x) v| = n |v|`. It satisfies the hypothesis of
`exists_linearIsometryEquiv_of_norm_fderiv` with `n = n′`. -/
theorem norm_fderiv_reflection (K : Submodule ℝ E) [K.HasOrthogonalProjection] (n : ℝ)
    (x v : E) : n * ‖fderiv ℝ K.reflection x v‖ = n * ‖v‖ := by
  have h : fderiv ℝ (⇑K.reflection) x =
      ((K.reflection.toContinuousLinearEquiv : E ≃L[ℝ] E) : E →L[ℝ] E) :=
    ContinuousLinearMap.fderiv (x := x)
      ((K.reflection.toContinuousLinearEquiv : E ≃L[ℝ] E) : E →L[ℝ] E)
  rw [h]
  simp

/-- The reflection is twice continuously differentiable. -/
theorem contDiff_reflection (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    ContDiff ℝ 2 K.reflection :=
  K.reflection.toContinuousLinearEquiv.contDiff

variable [FiniteDimensional ℝ E]

/-- If the derivative of a twice differentiable map multiplies every length by the same factor
`k > 0` on a neighbourhood of `x`, the second derivative vanishes at `x`. -/
theorem fderiv_fderiv_eq_zero_of_norm {φ : E → E} {x : E} {k : ℝ} (hk : 0 < k)
    (hφ : ContDiffAt ℝ 2 φ x)
    (hA : ∀ᶠ y in 𝓝 x, ∀ v, ‖fderiv ℝ φ y v‖ = k * ‖v‖) :
    fderiv ℝ (fderiv ℝ φ) x = 0 := by
  set B := fderiv ℝ (fderiv ℝ φ) x with hB
  have hD : HasFDerivAt (fderiv ℝ φ) B x :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  -- differentiate `⟪Dφ u, Dφ v⟫ = k² ⟪u, v⟫`
  have hvar : ∀ w u v, ⟪B w u, fderiv ℝ φ x v⟫ + ⟪fderiv ℝ φ x u, B w v⟫ = 0 := by
    intro w u v
    have hu : HasFDerivAt (fun y => fderiv ℝ φ y u) (B.flip u) x := by
      simpa using hD.clm_apply (hasFDerivAt_const u x)
    have hv : HasFDerivAt (fun y => fderiv ℝ φ y v) (B.flip v) x := by
      simpa using hD.clm_apply (hasFDerivAt_const v x)
    have h1 := hu.inner (𝕜 := ℝ) hv
    have h2 : HasFDerivAt (fun y => ⟪fderiv ℝ φ y u, fderiv ℝ φ y v⟫) (0 : E →L[ℝ] ℝ) x := by
      refine (hasFDerivAt_const (k ^ 2 * ⟪u, v⟫) x).congr_of_eventuallyEq ?_
      filter_upwards [hA] with y hy
      exact inner_map_map_of_norm hy u v
    have h3 := congrArg (fun L : E →L[ℝ] ℝ => L w) (h1.unique h2)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, ContinuousLinearMap.flip_apply, zero_apply] at h3
    linarith
  have hsymm := hφ.isSymmSndFDerivAt (by simp)
  have hT : ∀ w u v, ⟪B w u, fderiv ℝ φ x v⟫ = 0 := by
    refine eq_zero_of_symm_of_antisymm (fun w u v => ⟪B w u, fderiv ℝ φ x v⟫) ?_ ?_
    · intro a b c
      simp only [hB, hsymm a b]
    · intro a b c
      have h1 := hvar a c b
      have h2 := real_inner_comm (fderiv ℝ φ x c) (B a b)
      linarith
  -- `Dφ(x)` is onto, since it is injective
  have hinj : Function.Injective (fderiv ℝ φ x : E →ₗ[ℝ] E) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h := hA.self_of_nhds v
    simp only [ContinuousLinearMap.coe_coe] at hv
    rw [hv, norm_zero] at h
    have : ‖v‖ = 0 := by
      rcases mul_eq_zero.mp h.symm with h | h
      · exact absurd h hk.ne'
      · exact h
    exact norm_eq_zero.mp this
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  ext w u
  obtain ⟨v, hv⟩ := hsurj (B w u)
  have h := hT w u v
  simp only [ContinuousLinearMap.coe_coe] at hv
  rw [hv, real_inner_self_eq_norm_sq] at h
  simpa using h

/-- **Carathéodory's theorem.** A twice continuously differentiable map whose derivative
multiplies every length by `n/n′` on a connected open set, `n′ |Dφ(x) v| = n |v|`, is a similarity
of ratio `n/n′` there: `φ(x) = (n/n′) L x + c` with a linear isometry `L`. -/
theorem exists_linearIsometryEquiv_of_norm_fderiv {n n' : ℝ} (hn : 0 < n) (hn' : 0 < n')
    {φ : E → E} {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hφ : ContDiffOn ℝ 2 φ Ω)
    (hiso : ∀ x ∈ Ω, ∀ v, n' * ‖fderiv ℝ φ x v‖ = n * ‖v‖) :
    ∃ (L : E ≃ₗᵢ[ℝ] E) (c : E), ∀ x ∈ Ω, φ x = (n / n') • L x + c := by
  set k := n / n' with hk_def
  have hk : 0 < k := div_pos hn hn'
  have hA : ∀ x ∈ Ω, ∀ v, ‖fderiv ℝ φ x v‖ = k * ‖v‖ := by
    intro x hx v
    rw [hk_def, div_mul_eq_mul_div, eq_div_iff hn'.ne', mul_comm, hiso x hx v]
  have hB : ∀ x ∈ Ω, fderiv ℝ (fderiv ℝ φ) x = 0 := fun x hx =>
    fderiv_fderiv_eq_zero_of_norm hk (hφ.contDiffAt (hΩ.mem_nhds hx))
      (Filter.eventually_of_mem (hΩ.mem_nhds hx) hA)
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨LinearIsometryEquiv.refl ℝ E, 0, by simp⟩
  have hDφ : DifferentiableOn ℝ (fderiv ℝ φ) Ω :=
    (hφ.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).differentiableOn one_ne_zero
  have hconst : ∀ x ∈ Ω, fderiv ℝ φ x = fderiv ℝ φ x₀ := fun x hx =>
    hΩ.is_const_of_fderiv_eq_zero hΩc hDφ (fun y hy => hB y hy) hx hx₀
  set A := fderiv ℝ φ x₀ with hA_def
  obtain ⟨c, hc⟩ := hΩ.exists_eq_add_of_fderiv_eq hΩc (hφ.differentiableOn (by norm_num))
    A.differentiableOn (fun x hx => by simp only [hconst x hx, A.fderiv])
  have hA₀ : ∀ v, ‖A v‖ = k * ‖v‖ := hA x₀ hx₀
  let L₀ : E →ₗᵢ[ℝ] E :=
    { toLinearMap := ((k⁻¹ • A : E →L[ℝ] E) : E →ₗ[ℝ] E)
      norm_map' := fun v => by
        simp only [ContinuousLinearMap.coe_coe, FunLike.coe_smul, Pi.smul_apply,
          norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk, hA₀ v]
        field_simp }
  refine ⟨L₀.toLinearIsometryEquiv rfl, c, fun x hx => ?_⟩
  rw [hc hx]
  simp [L₀, smul_smul, hk.ne']

end ProjectAinos.SmoothGeometry.Similarity
