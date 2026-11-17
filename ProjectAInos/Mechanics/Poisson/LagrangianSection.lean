/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.JointFlowSymplectic

/-!
# The Lagrangian transversal spanned by the gradients

For integrals `Fᵢ` in involution and a point `x`, the gradients `∇Fₖ(x)` span a
subspace on which the symplectic form vanishes, and it is transversal to the
level set of `F` through `x` where the differentials are linearly independent.

* `gradientMap F x a = Σₖ aₖ ∇Fₖ(x)`.
* `symplecticForm_gradientMap`: `ω(L a, L a′) = 0`.
* `exists_gram_equiv`: `DF(x) ∘ L` is invertible.
-/

@[expose] public section
noncomputable section

open Set Module
open scoped ContDiff

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The value of the canonical bracket at a point. -/
theorem canonical_bracket_val (G H : PhaseSpace ι) (z : ι ⊕ ι → ℝ) :
    ((PhaseSpace.canonical ι).bracket G H).val z =
      ∑ i, ((partialDerivation (Sum.inl i) G).val z * (partialDerivation (Sum.inr i) H).val z -
        (partialDerivation (Sum.inr i) G).val z * (partialDerivation (Sum.inl i) H).val z) := by
  rw [PhaseSpace.canonical_bracket, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rfl

/-- The gradient of `F k` at `x`: the vector of its partial derivatives. -/
def gradient (F : ι → PhaseSpace ι) (x : ι ⊕ ι → ℝ) (k : ι) : ι ⊕ ι → ℝ :=
  fun a => (partialDerivation a (F k)).val x

/-- The linear map `a ↦ Σₖ aₖ ∇Fₖ(x)`. -/
def gradientMap (F : ι → PhaseSpace ι) (x : ι ⊕ ι → ℝ) : (ι → ℝ) →L[ℝ] (ι ⊕ ι → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => ∑ k, a k • gradient F x k
      map_add' := fun a b => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }

theorem gradientMap_apply (F : ι → PhaseSpace ι) (x : ι ⊕ ι → ℝ) (a : ι → ℝ) :
    gradientMap F x a = ∑ k, a k • gradient F x k := rfl

theorem gradientMap_apply_apply (F : ι → PhaseSpace ι) (x : ι ⊕ ι → ℝ) (a : ι → ℝ)
    (b : ι ⊕ ι) : gradientMap F x a b = ∑ k, a k * gradient F x k b := by
  rw [gradientMap_apply, Finset.sum_apply]
  rfl

theorem fderiv_val_eq_sum_gradient (F : ι → PhaseSpace ι) (x w : ι ⊕ ι → ℝ) (j : ι) :
    fderiv ℝ ((F j).val : (ι ⊕ ι → ℝ) → ℝ) x w = ∑ b, gradient F x j b * w b :=
  fderiv_val_apply _ _ _

theorem symplecticForm_gradient {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (x : ι ⊕ ι → ℝ) (j k : ι) :
    symplecticForm ι (gradient F x j) (gradient F x k) = 0 := by
  have h := canonical_bracket_val (F j) (F k) x
  rw [hF j k] at h
  rw [symplecticForm_apply]
  exact h.symm

/-- The symplectic form vanishes on the span of the gradients. -/
theorem symplecticForm_gradientMap {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (x : ι ⊕ ι → ℝ)
    (a a' : ι → ℝ) : symplecticForm ι (gradientMap F x a) (gradientMap F x a') = 0 := by
  rw [gradientMap_apply F x a', map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, symplecticForm_swap, gradientMap_apply, map_sum]
  have h0 : ∑ j, symplecticForm ι (gradient F x k) (a j • gradient F x j) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [map_smul, symplecticForm_gradient hF, smul_zero]
  rw [h0, neg_zero, smul_zero]

/-- Where the differentials are linearly independent, the derivative of the
integrals is invertible on the span of the gradients. -/
theorem exists_gram_equiv {F : ι → PhaseSpace ι} {x : ι ⊕ ι → ℝ}
    (hind : LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) x) :
    ∃ N : (ι → ℝ) ≃L[ℝ] (ι → ℝ),
      ∀ a, fderiv ℝ (integralMap F) x (gradientMap F x a) = N a := by
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ),
      ∀ a, N₀ a = fderiv ℝ (integralMap F) x (gradientMap F x a) :=
    ⟨(fderiv ℝ (integralMap F) x : (ι ⊕ ι → ℝ) →ₗ[ℝ] ι → ℝ) ∘ₗ
      (gradientMap F x : (ι → ℝ) →ₗ[ℝ] ι ⊕ ι → ℝ), fun a => rfl⟩
  have hinj : Function.Injective N₀ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hsq : ∑ b, gradientMap F x a b * gradientMap F x a b = ∑ j, a j * N₀ a j := by
      simp only [hN₀, fderiv_integralMap_apply, fderiv_val_eq_sum_gradient, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [gradientMap_apply_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [ha] at hsq
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hsq
    have hL0 : ∀ b, gradientMap F x a b = 0 := fun b => by
      have h := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => mul_self_nonneg _).mp hsq b
        (Finset.mem_univ b)
      exact mul_self_eq_zero.mp h
    have hcov : ∑ k, a k • fderiv ℝ ((F k).val : (ι ⊕ ι → ℝ) → ℝ) x = 0 := by
      refine ContinuousLinearMap.ext fun w => ?_
      have hw : (∑ k, a k • fderiv ℝ ((F k).val : (ι ⊕ ι → ℝ) → ℝ) x) w =
          ∑ k, a k * fderiv ℝ ((F k).val : (ι ⊕ ι → ℝ) → ℝ) x w := by
        change ContinuousLinearMap.apply ℝ ℝ w
          (∑ k, a k • fderiv ℝ ((F k).val : (ι ⊕ ι → ℝ) → ℝ) x) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul]
        rfl
      rw [hw]
      simp only [fderiv_val_eq_sum_gradient, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun b _ => ?_
      have e : ∑ k, a k * (gradient F x k b * w b) = gradientMap F x a b * w b := by
        rw [gradientMap_apply_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e, hL0 b, zero_mul]
    exact funext fun k => Fintype.linearIndependent_iff.mp hind a hcov k
  refine ⟨(LinearEquiv.ofInjectiveEndo N₀ hinj).toContinuousLinearEquiv, fun a => ?_⟩
  rw [← hN₀ a]
  rfl

end ProjectAInos.Mechanics
