/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Angular velocity

The Lie algebra `so(3)` of skew-symmetric matrices is identified with `ℝ³`: the
matrix `hat Ω` acts on vectors as `r ↦ Ω × r`, every skew-symmetric matrix is of
this form for a unique `Ω`, and the commutator of matrices corresponds to the
cross product (Landau–Lifshitz §31).

The velocity field of a rigid motion is `r ↦ V + Ω × r`. Changing the origin by
`a` replaces `V` by `V + Ω × a` and leaves `Ω` unchanged, and a rigid velocity
field determines `V` and `Ω`. For a motion `x(t) = c(t) + R(t) r₀` with `R(t)`
orthogonal, `Ṙ Rᵀ` is skew-symmetric, and the velocity of the body point is
`ċ + Ω × (x − c)` with `Ω` the vector of `Ṙ Rᵀ`.
-/

@[expose] public section

namespace ProjectAInos.Mechanics.Rigid

open Matrix

section Algebra

variable {R : Type*} [CommRing R]

/-- The skew-symmetric matrix of a vector: `hat Ω *ᵥ r = Ω × r`. -/
def hat (Ω : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, -Ω 2, Ω 1; Ω 2, 0, -Ω 0; -Ω 1, Ω 0, 0]

/-- The vector of a matrix; on skew-symmetric matrices it inverts `hat`. -/
def vee (A : Matrix (Fin 3) (Fin 3) R) : Fin 3 → R := ![A 2 1, A 0 2, A 1 0]

theorem hat_mulVec (Ω r : Fin 3 → R) : hat Ω *ᵥ r = Ω ⨯₃ r := by
  ext a
  fin_cases a <;> simp [hat, mulVec, dotProduct, Fin.sum_univ_three, cross_apply] <;> ring

/-- `hat Ω` is skew-symmetric. -/
theorem transpose_hat (Ω : Fin 3 → R) : (hat Ω)ᵀ = -hat Ω := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [hat]

theorem vee_hat (Ω : Fin 3 → R) : vee (hat Ω) = Ω := by
  ext a
  fin_cases a <;> simp [vee, hat]

theorem hat_add (Ω Ω' : Fin 3 → R) : hat (Ω + Ω') = hat Ω + hat Ω' := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [hat] <;> ring

theorem hat_smul (c : R) (Ω : Fin 3 → R) : hat (c • Ω) = c • hat Ω := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [hat]

/-- The cross product corresponds to the commutator of matrices. -/
theorem hat_cross (Ω Ω' : Fin 3 → R) :
    hat (Ω ⨯₃ Ω') = hat Ω * hat Ω' - hat Ω' * hat Ω := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [hat, cross_apply] <;> ring

/-- The velocity field `r ↦ V + Ω × r` of a rigid motion. -/
def velocityField (V Ω r : Fin 3 → R) : Fin 3 → R := V + Ω ⨯₃ r

/-- Change of origin: about a point displaced by `a`, the velocity of the origin
becomes `V + Ω × a` and the angular velocity is unchanged. -/
theorem velocityField_add (V Ω a r : Fin 3 → R) :
    velocityField V Ω (r + a) = velocityField (V + Ω ⨯₃ a) Ω r := by
  rw [velocityField, velocityField, map_add]
  abel

/-- A rigid velocity field determines the velocity of the origin and the
angular velocity. -/
theorem velocityField_injective {V V' Ω Ω' : Fin 3 → R}
    (h : ∀ r, velocityField V Ω r = velocityField V' Ω' r) : V = V' ∧ Ω = Ω' := by
  have hV : V = V' := by
    have h0 := h 0
    simpa [velocityField] using h0
  refine ⟨hV, ?_⟩
  have hcross (r : Fin 3 → R) : Ω ⨯₃ r = Ω' ⨯₃ r := by
    have hr := h r
    rw [velocityField, velocityField, hV] at hr
    exact add_left_cancel hr
  have h0 := hcross ![1, 0, 0]
  have h1 := hcross ![0, 1, 0]
  rw [cross_apply, cross_apply] at h0 h1
  ext a
  fin_cases a
  · simpa using congrFun h1 2
  · simpa using congrFun h0 2
  · simpa using congrFun h0 1

/-- The angular velocity does not depend on the origin: if the same velocity
field is described from an origin displaced by `a`, the angular velocity is the
same and the velocity of the origin changes by `Ω × a`. -/
theorem velocityField_change_of_origin {V V' Ω Ω' a : Fin 3 → R}
    (h : ∀ r, velocityField V Ω (r + a) = velocityField V' Ω' r) :
    V' = V + Ω ⨯₃ a ∧ Ω' = Ω := by
  have h' := velocityField_injective fun r => (velocityField_add V Ω a r).symm.trans (h r)
  exact ⟨h'.1.symm, h'.2.symm⟩

end Algebra

section Real

/-- Over the reals, every skew-symmetric matrix is `hat` of its vector. -/
theorem hat_vee {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = -A) : hat (vee A) = A := by
  have h (a b : Fin 3) : A b a = -A a b := by
    have := congrFun (congrFun hA a) b
    simpa using this
  have hd (a : Fin 3) : A a a = 0 := by
    have := h a a
    linarith
  ext a b
  fin_cases a <;> fin_cases b <;> simp [hat, vee, hd]
  · exact (h 1 0).symm
  · exact (h 2 1).symm
  · exact (h 0 2).symm

theorem hat_mem_so (Ω : Fin 3 → ℝ) : hat Ω ∈ LieAlgebra.Orthogonal.so (Fin 3) ℝ :=
  (LieAlgebra.Orthogonal.mem_so _ _ _).mpr (transpose_hat Ω)

/-- `so(3) ≅ ℝ³`: the linear equivalence between vectors and skew-symmetric
matrices. By `hat_cross` it sends the cross product to the commutator. -/
noncomputable def hatEquiv : (Fin 3 → ℝ) ≃ₗ[ℝ] LieAlgebra.Orthogonal.so (Fin 3) ℝ where
  toFun Ω := ⟨hat Ω, hat_mem_so Ω⟩
  map_add' Ω Ω' := Subtype.ext (hat_add Ω Ω')
  map_smul' c Ω := Subtype.ext (hat_smul c Ω)
  invFun A := vee A.1
  left_inv Ω := vee_hat Ω
  right_inv A := Subtype.ext (hat_vee ((LieAlgebra.Orthogonal.mem_so _ _ _).mp A.2))

@[simp] theorem coe_hatEquiv (Ω : Fin 3 → ℝ) :
    ((hatEquiv Ω : LieAlgebra.Orthogonal.so (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = hat Ω :=
  rfl

attribute [local instance] LieRing.ofAssociativeRing in
/-- The identification `so(3) ≅ ℝ³` is an isomorphism of Lie algebras for the
cross product. -/
theorem hatEquiv_cross (Ω Ω' : Fin 3 → ℝ) :
    hatEquiv (Ω ⨯₃ Ω') = ⁅hatEquiv Ω, hatEquiv Ω'⁆ := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, coe_hatEquiv, coe_hatEquiv, coe_hatEquiv, Ring.lie_def,
    hat_cross]

/-- For a differentiable family of orthogonal matrices, `Ṙ Rᵀ` is
skew-symmetric. Derivatives are taken entry by entry. -/
theorem transpose_deriv_mul_transpose {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {R' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t)
    (horth : ∀ s, R s * (R s)ᵀ = 1) : (R' * (R t)ᵀ)ᵀ = -(R' * (R t)ᵀ) := by
  have hentry (a b : Fin 3) : (R' * (R t)ᵀ) a b + (R' * (R t)ᵀ) b a = 0 := by
    have hprod : HasDerivAt (fun s => ∑ k, R s a k * R s b k)
        (∑ k, (R' a k * R t b k + R t a k * R' b k)) t :=
      HasDerivAt.fun_sum fun k _ => (hR a k).mul (hR b k)
    have hconst : (fun s => ∑ k, R s a k * R s b k) =
        fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b := by
      funext s
      have h := congrFun (congrFun (horth s) a) b
      rw [Matrix.mul_apply] at h
      simpa [Matrix.transpose_apply] using h
    rw [hconst] at hprod
    have hzero := hprod.unique (hasDerivAt_const t _)
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    rw [← hzero]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Matrix.transpose_apply, Matrix.transpose_apply]
      ring
  ext a b
  rw [Matrix.transpose_apply, Matrix.neg_apply]
  linarith [hentry a b]

/-- The angular velocity of a differentiable family of orthogonal matrices:
the vector of the skew-symmetric matrix `Ṙ Rᵀ`. -/
def angularVelocity (R R' : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ := vee (R' * Rᵀ)

/-- The velocity of a point of a rigid body. For the motion
`x(s) = c(s) + R(s) r₀` with `R(s)` orthogonal, the velocity at time `t` is
`ċ + Ω × (x − c)`, where `Ω` is the angular velocity (Landau–Lifshitz §31). -/
theorem hasDerivAt_rigidMotion {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {R' : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ → Fin 3 → ℝ} {c' : Fin 3 → ℝ} {t : ℝ}
    (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t)
    (horth : ∀ s, R s * (R s)ᵀ = 1) (hc : ∀ a, HasDerivAt (fun s => c s a) (c' a) t)
    (r₀ : Fin 3 → ℝ) (a : Fin 3) :
    HasDerivAt (fun s => (c s + R s *ᵥ r₀) a)
      (velocityField c' (angularVelocity (R t) R') (R t *ᵥ r₀) a) t := by
  have hmul : HasDerivAt (fun s => (R s *ᵥ r₀) a) ((R' *ᵥ r₀) a) t := by
    have h : HasDerivAt (fun s => ∑ b, R s a b * r₀ b) (∑ b, R' a b * r₀ b) t :=
      HasDerivAt.fun_sum fun b _ => (hR a b).mul_const (r₀ b)
    exact h
  have horth' : (R t)ᵀ * R t = 1 := mul_eq_one_comm.mp (horth t)
  have hvel : R' *ᵥ r₀ = angularVelocity (R t) R' ⨯₃ (R t *ᵥ r₀) := by
    rw [angularVelocity, ← hat_mulVec, hat_vee (transpose_deriv_mul_transpose hR horth),
      Matrix.mulVec_mulVec, Matrix.mul_assoc, horth', Matrix.mul_one]
  rw [hvel] at hmul
  have hsum : HasDerivAt (fun s => c s a + (R s *ᵥ r₀) a)
      (c' a + (angularVelocity (R t) R' ⨯₃ (R t *ᵥ r₀)) a) t := (hc a).fun_add hmul
  exact hsum

end Real

end ProjectAInos.Mechanics.Rigid
