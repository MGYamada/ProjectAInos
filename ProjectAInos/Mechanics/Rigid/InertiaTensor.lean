/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The inertia tensor

For point masses `m a` at positions `r a`, the inertia tensor is
`I = Σₐ mₐ (|rₐ|² 1 − rₐ rₐᵀ)` (Landau–Lifshitz §32). It is symmetric. The
angular momentum of the rotation with angular velocity `Ω` is
`Σₐ mₐ rₐ × (Ω × rₐ) = I Ω`, and twice the kinetic energy is
`Ω · I Ω = Σₐ mₐ |Ω × rₐ|²`, which is non-negative for non-negative masses.

The parallel-axis theorem gives the tensor about a point displaced by `a` from
the centre of mass: `I + μ (|a|² 1 − a aᵀ)` with `μ` the total mass.

The principal moments of inertia are the eigenvalues of `I`, and the principal
axes are an orthonormal basis of eigenvectors, which exists by the spectral
theorem. For non-negative masses the principal moments are non-negative and
each is at most the sum of the other two.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.Rigid

open Matrix

variable {ι : Type*} [Fintype ι]

/-- The inertia tensor `Σₐ mₐ (|rₐ|² δᵢₖ − rₐᵢ rₐₖ)` of point masses. -/
def inertia (m : ι → ℝ) (r : ι → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i k => ∑ a, m a * ((r a ⬝ᵥ r a) * (if i = k then 1 else 0) - r a i * r a k)

theorem inertia_apply (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (i k : Fin 3) :
    inertia m r i k =
      ∑ a, m a * ((r a ⬝ᵥ r a) * (if i = k then 1 else 0) - r a i * r a k) := rfl

/-- The inertia tensor is symmetric. -/
theorem transpose_inertia (m : ι → ℝ) (r : ι → Fin 3 → ℝ) : (inertia m r)ᵀ = inertia m r := by
  ext i k
  rw [Matrix.transpose_apply, inertia_apply, inertia_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm (r a k) (r a i)]
  simp only [eq_comm]

theorem inertia_isHermitian (m : ι → ℝ) (r : ι → Fin 3 → ℝ) : (inertia m r).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, transpose_inertia]

/-- The angular momentum: `(I Ω)ᵢ = Σₐ mₐ (rₐ × (Ω × rₐ))ᵢ` (Landau–Lifshitz §33). -/
theorem inertia_mulVec_apply (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (Ω : Fin 3 → ℝ) (i : Fin 3) :
    (inertia m r *ᵥ Ω) i = ∑ a, m a * (r a ⨯₃ (Ω ⨯₃ r a)) i := by
  simp only [mulVec, dotProduct, inertia_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.sum_univ_three]
  fin_cases i <;> simp [cross_apply] <;> ring

/-- `M = I Ω`: the angular momentum of point masses rotating with angular
velocity `Ω`. -/
theorem inertia_mulVec (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (Ω : Fin 3 → ℝ) :
    inertia m r *ᵥ Ω = ∑ a, m a • (r a ⨯₃ (Ω ⨯₃ r a)) := by
  ext i
  rw [inertia_mulVec_apply, Finset.sum_apply]
  rfl

/-- Twice the kinetic energy: `Ω · I Ω = Σₐ mₐ |Ω × rₐ|²`. -/
theorem dotProduct_inertia_mulVec (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (x : Fin 3 → ℝ) :
    x ⬝ᵥ (inertia m r *ᵥ x) = ∑ a, m a * ((x ⨯₃ r a) ⬝ᵥ (x ⨯₃ r a)) := by
  simp only [dotProduct, inertia_mulVec_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The inertia tensor of non-negative masses is non-negative. -/
theorem dotProduct_inertia_mulVec_nonneg {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a)
    (r : ι → Fin 3 → ℝ) (x : Fin 3 → ℝ) : 0 ≤ x ⬝ᵥ (inertia m r *ᵥ x) := by
  rw [dotProduct_inertia_mulVec]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (hm a) (Finset.sum_nonneg fun i _ => mul_self_nonneg _)

/-- The trace of the inertia tensor is `2 Σₐ mₐ |rₐ|²`. -/
theorem trace_inertia (m : ι → ℝ) (r : ι → Fin 3 → ℝ) :
    (inertia m r).trace = 2 * ∑ a, m a * (r a ⬝ᵥ r a) := by
  simp only [Matrix.trace, Matrix.diag_apply, inertia_apply, Fin.sum_univ_three, ite_true]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [dotProduct, Fin.sum_univ_three]
  ring

/-- For a unit vector `n`, twice the moment of inertia about `n` is at most the
trace. This is the basis-free form of the triangle inequality for the principal
moments. -/
theorem two_mul_dotProduct_inertia_mulVec_le_trace {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a)
    (r : ι → Fin 3 → ℝ) {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) :
    2 * (n ⬝ᵥ (inertia m r *ᵥ n)) ≤ (inertia m r).trace := by
  rw [dotProduct_inertia_mulVec, trace_inertia]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
  refine mul_le_mul_of_nonneg_left ?_ (hm a)
  rw [cross_dot_cross, hn, one_mul]
  have h : 0 ≤ n ⬝ᵥ r a * n ⬝ᵥ r a := mul_self_nonneg _
  rw [dotProduct_comm (r a) n]
  linarith

/-- The parallel-axis theorem (Landau–Lifshitz §32): for a system with centre of
mass at the origin, the inertia tensor of the positions displaced by `a` is
`I + μ (|a|² δᵢₖ − aᵢ aₖ)`, with `μ` the total mass. -/
theorem inertia_add_apply (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (hcm : ∑ b, m b • r b = 0)
    (a : Fin 3 → ℝ) (i k : Fin 3) :
    inertia m (fun b => r b + a) i k =
      inertia m r i k + (∑ b, m b) * ((a ⬝ᵥ a) * (if i = k then 1 else 0) - a i * a k) := by
  have hsum (j : Fin 3) : ∑ b, m b * r b j = 0 := by
    have h := congrFun hcm j
    simpa [Finset.sum_apply] using h
  have hterm (b : ι) :
      m b * (((r b + a) ⬝ᵥ (r b + a)) * (if i = k then 1 else 0) - (r b + a) i * (r b + a) k) =
        m b * ((r b ⬝ᵥ r b) * (if i = k then 1 else 0) - r b i * r b k) +
          m b * ((a ⬝ᵥ a) * (if i = k then 1 else 0) - a i * a k) +
          (2 * (if i = k then 1 else 0) *
              (a 0 * (m b * r b 0) + a 1 * (m b * r b 1) + a 2 * (m b * r b 2)) -
            a k * (m b * r b i) - a i * (m b * r b k)) := by
    simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply]
    ring
  rw [inertia_apply, inertia_apply, Finset.sum_congr rfl fun b _ => hterm b,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hcross : ∑ b, (2 * (if i = k then 1 else 0) *
        (a 0 * (m b * r b 0) + a 1 * (m b * r b 1) + a 2 * (m b * r b 2)) -
      a k * (m b * r b i) - a i * (m b * r b k)) = 0 := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, hsum, mul_zero,
      add_zero, sub_zero]
  rw [hcross, add_zero]

/-- The principal moments of inertia: the eigenvalues of the inertia tensor. -/
def principalMoments (m : ι → ℝ) (r : ι → Fin 3 → ℝ) : Fin 3 → ℝ :=
  (inertia_isHermitian m r).eigenvalues

/-- The principal axes: an orthonormal basis of eigenvectors of the inertia
tensor. -/
def principalAxes (m : ι → ℝ) (r : ι → Fin 3 → ℝ) :
    OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (inertia_isHermitian m r).eigenvectorBasis

/-- The inertia tensor acts on a principal axis by the principal moment. -/
theorem inertia_mulVec_principalAxes (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (c : Fin 3) :
    inertia m r *ᵥ ⇑(principalAxes m r c) = principalMoments m r c • ⇑(principalAxes m r c) :=
  (inertia_isHermitian m r).mulVec_eigenvectorBasis c

/-- The principal axes are unit vectors. -/
theorem dotProduct_principalAxes_self (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (c : Fin 3) :
    ⇑(principalAxes m r c) ⬝ᵥ ⇑(principalAxes m r c) = 1 := by
  have h1 : ‖principalAxes m r c‖ = 1 := (principalAxes m r).orthonormal.1 c
  have h2 := EuclideanSpace.real_norm_sq_eq (principalAxes m r c)
  rw [h1, one_pow] at h2
  rw [dotProduct, h2]
  exact Finset.sum_congr rfl fun i _ => (sq _).symm

/-- A principal moment is the moment of inertia about its principal axis. -/
theorem principalMoments_eq (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (c : Fin 3) :
    principalMoments m r c =
      ⇑(principalAxes m r c) ⬝ᵥ (inertia m r *ᵥ ⇑(principalAxes m r c)) := by
  rw [inertia_mulVec_principalAxes, dotProduct_smul, dotProduct_principalAxes_self, smul_eq_mul,
    mul_one]

/-- The principal moments of non-negative masses are non-negative. -/
theorem principalMoments_nonneg {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a) (r : ι → Fin 3 → ℝ)
    (c : Fin 3) : 0 ≤ principalMoments m r c := by
  rw [principalMoments_eq]
  exact dotProduct_inertia_mulVec_nonneg hm r _

/-- The trace of the inertia tensor is the sum of the principal moments. -/
theorem trace_inertia_eq_sum_principalMoments (m : ι → ℝ) (r : ι → Fin 3 → ℝ) :
    (inertia m r).trace = ∑ c, principalMoments m r c := by
  rw [(inertia_isHermitian m r).trace_eq_sum_eigenvalues]
  rfl

/-- Twice a principal moment is at most the sum of all three. -/
theorem two_mul_principalMoments_le {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a) (r : ι → Fin 3 → ℝ)
    (c : Fin 3) : 2 * principalMoments m r c ≤ ∑ b, principalMoments m r b := by
  rw [← trace_inertia_eq_sum_principalMoments, principalMoments_eq]
  exact two_mul_dotProduct_inertia_mulVec_le_trace hm r (dotProduct_principalAxes_self m r c)

/-- The triangle inequality for the principal moments of inertia
(Landau–Lifshitz §32): `I₂ ≤ I₀ + I₁`, and likewise for the other two. -/
theorem principalMoments_two_le {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a) (r : ι → Fin 3 → ℝ) :
    principalMoments m r 2 ≤ principalMoments m r 0 + principalMoments m r 1 := by
  have h := two_mul_principalMoments_le hm r 2
  rw [Fin.sum_univ_three] at h
  linarith

theorem principalMoments_one_le {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a) (r : ι → Fin 3 → ℝ) :
    principalMoments m r 1 ≤ principalMoments m r 0 + principalMoments m r 2 := by
  have h := two_mul_principalMoments_le hm r 1
  rw [Fin.sum_univ_three] at h
  linarith

theorem principalMoments_zero_le {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a) (r : ι → Fin 3 → ℝ) :
    principalMoments m r 0 ≤ principalMoments m r 1 + principalMoments m r 2 := by
  have h := two_mul_principalMoments_le hm r 0
  rw [Fin.sum_univ_three] at h
  linarith

end ProjectAInos.Mechanics.Rigid
