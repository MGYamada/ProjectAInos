/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Poisson.Canonical
public import ProjectAInos.SmoothAlgebra.FreeChainRule
public import Mathlib.Data.Matrix.Block
public import Mathlib.Algebra.Lie.Classical
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Homogeneous and quadratic Hamiltonians

The Euler vector field `E = Σₐ xₐ ∂ₐ` of a free C-infinity ring measures the
degree of homogeneity: `f` is homogeneous of degree `k` in the sense of Euler
when `E f = k f`. For the canonical bracket, the bracket of elements of
degrees `j` and `k` has the degree `j + k − 2` (Proposition 70 of the
manuscript, first statement).

The quadratic forms `Q_S = ½ Σ Sₐ_b xₐ x_b` of phase space are closed under
the canonical bracket, `{Q_S, Q_T} = Q_{SJT − TJS}`, and `S ↦ J S` identifies
them with the Lie algebra `sp(2n, ℝ)`: with `H_A = Q_{−JA}`,

* `{xₐ, H_A} = Σ_c Aₐ_c x_c`, so the Hamiltonian vector field is linear;
* `{H_A, H_B} = H_{[A, B]}`, and `A ↦ H_A` is injective on `sp(2n, ℝ)`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open SmoothRing FreeSmoothRing
open scoped Matrix

section Euler

variable {κ : Type*}

/-- The Euler vector field `Σₐ xₐ ∂ₐ` of a free C-infinity ring. -/
def eulerField : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ) :=
  FreeSmoothRing.derivation fun a => generator a

@[simp] theorem eulerField_generator (a : κ) : eulerField (generator a) = generator a :=
  derivation_generator _ a

/-- `f` is homogeneous of degree `k` in the sense of Euler: `Σₐ xₐ ∂ₐ f = k f`. -/
def IsEulerHomogeneous (k : ℝ) (f : FreeSmoothRing κ) : Prop :=
  eulerField f = algebraMap ℝ (FreeSmoothRing κ) k * f

/-- A generator has the degree one. -/
theorem isEulerHomogeneous_generator (a : κ) : IsEulerHomogeneous 1 (generator a) := by
  rw [IsEulerHomogeneous, eulerField_generator, map_one, one_mul]

/-- A constant has the degree zero. -/
theorem isEulerHomogeneous_algebraMap (r : ℝ) :
    IsEulerHomogeneous 0 (algebraMap ℝ (FreeSmoothRing κ) r) := by
  rw [IsEulerHomogeneous, SmoothDerivation.map_algebraMap, map_zero, zero_mul]

theorem IsEulerHomogeneous.add {k : ℝ} {f g : FreeSmoothRing κ} (hf : IsEulerHomogeneous k f)
    (hg : IsEulerHomogeneous k g) : IsEulerHomogeneous k (f + g) := by
  unfold IsEulerHomogeneous at hf hg ⊢
  rw [map_add, hf, hg, mul_add]

theorem IsEulerHomogeneous.sum {k : ℝ} {α : Type*} (s : Finset α) {f : α → FreeSmoothRing κ}
    (h : ∀ i ∈ s, IsEulerHomogeneous k (f i)) : IsEulerHomogeneous k (∑ i ∈ s, f i) := by
  unfold IsEulerHomogeneous at h ⊢
  rw [map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl h

/-- The degrees add under multiplication. -/
theorem IsEulerHomogeneous.mul {j k : ℝ} {f g : FreeSmoothRing κ} (hf : IsEulerHomogeneous j f)
    (hg : IsEulerHomogeneous k g) : IsEulerHomogeneous (j + k) (f * g) := by
  unfold IsEulerHomogeneous at hf hg ⊢
  rw [SmoothDerivation.map_mul, hf, hg, map_add]
  simp only [smul_eq_mul]
  ring

variable [DecidableEq κ]

/-- `[∂ₐ, E] = ∂ₐ`: a partial derivative lowers the degree by one. -/
theorem partialDerivation_eulerField (a : κ) (f : FreeSmoothRing κ) :
    partialDerivation a (eulerField f) =
      eulerField (partialDerivation a f) + partialDerivation a f := by
  have h : ⁅partialDerivation a, eulerField⁆ = partialDerivation a := derivation_ext fun b => by
    rw [SmoothDerivation.commutator_apply, eulerField_generator, partialDerivation_generator]
    split_ifs <;> simp
  have hf := DFunLike.congr_fun h f
  rw [SmoothDerivation.commutator_apply] at hf
  exact sub_eq_iff_eq_add'.mp hf

/-- A partial derivative of an element of degree `k` has the degree `k − 1`. -/
theorem IsEulerHomogeneous.partialDerivation {k : ℝ} {f : FreeSmoothRing κ}
    (hf : IsEulerHomogeneous k f) (a : κ) :
    IsEulerHomogeneous (k - 1) (FreeSmoothRing.partialDerivation a f) := by
  unfold IsEulerHomogeneous at hf ⊢
  have h := partialDerivation_eulerField a f
  rw [hf, SmoothDerivation.map_algebraMap_mul, smul_eq_mul] at h
  rw [map_sub, map_one]
  linear_combination -h

end Euler

section CanonicalBracket

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- For the canonical bracket, the bracket of elements homogeneous of degrees
`j` and `k` is homogeneous of degree `j + k − 2`. -/
theorem IsEulerHomogeneous.canonical_bracket {j k : ℝ} {f g : PhaseSpace ι}
    (hf : IsEulerHomogeneous j f) (hg : IsEulerHomogeneous k g) :
    IsEulerHomogeneous (j + k - 2) ((PhaseSpace.canonical ι).bracket f g) := by
  have hfa (a : ι ⊕ ι) := hf.partialDerivation a
  have hga (a : ι ⊕ ι) := hg.partialDerivation a
  have hc : algebraMap ℝ (PhaseSpace ι) (j + k - 2) =
      algebraMap ℝ (PhaseSpace ι) (j - 1) + algebraMap ℝ (PhaseSpace ι) (k - 1) := by
    rw [← map_add]
    congr 1
    ring
  unfold IsEulerHomogeneous at hfa hga ⊢
  rw [PhaseSpace.canonical_bracket, map_sum, Finset.mul_sum, hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, SmoothDerivation.map_mul, SmoothDerivation.map_mul, hfa, hga, hfa, hga]
  simp only [smul_eq_mul]
  ring

end CanonicalBracket

/-! ### Bilinear and quadratic expressions in the generators -/

section Bilinear

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The expression `Σ N_ab x_a x_b` in the generators of a free ring. -/
def bilinearForm (N : Matrix κ κ ℝ) : FreeSmoothRing κ :=
  ∑ a, ∑ b, algebraMap ℝ (FreeSmoothRing κ) (N a b) * (generator a * generator b)

/-- The quadratic form `½ Σ S_ab x_a x_b`. -/
def quadraticForm (S : Matrix κ κ ℝ) : FreeSmoothRing κ :=
  bilinearForm ((1 / 2 : ℝ) • S)

omit [DecidableEq κ] in
/-- A bilinear form is homogeneous of degree two. -/
theorem isEulerHomogeneous_bilinearForm (N : Matrix κ κ ℝ) :
    IsEulerHomogeneous 2 (bilinearForm N) := by
  refine IsEulerHomogeneous.sum _ fun a _ => IsEulerHomogeneous.sum _ fun b _ => ?_
  have h := (isEulerHomogeneous_algebraMap (κ := κ) (N a b)).mul
    ((isEulerHomogeneous_generator a).mul (isEulerHomogeneous_generator b))
  have h2 : (0 : ℝ) + (1 + 1) = 2 := by norm_num
  rwa [h2] at h

omit [DecidableEq κ] in
theorem isEulerHomogeneous_quadraticForm (S : Matrix κ κ ℝ) :
    IsEulerHomogeneous 2 (quadraticForm S) :=
  isEulerHomogeneous_bilinearForm _

omit [DecidableEq κ] in
theorem bilinearForm_transpose (N : Matrix κ κ ℝ) : bilinearForm Nᵀ = bilinearForm N := by
  unfold bilinearForm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.transpose_apply, mul_comm (generator b)]

omit [DecidableEq κ] in
theorem bilinearForm_sub (N N' : Matrix κ κ ℝ) :
    bilinearForm (N - N') = bilinearForm N - bilinearForm N' := by
  unfold bilinearForm
  simp only [Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq κ] in
theorem bilinearForm_smul (c : ℝ) (N : Matrix κ κ ℝ) :
    bilinearForm (c • N) = algebraMap ℝ (FreeSmoothRing κ) c * bilinearForm N := by
  unfold bilinearForm
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

omit [DecidableEq κ] in
theorem bilinearForm_neg (N : Matrix κ κ ℝ) : bilinearForm (-N) = -bilinearForm N := by
  rw [← neg_one_smul ℝ N, bilinearForm_smul, map_neg, map_one]
  ring

omit [DecidableEq κ] in
/-- A product of two linear expressions, summed over an index. -/
theorem sum_linear_mul_linear (A B : Matrix κ κ ℝ) :
    ∑ a, (∑ b, algebraMap ℝ (FreeSmoothRing κ) (A a b) * generator b) *
        (∑ c, algebraMap ℝ (FreeSmoothRing κ) (B a c) * generator c) =
      bilinearForm (Aᵀ * B) := by
  have hL : ∑ a, (∑ b, algebraMap ℝ (FreeSmoothRing κ) (A a b) * generator b) *
        (∑ c, algebraMap ℝ (FreeSmoothRing κ) (B a c) * generator c) =
      ∑ a, ∑ b, ∑ c, algebraMap ℝ (FreeSmoothRing κ) (A a b) * generator b *
        (algebraMap ℝ (FreeSmoothRing κ) (B a c) * generator c) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_mul_sum _ _ _ _
  have hR : bilinearForm (Aᵀ * B) =
      ∑ b, ∑ c, ∑ a, algebraMap ℝ (FreeSmoothRing κ) (A a b) *
        algebraMap ℝ (FreeSmoothRing κ) (B a c) * (generator b * generator c) := by
    unfold bilinearForm
    simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, Finset.sum_mul]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-- The gradient of a bilinear expression. -/
theorem partialDerivation_bilinearForm (N : Matrix κ κ ℝ) (c : κ) :
    partialDerivation c (bilinearForm N) =
      ∑ a, algebraMap ℝ (FreeSmoothRing κ) (N c a + N a c) * generator a := by
  have hterm (a b : κ) : partialDerivation c
      (algebraMap ℝ (FreeSmoothRing κ) (N a b) * (generator a * generator b)) =
      (if b = c then algebraMap ℝ (FreeSmoothRing κ) (N a b) * generator a else 0) +
      if a = c then algebraMap ℝ (FreeSmoothRing κ) (N a b) * generator b else 0 := by
    rw [SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul,
      partialDerivation_generator, partialDerivation_generator]
    split_ifs <;> simp [mul_add]
  simp only [bilinearForm, map_sum, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_add]
  ring

/-- The gradient of a quadratic form with a symmetric matrix is linear:
`∂_c (½ Σ S_ab x_a x_b) = Σ_a S_ca x_a`. -/
theorem partialDerivation_quadraticForm {S : Matrix κ κ ℝ} (hS : S.IsSymm) (c : κ) :
    partialDerivation c (quadraticForm S) =
      ∑ a, algebraMap ℝ (FreeSmoothRing κ) (S c a) * generator a := by
  rw [quadraticForm, partialDerivation_bilinearForm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ((1 / 2 : ℝ) • S) c a + ((1 / 2 : ℝ) • S) a c = S c a := by
    rw [Matrix.smul_apply, Matrix.smul_apply, ← hS.apply c a, smul_eq_mul]
    ring
  rw [h]

/-- A symmetric matrix is determined by its quadratic form. -/
theorem quadraticForm_injective {S T : Matrix κ κ ℝ} (hS : S.IsSymm) (hT : T.IsSymm)
    (h : quadraticForm S = quadraticForm T) : S = T := by
  ext a b
  have hd (U : Matrix κ κ ℝ) (hU : U.IsSymm) :
      FreeSmoothRing.lift (fun _ : κ => (0 : ℝ))
        (partialDerivation b (partialDerivation a (quadraticForm U))) = U a b := by
    rw [partialDerivation_quadraticForm hU, map_sum, Finset.sum_eq_single b]
    · rw [SmoothDerivation.map_algebraMap_mul, partialDerivation_generator_self, smul_eq_mul,
        mul_one, SmoothRingHom.map_algebraMap]
      rfl
    · intro c _ hcb
      rw [SmoothDerivation.map_algebraMap_mul, partialDerivation_generator_of_ne hcb, smul_zero]
    · intro h'
      exact absurd (Finset.mem_univ b) h'
  rw [← hd S hS, ← hd T hT, h]

end Bilinear

/-! ### Quadratic Hamiltonians of the canonical bracket -/

namespace PhaseSpace

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable (ι) in
/-- The matrix `J` of the canonical bracket: `{xₐ, x_b} = J_ab`. -/
def canonicalForm : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := Matrix.fromBlocks 0 1 (-1) 0

omit [Fintype ι] in
theorem transpose_canonicalForm : (canonicalForm ι)ᵀ = -canonicalForm ι := by
  rw [canonicalForm, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  simp

theorem canonicalForm_mul_self : canonicalForm ι * canonicalForm ι = -1 := by
  rw [canonicalForm, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

omit [Fintype ι] in
theorem canonicalMatrix_eq (a b : ι ⊕ ι) :
    (canonicalMatrix a b : PhaseSpace ι) =
      algebraMap ℝ (PhaseSpace ι) (canonicalForm ι a b) := by
  rcases a with i | i <;> rcases b with j | j
  · simp [canonicalMatrix, canonicalForm]
  · by_cases h : i = j <;> simp [canonicalMatrix, canonicalForm, h]
  · by_cases h : i = j <;> simp [canonicalMatrix, canonicalForm, h]
  · simp [canonicalMatrix, canonicalForm]

/-- The bracket of a generator with an element:
`{xₐ, f} = Σ_b J_ab ∂_b f`. -/
theorem canonical_bracket_generator_left (a : ι ⊕ ι) (f : PhaseSpace ι) :
    (canonical ι).bracket (generator a) f =
      ∑ b, algebraMap ℝ (PhaseSpace ι) (canonicalForm ι a b) * partialDerivation b f := by
  have h := almostPoisson_bracket_generator_left canonicalMatrix canonicalMatrix_skew a f
  refine h.trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [canonicalMatrix_eq, mul_comm]

/-- The Hamiltonian vector field of a quadratic Hamiltonian is linear
(Proposition 70): `{xₐ, ½ Σ S x x} = Σ_c (J S)_ac x_c`. -/
theorem canonical_bracket_generator_quadraticForm {S : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hS : S.IsSymm) (a : ι ⊕ ι) :
    (canonical ι).bracket (generator a) (quadraticForm S) =
      ∑ c, algebraMap ℝ (PhaseSpace ι) ((canonicalForm ι * S) a c) * generator c := by
  rw [canonical_bracket_generator_left]
  simp only [partialDerivation_quadraticForm hS, Finset.mul_sum, Matrix.mul_apply, map_sum,
    map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

/-- The quadratic Hamiltonians are closed under the bracket (Proposition 70):
`{Q_S, Q_T} = Q_{S J T − T J S}`. -/
theorem canonical_bracket_quadraticForm {S T : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hS : S.IsSymm)
    (hT : T.IsSymm) :
    (canonical ι).bracket (quadraticForm S) (quadraticForm T) =
      quadraticForm (S * canonicalForm ι * T - T * canonicalForm ι * S) := by
  have h2 : algebraMap ℝ (PhaseSpace ι) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℝ (PhaseSpace ι)) 2, ← map_mul]
    norm_num
  have hL : (canonical ι).bracket (quadraticForm S) (quadraticForm T) =
      bilinearForm (S * canonicalForm ι * T) := by
    have h := almostPoisson_bracket_eq_sum_left canonicalMatrix canonicalMatrix_skew
      (quadraticForm S) (quadraticForm T)
    refine h.trans ?_
    have hg (a : ι ⊕ ι) : (almostPoisson canonicalMatrix canonicalMatrix_skew).bracket
        (generator a) (quadraticForm T) =
        ∑ c, algebraMap ℝ (PhaseSpace ι) ((canonicalForm ι * T) a c) * generator c :=
      canonical_bracket_generator_quadraticForm hT a
    simp only [partialDerivation_quadraticForm hS, hg]
    rw [sum_linear_mul_linear, hS.eq, Matrix.mul_assoc]
  have hT' : (T * canonicalForm ι * S)ᵀ = -(S * canonicalForm ι * T) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hS.eq, hT.eq, transpose_canonicalForm,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  rw [hL, quadraticForm, bilinearForm_smul, bilinearForm_sub,
    ← bilinearForm_transpose (T * canonicalForm ι * S), hT', bilinearForm_neg]
  linear_combination (-bilinearForm (S * canonicalForm ι * T)) * h2

/-- A matrix `J S` is in the symplectic Lie algebra exactly when `S` is
symmetric: `(J S)ᵀ J + J (J S) = 0` if and only if `Sᵀ = S`. -/
theorem transpose_mul_add_mul_eq_zero_iff (S : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    (canonicalForm ι * S)ᵀ * canonicalForm ι + canonicalForm ι * (canonicalForm ι * S) = 0 ↔
      S.IsSymm := by
  have h : (canonicalForm ι * S)ᵀ * canonicalForm ι + canonicalForm ι * (canonicalForm ι * S) =
      Sᵀ - S := by
    rw [Matrix.transpose_mul, transpose_canonicalForm, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, canonicalForm_mul_self, ← Matrix.mul_assoc, canonicalForm_mul_self]
    simp [sub_eq_add_neg]
  rw [h, sub_eq_zero]
  rfl

/-- Every matrix `A` with `Aᵀ J + J A = 0` is `J S` for the symmetric matrix
`S = −J A`. -/
theorem canonicalForm_mul_neg_canonicalForm_mul (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    canonicalForm ι * (-(canonicalForm ι * A)) = A := by
  rw [Matrix.mul_neg, ← Matrix.mul_assoc, canonicalForm_mul_self]
  simp

/-- The correspondence `S ↦ J S` takes the bracket of quadratic Hamiltonians
to the commutator of matrices: `J (S J T − T J S) = (J S)(J T) − (J T)(J S)`. -/
theorem canonicalForm_mul_sub (S T : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    canonicalForm ι * (S * canonicalForm ι * T - T * canonicalForm ι * S) =
      canonicalForm ι * S * (canonicalForm ι * T) -
        canonicalForm ι * T * (canonicalForm ι * S) := by
  rw [Matrix.mul_sub]
  simp only [Matrix.mul_assoc]

theorem canonicalForm_mul_canonicalForm_mul (X : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    canonicalForm ι * (canonicalForm ι * X) = -X := by
  rw [← Matrix.mul_assoc, canonicalForm_mul_self, Matrix.neg_mul, Matrix.one_mul]

omit [Fintype ι] in
/-- Mathlib's matrix `J` of the symplectic form is `−canonicalForm`. -/
theorem J_eq_neg_canonicalForm : Matrix.J ι ℝ = -canonicalForm ι := by
  rw [Matrix.J, canonicalForm, Matrix.fromBlocks_neg, neg_zero, neg_neg]

/-- The Lie algebra `sp(2n, ℝ)` of Mathlib is the set of the matrices `A` with
`Aᵀ J + J A = 0`. -/
theorem mem_sp_iff (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    A ∈ LieAlgebra.Symplectic.sp ι ℝ ↔ Aᵀ * canonicalForm ι + canonicalForm ι * A = 0 := by
  change A ∈ skewAdjointMatricesSubmodule (Matrix.J ι ℝ) ↔ _
  rw [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
    J_eq_neg_canonicalForm, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
    neg_eq_iff_add_eq_zero]

/-- `J S` is in `sp(2n, ℝ)` exactly when `S` is symmetric. -/
theorem canonicalForm_mul_mem_sp_iff (S : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    canonicalForm ι * S ∈ LieAlgebra.Symplectic.sp ι ℝ ↔ S.IsSymm := by
  rw [mem_sp_iff, transpose_mul_add_mul_eq_zero_iff]

theorem isSymm_neg_canonicalForm_mul {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hA : A ∈ LieAlgebra.Symplectic.sp ι ℝ) : (-(canonicalForm ι * A)).IsSymm := by
  rw [← canonicalForm_mul_mem_sp_iff, canonicalForm_mul_neg_canonicalForm_mul]
  exact hA

/-- The quadratic Hamiltonian `−½ xᵀ J A x` of a matrix `A`. For `A` in
`sp(2n, ℝ)` its Hamiltonian vector field is the linear vector field `A`. -/
def spHamiltonian (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : PhaseSpace ι :=
  quadraticForm (-(canonicalForm ι * A))

/-- Every quadratic form is the Hamiltonian of the matrix `J S`. -/
theorem quadraticForm_eq_spHamiltonian (S : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    quadraticForm S = spHamiltonian (canonicalForm ι * S) := by
  rw [spHamiltonian, canonicalForm_mul_canonicalForm_mul, neg_neg]

/-- `X_H` is linear for quadratic `H` (Proposition 70): `{xₐ, H_A} = Σ_c Aₐ_c x_c`. -/
theorem canonical_bracket_generator_spHamiltonian {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hA : A ∈ LieAlgebra.Symplectic.sp ι ℝ) (a : ι ⊕ ι) :
    (canonical ι).bracket (generator a) (spHamiltonian A) =
      ∑ c, algebraMap ℝ (PhaseSpace ι) (A a c) * generator c := by
  rw [spHamiltonian, canonical_bracket_generator_quadraticForm (isSymm_neg_canonicalForm_mul hA),
    canonicalForm_mul_neg_canonicalForm_mul]

/-- The quadratic Hamiltonians form a Lie algebra isomorphic to `sp(2n, ℝ)`
(Proposition 70): `{H_A, H_B} = H_{[A, B]}`. -/
theorem canonical_bracket_spHamiltonian {A B : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hA : A ∈ LieAlgebra.Symplectic.sp ι ℝ) (hB : B ∈ LieAlgebra.Symplectic.sp ι ℝ) :
    (canonical ι).bracket (spHamiltonian A) (spHamiltonian B) = spHamiltonian ⁅A, B⁆ := by
  have h := canonicalForm_mul_sub (-(canonicalForm ι * A)) (-(canonicalForm ι * B))
  rw [canonicalForm_mul_neg_canonicalForm_mul, canonicalForm_mul_neg_canonicalForm_mul] at h
  unfold spHamiltonian
  rw [canonical_bracket_quadraticForm (isSymm_neg_canonicalForm_mul hA)
    (isSymm_neg_canonicalForm_mul hB), Ring.lie_def, ← h, canonicalForm_mul_canonicalForm_mul,
    neg_neg]

/-- The Hamiltonian determines the matrix. -/
theorem spHamiltonian_injective {A B : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hA : A ∈ LieAlgebra.Symplectic.sp ι ℝ) (hB : B ∈ LieAlgebra.Symplectic.sp ι ℝ)
    (h : spHamiltonian A = spHamiltonian B) : A = B := by
  have h' := quadraticForm_injective (isSymm_neg_canonicalForm_mul hA)
    (isSymm_neg_canonicalForm_mul hB) h
  rw [← canonicalForm_mul_neg_canonicalForm_mul A, h', canonicalForm_mul_neg_canonicalForm_mul]

end PhaseSpace

end ProjectAInos.SmoothAlgebra
