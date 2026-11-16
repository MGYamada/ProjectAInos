/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Symmetry
public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The symmetry types of the normal modes

Landau–Lifshitz §24. Let `Sᵀ M S = 1` and `Sᵀ K S = diag λ` be a simultaneous
diagonalization of the matrices of a system of small oscillations.

* `isInternal_modeSpace`: the space of the co-ordinates is the direct sum of
  the spaces `modeSpace M K c` of the modes, over the values `c` of `λ`;
  `finrank_modeSpace`: the space of the value `c` has the dimension of the
  number of the indices with `λ = c`.
* `IsSymmetryRep ρ M K`: a representation of a group by linear maps that
  commute with `M` and `K`. Each space of modes is then a subrepresentation
  (`modeSubrep`, `modeRep`), and the character of `ρ` is the sum of the
  characters on these spaces (`character_eq_sum_modeRep`).
* `sum_finrank_intertwiningMap_modeRep`: for a representation `σ` of the same
  group, the dimensions of the spaces of the equivariant maps from `σ` to the
  modes of each frequency add up to the scalar product of the characters,
  `(1/|G|) Σ_g χ_ρ(g) χ_σ(g⁻¹)`. For an irreducible `σ` whose equivariant
  endomorphisms are the scalars, this dimension is the number of times the
  symmetry type `σ` occurs.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.NormalModes

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The decomposition into the spaces of the modes -/

section Decomposition

variable {M K S : Matrix n n ℝ} {lam : n → ℝ}

/-- The space of the modes of the value `c` is an eigenspace of `S Sᵀ K`, the
matrix `M⁻¹ K`. -/
theorem modeSpace_eq_eigenspace (hSM : Sᵀ * M * S = 1) (c : ℝ) :
    modeSpace M K c = End.eigenspace (toLin' (S * Sᵀ * K)) c := by
  ext v
  rw [mem_modeSpace, End.mem_eigenspace_iff, toLin'_apply]
  constructor
  · intro h
    rw [← mulVec_mulVec, h, mulVec_smul, mulVec_mulVec, Matrix.mul_assoc,
      mul_transpose_mul_eq_one hSM, one_mulVec]
  · intro h
    have h1 : M *ᵥ ((S * Sᵀ * K) *ᵥ v) = M *ᵥ (c • v) := congrArg (fun w => M *ᵥ w) h
    rwa [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_mul_transpose_eq_one hSM,
      Matrix.one_mul, mulVec_smul] at h1

/-- The columns of `S` are modes. -/
theorem mulVec_single_mem_modeSpace (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (a : n) : S *ᵥ Pi.single a 1 ∈ modeSpace M K (lam a) := by
  have hd : diagonal lam *ᵥ Pi.single a (1 : ℝ) = lam a • Pi.single a 1 := by
    ext b
    rw [mulVec_diagonal]
    by_cases h : b = a <;> simp [h]
  rw [mem_modeSpace, mulVec_mulVec, mul_eq_mul_mul_diagonal hSM hSK, ← mulVec_mulVec, hd,
    mulVec_smul, ← mulVec_mulVec]

/-- The spaces of the modes are independent. -/
theorem iSupIndep_modeSpace (hSM : Sᵀ * M * S = 1) (s : Finset ℝ) :
    iSupIndep fun c : s => modeSpace M K c := by
  have h := (End.eigenspaces_iSupIndep (toLin' (S * Sᵀ * K))).comp
    (Subtype.val_injective (p := fun c : ℝ => c ∈ s))
  have heq : (fun c : s => modeSpace M K c) =
      (End.eigenspace (toLin' (S * Sᵀ * K))) ∘ (Subtype.val : s → ℝ) :=
    funext fun c => modeSpace_eq_eigenspace hSM c
  rw [heq]
  exact h

/-- The spaces of the modes of the values of `λ` span the space. -/
theorem iSup_modeSpace_eq_top (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam) :
    ⨆ c : (Finset.univ.image lam), modeSpace M K c = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ a, ((Sᵀ * M) *ᵥ v) a • (S *ᵥ Pi.single a 1) := by
    have h1 : v = S *ᵥ ((Sᵀ * M) *ᵥ v) := by
      rw [mulVec_mulVec, mul_transpose_mul_eq_one hSM, one_mulVec]
    conv_lhs => rw [h1]
    ext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hv]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem
      (⟨lam a, Finset.mem_image_of_mem lam (Finset.mem_univ a)⟩ : (Finset.univ.image lam))
      (mulVec_single_mem_modeSpace hSM hSK a))

/-- The space of the co-ordinates is the direct sum of the spaces of the modes. -/
theorem isInternal_modeSpace (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam) :
    DirectSum.IsInternal fun c : (Finset.univ.image lam) => modeSpace M K c :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_modeSpace hSM _)
    (iSup_modeSpace_eq_top hSM hSK)

omit [DecidableEq n] in
/-- The modes of the value `c` are the kernel of `K − c M`. -/
theorem modeSpace_eq_ker (M K : Matrix n n ℝ) (c : ℝ) :
    modeSpace M K c = LinearMap.ker (K - c • M).mulVecLin := by
  ext v
  rw [mem_modeSpace, LinearMap.mem_ker, mulVecLin_apply, sub_mulVec, smul_mulVec, sub_eq_zero]

/-- The number of the modes of the value `c`: the dimension of their space is
the number of the indices with `λ = c`. -/
theorem finrank_modeSpace (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam) (c : ℝ) :
    finrank ℝ (modeSpace M K c) = Fintype.card {a // lam a = c} := by
  have hdiag : Sᵀ * (K - c • M) * S = diagonal fun a => lam a - c := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hSK, Matrix.mul_smul, Matrix.smul_mul, hSM]
    ext a b
    by_cases h : a = b <;> simp [h]
  have hrank := card_ne_zero_eq_rank (M := M) (K := K - c • M) hSM hdiag
  have hnull := LinearMap.finrank_range_add_finrank_ker (K - c • M).mulVecLin
  rw [← modeSpace_eq_ker, finrank_pi, ← Matrix.rank, ← hrank] at hnull
  have hsplit : Fintype.card {a // lam a - c ≠ 0} + Fintype.card {a // lam a = c} =
      Fintype.card n := by
    have h := Fintype.card_subtype_compl (fun a : n => lam a - c ≠ 0)
    have heq : Fintype.card {a // ¬lam a - c ≠ 0} = Fintype.card {a // lam a = c} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun a => by rw [not_not, sub_eq_zero])
    have hle := Fintype.card_subtype_le (fun a : n => lam a - c ≠ 0)
    omega
  omega

end Decomposition

/-! ### Representations by symmetries -/

section Representation

variable {G : Type*} [Group G] {M K S : Matrix n n ℝ} {lam : n → ℝ}

/-- A representation of a group on the co-ordinates by symmetries: every
element commutes with the matrices `M` and `K`. -/
structure IsSymmetryRep (ρ : Representation ℝ G (n → ℝ)) (M K : Matrix n n ℝ) : Prop where
  mass : ∀ g v, M *ᵥ ρ g v = ρ g (M *ᵥ v)
  stiffness : ∀ g v, K *ᵥ ρ g v = ρ g (K *ᵥ v)

omit [DecidableEq n] in
/-- The trivial representation is a representation by symmetries. -/
theorem isSymmetryRep_one (M K : Matrix n n ℝ) :
    IsSymmetryRep (1 : Representation ℝ G (n → ℝ)) M K :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

variable {ρ : Representation ℝ G (n → ℝ)}

/-- The modes of a frequency are a subrepresentation. -/
def modeSubrep (h : IsSymmetryRep ρ M K) (c : ℝ) : Subrepresentation ρ where
  toSubmodule := modeSpace M K c
  apply_mem_toSubmodule g v hv := by
    rw [mem_modeSpace] at hv ⊢
    rw [h.stiffness, hv, map_smul, h.mass]

/-- The representation of the group on the modes of a frequency. -/
def modeRep (h : IsSymmetryRep ρ M K) (c : ℝ) : Representation ℝ G (modeSpace M K c) :=
  (modeSubrep h c).toRepresentation

omit [DecidableEq n] in
@[simp] theorem coe_modeRep_apply (h : IsSymmetryRep ρ M K) (c : ℝ) (g : G)
    (v : modeSpace M K c) : (modeRep h c g v : n → ℝ) = ρ g v := rfl

/-- The character of a representation by symmetries is the sum of its
characters on the modes of each frequency. -/
theorem character_eq_sum_modeRep (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (h : IsSymmetryRep ρ M K) (g : G) :
    ρ.character g = ∑ c ∈ Finset.univ.image lam, (modeRep h c).character g := by
  have htr := LinearMap.trace_eq_sum_trace_restrict (isInternal_modeSpace hSM hSK) (f := ρ g)
    (fun c _ hv => (modeSubrep h c).apply_mem_toSubmodule g hv)
  rw [← Finset.sum_coe_sort]
  exact htr

variable [Fintype G] {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- The number of the modes of a symmetry type. For a representation `σ`, the
dimensions of the spaces of the equivariant maps from `σ` to the modes of each
frequency add up to the scalar product of the characters of `ρ` and `σ`. -/
theorem sum_finrank_intertwiningMap_modeRep (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam) (h : IsSymmetryRep ρ M K) (σ : Representation ℝ G W) :
    ∑ c ∈ Finset.univ.image lam,
        (finrank ℝ (Representation.IntertwiningMap σ (modeRep h c)) : ℝ) =
      (Nat.card G : ℝ)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ := by
  have : Invertible (Nat.card G : ℝ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  simp_rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ (modeRep h _)]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [character_eq_sum_modeRep hSM hSK h g, Finset.sum_mul]

/-- The same number for the whole space: the dimension of the space of the
equivariant maps from `σ` to `ρ` is the sum over the frequencies. -/
theorem finrank_intertwiningMap_eq_sum (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam) (h : IsSymmetryRep ρ M K) (σ : Representation ℝ G W) :
    (finrank ℝ (Representation.IntertwiningMap σ ρ) : ℝ) =
      ∑ c ∈ Finset.univ.image lam,
        (finrank ℝ (Representation.IntertwiningMap σ (modeRep h c)) : ℝ) := by
  have : Invertible (Nat.card G : ℝ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [sum_finrank_intertwiningMap_modeRep hSM hSK h σ,
    Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ ρ]

end Representation

end ProjectAInos.Mechanics.NormalModes
