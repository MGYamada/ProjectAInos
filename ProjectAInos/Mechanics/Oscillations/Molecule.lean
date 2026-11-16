/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.SymmetryTypes
public import ProjectAInos.Mechanics.Rigid.Dynamics
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The vibrations of a molecule and its symmetry group

Landau–Lifshitz §24. The atoms of a molecule are indexed by `ι`, and a
displacement is a function on `ι × Fin 3`. A group `G` acts on space by the
matrices `O g` and permutes the atoms by `π g`.

* `displacementRep O π`: the representation on the displacements,
  `(g u)ₐ = O_g u_{π_g⁻¹ a}`. Its character is `N_g · tr O_g`, with `N_g` the
  number of the atoms that `g` leaves in place (`character_displacementRep`).
* `rigidMap r`: the displacement `uₐ = t + ω × rₐ` of the translation `t` and
  the rotation `ω` of the configuration `r`. If the matrices `O g` are
  orthogonal and the configuration is symmetric, `O_g rₐ = r_{π_g a}`, it is
  equivariant from the representation `rigidRep O` of the vectors and the
  axial vectors, whose character is `(1 + det O_g) tr O_g`
  (`rigidMap_comp_rigidRep`, `character_rigidRep`).
* `sum_finrank_vibration`: if the rigid displacements are the modes of
  frequency zero and `rigidMap r` is injective, the number of the modes of
  non-zero frequency of the symmetry type `σ` is the scalar product of the
  character of `σ` with `(N_g − 1 − det O_g) tr O_g`.
* `card_vibration_add_six`: there are then `3N − 6` modes of non-zero
  frequency.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.Molecule

open Matrix Module NormalModes
open scoped Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [Group G]

/-- The displacement of the atom `a`. -/
def atom (u : ι × Fin 3 → ℝ) (a : ι) : Fin 3 → ℝ := fun j => u (a, j)

omit [Fintype ι] [DecidableEq ι] in
theorem atom_ext {u v : ι × Fin 3 → ℝ} (h : ∀ a, atom u a = atom v a) : u = v := by
  funext p
  exact congrFun (h p.1) p.2

/-! ### The representation on the displacements -/

/-- The matrix of an element of the group on the displacements. -/
def displacementMatrix (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (π : G →* Equiv.Perm ι) (g : G) :
    Matrix (ι × Fin 3) (ι × Fin 3) ℝ :=
  Matrix.permMatrixHom (R := ℝ) (π g) ⊗ₖ O g

theorem displacementMatrix_one (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (π : G →* Equiv.Perm ι) :
    displacementMatrix O π 1 = 1 := by
  rw [displacementMatrix, map_one, map_one, map_one, one_kronecker_one]

theorem displacementMatrix_mul (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (π : G →* Equiv.Perm ι)
    (g h : G) :
    displacementMatrix O π (g * h) = displacementMatrix O π g * displacementMatrix O π h := by
  rw [displacementMatrix, map_mul, map_mul, map_mul, mul_kronecker_mul]
  rfl

/-- The representation of the group on the displacements of the atoms. -/
def displacementRep (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (π : G →* Equiv.Perm ι) :
    Representation ℝ G (ι × Fin 3 → ℝ) where
  toFun g := toLin' (displacementMatrix O π g)
  map_one' := by
    rw [displacementMatrix_one, toLin'_one]
    rfl
  map_mul' g h := by
    rw [displacementMatrix_mul, toLin'_mul]
    rfl

/-- `(g u)ₐ = O_g u_{π_g⁻¹ a}`. -/
theorem atom_displacementRep (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (π : G →* Equiv.Perm ι)
    (g : G) (u : ι × Fin 3 → ℝ) (a : ι) :
    atom (displacementRep O π g u) a = O g *ᵥ atom u ((π g)⁻¹ a) := by
  funext i
  have hperm : ∀ b, (((π g)⁻¹).permMatrix ℝ) a b = if (π g)⁻¹ a = b then 1 else 0 := fun b => by
    simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.Perm.inv_def]
  change (displacementMatrix O π g *ᵥ u) (a, i) = _
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, displacementMatrix, kronecker_apply,
    permMatrixHom_apply, atom, hperm]
  rw [Finset.sum_eq_single ((π g)⁻¹ a)]
  · simp
  · intro b _ hb
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      ite_eq_right_iff]
    intro h
    exact absurd h.symm hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The character of the representation on the displacements: the number of
the atoms left in place times the trace of the matrix on space. -/
theorem character_displacementRep (O : G →* Matrix (Fin 3) (Fin 3) ℝ)
    (π : G →* Equiv.Perm ι) (g : G) :
    (displacementRep O π).character g =
      ((Function.fixedPoints (π g)).ncard : ℝ) * (O g).trace := by
  have hfix : Function.fixedPoints ⇑(π g)⁻¹ = Function.fixedPoints ⇑(π g) := by
    ext a
    simp only [Function.mem_fixedPoints, Function.IsFixedPt]
    exact Equiv.Perm.inv_eq_iff_eq.trans eq_comm
  change LinearMap.trace ℝ _ (toLin' (displacementMatrix O π g)) = _
  rw [Matrix.trace_toLin'_eq, displacementMatrix, trace_kronecker, permMatrixHom_apply,
    trace_permutation, hfix]

/-! ### Translations and rotations -/

/-- The displacement `uₐ = t + ω × rₐ` of the rigid motion with the translation
`t` and the rotation `ω`. -/
def rigidMap (r : ι → Fin 3 → ℝ) : (Fin 3 → ℝ) × (Fin 3 → ℝ) →ₗ[ℝ] (ι × Fin 3 → ℝ) where
  toFun x := fun p => (x.1 + x.2 ⨯₃ r p.1) p.2
  map_add' x y := by
    funext p
    simp only [Prod.fst_add, Prod.snd_add, LinearMap.map_add₂, Pi.add_apply]
    ring
  map_smul' c x := by
    funext p
    simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.map_smul₂, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem atom_rigidMap (r : ι → Fin 3 → ℝ) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (a : ι) :
    atom (rigidMap r x) a = x.1 + x.2 ⨯₃ r a := rfl

/-- The representation on the vectors. -/
def vectorRep (O : G →* Matrix (Fin 3) (Fin 3) ℝ) : Representation ℝ G (Fin 3 → ℝ) where
  toFun g := toLin' (O g)
  map_one' := by
    rw [map_one, toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, toLin'_mul]
    rfl

/-- The representation on the axial vectors: `ω ↦ det O_g · O_g ω`. -/
def axialRep (O : G →* Matrix (Fin 3) (Fin 3) ℝ) : Representation ℝ G (Fin 3 → ℝ) where
  toFun g := toLin' ((O g).det • O g)
  map_one' := by
    rw [map_one, det_one, one_smul, toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, det_mul, ← smul_smul, ← Matrix.mul_smul, ← Matrix.smul_mul, toLin'_mul]
    rfl

/-- The representation on the translations and the rotations. -/
def rigidRep (O : G →* Matrix (Fin 3) (Fin 3) ℝ) :
    Representation ℝ G ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  (vectorRep O).prod (axialRep O)

theorem character_rigidRep (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (g : G) :
    (rigidRep O).character g = (1 + (O g).det) * (O g).trace := by
  change LinearMap.trace ℝ _ ((toLin' (O g)).prodMap (toLin' ((O g).det • O g))) = _
  rw [LinearMap.trace_prodMap', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq,
    Matrix.trace_smul, smul_eq_mul]
  ring

/-- An orthogonal matrix and the cross product:
`A (x × y) = det A · (A x × A y)`. -/
theorem mulVec_cross_of_orthogonal {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1)
    (x y : Fin 3 → ℝ) : A *ᵥ (x ⨯₃ y) = A.det • ((A *ᵥ x) ⨯₃ (A *ᵥ y)) := by
  have hdet : A.det * A.det = 1 := by
    have h := congrArg Matrix.det hA
    rwa [det_mul, det_transpose, det_one] at h
  have hadj : adjugate A = A.det • Aᵀ := by
    calc adjugate A = Aᵀ * A * adjugate A := by rw [hA, Matrix.one_mul]
      _ = A.det • Aᵀ := by
        rw [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [Rigid.mulVec_cross_mulVec, hadj, transpose_smul, transpose_transpose, smul_mulVec,
    smul_smul, hdet, one_smul]

/-- A symmetric configuration: the rigid displacements are carried to rigid
displacements, with the translation as a vector and the rotation as an axial
vector. -/
theorem displacementRep_rigidMap {O : G →* Matrix (Fin 3) (Fin 3) ℝ} {π : G →* Equiv.Perm ι}
    {r : ι → Fin 3 → ℝ} (hO : ∀ g, (O g)ᵀ * O g = 1) (hr : ∀ g a, O g *ᵥ r a = r (π g a))
    (g : G) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    displacementRep O π g (rigidMap r x) = rigidMap r (rigidRep O g x) := by
  refine atom_ext fun a => ?_
  have hra : O g *ᵥ r ((π g)⁻¹ a) = r a := by
    rw [hr]
    exact congrArg r ((π g).apply_symm_apply a)
  rw [atom_displacementRep, atom_rigidMap, atom_rigidMap, mulVec_add,
    mulVec_cross_of_orthogonal (hO g), hra]
  change O g *ᵥ x.1 + (O g).det • ((O g *ᵥ x.2) ⨯₃ r a) =
    O g *ᵥ x.1 + (((O g).det • O g) *ᵥ x.2) ⨯₃ r a
  rw [smul_mulVec, LinearMap.map_smul₂]

/-! ### The modes of non-zero frequency -/

section Vibration

variable {M K S : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} {lam : ι × Fin 3 → ℝ}
  {O : G →* Matrix (Fin 3) (Fin 3) ℝ} {π : G →* Equiv.Perm ι} {r : ι → Fin 3 → ℝ}

/-- If the rigid displacements are the modes of frequency zero, the
representation on these modes is the one on the translations and the
rotations. -/
def rigidEquiv (h : IsSymmetryRep (displacementRep O π) M K) (hO : ∀ g, (O g)ᵀ * O g = 1)
    (hr : ∀ g a, O g *ᵥ r a = r (π g a)) (hinj : Function.Injective (rigidMap r))
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) :
    Representation.Equiv (rigidRep O) (modeRep h 0) :=
  Representation.Equiv.mk
    ((LinearEquiv.ofInjective (rigidMap r) hinj).trans (LinearEquiv.ofEq _ _ hzero))
    (fun g => by
      refine LinearMap.ext fun x => ?_
      apply Subtype.ext
      exact (displacementRep_rigidMap hO hr g x).symm)

/-- The character on the modes of frequency zero. -/
theorem character_modeRep_zero (h : IsSymmetryRep (displacementRep O π) M K)
    (hO : ∀ g, (O g)ᵀ * O g = 1) (hr : ∀ g a, O g *ᵥ r a = r (π g a))
    (hinj : Function.Injective (rigidMap r))
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) (g : G) :
    (modeRep h 0).character g = (1 + (O g).det) * (O g).trace := by
  rw [← Representation.char_iso (rigidEquiv h hO hr hinj hzero), character_rigidRep]

omit [Group G] [DecidableEq ι] in
/-- There are six independent modes of frequency zero. -/
theorem finrank_modeSpace_zero (hinj : Function.Injective (rigidMap r))
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) :
    finrank ℝ (modeSpace M K 0) = 6 := by
  rw [← hzero, LinearMap.finrank_range_of_inj hinj, finrank_prod, finrank_pi]
  simp

omit [Group G] in
/-- The modes of non-zero frequency and the independent rigid displacements
add up to the `3N` degrees of freedom, if the rigid displacements are the
modes of frequency zero. For a molecule on a line the rigid displacements
have the dimension five. -/
theorem card_vibration_add_finrank_range (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam)
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) :
    Fintype.card {p // lam p ≠ 0} + finrank ℝ (LinearMap.range (rigidMap r)) =
      3 * Fintype.card ι := by
  rw [hzero, finrank_modeSpace hSM hSK]
  have hsplit := Fintype.card_subtype_compl (fun p : ι × Fin 3 => lam p ≠ 0)
  have heq : Fintype.card {p // ¬lam p ≠ 0} = Fintype.card {p // lam p = 0} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun p => by rw [not_not])
  have hle := Fintype.card_subtype_le (fun p : ι × Fin 3 => lam p ≠ 0)
  have hcard : Fintype.card (ι × Fin 3) = 3 * Fintype.card ι := by
    rw [Fintype.card_prod, Fintype.card_fin, mul_comm]
  omega

omit [Group G] in
/-- The number of the modes of non-zero frequency is `3N − 6`. -/
theorem card_vibration_add_six (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (hinj : Function.Injective (rigidMap r))
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) :
    Fintype.card {p // lam p ≠ 0} + 6 = 3 * Fintype.card ι := by
  have h6 := finrank_modeSpace_zero hinj hzero
  rw [finrank_modeSpace hSM hSK] at h6
  have hsplit := Fintype.card_subtype_compl (fun p : ι × Fin 3 => lam p ≠ 0)
  have heq : Fintype.card {p // ¬lam p ≠ 0} = Fintype.card {p // lam p = 0} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun p => by rw [not_not])
  have hle := Fintype.card_subtype_le (fun p : ι × Fin 3 => lam p ≠ 0)
  have hcard : Fintype.card (ι × Fin 3) = 3 * Fintype.card ι := by
    rw [Fintype.card_prod, Fintype.card_fin, mul_comm]
  omega

variable [Fintype G] {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- The number of the vibrations of a symmetry type. If the rigid
displacements are the modes of frequency zero, the modes of non-zero frequency
contain the symmetry type `σ` as many times as the scalar product of its
character with `(N_g − 1 − det O_g) tr O_g`. -/
theorem sum_finrank_vibration (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (h : IsSymmetryRep (displacementRep O π) M K) (hO : ∀ g, (O g)ᵀ * O g = 1)
    (hr : ∀ g a, O g *ᵥ r a = r (π g a)) (hinj : Function.Injective (rigidMap r))
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) (σ : Representation ℝ G W) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap σ (modeRep h c)) : ℝ) =
      (Nat.card G : ℝ)⁻¹ * ∑ g : G,
        (((Function.fixedPoints (π g)).ncard : ℝ) - 1 - (O g).det) * (O g).trace *
          σ.character g⁻¹ := by
  have hinv : Invertible (Nat.card G : ℝ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h0 : (0 : ℝ) ∈ Finset.univ.image lam := by
    have h6 := finrank_modeSpace_zero hinj hzero
    rw [finrank_modeSpace hSM hSK] at h6
    have hne : Nonempty {p // lam p = 0} := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨p, hp⟩ := hne
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩
  rw [Finset.sum_erase_eq_sub h0, sum_finrank_intertwiningMap_modeRep hSM hSK h σ,
    ← Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ (modeRep h 0), ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [character_displacementRep, character_modeRep_zero h hO hr hinj hzero]
  ring

end Vibration

end ProjectAInos.Mechanics.Molecule
