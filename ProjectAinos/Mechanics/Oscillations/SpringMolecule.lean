/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Oscillations.Molecule
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# A molecule with springs along its bonds

A model of the potential energy of a molecule near its equilibrium
configuration `r`: a spring of stiffness `κ a b` along the line joining each
pair of atoms, so that to second order the energy is a sum of the squares of
the stretchings `(uₐ − u_b) · (rₐ − r_b)` of the bonds.

* `massMatrix m`, `springMatrix r κ`: the matrices `M` and `K` of the small
  oscillations; `K` is symmetric and `M` is positive definite for positive
  masses.
* `springMatrix_mulVec_eq_zero_iff`: for positive stiffnesses the modes of
  frequency zero are the displacements that stretch no bond, and the rigid
  displacements are among them (`rigidMap_mem_modeSpace_zero`).
* `isSymmetryRep_spring`: a group that acts by orthogonal matrices, permutes
  the atoms of the configuration, and preserves the masses and the
  stiffnesses, acts on the displacements by symmetries.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Mechanics.Molecule

open Matrix Module NormalModes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The matrices -/

/-- The mass matrix of atoms with the masses `m`. -/
def massMatrix (m : ι → ℝ) : Matrix (ι × Fin 3) (ι × Fin 3) ℝ :=
  diagonal fun p => m p.1

theorem atom_massMatrix_mulVec (m : ι → ℝ) (u : ι × Fin 3 → ℝ) (a : ι) :
    atom (massMatrix m *ᵥ u) a = m a • atom u a := by
  funext j
  simp [atom, massMatrix, mulVec_diagonal]

omit [Fintype ι] in
theorem posDef_massMatrix {m : ι → ℝ} (hm : ∀ a, 0 < m a) : (massMatrix m).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun p => hm p.1

/-- The coefficients of the stretching of the bond between the atoms `a` and
`b`, the linear form `u ↦ (uₐ − u_b) · (rₐ − r_b)`. -/
def bondVector (r : ι → Fin 3 → ℝ) (a b : ι) : ι × Fin 3 → ℝ :=
  fun p => ((if p.1 = a then 1 else 0) - (if p.1 = b then 1 else 0)) * (r a p.2 - r b p.2)

omit [Fintype ι] in
theorem atom_bondVector (r : ι → Fin 3 → ℝ) (a b c : ι) :
    atom (bondVector r a b) c =
      (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ)) • (r a - r b) := rfl

theorem bondVector_dotProduct (r : ι → Fin 3 → ℝ) (a b : ι) (u : ι × Fin 3 → ℝ) :
    bondVector r a b ⬝ᵥ u = (r a - r b) ⬝ᵥ (atom u a - atom u b) := by
  rw [dotProduct, Fintype.sum_prod_type]
  have h : ∀ c : ι, ∑ j, bondVector r a b (c, j) * u (c, j) =
      ((if c = a then 1 else 0) - (if c = b then 1 else 0)) * ((r a - r b) ⬝ᵥ atom u c) :=
    fun c => by
      simp only [bondVector, dotProduct, atom, Finset.mul_sum, Pi.sub_apply]
      exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, dotProduct_sub]

/-- The matrix of the potential energy of springs along the bonds. -/
def springMatrix (r : ι → Fin 3 → ℝ) (κ : ι → ι → ℝ) : Matrix (ι × Fin 3) (ι × Fin 3) ℝ :=
  Matrix.of fun p q => ∑ a, ∑ b, κ a b * (bondVector r a b p * bondVector r a b q)

theorem transpose_springMatrix (r : ι → Fin 3 → ℝ) (κ : ι → ι → ℝ) :
    (springMatrix r κ)ᵀ = springMatrix r κ := by
  ext p q
  simp only [transpose_apply, springMatrix, of_apply]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem springMatrix_mulVec (r : ι → Fin 3 → ℝ) (κ : ι → ι → ℝ) (u : ι × Fin 3 → ℝ) :
    springMatrix r κ *ᵥ u =
      ∑ a, ∑ b, (κ a b * (bondVector r a b ⬝ᵥ u)) • bondVector r a b := by
  funext p
  simp only [mulVec, dotProduct, springMatrix, of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Twice the potential energy: `u · K u = Σ κ_ab ((uₐ − u_b) · (rₐ − r_b))²`. -/
theorem dotProduct_springMatrix_mulVec (r : ι → Fin 3 → ℝ) (κ : ι → ι → ℝ)
    (u : ι × Fin 3 → ℝ) :
    u ⬝ᵥ (springMatrix r κ *ᵥ u) = ∑ a, ∑ b, κ a b * (bondVector r a b ⬝ᵥ u) ^ 2 := by
  rw [springMatrix_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm u]
  ring

/-- For positive stiffnesses, the displacements annihilated by `K` are those
that stretch no bond. -/
theorem springMatrix_mulVec_eq_zero_iff (r : ι → Fin 3 → ℝ) {κ : ι → ι → ℝ}
    (hκ : ∀ a b, 0 < κ a b) (u : ι × Fin 3 → ℝ) :
    springMatrix r κ *ᵥ u = 0 ↔ ∀ a b, bondVector r a b ⬝ᵥ u = 0 := by
  constructor
  · intro h a b
    have hq := dotProduct_springMatrix_mulVec r κ u
    rw [h, dotProduct_zero] at hq
    have hnn : ∀ a ∈ Finset.univ, 0 ≤ ∑ b, κ a b * (bondVector r a b ⬝ᵥ u) ^ 2 := fun a _ =>
      Finset.sum_nonneg fun b _ => mul_nonneg (hκ a b).le (sq_nonneg _)
    have ha := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hq.symm a (Finset.mem_univ a)
    have hb := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => mul_nonneg (hκ a b).le (sq_nonneg _))).mp ha b (Finset.mem_univ b)
    rcases mul_eq_zero.mp hb with h0 | h0
    · exact absurd h0 (hκ a b).ne'
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h0
  · intro h
    rw [springMatrix_mulVec]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [h a b, mul_zero, zero_smul]

omit [DecidableEq ι] in
theorem mem_modeSpace_zero {M K : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} {u : ι × Fin 3 → ℝ} :
    u ∈ modeSpace M K 0 ↔ K *ᵥ u = 0 := by
  rw [mem_modeSpace, zero_smul]

/-- A rigid displacement stretches no bond. -/
theorem bondVector_dotProduct_rigidMap (r : ι → Fin 3 → ℝ) (a b : ι)
    (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : bondVector r a b ⬝ᵥ rigidMap r x = 0 := by
  rw [bondVector_dotProduct, atom_rigidMap, atom_rigidMap, add_sub_add_left_eq_sub, ← map_sub,
    dot_cross_self]

/-- The rigid displacements are modes of frequency zero. -/
theorem rigidMap_mem_modeSpace_zero (m : ι → ℝ) (r : ι → Fin 3 → ℝ) {κ : ι → ι → ℝ}
    (hκ : ∀ a b, 0 < κ a b) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    rigidMap r x ∈ modeSpace (massMatrix m) (springMatrix r κ) 0 :=
  mem_modeSpace_zero.mpr ((springMatrix_mulVec_eq_zero_iff r hκ _).mpr fun a b =>
    bondVector_dotProduct_rigidMap r a b x)

/-! ### Symmetry -/

section Symmetry

variable {G : Type*} [Group G] {O : G →* Matrix (Fin 3) (Fin 3) ℝ} {π : G →* Equiv.Perm ι}
  {r : ι → Fin 3 → ℝ}

/-- The group permutes the bonds of a symmetric configuration. -/
theorem displacementRep_bondVector (hr : ∀ g a, O g *ᵥ r a = r (π g a)) (g : G) (a b : ι) :
    displacementRep O π g (bondVector r a b) = bondVector r (π g a) (π g b) := by
  refine atom_ext fun c => ?_
  rw [atom_displacementRep, atom_bondVector, atom_bondVector, mulVec_smul, mulVec_sub, hr, hr]
  simp only [Equiv.Perm.inv_eq_iff_eq]

/-- The stretching of a bond after a symmetry is the stretching of the bond it
comes from. -/
theorem bondVector_dotProduct_displacementRep (hO : ∀ g, (O g)ᵀ * O g = 1)
    (hr : ∀ g a, O g *ᵥ r a = r (π g a)) (g : G) (a b : ι) (u : ι × Fin 3 → ℝ) :
    bondVector r (π g a) (π g b) ⬝ᵥ displacementRep O π g u = bondVector r a b ⬝ᵥ u := by
  have hinv (d : ι) : (π g)⁻¹ (π g d) = d := (π g).symm_apply_apply d
  rw [bondVector_dotProduct, bondVector_dotProduct, atom_displacementRep, atom_displacementRep,
    hinv, hinv, ← hr, ← hr, ← mulVec_sub, ← mulVec_sub,
    Rigid.mulVec_dotProduct_mulVec (hO g)]

/-- A group of symmetries of the configuration that preserves the masses and
the stiffnesses acts on the displacements by symmetries of the oscillations. -/
theorem isSymmetryRep_spring (hO : ∀ g, (O g)ᵀ * O g = 1)
    (hr : ∀ g a, O g *ᵥ r a = r (π g a)) {m : ι → ℝ} (hm : ∀ g a, m (π g a) = m a)
    {κ : ι → ι → ℝ} (hκ : ∀ g a b, κ (π g a) (π g b) = κ a b) :
    IsSymmetryRep (displacementRep O π) (massMatrix m) (springMatrix r κ) where
  mass g u := by
    refine atom_ext fun c => ?_
    have hmc : m ((π g)⁻¹ c) = m c := by
      rw [← hm g ((π g)⁻¹ c)]
      exact congrArg m ((π g).apply_symm_apply c)
    rw [atom_massMatrix_mulVec, atom_displacementRep, atom_displacementRep,
      atom_massMatrix_mulVec, mulVec_smul, hmc]
  stiffness g u := by
    rw [springMatrix_mulVec, springMatrix_mulVec, map_sum]
    rw [← Equiv.sum_comp (π g)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum, ← Equiv.sum_comp (π g)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hκ, bondVector_dotProduct_displacementRep hO hr, map_smul,
      displacementRep_bondVector hr]

end Symmetry

end ProjectAinos.Mechanics.Molecule
