/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.Mechanics.Oscillations.Triatomic

/-! Typed contracts for the symmetry of the vibrations of a molecule: the
decomposition into the spaces of the modes, representations by symmetries and
the number of the modes of a symmetry type, the representation on the
displacements of the atoms with its character, the rigid displacements, the
model with springs along the bonds, and the molecules of three atoms. These
examples use default elaborator options. -/

open ProjectAinos ProjectAinos.Mechanics ProjectAinos.Mechanics.NormalModes
open ProjectAinos.Mechanics.Molecule
open Matrix Module
open scoped Kronecker

noncomputable section

section SymmetryTypes

variable {n : Type*} [Fintype n] [DecidableEq n] {G : Type*} [Group G] {M K S : Matrix n n ℝ}
  {lam : n → ℝ} {ρ : Representation ℝ G (n → ℝ)}

example (hSM : Sᵀ * M * S = 1) (c : ℝ) :
    modeSpace M K c = End.eigenspace (toLin' (S * Sᵀ * K)) c :=
  modeSpace_eq_eigenspace hSM c

example (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (a : n) :
    S *ᵥ Pi.single a 1 ∈ modeSpace M K (lam a) :=
  mulVec_single_mem_modeSpace hSM hSK a

example (hSM : Sᵀ * M * S = 1) (s : Finset ℝ) :
    iSupIndep fun c : s => modeSpace M K c :=
  iSupIndep_modeSpace hSM s

example (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam) :
    ⨆ c : (Finset.univ.image lam), modeSpace M K c = ⊤ :=
  iSup_modeSpace_eq_top hSM hSK

example (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam) :
    DirectSum.IsInternal fun c : (Finset.univ.image lam) => modeSpace M K c :=
  isInternal_modeSpace hSM hSK

example (M K : Matrix n n ℝ) (c : ℝ) :
    modeSpace M K c = LinearMap.ker (K - c • M).mulVecLin :=
  modeSpace_eq_ker M K c

example (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam) (c : ℝ) :
    finrank ℝ (modeSpace M K c) = Fintype.card {a // lam a = c} :=
  finrank_modeSpace hSM hSK c

example (h : IsSymmetryRep ρ M K) (g : G) (v : n → ℝ) : M *ᵥ ρ g v = ρ g (M *ᵥ v) :=
  h.mass g v

example (h : IsSymmetryRep ρ M K) (g : G) (v : n → ℝ) : K *ᵥ ρ g v = ρ g (K *ᵥ v) :=
  h.stiffness g v

example (M K : Matrix n n ℝ) :
    IsSymmetryRep (1 : Representation ℝ G (n → ℝ)) M K :=
  isSymmetryRep_one M K

example (h : IsSymmetryRep ρ M K) (c : ℝ) :
    (modeSubrep h c).toSubmodule = modeSpace M K c := rfl

example (h : IsSymmetryRep ρ M K) (c : ℝ) :
    modeRep h c =
      (modeSubrep h c).toRepresentation := rfl

example (h : IsSymmetryRep ρ M K) (c : ℝ) (g : G)
    (v : modeSpace M K c) :
    (modeRep h c g v : n → ℝ) = ρ g v :=
  coe_modeRep_apply h c g v

example (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (h : IsSymmetryRep ρ M K) (g : G) :
    ρ.character g = ∑ c ∈ Finset.univ.image lam, (modeRep h c).character g :=
  character_eq_sum_modeRep hSM hSK h g

example [Fintype G] {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam) (h : IsSymmetryRep ρ M K) (σ : Representation ℝ G W) :
    ∑ c ∈ Finset.univ.image lam,
        (finrank ℝ (Representation.IntertwiningMap σ (modeRep h c)) : ℝ) =
      (Nat.card G : ℝ)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ :=
  sum_finrank_intertwiningMap_modeRep hSM hSK h σ

example [Fintype G] {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam) (h : IsSymmetryRep ρ M K) (σ : Representation ℝ G W) :
    (finrank ℝ (Representation.IntertwiningMap σ ρ) : ℝ) =
      ∑ c ∈ Finset.univ.image lam,
        (finrank ℝ (Representation.IntertwiningMap σ (modeRep h c)) : ℝ) :=
  finrank_intertwiningMap_eq_sum hSM hSK h σ

end SymmetryTypes

section Molecule

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [Group G]
  {M K S : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} {lam : ι × Fin 3 → ℝ}
  {O : G →* Matrix (Fin 3) (Fin 3) ℝ} {π : G →* Equiv.Perm ι} {r : ι → Fin 3 → ℝ}

example (u : ι × Fin 3 → ℝ) (a : ι) :
    atom u a =
      fun j => u (a, j) := rfl

example {u v : ι × Fin 3 → ℝ} (h : ∀ a, atom u a = atom v a) :
    u = v :=
  atom_ext h

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (π : G →* Equiv.Perm ι) (g : G) :
    displacementMatrix O π g =
      Matrix.permMatrixHom (R := ℝ) (π g) ⊗ₖ O g := rfl

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (π : G →* Equiv.Perm ι) :
    displacementMatrix O π 1 = 1 :=
  displacementMatrix_one O π

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (π : G →* Equiv.Perm ι)
    (g h : G) :
    displacementMatrix O π (g * h) = displacementMatrix O π g * displacementMatrix O π h :=
  displacementMatrix_mul O π g h

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (π : G →* Equiv.Perm ι) (g : G) :
    displacementRep O π g = toLin' (displacementMatrix O π g) := rfl

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (π : G →* Equiv.Perm ι)
    (g : G) (u : ι × Fin 3 → ℝ) (a : ι) :
    atom (displacementRep O π g u) a = O g *ᵥ atom u ((π g)⁻¹ a) :=
  atom_displacementRep O π g u a

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ)
    (π : G →* Equiv.Perm ι) (g : G) :
    (displacementRep O π).character g =
      ((Function.fixedPoints (π g)).ncard : ℝ) * (O g).trace :=
  character_displacementRep O π g

example (r : ι → Fin 3 → ℝ) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (p : ι × Fin 3) :
    rigidMap r x p = (x.1 + x.2 ⨯₃ r p.1) p.2 := rfl

example (r : ι → Fin 3 → ℝ) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (a : ι) :
    atom (rigidMap r x) a = x.1 + x.2 ⨯₃ r a :=
  atom_rigidMap r x a

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (g : G) :
    vectorRep O g = toLin' (O g) := rfl

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (g : G) :
    axialRep O g = toLin' ((O g).det • O g) := rfl

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ) :
    rigidRep O =
      (vectorRep O).prod (axialRep O) := rfl

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (g : G) :
    (rigidRep O).character g = (1 + (O g).det) * (O g).trace :=
  character_rigidRep O g

example {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1)
    (x y : Fin 3 → ℝ) :
    A *ᵥ (x ⨯₃ y) = A.det • ((A *ᵥ x) ⨯₃ (A *ᵥ y)) :=
  mulVec_cross_of_orthogonal hA x y

example {O : G →* Matrix (Fin 3) (Fin 3) ℝ} {π : G →* Equiv.Perm ι}
    {r : ι → Fin 3 → ℝ} (hO : ∀ g, (O g)ᵀ * O g = 1) (hr : ∀ g a, O g *ᵥ r a = r (π g a))
    (g : G) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    displacementRep O π g (rigidMap r x) = rigidMap r (rigidRep O g x) :=
  displacementRep_rigidMap hO hr g x

example (h : IsSymmetryRep (displacementRep O π) M K) (hO : ∀ g, (O g)ᵀ * O g = 1)
    (hr : ∀ g a, O g *ᵥ r a = r (π g a)) (hinj : Function.Injective (rigidMap r))
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) :
    Representation.Equiv (rigidRep O) (modeRep h 0) :=
  rigidEquiv h hO hr hinj hzero

example (h : IsSymmetryRep (displacementRep O π) M K)
    (hO : ∀ g, (O g)ᵀ * O g = 1) (hr : ∀ g a, O g *ᵥ r a = r (π g a))
    (hinj : Function.Injective (rigidMap r))
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) (g : G) :
    (modeRep h 0).character g = (1 + (O g).det) * (O g).trace :=
  character_modeRep_zero h hO hr hinj hzero g

example (hinj : Function.Injective (rigidMap r))
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) :
    finrank ℝ (modeSpace M K 0) = 6 :=
  finrank_modeSpace_zero hinj hzero

example (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam)
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) :
    Fintype.card {p // lam p ≠ 0} + finrank ℝ (LinearMap.range (rigidMap r)) =
      3 * Fintype.card ι :=
  card_vibration_add_finrank_range hSM hSK hzero

example (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (hinj : Function.Injective (rigidMap r))
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) :
    Fintype.card {p // lam p ≠ 0} + 6 = 3 * Fintype.card ι :=
  card_vibration_add_six hSM hSK hinj hzero

example [Fintype G] {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (h : IsSymmetryRep (displacementRep O π) M K) (hO : ∀ g, (O g)ᵀ * O g = 1)
    (hr : ∀ g a, O g *ᵥ r a = r (π g a)) (hinj : Function.Injective (rigidMap r))
    (hzero : LinearMap.range (rigidMap r) = modeSpace M K 0) (σ : Representation ℝ G W) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap σ (modeRep h c)) : ℝ) =
      (Nat.card G : ℝ)⁻¹ * ∑ g : G,
        (((Function.fixedPoints (π g)).ncard : ℝ) - 1 - (O g).det) * (O g).trace *
          σ.character g⁻¹ :=
  sum_finrank_vibration hSM hSK h hO hr hinj hzero σ

end Molecule

section SpringMolecule

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [Group G]
  {O : G →* Matrix (Fin 3) (Fin 3) ℝ} {π : G →* Equiv.Perm ι} {r : ι → Fin 3 → ℝ}

example (m : ι → ℝ) :
    massMatrix m =
      diagonal fun p => m p.1 := rfl

example (m : ι → ℝ) (u : ι × Fin 3 → ℝ) (a : ι) :
    atom (massMatrix m *ᵥ u) a = m a • atom u a :=
  atom_massMatrix_mulVec m u a

example {m : ι → ℝ} (hm : ∀ a, 0 < m a) :
    (massMatrix m).PosDef :=
  posDef_massMatrix hm

example (r : ι → Fin 3 → ℝ) (a b : ι) :
    bondVector r a b =
      fun p => ((if p.1 = a then 1 else 0) - (if p.1 = b then 1 else 0)) *
        (r a p.2 - r b p.2) := rfl

example (r : ι → Fin 3 → ℝ) (a b c : ι) :
    atom (bondVector r a b) c =
      (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ)) • (r a - r b) :=
  atom_bondVector r a b c

example (r : ι → Fin 3 → ℝ) (a b : ι) (u : ι × Fin 3 → ℝ) :
    bondVector r a b ⬝ᵥ u = (r a - r b) ⬝ᵥ (atom u a - atom u b) :=
  bondVector_dotProduct r a b u

example (r : ι → Fin 3 → ℝ) (κ : ι → ι → ℝ) :
    springMatrix r κ =
      Matrix.of fun p q => ∑ a, ∑ b, κ a b * (bondVector r a b p * bondVector r a b q) := rfl

example (r : ι → Fin 3 → ℝ) (κ : ι → ι → ℝ) :
    (springMatrix r κ)ᵀ = springMatrix r κ :=
  transpose_springMatrix r κ

example (r : ι → Fin 3 → ℝ) (κ : ι → ι → ℝ) (u : ι × Fin 3 → ℝ) :
    springMatrix r κ *ᵥ u =
      ∑ a, ∑ b, (κ a b * (bondVector r a b ⬝ᵥ u)) • bondVector r a b :=
  springMatrix_mulVec r κ u

example (r : ι → Fin 3 → ℝ) (κ : ι → ι → ℝ)
    (u : ι × Fin 3 → ℝ) :
    u ⬝ᵥ (springMatrix r κ *ᵥ u) = ∑ a, ∑ b, κ a b * (bondVector r a b ⬝ᵥ u) ^ 2 :=
  dotProduct_springMatrix_mulVec r κ u

example (r : ι → Fin 3 → ℝ) {κ : ι → ι → ℝ}
    (hκ : ∀ a b, 0 < κ a b) (u : ι × Fin 3 → ℝ) :
    springMatrix r κ *ᵥ u = 0 ↔ ∀ a b, bondVector r a b ⬝ᵥ u = 0 :=
  springMatrix_mulVec_eq_zero_iff r hκ u

example {M K : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} {u : ι × Fin 3 → ℝ} :
    u ∈ modeSpace M K 0 ↔ K *ᵥ u = 0 :=
  mem_modeSpace_zero

example (r : ι → Fin 3 → ℝ) (a b : ι)
    (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    bondVector r a b ⬝ᵥ rigidMap r x = 0 :=
  bondVector_dotProduct_rigidMap r a b x

example (m : ι → ℝ) (r : ι → Fin 3 → ℝ) {κ : ι → ι → ℝ}
    (hκ : ∀ a b, 0 < κ a b) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    rigidMap r x ∈ modeSpace (massMatrix m) (springMatrix r κ) 0 :=
  rigidMap_mem_modeSpace_zero m r hκ x

example (hr : ∀ g a, O g *ᵥ r a = r (π g a)) (g : G) (a b : ι) :
    displacementRep O π g (bondVector r a b) = bondVector r (π g a) (π g b) :=
  displacementRep_bondVector hr g a b

example (hO : ∀ g, (O g)ᵀ * O g = 1)
    (hr : ∀ g a, O g *ᵥ r a = r (π g a)) (g : G) (a b : ι) (u : ι × Fin 3 → ℝ) :
    bondVector r (π g a) (π g b) ⬝ᵥ displacementRep O π g u = bondVector r a b ⬝ᵥ u :=
  bondVector_dotProduct_displacementRep hO hr g a b u

example (hO : ∀ g, (O g)ᵀ * O g = 1)
    (hr : ∀ g a, O g *ᵥ r a = r (π g a)) {m : ι → ℝ} (hm : ∀ g a, m (π g a) = m a)
    {κ : ι → ι → ℝ} (hκ : ∀ g a b, κ (π g a) (π g b) = κ a b) :
    IsSymmetryRep (displacementRep O π) (massMatrix m) (springMatrix r κ) :=
  isSymmetryRep_spring hO hr hm hκ

end SpringMolecule

section Triangle

variable {r : Fin 3 → Fin 3 → ℝ} {m : Fin 3 → ℝ} {κ : Fin 3 → Fin 3 → ℝ}
  {S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ} {lam : Fin 3 × Fin 3 → ℝ}
  {G : Type*} [Group G] {O : G →* Matrix (Fin 3) (Fin 3) ℝ} {π : G →* Equiv.Perm (Fin 3)}

example (w p q : Fin 3 → ℝ) :
    ((p ⨯₃ q) ⬝ᵥ (p ⨯₃ q)) • w =
      ((w ⨯₃ q) ⬝ᵥ (p ⨯₃ q)) • p - ((w ⨯₃ p) ⬝ᵥ (p ⨯₃ q)) • q +
        ((w ⨯₃ p) ⬝ᵥ q) • (p ⨯₃ q) :=
  smul_eq_of_cross w p q

example (d e p q : Fin 3 → ℝ) :
    ((e ⬝ᵥ (p ⨯₃ q)) • p - (d ⬝ᵥ (p ⨯₃ q)) • q + (d ⬝ᵥ q) • (p ⨯₃ q)) ⨯₃ p =
      ((p ⨯₃ q) ⬝ᵥ (p ⨯₃ q)) • d - (d ⬝ᵥ p) • ((q ⬝ᵥ q) • p - (q ⬝ᵥ p) • q) :=
  cross_left_identity d e p q

example (d e p q : Fin 3 → ℝ) :
    ((e ⬝ᵥ (p ⨯₃ q)) • p - (d ⬝ᵥ (p ⨯₃ q)) • q + (d ⬝ᵥ q) • (p ⨯₃ q)) ⨯₃ q =
      ((p ⨯₃ q) ⬝ᵥ (p ⨯₃ q)) • e + (d ⬝ᵥ q + e ⬝ᵥ p) • ((p ⨯₃ q) ⨯₃ q) -
        (e ⬝ᵥ q) • ((p ⬝ᵥ p) • q - (p ⬝ᵥ q) • p) :=
  cross_right_identity d e p q

example (hn : (r 1 - r 0) ⨯₃ (r 2 - r 0) ≠ 0) :
    Function.Injective (rigidMap r) :=
  rigidMap_injective hn

example (hn : (r 1 - r 0) ⨯₃ (r 2 - r 0) ≠ 0) {u : Fin 3 × Fin 3 → ℝ}
    (h : ∀ a b, bondVector r a b ⬝ᵥ u = 0) :
    ∃ x, rigidMap r x = u :=
  exists_rigidMap_eq hn h

example (m : Fin 3 → ℝ)
    (hn : (r 1 - r 0) ⨯₃ (r 2 - r 0) ≠ 0) {κ : Fin 3 → Fin 3 → ℝ} (hκ : ∀ a b, 0 < κ a b) :
    LinearMap.range (rigidMap r) = modeSpace (massMatrix m) (springMatrix r κ) 0 :=
  range_rigidMap_eq_modeSpace_zero m hn hκ

example (hn : (r 1 - r 0) ⨯₃ (r 2 - r 0) ≠ 0)
    (hκ : ∀ a b, 0 < κ a b) (hSM : Sᵀ * massMatrix m * S = 1)
    (hSK : Sᵀ * springMatrix r κ * S = diagonal lam) :
    Fintype.card {p // lam p ≠ 0} = 3 :=
  card_vibration_triatomic hn hκ hSM hSK

example [Fintype G] {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (hO : ∀ g, (O g)ᵀ * O g = 1)
    (hr : ∀ g a, O g *ᵥ r a = r (π g a)) (hm : ∀ g a, m (π g a) = m a)
    (hκs : ∀ g a b, κ (π g a) (π g b) = κ a b) (hn : (r 1 - r 0) ⨯₃ (r 2 - r 0) ≠ 0)
    (hκ : ∀ a b, 0 < κ a b) (hSM : Sᵀ * massMatrix m * S = 1)
    (hSK : Sᵀ * springMatrix r κ * S = diagonal lam) (σ : Representation ℝ G W) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap σ
          (modeRep (isSymmetryRep_spring hO hr hm hκs) c)) : ℝ) =
      (Nat.card G : ℝ)⁻¹ * ∑ g : G,
        (((Function.fixedPoints (π g)).ncard : ℝ) - 1 - (O g).det) * (O g).trace *
          σ.character g⁻¹ :=
  sum_finrank_vibration_triatomic hO hr hm hκs hn hκ hSM hSK σ

end Triangle

section Scalar

variable {G : Type*} [Group G]

example (χ : G →* ℝ) (g : G) : scalarRep χ g = χ g • LinearMap.id := rfl

example (χ : G →* ℝ) (g : G) :
    (scalarRep χ).character g = χ g :=
  character_scalarRep χ g

example (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (g : G) :
    (vectorRep O).character g = (O g).trace :=
  character_vectorRep O g

example (g : Equiv.Perm (Fin 3)) :
    fixCount g =
      (Finset.univ.filter fun a => g a = a).card := rfl

example (g : Equiv.Perm (Fin 3)) :
    (Function.fixedPoints ⇑g).ncard = fixCount g :=
  ncard_fixedPoints g

end Scalar

section Equilateral

open ProjectAinos.Mechanics.Molecule.Equilateral

variable {μ k : ℝ} {S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ} {lam : Fin 3 × Fin 3 → ℝ}

example : Equilateral.position = fun a => Pi.single a 1 := rfl

example :
    Equilateral.signHom =
      (Int.castRingHom ℝ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign) := rfl

example (g : Equiv.Perm (Fin 3)) :
    signHom g = ((Equiv.Perm.sign g : ℤ) : ℝ) :=
  Equilateral.signHom_apply g

example (g : Equiv.Perm (Fin 3)) :
    (permMatrixHom (R := ℝ) g)ᵀ * permMatrixHom g = 1 :=
  Equilateral.transpose_mul_permMatrixHom g

example (g : Equiv.Perm (Fin 3)) (a : Fin 3) :
    permMatrixHom (R := ℝ) g *ᵥ position a = position (MonoidHom.id _ g a) :=
  Equilateral.permMatrixHom_mulVec_position g a

example :
    (position 1 - position 0) ⨯₃ (position 2 - position 0) ≠ 0 :=
  Equilateral.not_collinear

example (g : Equiv.Perm (Fin 3)) :
    (permMatrixHom (R := ℝ) g).trace = (fixCount g⁻¹ : ℝ) :=
  Equilateral.trace_permMatrixHom g

example (g : Equiv.Perm (Fin 3)) :
    (permMatrixHom (R := ℝ) g).det = ((Equiv.Perm.sign g⁻¹ : ℤ) : ℝ) :=
  Equilateral.det_permMatrixHom g

example (μ k : ℝ) :
    IsSymmetryRep (displacementRep (permMatrixHom (R := ℝ)) (MonoidHom.id _))
      (massMatrix fun _ => μ) (springMatrix position fun _ _ => k) :=
  Equilateral.isSymmetryRep μ k

example (hk : 0 < k) (hSM : Sᵀ * (massMatrix fun _ => μ) * S = 1)
    (hSK : Sᵀ * (springMatrix position fun _ _ => k) * S = diagonal lam) {W : Type*}
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (σ : Representation ℝ (Equiv.Perm (Fin 3)) W) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap σ (modeRep (isSymmetryRep μ k) c)) : ℝ) =
      (6 : ℝ)⁻¹ * ∑ g : Equiv.Perm (Fin 3),
        ((fixCount g : ℝ) - 1 - ((Equiv.Perm.sign g⁻¹ : ℤ) : ℝ)) * (fixCount g⁻¹ : ℝ) *
          σ.character g⁻¹ :=
  Equilateral.sum_finrank hk hSM hSK σ

example (hk : 0 < k) (hSM : Sᵀ * (massMatrix fun _ => μ) * S = 1)
    (hSK : Sᵀ * (springMatrix position fun _ _ => k) * S = diagonal lam) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap (scalarRep 1)
          (modeRep (isSymmetryRep μ k) c)) : ℝ) = 1 :=
  Equilateral.sum_finrank_trivial hk hSM hSK

example (hk : 0 < k) (hSM : Sᵀ * (massMatrix fun _ => μ) * S = 1)
    (hSK : Sᵀ * (springMatrix position fun _ _ => k) * S = diagonal lam) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap (scalarRep signHom)
          (modeRep (isSymmetryRep μ k) c)) : ℝ) = 0 :=
  Equilateral.sum_finrank_sign hk hSM hSK

example (hk : 0 < k) (hSM : Sᵀ * (massMatrix fun _ => μ) * S = 1)
    (hSK : Sᵀ * (springMatrix position fun _ _ => k) * S = diagonal lam) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap (vectorRep (permMatrixHom (R := ℝ)))
          (modeRep (isSymmetryRep μ k) c)) : ℝ) = 2 :=
  Equilateral.sum_finrank_permutation hk hSM hSK

example (hμ : 0 < μ) (k : ℝ) :
    ∃ (S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ) (lam : Fin 3 × Fin 3 → ℝ),
      Sᵀ * (massMatrix fun _ => μ) * S = 1 ∧
        Sᵀ * (springMatrix position fun _ _ => k) * S = diagonal lam :=
  Equilateral.exists_diagonalization hμ k

end Equilateral

section Isosceles

open ProjectAinos.Mechanics.Molecule.Isosceles

variable {h d m₀ m₁ k₁ k₂ : ℝ} {S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ}
  {lam : Fin 3 × Fin 3 → ℝ}

example (h d : ℝ) :
    Isosceles.position h d = ![![0, h, 0], ![d, 0, 0], ![-d, 0, 0]] := rfl

example :
    Isosceles.unitHom =
      (Int.castRingHom ℝ).toMonoidHom.comp (Units.coeHom ℤ) := rfl

example (u : ℤˣ) :
    unitHom u = ((u : ℤ) : ℝ) :=
  Isosceles.unitHom_apply u

example (u : ℤˣ) :
    unitHom u * unitHom u = 1 :=
  Isosceles.unitHom_mul_self u

example :
    diagonal ![(1 : ℝ), 1, 1] = 1 :=
  Isosceles.diagonal_ones

example (g : ℤˣ × ℤˣ) :
    rot g = diagonal ![unitHom g.1, 1, unitHom g.2] :=
  Isosceles.rot_apply g

example (g : ℤˣ × ℤˣ) :
    perm g = if g.1 = 1 then 1 else Equiv.swap 1 2 :=
  Isosceles.perm_apply g

example (g : ℤˣ × ℤˣ) :
    (rot g)ᵀ * rot g = 1 :=
  Isosceles.transpose_mul_rot g

example (h d : ℝ) (g : ℤˣ × ℤˣ) (a : Fin 3) :
    rot g *ᵥ position h d a = position h d (perm g a) :=
  Isosceles.rot_mulVec_position h d g a

example {h d : ℝ} (hh : h ≠ 0) (hd : d ≠ 0) :
    (position h d 1 - position h d 0) ⨯₃ (position h d 2 - position h d 0) ≠ 0 :=
  Isosceles.not_collinear hh hd

example (m₀ m₁ : ℝ) :
    Isosceles.mass m₀ m₁ =
      ![m₀, m₁, m₁] := rfl

example (k₁ k₂ : ℝ) :
    Isosceles.stiffness k₁ k₂ =
      fun a b => if a = 0 ∨ b = 0 then k₁ else k₂ := rfl

example (g : ℤˣ × ℤˣ) (a : Fin 3) :
    perm g a = 0 ↔ a = 0 :=
  Isosceles.perm_apply_eq_zero g a

example (m₀ m₁ : ℝ) (g : ℤˣ × ℤˣ) (a : Fin 3) :
    mass m₀ m₁ (perm g a) = mass m₀ m₁ a :=
  Isosceles.mass_perm m₀ m₁ g a

example (k₁ k₂ : ℝ) (g : ℤˣ × ℤˣ) (a b : Fin 3) :
    stiffness k₁ k₂ (perm g a) (perm g b) = stiffness k₁ k₂ a b :=
  Isosceles.stiffness_perm k₁ k₂ g a b

example {k₁ k₂ : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (a b : Fin 3) :
    0 < stiffness k₁ k₂ a b :=
  Isosceles.stiffness_pos h₁ h₂ a b

example (h d m₀ m₁ k₁ k₂ : ℝ) :
    IsSymmetryRep (displacementRep rot perm) (massMatrix (mass m₀ m₁))
      (springMatrix (position h d) (stiffness k₁ k₂)) :=
  Isosceles.isSymmetryRep h d m₀ m₁ k₁ k₂

example (f : ℤˣ → ℝ) :
    ∑ u, f u = f 1 + f (-1) :=
  Isosceles.sum_units_int f

example (g : ℤˣ × ℤˣ) :
    (rot g).trace = unitHom g.1 + 1 + unitHom g.2 :=
  Isosceles.trace_rot g

example (g : ℤˣ × ℤˣ) :
    (rot g).det = unitHom g.1 * unitHom g.2 :=
  Isosceles.det_rot g

example (hh : h ≠ 0) (hd : d ≠ 0) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hSM : Sᵀ * massMatrix (mass m₀ m₁) * S = 1)
    (hSK : Sᵀ * springMatrix (position h d) (stiffness k₁ k₂) * S = diagonal lam)
    (χ : ℤˣ × ℤˣ →* ℝ) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap (scalarRep χ)
          (modeRep (isSymmetryRep h d m₀ m₁ k₁ k₂) c)) : ℝ) =
      (3 * χ (1, 1) + 3 * χ (1, -1) + χ (-1, 1) + χ (-1, -1)) / 4 :=
  Isosceles.sum_finrank hh hd h₁ h₂ hSM hSK χ

example (hh : h ≠ 0) (hd : d ≠ 0) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hSM : Sᵀ * massMatrix (mass m₀ m₁) * S = 1)
    (hSK : Sᵀ * springMatrix (position h d) (stiffness k₁ k₂) * S = diagonal lam) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap (scalarRep 1)
          (modeRep (isSymmetryRep h d m₀ m₁ k₁ k₂) c)) : ℝ) = 2 :=
  Isosceles.sum_finrank_symmetric hh hd h₁ h₂ hSM hSK

example (hh : h ≠ 0) (hd : d ≠ 0) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hSM : Sᵀ * massMatrix (mass m₀ m₁) * S = 1)
    (hSK : Sᵀ * springMatrix (position h d) (stiffness k₁ k₂) * S = diagonal lam) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap
          (scalarRep (unitHom.comp (MonoidHom.fst ℤˣ ℤˣ)))
          (modeRep (isSymmetryRep h d m₀ m₁ k₁ k₂) c)) : ℝ) = 1 :=
  Isosceles.sum_finrank_antisymmetric hh hd h₁ h₂ hSM hSK

example (hh : h ≠ 0) (hd : d ≠ 0) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hSM : Sᵀ * massMatrix (mass m₀ m₁) * S = 1)
    (hSK : Sᵀ * springMatrix (position h d) (stiffness k₁ k₂) * S = diagonal lam)
    (χ : ℤˣ →* ℝ) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap
          (scalarRep ((χ.comp (MonoidHom.fst ℤˣ ℤˣ)) * unitHom.comp (MonoidHom.snd ℤˣ ℤˣ)))
          (modeRep (isSymmetryRep h d m₀ m₁ k₁ k₂) c)) : ℝ) = 0 :=
  Isosceles.sum_finrank_plane hh hd h₁ h₂ hSM hSK χ

example (h d : ℝ) (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) (k₁ k₂ : ℝ) :
    ∃ (S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ) (lam : Fin 3 × Fin 3 → ℝ),
      Sᵀ * massMatrix (mass m₀ m₁) * S = 1 ∧
        Sᵀ * springMatrix (position h d) (stiffness k₁ k₂) * S = diagonal lam :=
  Isosceles.exists_diagonalization h d hm₀ hm₁ k₁ k₂

end Isosceles
