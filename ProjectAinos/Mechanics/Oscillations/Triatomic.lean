/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Oscillations.SpringMolecule
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The vibrations of a molecule of three atoms

Three atoms that are not on a line, with a spring along each of the three
bonds (Landau–Lifshitz §24).

* `rigidMap_injective`, `exists_rigidMap_eq`: the translations and rotations
  of the triangle are six independent displacements, and a displacement that
  stretches no bond is one of them. Hence the modes of frequency zero are the
  rigid displacements (`range_rigidMap_eq_modeSpace_zero`), and there are
  three modes of non-zero frequency (`card_vibration_triatomic`).
* `sum_finrank_vibration_triatomic`: for a group of symmetries of the
  molecule, the number of the vibrations of a symmetry type is the scalar
  product of its character with `(N_g − 1 − det O_g) tr O_g`.
* `Equilateral`: three equal atoms at the corners of an equilateral triangle,
  with the group of the permutations of the corners. The vibrations contain
  the trivial representation once, the sign representation never, and the
  permutation representation twice: one totally symmetric vibration and one
  pair of the two-dimensional type.
* `Isosceles`: an isosceles molecule with its group of four symmetries. Two
  vibrations are symmetric under both reflections, one changes sign under the
  reflection that exchanges the two atoms of the base, and none changes sign
  under the reflection in the plane of the molecule.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Mechanics.Molecule

open Matrix Module NormalModes

/-! ### Identities of the cross product -/

/-- A vector is determined by its cross products with two vectors that are not
parallel. -/
theorem smul_eq_of_cross (w p q : Fin 3 → ℝ) :
    ((p ⨯₃ q) ⬝ᵥ (p ⨯₃ q)) • w =
      ((w ⨯₃ q) ⬝ᵥ (p ⨯₃ q)) • p - ((w ⨯₃ p) ⬝ᵥ (p ⨯₃ q)) • q +
        ((w ⨯₃ p) ⬝ᵥ q) • (p ⨯₃ q) := by
  ext i
  fin_cases i <;> simp [cross_apply, dotProduct, Fin.sum_univ_three] <;> ring

theorem cross_left_identity (d e p q : Fin 3 → ℝ) :
    ((e ⬝ᵥ (p ⨯₃ q)) • p - (d ⬝ᵥ (p ⨯₃ q)) • q + (d ⬝ᵥ q) • (p ⨯₃ q)) ⨯₃ p =
      ((p ⨯₃ q) ⬝ᵥ (p ⨯₃ q)) • d - (d ⬝ᵥ p) • ((q ⬝ᵥ q) • p - (q ⬝ᵥ p) • q) := by
  ext i
  fin_cases i <;>
    simp [cross_apply, dotProduct, Fin.sum_univ_three, vecHead, vecTail] <;> ring

theorem cross_right_identity (d e p q : Fin 3 → ℝ) :
    ((e ⬝ᵥ (p ⨯₃ q)) • p - (d ⬝ᵥ (p ⨯₃ q)) • q + (d ⬝ᵥ q) • (p ⨯₃ q)) ⨯₃ q =
      ((p ⨯₃ q) ⬝ᵥ (p ⨯₃ q)) • e + (d ⬝ᵥ q + e ⬝ᵥ p) • ((p ⨯₃ q) ⨯₃ q) -
        (e ⬝ᵥ q) • ((p ⬝ᵥ p) • q - (p ⬝ᵥ q) • p) := by
  ext i
  fin_cases i <;>
    simp [cross_apply, dotProduct, Fin.sum_univ_three, vecHead, vecTail] <;> ring

/-! ### The rigid displacements of a triangle -/

section Triangle

variable {r : Fin 3 → Fin 3 → ℝ}

/-- The translations and the rotations of three points that are not on a line
are independent. -/
theorem rigidMap_injective (hn : (r 1 - r 0) ⨯₃ (r 2 - r 0) ≠ 0) :
    Function.Injective (rigidMap r) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨t, w⟩ h
  have ha : ∀ a, t + w ⨯₃ r a = 0 := fun a => congrArg (fun u => atom u a) h
  have hsub : ∀ a, w ⨯₃ (r a - r 0) = 0 := fun a => by
    have h1 : w ⨯₃ r a - w ⨯₃ r 0 = (t + w ⨯₃ r a) - (t + w ⨯₃ r 0) := by abel
    rw [map_sub, h1, ha a, ha 0, sub_zero]
  have hnn : ((r 1 - r 0) ⨯₃ (r 2 - r 0)) ⬝ᵥ ((r 1 - r 0) ⨯₃ (r 2 - r 0)) ≠ 0 :=
    fun h0 => hn (dotProduct_self_eq_zero.mp h0)
  have hid := smul_eq_of_cross w (r 1 - r 0) (r 2 - r 0)
  rw [hsub 1, hsub 2] at hid
  simp only [zero_dotProduct, zero_smul, sub_zero, add_zero] at hid
  have hw : w = 0 := (smul_eq_zero.mp hid).resolve_left hnn
  have ht : t = 0 := by
    have h0 := ha 0
    rwa [hw, LinearMap.map_zero₂, add_zero] at h0
  rw [ht, hw]
  rfl

/-- A displacement of three points that are not on a line which stretches none
of the three bonds is a translation and a rotation. -/
theorem exists_rigidMap_eq (hn : (r 1 - r 0) ⨯₃ (r 2 - r 0) ≠ 0) {u : Fin 3 × Fin 3 → ℝ}
    (h : ∀ a b, bondVector r a b ⬝ᵥ u = 0) : ∃ x, rigidMap r x = u := by
  obtain ⟨p, hp⟩ : ∃ p, r 1 = r 0 + p := ⟨r 1 - r 0, by abel⟩
  obtain ⟨q, hq⟩ : ∃ q, r 2 = r 0 + q := ⟨r 2 - r 0, by abel⟩
  obtain ⟨d, hd⟩ : ∃ d, atom u 1 = atom u 0 + d := ⟨atom u 1 - atom u 0, by abel⟩
  obtain ⟨e, he⟩ : ∃ e, atom u 2 = atom u 0 + e := ⟨atom u 2 - atom u 0, by abel⟩
  have h10 := h 1 0
  have h20 := h 2 0
  have h21 := h 2 1
  rw [bondVector_dotProduct, hp, hd, add_sub_cancel_left, add_sub_cancel_left] at h10
  rw [bondVector_dotProduct, hq, he, add_sub_cancel_left, add_sub_cancel_left] at h20
  rw [bondVector_dotProduct, hp, hq, hd, he, add_sub_add_left_eq_sub, add_sub_add_left_eq_sub,
    sub_dotProduct, dotProduct_sub, dotProduct_sub] at h21
  rw [hp, hq, add_sub_cancel_left, add_sub_cancel_left] at hn
  have hnn : (p ⨯₃ q) ⬝ᵥ (p ⨯₃ q) ≠ 0 := fun h0 => hn (dotProduct_self_eq_zero.mp h0)
  have hdp : d ⬝ᵥ p = 0 := by rw [dotProduct_comm]; exact h10
  have heq : e ⬝ᵥ q = 0 := by rw [dotProduct_comm]; exact h20
  have hde : d ⬝ᵥ q + e ⬝ᵥ p = 0 := by
    rw [dotProduct_comm d q, dotProduct_comm e p]
    linarith
  obtain ⟨w, hwp, hwq⟩ : ∃ w : Fin 3 → ℝ, w ⨯₃ p = d ∧ w ⨯₃ q = e := by
    refine ⟨((p ⨯₃ q) ⬝ᵥ (p ⨯₃ q))⁻¹ •
      ((e ⬝ᵥ (p ⨯₃ q)) • p - (d ⬝ᵥ (p ⨯₃ q)) • q + (d ⬝ᵥ q) • (p ⨯₃ q)), ?_, ?_⟩
    · rw [LinearMap.map_smul₂, cross_left_identity, hdp, zero_smul, sub_zero, smul_smul,
        inv_mul_cancel₀ hnn, one_smul]
    · rw [LinearMap.map_smul₂, cross_right_identity, hde, heq, zero_smul, zero_smul, add_zero,
        sub_zero, smul_smul, inv_mul_cancel₀ hnn, one_smul]
  refine ⟨(atom u 0 - w ⨯₃ r 0, w), atom_ext fun a => ?_⟩
  rw [atom_rigidMap]
  fin_cases a
  · change atom u 0 - w ⨯₃ r 0 + w ⨯₃ r 0 = atom u 0
    abel
  · change atom u 0 - w ⨯₃ r 0 + w ⨯₃ r 1 = atom u 1
    rw [hp, hd, map_add, hwp]
    abel
  · change atom u 0 - w ⨯₃ r 0 + w ⨯₃ r 2 = atom u 2
    rw [hq, he, map_add, hwq]
    abel

/-- For three atoms that are not on a line, joined by three springs, the modes
of frequency zero are the rigid displacements. -/
theorem range_rigidMap_eq_modeSpace_zero (m : Fin 3 → ℝ)
    (hn : (r 1 - r 0) ⨯₃ (r 2 - r 0) ≠ 0) {κ : Fin 3 → Fin 3 → ℝ} (hκ : ∀ a b, 0 < κ a b) :
    LinearMap.range (rigidMap r) = modeSpace (massMatrix m) (springMatrix r κ) 0 := by
  ext u
  rw [LinearMap.mem_range, mem_modeSpace_zero, springMatrix_mulVec_eq_zero_iff r hκ]
  constructor
  · rintro ⟨x, rfl⟩ a b
    exact bondVector_dotProduct_rigidMap r a b x
  · exact exists_rigidMap_eq hn

variable {m : Fin 3 → ℝ} {κ : Fin 3 → Fin 3 → ℝ}
  {S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ} {lam : Fin 3 × Fin 3 → ℝ}

/-- A molecule of three atoms that are not on a line has three modes of
non-zero frequency. -/
theorem card_vibration_triatomic (hn : (r 1 - r 0) ⨯₃ (r 2 - r 0) ≠ 0)
    (hκ : ∀ a b, 0 < κ a b) (hSM : Sᵀ * massMatrix m * S = 1)
    (hSK : Sᵀ * springMatrix r κ * S = diagonal lam) :
    Fintype.card {p // lam p ≠ 0} = 3 := by
  have h := card_vibration_add_six hSM hSK (rigidMap_injective hn)
    (range_rigidMap_eq_modeSpace_zero m hn hκ)
  rw [Fintype.card_fin] at h
  omega

variable {G : Type*} [Group G] [Fintype G] {O : G →* Matrix (Fin 3) (Fin 3) ℝ}
  {π : G →* Equiv.Perm (Fin 3)} {W : Type*} [AddCommGroup W] [Module ℝ W]
  [FiniteDimensional ℝ W]

/-- The number of the vibrations of each symmetry type, for a molecule of
three atoms with a group of symmetries. -/
theorem sum_finrank_vibration_triatomic (hO : ∀ g, (O g)ᵀ * O g = 1)
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
  sum_finrank_vibration hSM hSK _ hO hr (rigidMap_injective hn)
    (range_rigidMap_eq_modeSpace_zero m hn hκ) σ

end Triangle

/-! ### One-dimensional symmetry types -/

section Scalar

variable {G : Type*} [Group G]

/-- The representation on the line by a real character. -/
def scalarRep (χ : G →* ℝ) : Representation ℝ G ℝ where
  toFun g := χ g • LinearMap.id
  map_one' := by
    rw [map_one, one_smul]
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    change χ (g * h) * x = χ g * (χ h * x)
    rw [map_mul, mul_assoc]

theorem character_scalarRep (χ : G →* ℝ) (g : G) : (scalarRep χ).character g = χ g := by
  change LinearMap.trace ℝ ℝ (χ g • LinearMap.id) = χ g
  rw [map_smul, LinearMap.trace_id, finrank_self, Nat.cast_one, smul_eq_mul, mul_one]

theorem character_vectorRep (O : G →* Matrix (Fin 3) (Fin 3) ℝ) (g : G) :
    (vectorRep O).character g = (O g).trace :=
  Matrix.trace_toLin'_eq (O g)

end Scalar

/-- The number of the points that a permutation of three points leaves in
place. -/
def fixCount (g : Equiv.Perm (Fin 3)) : ℕ := (Finset.univ.filter fun a => g a = a).card

theorem ncard_fixedPoints (g : Equiv.Perm (Fin 3)) :
    (Function.fixedPoints ⇑g).ncard = fixCount g := by
  rw [fixCount, ← Set.ncard_coe_finset]
  congr 1
  ext a
  simp [Function.mem_fixedPoints, Function.IsFixedPt]

/-! ### Three equal atoms at the corners of an equilateral triangle -/

namespace Equilateral

/-- The corners: the points of the three axes at the distance one. -/
def position : Fin 3 → Fin 3 → ℝ := fun a => Pi.single a 1

/-- The sign of a permutation as a real character. -/
def signHom : Equiv.Perm (Fin 3) →* ℝ :=
  (Int.castRingHom ℝ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

theorem signHom_apply (g : Equiv.Perm (Fin 3)) :
    signHom g = ((Equiv.Perm.sign g : ℤ) : ℝ) := rfl

theorem transpose_mul_permMatrixHom (g : Equiv.Perm (Fin 3)) :
    (permMatrixHom (R := ℝ) g)ᵀ * permMatrixHom g = 1 := by
  rw [permMatrixHom_apply, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel,
    permMatrix_one]

theorem permMatrixHom_mulVec_position (g : Equiv.Perm (Fin 3)) (a : Fin 3) :
    permMatrixHom (R := ℝ) g *ᵥ position a = position (MonoidHom.id _ g a) := by
  rw [permMatrixHom_apply, permMatrix_mulVec]
  funext i
  simp [position, Pi.single_apply, Equiv.symm_apply_eq]

theorem not_collinear : (position 1 - position 0) ⨯₃ (position 2 - position 0) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [position, cross_apply] at h0

theorem trace_permMatrixHom (g : Equiv.Perm (Fin 3)) :
    (permMatrixHom (R := ℝ) g).trace = (fixCount g⁻¹ : ℝ) := by
  rw [permMatrixHom_apply, trace_permutation, ncard_fixedPoints]

theorem det_permMatrixHom (g : Equiv.Perm (Fin 3)) :
    (permMatrixHom (R := ℝ) g).det = ((Equiv.Perm.sign g⁻¹ : ℤ) : ℝ) := by
  rw [permMatrixHom_apply, det_permutation]

variable {μ k : ℝ} {S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ} {lam : Fin 3 × Fin 3 → ℝ}

/-- The permutations of the corners act by symmetries. -/
theorem isSymmetryRep (μ k : ℝ) :
    IsSymmetryRep (displacementRep (permMatrixHom (R := ℝ)) (MonoidHom.id _))
      (massMatrix fun _ => μ) (springMatrix position fun _ _ => k) :=
  isSymmetryRep_spring transpose_mul_permMatrixHom permMatrixHom_mulVec_position
    (fun _ _ => rfl) (fun _ _ _ => rfl)

/-- The number of the vibrations of a symmetry type of the equilateral
molecule, as a sum over the permutations. -/
theorem sum_finrank (hk : 0 < k) (hSM : Sᵀ * (massMatrix fun _ => μ) * S = 1)
    (hSK : Sᵀ * (springMatrix position fun _ _ => k) * S = diagonal lam) {W : Type*}
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (σ : Representation ℝ (Equiv.Perm (Fin 3)) W) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap σ (modeRep (isSymmetryRep μ k) c)) : ℝ) =
      (6 : ℝ)⁻¹ * ∑ g : Equiv.Perm (Fin 3),
        ((fixCount g : ℝ) - 1 - ((Equiv.Perm.sign g⁻¹ : ℤ) : ℝ)) * (fixCount g⁻¹ : ℝ) *
          σ.character g⁻¹ := by
  have hcard : (Nat.card (Equiv.Perm (Fin 3)) : ℝ) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  refine (sum_finrank_vibration_triatomic (O := permMatrixHom (R := ℝ)) (π := MonoidHom.id _)
    (r := position) (m := fun _ => μ) (κ := fun _ _ => k) transpose_mul_permMatrixHom
    permMatrixHom_mulVec_position (fun _ _ => rfl) (fun _ _ _ => rfl) not_collinear
    (fun _ _ => hk) hSM hSK σ).trans ?_
  rw [hcard]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [trace_permMatrixHom, det_permMatrixHom]
  change (((Function.fixedPoints ⇑g).ncard : ℝ) - 1 - _) * _ * _ = _
  rw [ncard_fixedPoints]

/-- The totally symmetric type occurs once among the vibrations. -/
theorem sum_finrank_trivial (hk : 0 < k) (hSM : Sᵀ * (massMatrix fun _ => μ) * S = 1)
    (hSK : Sᵀ * (springMatrix position fun _ _ => k) * S = diagonal lam) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap (scalarRep 1)
          (modeRep (isSymmetryRep μ k) c)) : ℝ) = 1 := by
  rw [sum_finrank hk hSM hSK]
  have hint : ∑ g : Equiv.Perm (Fin 3),
      (((fixCount g : ℤ) - 1 - (Equiv.Perm.sign g⁻¹ : ℤ)) * (fixCount g⁻¹ : ℤ)) = 6 := by
    decide
  have hsum : ∑ g : Equiv.Perm (Fin 3),
      ((fixCount g : ℝ) - 1 - ((Equiv.Perm.sign g⁻¹ : ℤ) : ℝ)) * (fixCount g⁻¹ : ℝ) *
        (scalarRep (1 : Equiv.Perm (Fin 3) →* ℝ)).character g⁻¹ = 6 := by
    simp_rw [character_scalarRep, MonoidHom.one_apply, mul_one]
    exact_mod_cast hint
  rw [hsum]
  norm_num

/-- The sign type does not occur among the vibrations. -/
theorem sum_finrank_sign (hk : 0 < k) (hSM : Sᵀ * (massMatrix fun _ => μ) * S = 1)
    (hSK : Sᵀ * (springMatrix position fun _ _ => k) * S = diagonal lam) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap (scalarRep signHom)
          (modeRep (isSymmetryRep μ k) c)) : ℝ) = 0 := by
  rw [sum_finrank hk hSM hSK]
  have hint : ∑ g : Equiv.Perm (Fin 3),
      (((fixCount g : ℤ) - 1 - (Equiv.Perm.sign g⁻¹ : ℤ)) * (fixCount g⁻¹ : ℤ) *
        (Equiv.Perm.sign g⁻¹ : ℤ)) = 0 := by
    decide
  have hsum : ∑ g : Equiv.Perm (Fin 3),
      ((fixCount g : ℝ) - 1 - ((Equiv.Perm.sign g⁻¹ : ℤ) : ℝ)) * (fixCount g⁻¹ : ℝ) *
        (scalarRep signHom).character g⁻¹ = 0 := by
    simp_rw [character_scalarRep, signHom_apply]
    exact_mod_cast hint
  rw [hsum, mul_zero]

/-- The permutation representation occurs twice among the vibrations. It is
the sum of the totally symmetric type and of the two-dimensional type, so the
vibrations are one totally symmetric vibration and one pair of the
two-dimensional type. -/
theorem sum_finrank_permutation (hk : 0 < k) (hSM : Sᵀ * (massMatrix fun _ => μ) * S = 1)
    (hSK : Sᵀ * (springMatrix position fun _ _ => k) * S = diagonal lam) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap (vectorRep (permMatrixHom (R := ℝ)))
          (modeRep (isSymmetryRep μ k) c)) : ℝ) = 2 := by
  rw [sum_finrank hk hSM hSK]
  have hint : ∑ g : Equiv.Perm (Fin 3),
      (((fixCount g : ℤ) - 1 - (Equiv.Perm.sign g⁻¹ : ℤ)) * (fixCount g⁻¹ : ℤ) *
        (fixCount g⁻¹⁻¹ : ℤ)) = 12 := by
    decide
  have hsum : ∑ g : Equiv.Perm (Fin 3),
      ((fixCount g : ℝ) - 1 - ((Equiv.Perm.sign g⁻¹ : ℤ) : ℝ)) * (fixCount g⁻¹ : ℝ) *
        (vectorRep (permMatrixHom (R := ℝ))).character g⁻¹ = 12 := by
    simp_rw [character_vectorRep, trace_permMatrixHom]
    exact_mod_cast hint
  rw [hsum]
  norm_num

/-- A simultaneous diagonalization exists for positive masses, so the
statements above are not empty. -/
theorem exists_diagonalization (hμ : 0 < μ) (k : ℝ) :
    ∃ (S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ) (lam : Fin 3 × Fin 3 → ℝ),
      Sᵀ * (massMatrix fun _ => μ) * S = 1 ∧
        Sᵀ * (springMatrix position fun _ _ => k) * S = diagonal lam :=
  exists_simultaneous_diagonalization (posDef_massMatrix fun _ => hμ)
    (transpose_springMatrix position _)

end Equilateral

/-! ### An isosceles molecule -/

namespace Isosceles

/-- The apex on the axis `1` at the height `h`, and the two other atoms at the
distance `d` on the two sides of the axis `0`. -/
def position (h d : ℝ) : Fin 3 → Fin 3 → ℝ := ![![0, h, 0], ![d, 0, 0], ![-d, 0, 0]]

/-- A unit of the integers as a real number. -/
def unitHom : ℤˣ →* ℝ := (Int.castRingHom ℝ).toMonoidHom.comp (Units.coeHom ℤ)

theorem unitHom_apply (u : ℤˣ) : unitHom u = ((u : ℤ) : ℝ) := rfl

theorem unitHom_mul_self (u : ℤˣ) : unitHom u * unitHom u = 1 := by
  rw [← map_mul, Int.units_mul_self, map_one]

theorem diagonal_ones : diagonal ![(1 : ℝ), 1, 1] = 1 := by
  rw [← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The group of the symmetries, with four elements: the first factor is the
reflection that exchanges the two atoms of the base, the second is the
reflection in the plane of the molecule. -/
def rot : ℤˣ × ℤˣ →* Matrix (Fin 3) (Fin 3) ℝ where
  toFun g := diagonal ![unitHom g.1, 1, unitHom g.2]
  map_one' := by
    rw [Prod.fst_one, Prod.snd_one, map_one, diagonal_ones]
  map_mul' g h := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp

theorem rot_apply (g : ℤˣ × ℤˣ) : rot g = diagonal ![unitHom g.1, 1, unitHom g.2] := rfl

/-- The permutation of the atoms: the first reflection exchanges the two atoms
of the base. -/
def perm : ℤˣ × ℤˣ →* Equiv.Perm (Fin 3) where
  toFun g := if g.1 = 1 then 1 else Equiv.swap 1 2
  map_one' := by simp
  map_mul' g h := by
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    rcases Int.units_eq_one_or g.1 with h1 | h1 <;>
      rcases Int.units_eq_one_or h.1 with h2 | h2 <;> simp [h1, h2, hne]

theorem perm_apply (g : ℤˣ × ℤˣ) : perm g = if g.1 = 1 then 1 else Equiv.swap 1 2 := rfl

theorem transpose_mul_rot (g : ℤˣ × ℤˣ) : (rot g)ᵀ * rot g = 1 := by
  rw [rot_apply, diagonal_transpose, diagonal_mul_diagonal, ← diagonal_ones]
  congr 1
  funext i
  fin_cases i <;> simp [unitHom_mul_self]

theorem rot_mulVec_position (h d : ℝ) (g : ℤˣ × ℤˣ) (a : Fin 3) :
    rot g *ᵥ position h d a = position h d (perm g a) := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or g.1 with h1 | h1 <;> fin_cases a <;> funext i <;> fin_cases i <;>
    simp [rot_apply, perm_apply, position, mulVec_diagonal, h1, hne, unitHom_apply,
      Equiv.swap_apply_def]

theorem not_collinear {h d : ℝ} (hh : h ≠ 0) (hd : d ≠ 0) :
    (position h d 1 - position h d 0) ⨯₃ (position h d 2 - position h d 0) ≠ 0 := by
  intro h0
  have h2 := congrFun h0 2
  simp [position, cross_apply] at h2
  have h3 : d * h = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact hd h4
  · exact hh h4

/-- The masses: `m₀` at the apex and `m₁` for the two atoms of the base. -/
def mass (m₀ m₁ : ℝ) : Fin 3 → ℝ := ![m₀, m₁, m₁]

/-- The stiffnesses: `k₁` for the two bonds at the apex and `k₂` for the base. -/
def stiffness (k₁ k₂ : ℝ) : Fin 3 → Fin 3 → ℝ := fun a b => if a = 0 ∨ b = 0 then k₁ else k₂

theorem perm_apply_eq_zero (g : ℤˣ × ℤˣ) (a : Fin 3) : perm g a = 0 ↔ a = 0 := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or g.1 with h1 | h1 <;> fin_cases a <;>
    simp [perm_apply, h1, hne, Equiv.swap_apply_def]

theorem mass_perm (m₀ m₁ : ℝ) (g : ℤˣ × ℤˣ) (a : Fin 3) :
    mass m₀ m₁ (perm g a) = mass m₀ m₁ a := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or g.1 with h1 | h1 <;> fin_cases a <;>
    simp [perm_apply, mass, h1, hne, Equiv.swap_apply_def]

theorem stiffness_perm (k₁ k₂ : ℝ) (g : ℤˣ × ℤˣ) (a b : Fin 3) :
    stiffness k₁ k₂ (perm g a) (perm g b) = stiffness k₁ k₂ a b := by
  simp only [stiffness, perm_apply_eq_zero]

theorem stiffness_pos {k₁ k₂ : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (a b : Fin 3) :
    0 < stiffness k₁ k₂ a b := by
  unfold stiffness
  split_ifs
  · exact h₁
  · exact h₂

variable {h d m₀ m₁ k₁ k₂ : ℝ} {S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ}
  {lam : Fin 3 × Fin 3 → ℝ}

/-- The four symmetries act by symmetries of the oscillations. -/
theorem isSymmetryRep (h d m₀ m₁ k₁ k₂ : ℝ) :
    IsSymmetryRep (displacementRep rot perm) (massMatrix (mass m₀ m₁))
      (springMatrix (position h d) (stiffness k₁ k₂)) :=
  isSymmetryRep_spring transpose_mul_rot (rot_mulVec_position h d) (mass_perm m₀ m₁)
    (stiffness_perm k₁ k₂)

theorem sum_units_int (f : ℤˣ → ℝ) : ∑ u, f u = f 1 + f (-1) := by
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from rfl, Finset.sum_pair (by decide)]

theorem trace_rot (g : ℤˣ × ℤˣ) : (rot g).trace = unitHom g.1 + 1 + unitHom g.2 := by
  rw [rot_apply, trace_diagonal, Fin.sum_univ_three]
  rfl

theorem det_rot (g : ℤˣ × ℤˣ) : (rot g).det = unitHom g.1 * unitHom g.2 := by
  rw [rot_apply, det_diagonal, Fin.prod_univ_three]
  change unitHom g.1 * 1 * unitHom g.2 = _
  rw [mul_one]

/-- The number of the vibrations of the symmetry type of a real character
`χ` of the group of the four symmetries. -/
theorem sum_finrank (hh : h ≠ 0) (hd : d ≠ 0) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hSM : Sᵀ * massMatrix (mass m₀ m₁) * S = 1)
    (hSK : Sᵀ * springMatrix (position h d) (stiffness k₁ k₂) * S = diagonal lam)
    (χ : ℤˣ × ℤˣ →* ℝ) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap (scalarRep χ)
          (modeRep (isSymmetryRep h d m₀ m₁ k₁ k₂) c)) : ℝ) =
      (3 * χ (1, 1) + 3 * χ (1, -1) + χ (-1, 1) + χ (-1, -1)) / 4 := by
  have hcard : (Nat.card (ℤˣ × ℤˣ) : ℝ) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_units_int]
    norm_num
  have hfix1 : ∀ g : ℤˣ × ℤˣ, g.1 = 1 → ((Function.fixedPoints ⇑(perm g)).ncard : ℝ) = 3 := by
    intro g hg
    rw [ncard_fixedPoints, perm_apply]
    simp only [hg, ↓reduceIte]
    have h3 : fixCount 1 = 3 := by decide
    rw [h3]
    norm_num
  have hfix2 : ∀ g : ℤˣ × ℤˣ, g.1 = -1 → ((Function.fixedPoints ⇑(perm g)).ncard : ℝ) = 1 := by
    intro g hg
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    rw [ncard_fixedPoints, perm_apply]
    simp only [hg, hne, ↓reduceIte]
    have h1 : fixCount (Equiv.swap 1 2) = 1 := by decide
    rw [h1]
    norm_num
  refine (sum_finrank_vibration_triatomic (O := rot) (π := perm) (r := position h d)
    (m := mass m₀ m₁) (κ := stiffness k₁ k₂) transpose_mul_rot (rot_mulVec_position h d)
    (mass_perm m₀ m₁) (stiffness_perm k₁ k₂) (not_collinear hh hd) (stiffness_pos h₁ h₂)
    hSM hSK (scalarRep χ)).trans ?_
  rw [hcard, Fintype.sum_prod_type, sum_units_int]
  simp only [sum_units_int, character_scalarRep, trace_rot, det_rot, hfix1 (1, 1) rfl,
    hfix1 (1, -1) rfl, hfix2 (-1, 1) rfl, hfix2 (-1, -1) rfl, Prod.inv_mk, inv_one, inv_neg_one]
  have hu1 : unitHom 1 = 1 := map_one _
  have hu2 : unitHom (-1) = -1 := by
    rw [unitHom_apply]
    norm_num
  rw [hu1, hu2]
  ring

/-- Two vibrations are symmetric under both reflections. -/
theorem sum_finrank_symmetric (hh : h ≠ 0) (hd : d ≠ 0) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hSM : Sᵀ * massMatrix (mass m₀ m₁) * S = 1)
    (hSK : Sᵀ * springMatrix (position h d) (stiffness k₁ k₂) * S = diagonal lam) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap (scalarRep 1)
          (modeRep (isSymmetryRep h d m₀ m₁ k₁ k₂) c)) : ℝ) = 2 := by
  rw [sum_finrank hh hd h₁ h₂ hSM hSK]
  simp only [MonoidHom.one_apply]
  norm_num

/-- One vibration changes sign under the reflection that exchanges the two
atoms of the base, and is symmetric under the reflection in the plane of the
molecule. -/
theorem sum_finrank_antisymmetric (hh : h ≠ 0) (hd : d ≠ 0) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hSM : Sᵀ * massMatrix (mass m₀ m₁) * S = 1)
    (hSK : Sᵀ * springMatrix (position h d) (stiffness k₁ k₂) * S = diagonal lam) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap
          (scalarRep (unitHom.comp (MonoidHom.fst ℤˣ ℤˣ)))
          (modeRep (isSymmetryRep h d m₀ m₁ k₁ k₂) c)) : ℝ) = 1 := by
  rw [sum_finrank hh hd h₁ h₂ hSM hSK]
  simp only [MonoidHom.comp_apply, MonoidHom.coe_fst, map_one, unitHom_apply]
  norm_num

/-- No vibration changes sign under the reflection in the plane of the
molecule: the vibrations stay in the plane. -/
theorem sum_finrank_plane (hh : h ≠ 0) (hd : d ≠ 0) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hSM : Sᵀ * massMatrix (mass m₀ m₁) * S = 1)
    (hSK : Sᵀ * springMatrix (position h d) (stiffness k₁ k₂) * S = diagonal lam)
    (χ : ℤˣ →* ℝ) :
    ∑ c ∈ (Finset.univ.image lam).erase 0,
        (finrank ℝ (Representation.IntertwiningMap
          (scalarRep ((χ.comp (MonoidHom.fst ℤˣ ℤˣ)) * unitHom.comp (MonoidHom.snd ℤˣ ℤˣ)))
          (modeRep (isSymmetryRep h d m₀ m₁ k₁ k₂) c)) : ℝ) = 0 := by
  rw [sum_finrank hh hd h₁ h₂ hSM hSK]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
    map_one, unitHom_apply]
  norm_num

/-- A simultaneous diagonalization exists for positive masses, so the
statements above are not empty. -/
theorem exists_diagonalization (h d : ℝ) (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) (k₁ k₂ : ℝ) :
    ∃ (S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ) (lam : Fin 3 × Fin 3 → ℝ),
      Sᵀ * massMatrix (mass m₀ m₁) * S = 1 ∧
        Sᵀ * springMatrix (position h d) (stiffness k₁ k₂) * S = diagonal lam :=
  exists_simultaneous_diagonalization
    (posDef_massMatrix fun a => by fin_cases a <;> simp [mass, hm₀, hm₁])
    (transpose_springMatrix _ _)

end Isosceles

end ProjectAinos.Mechanics.Molecule
