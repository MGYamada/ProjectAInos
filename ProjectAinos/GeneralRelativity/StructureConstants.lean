/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The structure constants of a three-dimensional Lie algebra

Landau–Lifshitz, §116, in 0-based indices `0, 1, 2`. A real array
`C : Fin 3 → Fin 3 → Fin 3 → ℝ` with `C c a b = C^c_{ab}` stands for the brackets
`[X_a, X_b] = Σ_c C^c_{ab} X_c` of three frame vectors. The Levi-Civita symbol `ε_{abc}`
with `ε_{012} = 1` is `levi`.

* `IsAntisymm`: `C^c_{ab} = −C^c_{ba}`; `Jacobi`: the Jacobi identity
  `Σ_d (C^d_{ab} C^e_{dc} + C^d_{bc} C^e_{da} + C^d_{ca} C^e_{db}) = 0`.
* `ofBianchi n a`: the decomposition (116.8)–(116.9),
  `C^c_{ij} = Σ_d ε_{ijd} n_{dc} + δ^c_j a_i − δ^c_i a_j`, with a symmetric matrix `n` and a vector
  `a`; it is antisymmetric (`isAntisymm_ofBianchi`).
* `bianchiA C b = ½ Σ_c C^c_{bc}` and `bianchiN C`, the symmetric part of the dual
  `M_{ec} = ½ Σ_{a,b} ε_{abe} C^c_{ab}` (`dualMatrix`), invert the decomposition:
  `dualMatrix_ofBianchi` (`M = n + ` an antisymmetric matrix of `a`), `bianchiN_ofBianchi`,
  `bianchiA_ofBianchi` (for symmetric `n`) and `ofBianchi_bianchiN_bianchiA` (for antisymmetric
  `C`); `existsUnique_bianchi`: every antisymmetric `C` is `ofBianchi n a` for exactly one pair
  with `n` symmetric.
* `jacobi_ofBianchi_apply`: for symmetric `n` the Jacobi sum is `2 ε_{abc} (n a)_e`;
  `jacobi_ofBianchi_iff`: the Jacobi identity holds if and only if `n^{ab} a_b = 0`
  (`n *ᵥ a = 0`); `jacobi_iff`: an antisymmetric `C` satisfies it if and only if
  `bianchiN C *ᵥ bianchiA C = 0`; `not_jacobi_ofBianchi_one`: `n = 1`, `a = (1, 0, 0)` violates it.
* `bianchiA_eq_zero_iff`: class A (`a = 0`) is the trace condition `Σ_c C^c_{bc} = 0`.
* The canonical forms of the Bianchi types (L&L's table), with `n` diagonal and `a = (α, 0, 0)`:
  `bianchiI`, `bianchiII`, `bianchiIV`, `bianchiV`, `bianchiVI h` (III is `bianchiVI 1`,
  VI₀ is `bianchiVI 0`), `bianchiVII h` (VII₀ is `bianchiVII 0`), `bianchiVIII`, `bianchiIX`; each
  satisfies the Jacobi identity (`jacobi_bianchiI`, …, `jacobi_bianchiIX`). The brackets:
  `bianchiI_apply` (abelian), `bianchiIX_apply` (`C^c_{ab} = ε_{abc}`), `bianchiII_apply` and
  `bianchiII_zero_one`, `bianchiII_zero_two`, `bianchiII_one_two` (`[X₁, X₂] = X₀`, the others
  vanish), `bianchiV_apply` and `bianchiV_zero_one`, `bianchiV_zero_two`, `bianchiV_one_two`
  (`[X₀, X₁] = X₁`, `[X₀, X₂] = X₂`, `[X₁, X₂] = 0`).
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.GeneralRelativity.StructureConstants

open Matrix

/-! ### The Levi-Civita symbol -/

/-- The Levi-Civita symbol `ε_{abc}` on `Fin 3`, with `ε_{012} = 1`, as an explicit table. -/
def levi : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- `ε_{012} = 1`. -/
theorem levi_zero_one_two : levi 0 1 2 = 1 := by
  simp [levi]

/-- The Levi-Civita symbol changes sign under the exchange of its first two indices. -/
theorem levi_swap_left (a b c : Fin 3) : levi b a c = -levi a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [levi]

/-- The Levi-Civita symbol changes sign under the exchange of its last two indices. -/
theorem levi_swap_right (a b c : Fin 3) : levi a c b = -levi a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [levi]

/-- The Levi-Civita symbol is invariant under a cyclic permutation of its indices. -/
theorem levi_cycle (a b c : Fin 3) : levi b c a = levi a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [levi]

/-! ### Antisymmetry, the Jacobi identity and the Bianchi decomposition -/

/-- The structure constants `C^c_{ab}` are antisymmetric in the lower indices `a, b`, as the
coefficients of the brackets `[X_a, X_b] = Σ_c C^c_{ab} X_c` are. -/
def IsAntisymm (C : Fin 3 → Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ c a b, C c a b = -C c b a

/-- The Jacobi identity `[[X_a, X_b], X_c] + [[X_b, X_c], X_a] + [[X_c, X_a], X_b] = 0` of the
brackets `[X_a, X_b] = Σ_c C^c_{ab} X_c`: the coefficient of `X_e` is
`Σ_d (C^d_{ab} C^e_{dc} + C^d_{bc} C^e_{da} + C^d_{ca} C^e_{db})`. -/
def Jacobi (C : Fin 3 → Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ e a b c, ∑ d, (C d a b * C e d c + C d b c * C e d a + C d c a * C e d b) = 0

/-- The Bianchi decomposition (L&L (116.8)–(116.9)) of the structure constants,
`C^c_{ij} = Σ_d ε_{ijd} n_{dc} + δ^c_j a_i − δ^c_i a_j`, from a matrix `n` (symmetric in the
intended use) and a vector `a`. -/
def ofBianchi (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun c i j => (∑ d, levi i j d * n d c) + (if c = j then a i else 0) - (if c = i then a j else 0)

/-- The structure constants of the Bianchi decomposition are antisymmetric. -/
theorem isAntisymm_ofBianchi (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    IsAntisymm (ofBianchi n a) := by
  intro c i j
  simp only [ofBianchi, levi_swap_left j i, neg_mul, Finset.sum_neg_distrib]
  ring

/-! ### The inverse maps -/

/-- The vector `a_b = ½ Σ_c C^c_{bc}` of the Bianchi decomposition. -/
def bianchiA (C : Fin 3 → Fin 3 → Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun b => (∑ c, C c b c) / 2

/-- The dual `M_{ec} = ½ Σ_{a,b} ε_{abe} C^c_{ab}` of the structure constants in the lower
indices. -/
def dualMatrix (C : Fin 3 → Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun e c => (∑ a, ∑ b, levi a b e * C c a b) / 2

/-- The symmetric matrix `n` of the Bianchi decomposition: the symmetric part of the dual
`dualMatrix C`. -/
def bianchiN (C : Fin 3 → Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun e c => (dualMatrix C e c + dualMatrix C c e) / 2

/-- The matrix `bianchiN C` is symmetric. -/
theorem bianchiN_isSymm (C : Fin 3 → Fin 3 → Fin 3 → ℝ) : (bianchiN C).IsSymm :=
  IsSymm.ext fun i j => by simp only [bianchiN, of_apply]; ring

/-- The dual of the Bianchi decomposition is `M_{ec} = n_{ec} + Σ_d ε_{edc} a_d`: `n` plus an
antisymmetric matrix of `a`. -/
theorem dualMatrix_ofBianchi (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    dualMatrix (ofBianchi n a) = n + Matrix.of fun e c => ∑ d, levi e d c * a d := by
  ext e c
  fin_cases e <;> fin_cases c <;>
    simp [dualMatrix, ofBianchi, levi, Fin.sum_univ_three] <;> ring

/-- The symmetric matrix of the Bianchi decomposition of a symmetric `n` is `n`. -/
theorem bianchiN_ofBianchi {n : Matrix (Fin 3) (Fin 3) ℝ} (hn : n.IsSymm) (a : Fin 3 → ℝ) :
    bianchiN (ofBianchi n a) = n := by
  ext e c
  have hec := hn.apply e c
  have hl : ∀ d, levi c d e = -levi e d c := fun d => by
    rw [levi_cycle e c d, levi_swap_right e d c]
  simp only [bianchiN, dualMatrix_ofBianchi, of_apply, add_apply, hec, hl, neg_mul,
    Finset.sum_neg_distrib]
  ring

/-- The vector of the Bianchi decomposition of a symmetric `n` is `a`. The symmetry is needed:
the antisymmetric part of `n` contributes to the trace `Σ_c C^c_{bc}`. -/
theorem bianchiA_ofBianchi {n : Matrix (Fin 3) (Fin 3) ℝ} (hn : n.IsSymm) (a : Fin 3 → ℝ) :
    bianchiA (ofBianchi n a) = a := by
  have h10 := hn.apply 0 1
  have h20 := hn.apply 0 2
  have h21 := hn.apply 1 2
  funext b
  fin_cases b <;> simp [bianchiA, ofBianchi, levi, Fin.sum_univ_three, h10, h20, h21] <;> ring

/-- An antisymmetric `C` is the Bianchi decomposition of `bianchiN C` and `bianchiA C`. -/
theorem ofBianchi_bianchiN_bianchiA {C : Fin 3 → Fin 3 → Fin 3 → ℝ} (hC : IsAntisymm C) :
    ofBianchi (bianchiN C) (bianchiA C) = C := by
  have h00 : ∀ c, C c 0 0 = 0 := fun c => by linarith [hC c 0 0]
  have h11 : ∀ c, C c 1 1 = 0 := fun c => by linarith [hC c 1 1]
  have h22 : ∀ c, C c 2 2 = 0 := fun c => by linarith [hC c 2 2]
  have h10 : ∀ c, C c 1 0 = -C c 0 1 := fun c => hC c 1 0
  have h20 : ∀ c, C c 2 0 = -C c 0 2 := fun c => hC c 2 0
  have h21 : ∀ c, C c 2 1 = -C c 1 2 := fun c => hC c 2 1
  funext c i j
  fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp [ofBianchi, bianchiN, dualMatrix, bianchiA, levi, Fin.sum_univ_three,
      h00, h11, h22, h10, h20, h21] <;> ring

/-- Every antisymmetric `C` is the Bianchi decomposition of exactly one pair `(n, a)` with `n`
symmetric. -/
theorem existsUnique_bianchi {C : Fin 3 → Fin 3 → Fin 3 → ℝ} (hC : IsAntisymm C) :
    ∃! p : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ), p.1.IsSymm ∧ ofBianchi p.1 p.2 = C := by
  refine ⟨(bianchiN C, bianchiA C), ⟨bianchiN_isSymm C, ofBianchi_bianchiN_bianchiA hC⟩, ?_⟩
  rintro ⟨n, a⟩ ⟨hn, rfl⟩
  exact Prod.ext (bianchiN_ofBianchi hn a).symm (bianchiA_ofBianchi hn a).symm

/-! ### The Jacobi identity -/

/-- For a symmetric `n`, the Jacobi sum of the Bianchi decomposition is `2 ε_{ijk} (n a)_e`. -/
theorem jacobi_ofBianchi_apply {n : Matrix (Fin 3) (Fin 3) ℝ} (hn : n.IsSymm) (a : Fin 3 → ℝ)
    (e i j k : Fin 3) :
    ∑ d, (ofBianchi n a d i j * ofBianchi n a e d k + ofBianchi n a d j k * ofBianchi n a e d i +
      ofBianchi n a d k i * ofBianchi n a e d j) = 2 * levi i j k * (n *ᵥ a) e := by
  have h10 := hn.apply 0 1
  have h20 := hn.apply 0 2
  have h21 := hn.apply 1 2
  fin_cases e <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [ofBianchi, levi, Fin.sum_univ_three, mulVec, dotProduct, h10, h20, h21] <;> ring

/-- The Bianchi decomposition with a symmetric `n` satisfies the Jacobi identity if and only if
`n^{ab} a_b = 0` (L&L, §116). -/
theorem jacobi_ofBianchi_iff {n : Matrix (Fin 3) (Fin 3) ℝ} (hn : n.IsSymm) (a : Fin 3 → ℝ) :
    Jacobi (ofBianchi n a) ↔ n *ᵥ a = 0 := by
  constructor
  · intro h
    funext e
    have he := h e 0 1 2
    rw [jacobi_ofBianchi_apply hn, levi_zero_one_two] at he
    simpa using he
  · intro h e i j k
    rw [jacobi_ofBianchi_apply hn, h]
    simp

/-- An antisymmetric `C` satisfies the Jacobi identity if and only if
`bianchiN C *ᵥ bianchiA C = 0`. -/
theorem jacobi_iff {C : Fin 3 → Fin 3 → Fin 3 → ℝ} (hC : IsAntisymm C) :
    Jacobi C ↔ bianchiN C *ᵥ bianchiA C = 0 := by
  conv_lhs => rw [← ofBianchi_bianchiN_bianchiA hC]
  exact jacobi_ofBianchi_iff (bianchiN_isSymm C) _

/-- The Jacobi identity is a real condition: `n = 1`, `a = (1, 0, 0)` violates it. -/
theorem not_jacobi_ofBianchi_one : ¬ Jacobi (ofBianchi 1 ![1, 0, 0]) := by
  rw [jacobi_ofBianchi_iff isSymm_one]
  intro h
  have h0 := congrFun h 0
  simp at h0

/-! ### Class A -/

/-- Class A, `a = 0`, is the trace condition `Σ_c C^c_{bc} = 0`. -/
theorem bianchiA_eq_zero_iff (C : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    bianchiA C = 0 ↔ ∀ b, ∑ c, C c b c = 0 := by
  simp [funext_iff, bianchiA]

/-! ### The canonical forms of the Bianchi types -/

/-- Bianchi type I: `n = 0`, `a = 0`, the abelian algebra. -/
def bianchiI : Fin 3 → Fin 3 → Fin 3 → ℝ := ofBianchi 0 0

/-- Bianchi type II: `n = diag(1, 0, 0)`, `a = 0`. -/
def bianchiII : Fin 3 → Fin 3 → Fin 3 → ℝ := ofBianchi (diagonal ![1, 0, 0]) 0

/-- Bianchi type IV: `n = diag(0, 0, 1)`, `a = (1, 0, 0)`. -/
def bianchiIV : Fin 3 → Fin 3 → Fin 3 → ℝ := ofBianchi (diagonal ![0, 0, 1]) ![1, 0, 0]

/-- Bianchi type V: `n = 0`, `a = (1, 0, 0)`. -/
def bianchiV : Fin 3 → Fin 3 → Fin 3 → ℝ := ofBianchi 0 ![1, 0, 0]

/-- Bianchi type VI_h: `n = diag(0, 1, −1)`, `a = (h, 0, 0)`. Type VI₀ is `h = 0`, and type III is
`h = 1`. -/
def bianchiVI (h : ℝ) : Fin 3 → Fin 3 → Fin 3 → ℝ := ofBianchi (diagonal ![0, 1, -1]) ![h, 0, 0]

/-- Bianchi type VII_h: `n = diag(0, 1, 1)`, `a = (h, 0, 0)`. Type VII₀ is `h = 0`. -/
def bianchiVII (h : ℝ) : Fin 3 → Fin 3 → Fin 3 → ℝ := ofBianchi (diagonal ![0, 1, 1]) ![h, 0, 0]

/-- Bianchi type VIII: `n = diag(1, 1, −1)`, `a = 0`. -/
def bianchiVIII : Fin 3 → Fin 3 → Fin 3 → ℝ := ofBianchi (diagonal ![1, 1, -1]) 0

/-- Bianchi type IX: `n = diag(1, 1, 1) = 1`, `a = 0`. -/
def bianchiIX : Fin 3 → Fin 3 → Fin 3 → ℝ := ofBianchi 1 0

/-- Bianchi type I satisfies the Jacobi identity. -/
theorem jacobi_bianchiI : Jacobi bianchiI :=
  (jacobi_ofBianchi_iff isSymm_zero _).2 (by simp)

/-- Bianchi type II satisfies the Jacobi identity. -/
theorem jacobi_bianchiII : Jacobi bianchiII :=
  (jacobi_ofBianchi_iff (isSymm_diagonal _) _).2 (by simp)

/-- Bianchi type IV satisfies the Jacobi identity. -/
theorem jacobi_bianchiIV : Jacobi bianchiIV :=
  (jacobi_ofBianchi_iff (isSymm_diagonal _) _).2 <| by
    funext i; fin_cases i <;> simp [mulVec_diagonal]

/-- Bianchi type V satisfies the Jacobi identity. -/
theorem jacobi_bianchiV : Jacobi bianchiV :=
  (jacobi_ofBianchi_iff isSymm_zero _).2 (by simp)

/-- Bianchi type VI_h satisfies the Jacobi identity. -/
theorem jacobi_bianchiVI (h : ℝ) : Jacobi (bianchiVI h) :=
  (jacobi_ofBianchi_iff (isSymm_diagonal _) _).2 <| by
    funext i; fin_cases i <;> simp [mulVec_diagonal]

/-- Bianchi type VII_h satisfies the Jacobi identity. -/
theorem jacobi_bianchiVII (h : ℝ) : Jacobi (bianchiVII h) :=
  (jacobi_ofBianchi_iff (isSymm_diagonal _) _).2 <| by
    funext i; fin_cases i <;> simp [mulVec_diagonal]

/-- Bianchi type VIII satisfies the Jacobi identity. -/
theorem jacobi_bianchiVIII : Jacobi bianchiVIII :=
  (jacobi_ofBianchi_iff (isSymm_diagonal _) _).2 (by simp)

/-- Bianchi type IX satisfies the Jacobi identity. -/
theorem jacobi_bianchiIX : Jacobi bianchiIX :=
  (jacobi_ofBianchi_iff isSymm_one _).2 (by simp)

/-! ### The brackets of types I, II, V and IX -/

/-- Type I is abelian: `C^c_{ab} = 0`. -/
@[simp]
theorem bianchiI_apply (c a b : Fin 3) : bianchiI c a b = 0 := by
  simp [bianchiI, ofBianchi]

/-- Type IX: `C^c_{ab} = ε_{abc}`, that is, `[X_a, X_b] = Σ_c ε_{abc} X_c`. -/
@[simp]
theorem bianchiIX_apply (c a b : Fin 3) : bianchiIX c a b = levi a b c := by
  simp [bianchiIX, ofBianchi, one_apply]

/-- Type II: `C^c_{ab} = ε_{ab0} δ^c_0`. -/
@[simp]
theorem bianchiII_apply (c a b : Fin 3) : bianchiII c a b = if c = 0 then levi a b 0 else 0 := by
  fin_cases c <;> simp [bianchiII, ofBianchi, diagonal_apply]

/-- Type II: `[X₀, X₁] = 0`. -/
theorem bianchiII_zero_one (c : Fin 3) : bianchiII c 0 1 = 0 := by
  simp [levi]

/-- Type II: `[X₀, X₂] = 0`. -/
theorem bianchiII_zero_two (c : Fin 3) : bianchiII c 0 2 = 0 := by
  simp [levi]

/-- Type II: `[X₁, X₂] = X₀`. -/
theorem bianchiII_one_two (c : Fin 3) : bianchiII c 1 2 = if c = 0 then 1 else 0 := by
  simp [levi]

/-- Type V: `C^c_{ab} = δ_{a0} δ^c_b − δ_{b0} δ^c_a`. -/
@[simp]
theorem bianchiV_apply (c a b : Fin 3) :
    bianchiV c a b = (if a = 0 ∧ c = b then 1 else 0) - (if b = 0 ∧ c = a then 1 else 0) := by
  fin_cases c <;> fin_cases a <;> fin_cases b <;> simp [bianchiV, ofBianchi]

/-- Type V: `[X₀, X₁] = X₁`. -/
theorem bianchiV_zero_one (c : Fin 3) : bianchiV c 0 1 = if c = 1 then 1 else 0 := by
  simp

/-- Type V: `[X₀, X₂] = X₂`. -/
theorem bianchiV_zero_two (c : Fin 3) : bianchiV c 0 2 = if c = 2 then 1 else 0 := by
  simp

/-- Type V: `[X₁, X₂] = 0`. -/
theorem bianchiV_one_two (c : Fin 3) : bianchiV c 1 2 = 0 := by
  simp

end ProjectAinos.GeneralRelativity.StructureConstants
