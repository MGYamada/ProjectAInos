/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.HomogeneousSpace
public import ProjectAinos.GeneralRelativity.StructureConstants
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Diagonal homogeneous models of class A

Landau–Lifshitz, §116 (and the equations used in §118). For an invariant frame whose structure
constants are `C^c_{ab} = ε_{abc} n_c` (`n = diag(n₁, n₂, n₃)`, `a = 0` in the Bianchi
decomposition: the types I, II, VI₀, VII₀, VIII and IX) and a diagonal triad
`e = diag(a₁, a₂, a₃)`, the metric is `ds² = −dt² + Σ_i a_i(t)² (ω^i)²`.

* `Data.diagonal`: the data of the model, from an invariant frame and three scale factors smooth
  and positive on an open set of times.
* `ofBianchi_diagonal`: the structure constants of `n = diag(n)`, `a = 0` are `ε_{abc} n_c`.
* `velocity_diagonal`, `spatialStructure_diagonal`, `lam_diagonal`: the commutator coefficients
  are `λ_{k0j} = −(ȧ_k/a_k) δ_{kj}` and `λ_{kij} = ε_{ijk} n_k a_k/(a_i a_j)`.
* `frameRicci_zero_zero`, `frameRicci_one_one`, `frameRicci_two_two`, `frameRicci_three_three`,
  `frameRicci_ne`: **the Ricci tensor in the orthonormal frame**:
  `R₀₀ = −Σ_i ä_i/a_i`, the off-diagonal components vanish, and
  `R_{ii} = ä_i/a_i + (ȧ_i/a_i)(ȧ_j/a_j + ȧ_k/a_k) +
  ((n_i a_i²)² − (n_j a_j² − n_k a_k²)²)/(2 (a₁a₂a₃)²)` for `{i, j, k} = {1, 2, 3}`.
  For type IX (`n = (1, 1, 1)`) these are the equations of L&L §118.
* `ricci_eq_zero_iff_diagonal`: **the vacuum equations** of these models are the four ordinary
  differential equations `R₀₀ = R₁₁ = R₂₂ = R₃₃ = 0` on `I`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.HomogeneousSpace

open SmoothGeometry CoordinateMetric LorentzMetric StructureConstants

/-- The structure constants with `n = diag(n)` and `a = 0` are `C^c_{ab} = ε_{abc} n_c`. -/
theorem ofBianchi_diagonal (n : Fin 3 → ℝ) (c a b : Fin 3) :
    ofBianchi (Matrix.diagonal n) 0 c a b = levi a b c * n c := by
  simp [ofBianchi, Matrix.diagonal_apply]

namespace Data

/-- **The data of a diagonal homogeneous model**: an invariant frame, an open set `I` of times and
three scale factors `a_i`, smooth and positive on `I`; the triad is `diag(a₁, a₂, a₃)`. -/
def diagonal (F : InvariantFrame) (I : Set ℝ) (hI : IsOpen I) (a : Fin 3 → ℝ → ℝ)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) I) (hpos : ∀ i, ∀ t ∈ I, 0 < a i t) : Data where
  F := F
  I := I
  isOpen_I := hI
  triad t := Matrix.diagonal fun i => a i t
  triadInv t := Matrix.diagonal fun i => (a i t)⁻¹
  smooth_triad k b := by
    by_cases h : k = b
    · subst h
      simpa [Matrix.diagonal_apply] using ha k
    · simpa [Matrix.diagonal_apply, h] using contDiffOn_const
  smooth_triadInv b i := by
    by_cases h : b = i
    · subst h
      simp only [Matrix.diagonal_apply_eq]
      exact (ha b).inv fun t ht => (hpos b t ht).ne'
    · simpa [Matrix.diagonal_apply, h] using contDiffOn_const
  triad_mul t ht := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one with i
    exact mul_inv_cancel₀ (hpos i t ht).ne'

variable {F : InvariantFrame} {I : Set ℝ} {hI : IsOpen I} {a : Fin 3 → ℝ → ℝ}
  {ha : ∀ i, ContDiffOn ℝ ∞ (a i) I} {hpos : ∀ i, ∀ t ∈ I, 0 < a i t} {t : ℝ}

/-- The rates `K_{kj} = −(ȧ_k/a_k) δ_{kj}` of the diagonal triad. -/
theorem velocity_diagonal (ht : t ∈ I) (k j : Fin 3) :
    (diagonal F I hI a ha hpos).velocity t k j =
      if k = j then -(deriv (a k) t / a k t) else 0 := by
  have hk := (hpos k t ht).ne'
  rw [Data.velocity, Finset.sum_eq_single k
    (fun q _ hq => by simp [diagonal, Matrix.diagonal_apply, Ne.symm hq])
    (fun h => absurd (Finset.mem_univ k) h)]
  simp only [diagonal, Matrix.diagonal_apply_eq]
  by_cases h : k = j
  · subst h
    have hfun : (fun s => (Matrix.diagonal fun i => (a i s)⁻¹) k k) = fun s => (a k s)⁻¹ := by
      funext s
      simp
    have hd : HasDerivAt (fun s => (a k s)⁻¹) _ t :=
      (FLRW.hasDerivAt_of_contDiffOn hI (ha k) ht).inv hk
    rw [hfun, hd.deriv]
    simp only [ite_true]
    field_simp
  · have hfun : (fun s => (Matrix.diagonal fun i => (a i s)⁻¹) k j) = fun _ => 0 := by
      funext s
      simp [h]
    rw [hfun, deriv_const]
    simp [h]

/-- The spatial commutator coefficients `λ_{kij} = ε_{ijk} n_k a_k/(a_i a_j)`. -/
theorem spatialStructure_diagonal {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (k i j : Fin 3) :
    (diagonal F I hI a ha hpos).spatialStructure t k i j =
      levi i j k * n k * a k t / (a i t * a j t) := by
  simp only [Data.spatialStructure, diagonal, hC, ofBianchi_diagonal]
  rw [Finset.sum_eq_single k (fun c _ hc => by simp [Matrix.diagonal_apply, Ne.symm hc])
    (fun h => absurd (Finset.mem_univ k) h)]
  rw [Finset.sum_eq_single i (fun c _ hc => by simp [hc])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Finset.sum_eq_single j (fun c _ hc => by simp [hc])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp only [Matrix.diagonal_apply_eq]
  field_simp

/-! ### The commutator coefficients in closed form -/

variable (a) in
/-- `−(ȧ_k/a_k) δ_{kj}`. -/
def diagVelocity (t : ℝ) (k j : Fin 3) : ℝ := if k = j then -(deriv (a k) t / a k t) else 0

variable (a) in
/-- The time derivative of `diagVelocity`: `−((ä_k a_k − ȧ_k²)/a_k²) δ_{kj}`. -/
def diagVelocityDeriv (t : ℝ) (k j : Fin 3) : ℝ :=
  if k = j then -((deriv (deriv (a k)) t * a k t - deriv (a k) t ^ 2) / a k t ^ 2) else 0

variable (a) in
/-- `ε_{ijk} n_k a_k/(a_i a_j)`. -/
def diagStructure (n : Fin 3 → ℝ) (t : ℝ) (k i j : Fin 3) : ℝ :=
  levi i j k * n k * a k t / (a i t * a j t)

variable (a) in
/-- The time derivative of `diagStructure`. -/
def diagStructureDeriv (n : Fin 3 → ℝ) (t : ℝ) (k i j : Fin 3) : ℝ :=
  levi i j k * n k * ((deriv (a k) t * (a i t * a j t) -
    a k t * (deriv (a i) t * a j t + a i t * deriv (a j) t)) / (a i t * a j t) ^ 2)

variable (a) in
/-- The commutator coefficients of the diagonal model in closed form. -/
def diagLam (n : Fin 3 → ℝ) (t : ℝ) (p b c : Fin 4) : ℝ :=
  Matrix.vecCons 0 (fun k => Matrix.vecCons
    (Matrix.vecCons 0 (fun j => diagVelocity a t k j) c)
    (fun i => Matrix.vecCons (-diagVelocity a t k i) (fun j => diagStructure a n t k i j) c) b) p

variable (a) in
/-- The time derivatives of the commutator coefficients in closed form. -/
def diagLamDeriv (n : Fin 3 → ℝ) (t : ℝ) (p b c : Fin 4) : ℝ :=
  Matrix.vecCons 0 (fun k => Matrix.vecCons
    (Matrix.vecCons 0 (fun j => diagVelocityDeriv a t k j) c)
    (fun i => Matrix.vecCons (-diagVelocityDeriv a t k i)
      (fun j => diagStructureDeriv a n t k i j) c) b) p

theorem lam_diagonal {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I)
    (p b c : Fin 4) : (diagonal F I hI a ha hpos).lam t p b c = diagLam a n t p b c := by
  refine Fin.cases ?_ (fun k => ?_) p
  · simp [diagLam]
  · refine Fin.cases ?_ (fun i => ?_) b <;> refine Fin.cases ?_ (fun j => ?_) c
    · simp [diagLam]
    · simp [diagLam, velocity_diagonal ht, diagVelocity]
    · simp [diagLam, velocity_diagonal ht, diagVelocity]
    · simp [diagLam, spatialStructure_diagonal hC, diagStructure]

include hI ha hpos in
theorem hasDerivAt_diagVelocity (ht : t ∈ I) (k j : Fin 3) :
    HasDerivAt (fun s => diagVelocity a s k j) (diagVelocityDeriv a t k j) t := by
  by_cases h : k = j
  · subst h
    simp only [diagVelocity, diagVelocityDeriv, ite_true]
    have hk := (hpos k t ht).ne'
    refine (((FLRW.hasDerivAt_of_contDiffOn hI (FLRW.contDiffOn_deriv_of_contDiffOn hI (ha k))
      ht).div (FLRW.hasDerivAt_of_contDiffOn hI (ha k) ht) hk).neg).congr_deriv ?_
    ring
  · simpa [diagVelocity, diagVelocityDeriv, h] using hasDerivAt_const t (0 : ℝ)

include hI ha hpos in
theorem hasDerivAt_diagStructure (ht : t ∈ I) (n : Fin 3 → ℝ) (k i j : Fin 3) :
    HasDerivAt (fun s => diagStructure a n s k i j) (diagStructureDeriv a n t k i j) t := by
  have hij : a i t * a j t ≠ 0 := mul_ne_zero (hpos i t ht).ne' (hpos j t ht).ne'
  have hd (m : Fin 3) := FLRW.hasDerivAt_of_contDiffOn hI (ha m) ht
  refine ((((hd k).const_mul (levi i j k * n k)).div ((hd i).fun_mul (hd j)) hij)).congr_deriv ?_
  simp only [diagStructureDeriv]
  ring

include hI ha hpos in
theorem hasDerivAt_diagLam (ht : t ∈ I) (n : Fin 3 → ℝ) (p b c : Fin 4) :
    HasDerivAt (fun s => diagLam a n s p b c) (diagLamDeriv a n t p b c) t := by
  refine Fin.cases ?_ (fun k => ?_) p
  · simpa [diagLam, diagLamDeriv] using hasDerivAt_const t (0 : ℝ)
  · refine Fin.cases ?_ (fun i => ?_) b <;> refine Fin.cases ?_ (fun j => ?_) c
    · simpa [diagLam, diagLamDeriv] using hasDerivAt_const t (0 : ℝ)
    · simpa [diagLam, diagLamDeriv] using
        hasDerivAt_diagVelocity (hI := hI) (ha := ha) (hpos := hpos) ht k j
    · simpa [diagLam, diagLamDeriv] using
        (hasDerivAt_diagVelocity (hI := hI) (ha := ha) (hpos := hpos) ht k i).fun_neg
    · simpa [diagLam, diagLamDeriv] using
        hasDerivAt_diagStructure (hI := hI) (ha := ha) (hpos := hpos) ht n k i j

variable (a) in
/-- The rotation coefficients of the diagonal model in closed form. -/
def diagRot (n : Fin 3 → ℝ) (t : ℝ) (p b c : Fin 4) : ℝ :=
  (diagLam a n t p b c + diagLam a n t b c p - diagLam a n t c p b) / 2

variable (a) in
/-- The time derivatives of the rotation coefficients in closed form. -/
def diagRotDeriv (n : Fin 3 → ℝ) (t : ℝ) (p b c : Fin 4) : ℝ :=
  (diagLamDeriv a n t p b c + diagLamDeriv a n t b c p - diagLamDeriv a n t c p b) / 2

theorem rot_diagonal {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I)
    (p b c : Fin 4) : (diagonal F I hI a ha hpos).rot t p b c = diagRot a n t p b c := by
  simp only [Data.rot, diagRot, lam_diagonal hC ht]

theorem deriv_rot_diagonal {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) (p b c : Fin 4) :
    deriv (fun s => (diagonal F I hI a ha hpos).rot s p b c) t = diagRotDeriv a n t p b c := by
  have h := (((hasDerivAt_diagLam (hI := hI) (ha := ha) (hpos := hpos) ht n p b c).fun_add
    (hasDerivAt_diagLam (hI := hI) (ha := ha) (hpos := hpos) ht n b c p)).fun_sub
    (hasDerivAt_diagLam (hI := hI) (ha := ha) (hpos := hpos) ht n c p b)).div_const 2
  have heq : (fun s => (diagonal F I hI a ha hpos).rot s p b c) =ᶠ[𝓝 t]
      fun s => (diagLam a n s p b c + diagLam a n s b c p - diagLam a n s c p b) / 2 := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact rot_diagonal hC hs p b c
  rw [heq.deriv_eq, h.deriv, diagRotDeriv]

variable (a) in
/-- The frame components of the Ricci tensor of the diagonal model in closed form, before the
sums are evaluated. -/
def diagFrameRicci (n : Fin 3 → ℝ) (t : ℝ) (b k : Fin 4) : ℝ :=
  ∑ i, lorentzSign .timeNegative i *
    ((if i = 0 then diagRotDeriv a n t k i b else 0) -
      (if b = 0 then diagRotDeriv a n t k i i else 0) -
      ∑ f, lorentzSign .timeNegative f * (diagRot a n t k f b * diagRot a n t i f i -
        diagRot a n t k f i * diagRot a n t i f b + diagLam a n t f i b * diagRot a n t k i f))

theorem frameRicci_diagonal {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) (b k : Fin 4) :
    (diagonal F I hI a ha hpos).frameRicci t b k = diagFrameRicci a n t b k := by
  simp only [Data.frameRicci, diagFrameRicci, rot_diagonal hC ht, deriv_rot_diagonal hC ht,
    lam_diagonal hC ht]

/-! ### The Ricci tensor -/

/-- **`R₀₀ = −Σ_i ä_i/a_i`.** -/
theorem frameRicci_zero_zero {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 0 0 =
      -(deriv (deriv (a 0)) t / a 0 t + deriv (deriv (a 1)) t / a 1 t +
        deriv (deriv (a 2)) t / a 2 t) := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]
  field_simp
  ring

/-- **`R_{11}`** in the orthonormal frame:
`ä/a + (ȧ/a)(ȧ'/a' + ȧ''/a'') + ((n a²)² − (n' a'² − n'' a''²)²)/(2 (a₁a₂a₃)²)`. -/
theorem frameRicci_one_one {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 1 1 =
      deriv (deriv (a 0)) t / a 0 t +
        deriv (a 0) t / a 0 t * (deriv (a 1) t / a 1 t + deriv (a 2) t / a 2 t) +
        ((n 0 * a 0 t ^ 2) ^ 2 - (n 1 * a 1 t ^ 2 - n 2 * a 2 t ^ 2) ^ 2) /
          (2 * (a 0 t * a 1 t * a 2 t) ^ 2) := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]
  field_simp
  ring

/-- **`R_{22}`** in the orthonormal frame:
`ä/a + (ȧ/a)(ȧ'/a' + ȧ''/a'') + ((n a²)² − (n' a'² − n'' a''²)²)/(2 (a₁a₂a₃)²)`. -/
theorem frameRicci_two_two {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 2 2 =
      deriv (deriv (a 1)) t / a 1 t +
        deriv (a 1) t / a 1 t * (deriv (a 0) t / a 0 t + deriv (a 2) t / a 2 t) +
        ((n 1 * a 1 t ^ 2) ^ 2 - (n 0 * a 0 t ^ 2 - n 2 * a 2 t ^ 2) ^ 2) /
          (2 * (a 0 t * a 1 t * a 2 t) ^ 2) := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]
  field_simp
  ring

/-- **`R_{33}`** in the orthonormal frame:
`ä/a + (ȧ/a)(ȧ'/a' + ȧ''/a'') + ((n a²)² − (n' a'² − n'' a''²)²)/(2 (a₁a₂a₃)²)`. -/
theorem frameRicci_three_three {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 3 3 =
      deriv (deriv (a 2)) t / a 2 t +
        deriv (a 2) t / a 2 t * (deriv (a 0) t / a 0 t + deriv (a 1) t / a 1 t) +
        ((n 2 * a 2 t ^ 2) ^ 2 - (n 0 * a 0 t ^ 2 - n 1 * a 1 t ^ 2) ^ 2) /
          (2 * (a 0 t * a 1 t * a 2 t) ^ 2) := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]
  field_simp
  ring

/-- The off-diagonal component `R_{01} = 0`. -/
theorem frameRicci_zero_one {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 0 1 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{02} = 0`. -/
theorem frameRicci_zero_two {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 0 2 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{03} = 0`. -/
theorem frameRicci_zero_three {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 0 3 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{10} = 0`. -/
theorem frameRicci_one_zero {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 1 0 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{12} = 0`. -/
theorem frameRicci_one_two {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 1 2 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{13} = 0`. -/
theorem frameRicci_one_three {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 1 3 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{20} = 0`. -/
theorem frameRicci_two_zero {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 2 0 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{21} = 0`. -/
theorem frameRicci_two_one {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 2 1 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{23} = 0`. -/
theorem frameRicci_two_three {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 2 3 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{30} = 0`. -/
theorem frameRicci_three_zero {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 3 0 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{31} = 0`. -/
theorem frameRicci_three_one {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 3 1 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- The off-diagonal component `R_{32} = 0`. -/
theorem frameRicci_three_two {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) : (diagonal F I hI a ha hpos).frameRicci t 3 2 = 0 := by
  have h0 := (hpos 0 t ht).ne'
  have h1 := (hpos 1 t ht).ne'
  have h2 := (hpos 2 t ht).ne'
  rw [frameRicci_diagonal hC ht]
  simp [diagFrameRicci, Fin.sum_univ_four, diagRot, diagRotDeriv, diagLam, diagLamDeriv,
    diagVelocity, diagVelocityDeriv, diagStructure, diagStructureDeriv, levi, lorentzSign]

/-- **The off-diagonal frame components of the Ricci tensor vanish.** -/
theorem frameRicci_ne {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0)
    (ht : t ∈ I) {b k : Fin 4} (hbk : b ≠ k) :
    (diagonal F I hI a ha hpos).frameRicci t b k = 0 := by
  fin_cases b <;> fin_cases k
  · exact absurd rfl hbk
  · exact frameRicci_zero_one hC ht
  · exact frameRicci_zero_two hC ht
  · exact frameRicci_zero_three hC ht
  · exact frameRicci_one_zero hC ht
  · exact absurd rfl hbk
  · exact frameRicci_one_two hC ht
  · exact frameRicci_one_three hC ht
  · exact frameRicci_two_zero hC ht
  · exact frameRicci_two_one hC ht
  · exact absurd rfl hbk
  · exact frameRicci_two_three hC ht
  · exact frameRicci_three_zero hC ht
  · exact frameRicci_three_one hC ht
  · exact frameRicci_three_two hC ht
  · exact absurd rfl hbk

/-- **The vacuum equations of a diagonal model of class A** are the four ordinary differential
equations `R₀₀ = R₁₁ = R₂₂ = R₃₃ = 0` on `I`; for type IX (`n = (1, 1, 1)`) these are the
equations of L&L §118. -/
theorem ricci_eq_zero_iff_diagonal {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) :
    (∀ y : (diagonal F I hI a ha hpos).domain,
        (metric (diagonal F I hI a ha hpos)).toLorentzMetric.ricci y = 0) ↔
      ∀ t ∈ I,
        deriv (deriv (a 0)) t / a 0 t + deriv (deriv (a 1)) t / a 1 t +
            deriv (deriv (a 2)) t / a 2 t = 0 ∧
        deriv (deriv (a 0)) t / a 0 t +
            deriv (a 0) t / a 0 t * (deriv (a 1) t / a 1 t + deriv (a 2) t / a 2 t) +
            ((n 0 * a 0 t ^ 2) ^ 2 - (n 1 * a 1 t ^ 2 - n 2 * a 2 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 ∧
        deriv (deriv (a 1)) t / a 1 t +
            deriv (a 1) t / a 1 t * (deriv (a 0) t / a 0 t + deriv (a 2) t / a 2 t) +
            ((n 1 * a 1 t ^ 2) ^ 2 - (n 0 * a 0 t ^ 2 - n 2 * a 2 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 ∧
        deriv (deriv (a 2)) t / a 2 t +
            deriv (a 2) t / a 2 t * (deriv (a 0) t / a 0 t + deriv (a 1) t / a 1 t) +
            ((n 2 * a 2 t ^ 2) ^ 2 - (n 0 * a 0 t ^ 2 - n 1 * a 1 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 := by
  rw [ricci_eq_zero_iff]
  refine forall₂_congr fun t ht => ?_
  have ht' : t ∈ I := ht
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h00 := h 0 0
      rw [frameRicci_zero_zero hC ht'] at h00
      linarith
    · rw [← frameRicci_one_one hC ht']
      exact h 1 1
    · rw [← frameRicci_two_two hC ht']
      exact h 2 2
    · rw [← frameRicci_three_three hC ht']
      exact h 3 3
  · rintro ⟨h0, h1, h2, h3⟩ b k
    by_cases hbk : b = k
    · subst hbk
      fin_cases b
      · exact (frameRicci_zero_zero hC ht').trans (by linarith)
      · exact (frameRicci_one_one hC ht').trans h1
      · exact (frameRicci_two_two hC ht').trans h2
      · exact (frameRicci_three_three hC ht').trans h3
    · exact frameRicci_ne hC ht' hbk

end Data

end ProjectAinos.GeneralRelativity.HomogeneousSpace
