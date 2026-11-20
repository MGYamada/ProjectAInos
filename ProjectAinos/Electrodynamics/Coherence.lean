/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Partially polarized light

A nearly monochromatic wave `E = E₀(t) e^{−iνt}` has a slowly varying complex amplitude
`E₀ : ℝ → Fin 2 → ℂ` in the plane transverse to the propagation (Landau–Lifshitz, *The Classical
Theory of Fields*, §50). Its polarization is described by the coherency matrix
`Jᵢⱼ = ⟨E₀ᵢ E₀ⱼ*⟩`, the long-time average of `E₀ E₀*`. The scope is a classical ensemble: a
continuous amplitude averaged over `[0, T]`, with the limit `T → ∞` as a named premise.

* `coherenceAverage E₀ T` is the average `(1/T) ∫₀ᵀ E₀ E₀* dt`. It is Hermitian
  (`isHermitian_coherenceAverage`), its quadratic form is the average of `|x* · E₀|²`
  (`dotProduct_mulVec_coherenceAverage`), so it is positive semidefinite for `T > 0`
  (`posSemidef_coherenceAverage`). A linear optical element `E₀ ↦ A E₀` transforms it as
  `J ↦ A J Aᴴ` (`coherenceAverage_mulVec`).
* `HasCoherenceMatrix E₀ J` is the premise that the averages converge to `J`. The cone of
  positive semidefinite matrices is closed, so `J` is positive semidefinite
  (`HasCoherenceMatrix.posSemidef`) with `det J ≥ 0` (`HasCoherenceMatrix.det_nonneg`), and
  `A *ᵥ E₀` has the coherency matrix `A J Aᴴ` (`HasCoherenceMatrix.mulVec`).
* `stokes J` are the Stokes parameters `(s₀, s₁, s₂, s₃)`: `s₀` is the intensity and
  `sₖ = s₀ ξₖ` with Landau–Lifshitz's parameters `ξₖ`. For a Hermitian `J`,
  `s₁² + s₂² + s₃² = s₀² − 4 det J` (`sum_sq_stokes`), so `s₁² + s₂² + s₃² ≤ s₀²` for a positive
  semidefinite `J` (`stokes_sq_le`).
* `degreeOfPolarization J = √(s₁² + s₂² + s₃²) / s₀` satisfies `P² = 1 − 4 det J / s₀²`
  (`degreeOfPolarization_sq`) and `0 ≤ P ≤ 1` (`degreeOfPolarization_nonneg`,
  `degreeOfPolarization_le_one`).
* `exists_decomposition`: a positive semidefinite `J` is the sum of the unpolarized part
  `((1 − P) s₀ / 2) · 1` and a polarized part `e e*` of the intensity `P s₀`; the two parts have
  `P = 0` and `P = 1` (`degreeOfPolarization_smul_one`, `degreeOfPolarization_vecMulVec`).
* `posSemidef_conj`, `posSemidef_conj_iff`: `A J Aᴴ` is positive semidefinite for a positive
  semidefinite `J`, and conversely for an invertible `A`.
* `posSemidef_iff_trace_det`: a 2×2 matrix is positive semidefinite exactly when it is Hermitian
  with `tr J ≥ 0` and `det J ≥ 0`.

The premise has proved instances. A constant amplitude `e` has the coherency matrix `e e*`
(`hasCoherenceMatrix_const`), completely polarized for `e ≠ 0`. Components `a e^{iνt}` and `b`
with `ν ≠ 0` are incoherent, with `J = diag(|a|², |b|²)` (`hasCoherenceMatrix_incoherent`) and
`P = ||a|² − |b|²| / (|a|² + |b|²)` (`degreeOfPolarization_incoherent`), partially polarized for
`0 < |b| < |a|`. With `a = b = 1` and `ν = 1`, the relative phase `θ₁ − θ₂ = t` gives natural
light, `J = 1` (`hasCoherenceMatrix_unpolarized`) and `P = 0` (`degreeOfPolarization_one`).
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics.Coherence

open Filter Matrix Topology
open scoped ComplexOrder ComplexConjugate

/-- The time average over `[0, T]` of the coherency matrix `E₀ᵢ E₀ⱼ*` of a complex amplitude
`E₀ : ℝ → Fin 2 → ℂ`. -/
def coherenceAverage (E₀ : ℝ → Fin 2 → ℂ) (T : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, vecMulVec (E₀ t) (star (E₀ t)) i j

/-- The entries of `coherenceAverage`. -/
theorem coherenceAverage_apply (E₀ : ℝ → Fin 2 → ℂ) (T : ℝ) (i j : Fin 2) :
    coherenceAverage E₀ T i j = (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, E₀ t i * star (E₀ t j) := by
  simp [coherenceAverage, vecMulVec_apply]

/-- The integral of a combination of the products `E₀ₖ E₀ₗ*` of a continuous amplitude. -/
private lemma integral_sum_sum {E₀ : ℝ → Fin 2 → ℂ} (hE : Continuous E₀) (T : ℝ)
    (c : Fin 2 → Fin 2 → ℂ) :
    ∫ t in (0 : ℝ)..T, ∑ k, ∑ l, c k l * (E₀ t k * star (E₀ t l)) =
      ∑ k, ∑ l, c k l * ∫ t in (0 : ℝ)..T, E₀ t k * star (E₀ t l) := by
  have hc : ∀ k l, Continuous fun t => c k l * (E₀ t k * star (E₀ t l)) := by
    intro k l
    fun_prop
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (continuous_finsetSum _ fun l _ => hc k l).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum fun l _ => (hc k l).intervalIntegrable _ _]
  simp

/-- The averaged coherency matrix is Hermitian. -/
theorem isHermitian_coherenceAverage (E₀ : ℝ → Fin 2 → ℂ) (T : ℝ) :
    (coherenceAverage E₀ T).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, coherenceAverage_apply, star_mul', Complex.star_def,
    ← intervalIntegral.intervalIntegral_conj, map_inv₀, Complex.conj_ofReal, map_mul,
    Complex.conj_conj]
  simp only [mul_comm]

/-- A linear optical element `A` acting on the amplitude, `E₀ ↦ A E₀`, transforms the averaged
coherency matrix as `J ↦ A J Aᴴ`. -/
theorem coherenceAverage_mulVec {E₀ : ℝ → Fin 2 → ℂ} (hE : Continuous E₀)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (T : ℝ) :
    coherenceAverage (fun t => A *ᵥ E₀ t) T = A * coherenceAverage E₀ T * Aᴴ := by
  ext i j
  have h : ∀ t, (A *ᵥ E₀ t) i * star ((A *ᵥ E₀ t) j) =
      ∑ k, ∑ l, (A i k * star (A j l)) * (E₀ t k * star (E₀ t l)) := by
    intro t
    simp [mulVec, dotProduct, Fin.sum_univ_two]
    ring
  simp only [coherenceAverage_apply, h]
  rw [integral_sum_sum hE]
  simp [Matrix.mul_apply, coherenceAverage_apply, Fin.sum_univ_two]
  ring

/-- The quadratic form of the averaged coherency matrix is the average of
`|x* · E₀|²`. -/
theorem dotProduct_mulVec_coherenceAverage {E₀ : ℝ → Fin 2 → ℂ} (hE : Continuous E₀)
    (T : ℝ) (x : Fin 2 → ℂ) :
    star x ⬝ᵥ (coherenceAverage E₀ T *ᵥ x) =
      ((T⁻¹ * ∫ t in (0 : ℝ)..T, Complex.normSq (star x ⬝ᵥ E₀ t) : ℝ) : ℂ) := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun _ j => star (x j) with hA
  have h1 : star x ⬝ᵥ (coherenceAverage E₀ T *ᵥ x) = (A * coherenceAverage E₀ T * Aᴴ) 0 0 := by
    simp [A, Matrix.mul_apply, dotProduct, mulVec, Fin.sum_univ_two]
    ring
  have h2 : ∀ t, (A *ᵥ E₀ t) 0 * star ((A *ᵥ E₀ t) 0) =
      (Complex.normSq (star x ⬝ᵥ E₀ t) : ℂ) := by
    intro t
    rw [Complex.star_def, Complex.mul_conj]
    simp [A, mulVec, dotProduct]
  rw [h1, ← coherenceAverage_mulVec hE]
  simp only [coherenceAverage_apply, h2]
  rw [intervalIntegral.integral_ofReal]
  push_cast
  rfl

/-- The averaged coherency matrix of a continuous amplitude over `[0, T]`, `T > 0`, is positive
semidefinite. -/
theorem posSemidef_coherenceAverage {E₀ : ℝ → Fin 2 → ℂ} (hE : Continuous E₀) {T : ℝ}
    (hT : 0 < T) : (coherenceAverage E₀ T).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_coherenceAverage E₀ T) fun x => ?_
  rw [dotProduct_mulVec_coherenceAverage hE, Complex.zero_le_real]
  exact mul_nonneg (inv_nonneg.2 hT.le)
    (intervalIntegral.integral_nonneg hT.le fun _ _ => Complex.normSq_nonneg _)

/-! ### The long-time limit -/

/-- The premise that the averages `coherenceAverage E₀ T` converge to `J` as `T → ∞`: `J` is the
coherency matrix of the amplitude `E₀`. -/
def HasCoherenceMatrix (E₀ : ℝ → Fin 2 → ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  Tendsto (coherenceAverage E₀) atTop (𝓝 J)

/-- The coherency matrix of a continuous amplitude is positive semidefinite. -/
theorem HasCoherenceMatrix.posSemidef {E₀ : ℝ → Fin 2 → ℂ} {J : Matrix (Fin 2) (Fin 2) ℂ}
    (h : HasCoherenceMatrix E₀ J) (hE : Continuous E₀) : J.PosSemidef :=
  posSemidef_is_closed.mem_of_tendsto h
    ((eventually_gt_atTop 0).mono fun _ hT => posSemidef_coherenceAverage hE hT)

/-- The determinant of the coherency matrix of a continuous amplitude is nonnegative. -/
theorem HasCoherenceMatrix.det_nonneg {E₀ : ℝ → Fin 2 → ℂ} {J : Matrix (Fin 2) (Fin 2) ℂ}
    (h : HasCoherenceMatrix E₀ J) (hE : Continuous E₀) : 0 ≤ J.det :=
  (h.posSemidef hE).det_nonneg

/-- A linear optical element `A` transforms the coherency matrix as `J ↦ A J Aᴴ`. -/
theorem HasCoherenceMatrix.mulVec {E₀ : ℝ → Fin 2 → ℂ} {J : Matrix (Fin 2) (Fin 2) ℂ}
    (h : HasCoherenceMatrix E₀ J) (hE : Continuous E₀) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    HasCoherenceMatrix (fun t => A *ᵥ E₀ t) (A * J * Aᴴ) := by
  unfold HasCoherenceMatrix
  simp only [funext (coherenceAverage_mulVec hE A)]
  exact (tendsto_const_nhds.mul h).mul tendsto_const_nhds

/-! ### Stokes parameters and the degree of polarization -/

/-- The Stokes parameters `(s₀, s₁, s₂, s₃)` of a coherency matrix: `s₀ = J₁₁ + J₂₂` is the
intensity and `sₖ = J ξₖ` with Landau–Lifshitz's parameters `ξ₁ = 2 Re ρ₁₂`, `ξ₂ = −2 Im ρ₁₂`,
`ξ₃ = ρ₁₁ − ρ₂₂` of `ρ = J / s₀`. -/
def stokes (J : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![(J 0 0 + J 1 1).re, 2 * (J 0 1).re, -2 * (J 0 1).im, (J 0 0 - J 1 1).re]

/-- The diagonal entries of a Hermitian matrix are real. -/
private lemma im_eq_zero {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.IsHermitian) (i : Fin 2) :
    (J i i).im = 0 := by
  have := hJ.apply i i
  rw [Complex.star_def, Complex.conj_eq_iff_im] at this
  exact this

/-- The entry `J₂₁` of a Hermitian 2×2 matrix is `J₁₂*`. -/
private lemma apply_one_zero {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.IsHermitian) :
    J 1 0 = conj (J 0 1) := by
  rw [← hJ.apply 1 0, Complex.star_def]

/-- The determinant of a Hermitian 2×2 matrix is `J₁₁ J₂₂ − |J₁₂|²`. -/
private lemma det_re {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.IsHermitian) :
    J.det.re = (J 0 0).re * (J 1 1).re - Complex.normSq (J 0 1) := by
  rw [det_fin_two, apply_one_zero hJ, Complex.mul_conj]
  simp [im_eq_zero hJ]

/-- For a Hermitian `J`, `s₁² + s₂² + s₃² = s₀² − 4 det J`. -/
theorem sum_sq_stokes {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.IsHermitian) :
    stokes J 1 ^ 2 + stokes J 2 ^ 2 + stokes J 3 ^ 2 = stokes J 0 ^ 2 - 4 * J.det.re := by
  rw [det_re hJ]
  simp [stokes, Complex.normSq_apply]
  ring

/-- The intensity `s₀` of a positive semidefinite coherency matrix is nonnegative. -/
theorem stokes_zero_nonneg {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) :
    0 ≤ stokes J 0 := by
  have := hJ.trace_nonneg
  rw [trace_fin_two, Complex.nonneg_iff] at this
  simpa [stokes] using this.1

/-- The Stokes parameters of a positive semidefinite coherency matrix satisfy
`s₁² + s₂² + s₃² ≤ s₀²`. -/
theorem stokes_sq_le {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) :
    stokes J 1 ^ 2 + stokes J 2 ^ 2 + stokes J 3 ^ 2 ≤ stokes J 0 ^ 2 := by
  have := hJ.det_nonneg
  rw [Complex.nonneg_iff] at this
  rw [sum_sq_stokes hJ.1]
  linarith [this.1]

/-- The degree of polarization `P = √(s₁² + s₂² + s₃²) / s₀`. -/
def degreeOfPolarization (J : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  √(stokes J 1 ^ 2 + stokes J 2 ^ 2 + stokes J 3 ^ 2) / stokes J 0

/-- Landau–Lifshitz's form of the degree of polarization: `P² = 1 − 4 det J / s₀²`. -/
theorem degreeOfPolarization_sq {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.IsHermitian)
    (h0 : stokes J 0 ≠ 0) :
    degreeOfPolarization J ^ 2 = 1 - 4 * J.det.re / stokes J 0 ^ 2 := by
  rw [degreeOfPolarization, div_pow, Real.sq_sqrt (by positivity), sum_sq_stokes hJ]
  field_simp

/-- The degree of polarization is nonnegative. -/
theorem degreeOfPolarization_nonneg {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) :
    0 ≤ degreeOfPolarization J :=
  div_nonneg (Real.sqrt_nonneg _) (stokes_zero_nonneg hJ)

/-- The degree of polarization is at most one. -/
theorem degreeOfPolarization_le_one {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) :
    degreeOfPolarization J ≤ 1 :=
  div_le_one_of_le₀ ((Real.sqrt_le_sqrt (stokes_sq_le hJ)).trans_eq
    (Real.sqrt_sq (stokes_zero_nonneg hJ))) (stokes_zero_nonneg hJ)

/-- A linear optical element preserves positive semidefiniteness: `A J Aᴴ ≥ 0` for `J ≥ 0`. -/
theorem posSemidef_conj {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : (A * J * Aᴴ).PosSemidef :=
  hJ.mul_mul_conjTranspose_same A

/-- For an invertible `A`, `A J Aᴴ` is positive semidefinite exactly when `J` is. -/
theorem posSemidef_conj_iff {J A : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsUnit A) :
    (A * J * Aᴴ).PosSemidef ↔ J.PosSemidef := by
  rw [← star_eq_conjTranspose]
  exact hA.posSemidef_star_right_conjugate_iff

/-! ### The decomposition into a polarized and an unpolarized part -/

/-- A Hermitian 2×2 matrix with nonnegative diagonal and vanishing determinant is `e e*`. -/
private lemma exists_vecMulVec_eq {p q : ℝ} {b : ℂ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : Complex.normSq b = p * q) :
    ∃ e : Fin 2 → ℂ, vecMulVec e (star e) = !![(p : ℂ), b; conj b, (q : ℂ)] := by
  rcases hp.eq_or_lt with hp0 | hp0
  · subst hp0
    have hb : b = 0 := by simpa using h
    subst hb
    refine ⟨![0, (√q : ℂ)], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hq]
  · have hs : (√p : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hp0).ne'
    have hss : (√p : ℂ) * √p = p := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp]
    refine ⟨![(√p : ℂ), conj b / √p], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [vecMulVec_apply, hss]
    · simp [vecMulVec_apply]
      field_simp
    · simp [vecMulVec_apply]
      field_simp
    · simp [vecMulVec_apply]
      have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
      rw [div_mul_div_comm, hss, mul_comm (conj b) b, Complex.mul_conj, h]
      push_cast
      field_simp

/-- A Hermitian 2×2 matrix with `s₀ ≥ 0` and `det J ≥ 0` is `λ · 1 + e e*` with
`λ = (s₀ − √(s₁² + s₂² + s₃²)) / 2 ≥ 0`. -/
private lemma decomposition_aux {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.IsHermitian)
    (h0 : 0 ≤ stokes J 0) (hdet : 0 ≤ J.det.re) :
    0 ≤ stokes J 0 - √(stokes J 1 ^ 2 + stokes J 2 ^ 2 + stokes J 3 ^ 2) ∧
      ∃ e : Fin 2 → ℂ, J =
        (((stokes J 0 - √(stokes J 1 ^ 2 + stokes J 2 ^ 2 + stokes J 3 ^ 2)) / 2 : ℝ) : ℂ) • 1 +
          vecMulVec e (star e) := by
  have hs0 : stokes J 0 = (J 0 0).re + (J 1 1).re := by simp [stokes]
  have hsum : stokes J 1 ^ 2 + stokes J 2 ^ 2 + stokes J 3 ^ 2 =
      ((J 0 0).re - (J 1 1).re) ^ 2 + 4 * Complex.normSq (J 0 1) := by
    simp [stokes, Complex.normSq_apply]
    ring
  rw [det_re hJ] at hdet
  rw [hs0] at h0 ⊢
  rw [hsum]
  have hb := Complex.normSq_nonneg (J 0 1)
  have hr0 := Real.sqrt_nonneg (((J 0 0).re - (J 1 1).re) ^ 2 + 4 * Complex.normSq (J 0 1))
  have hr2 := Real.sq_sqrt (show 0 ≤ ((J 0 0).re - (J 1 1).re) ^ 2 +
    4 * Complex.normSq (J 0 1) by positivity)
  have hrabs := abs_le.1 (Real.abs_le_sqrt (show ((J 0 0).re - (J 1 1).re) ^ 2 ≤
    ((J 0 0).re - (J 1 1).re) ^ 2 + 4 * Complex.normSq (J 0 1) by linarith))
  set r := √(((J 0 0).re - (J 1 1).re) ^ 2 + 4 * Complex.normSq (J 0 1))
  refine ⟨by nlinarith, ?_⟩
  obtain ⟨e, he⟩ := exists_vecMulVec_eq (p := ((J 0 0).re - (J 1 1).re + r) / 2)
    (q := ((J 1 1).re - (J 0 0).re + r) / 2) (b := J 0 1) (by linarith) (by linarith)
    (by linear_combination (-1 / 4 : ℝ) * hr2)
  refine ⟨e, ?_⟩
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [im_eq_zero hJ]
    ring
  · simp
  · simp [apply_one_zero hJ]
  · apply Complex.ext <;> simp [im_eq_zero hJ]
    ring

/-- The 2×2 criterion: a matrix is positive semidefinite exactly when it is Hermitian with a
nonnegative trace and a nonnegative determinant. -/
theorem posSemidef_iff_trace_det {J : Matrix (Fin 2) (Fin 2) ℂ} :
    J.PosSemidef ↔ J.IsHermitian ∧ 0 ≤ J.trace ∧ 0 ≤ J.det := by
  refine ⟨fun hJ => ⟨hJ.1, hJ.trace_nonneg, hJ.det_nonneg⟩, fun ⟨hJ, htr, hdet⟩ => ?_⟩
  have h0 : 0 ≤ stokes J 0 := by
    rw [trace_fin_two, Complex.nonneg_iff] at htr
    simpa [stokes] using htr.1
  obtain ⟨hl, e, he⟩ := decomposition_aux hJ h0 (Complex.nonneg_iff.1 hdet).1
  rw [he]
  exact (PosSemidef.one.smul (Complex.zero_le_real.2 (by linarith))).add
    (posSemidef_vecMulVec_self_star e)

/-- A positive semidefinite coherency matrix is the sum of an unpolarized part, a nonnegative
multiple `(1 − P) s₀ / 2` of the identity, and a polarized part `e e*` of the intensity `P s₀`. -/
theorem exists_decomposition {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) :
    ∃ e : Fin 2 → ℂ,
      J = (((1 - degreeOfPolarization J) * stokes J 0 / 2 : ℝ) : ℂ) • 1 +
          vecMulVec e (star e) ∧
        stokes (vecMulVec e (star e)) 0 = degreeOfPolarization J * stokes J 0 := by
  obtain ⟨-, e, he⟩ :=
    decomposition_aux hJ.1 (stokes_zero_nonneg hJ) (Complex.nonneg_iff.1 hJ.det_nonneg).1
  have hkey : (1 - degreeOfPolarization J) * stokes J 0 / 2 =
      (stokes J 0 - √(stokes J 1 ^ 2 + stokes J 2 ^ 2 + stokes J 3 ^ 2)) / 2 := by
    rcases (stokes_zero_nonneg hJ).eq_or_lt with h | h
    · have hsq : √(stokes J 1 ^ 2 + stokes J 2 ^ 2 + stokes J 3 ^ 2) = 0 :=
        Real.sqrt_eq_zero'.2 (by have := stokes_sq_le hJ; rw [← h] at this; linarith)
      simp [degreeOfPolarization, ← h, hsq]
    · unfold degreeOfPolarization
      field_simp
  rw [← hkey] at he
  refine ⟨e, he, ?_⟩
  generalize hc : (1 - degreeOfPolarization J) * stokes J 0 / 2 = c at he
  have h2 : stokes J 0 = 2 * c + stokes (vecMulVec e (star e)) 0 := by
    rw [he]
    simp [stokes]
    ring
  linear_combination -h2 + 2 * hc

/-- An unpolarized coherency matrix `c · 1` has the degree of polarization zero. -/
theorem degreeOfPolarization_smul_one (c : ℝ) :
    degreeOfPolarization ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
  simp [degreeOfPolarization, stokes]

/-- A polarized coherency matrix `e e*`, `e ≠ 0`, has the degree of polarization one. -/
theorem degreeOfPolarization_vecMulVec {e : Fin 2 → ℂ} (he : e ≠ 0) :
    degreeOfPolarization (vecMulVec e (star e)) = 1 := by
  have hdet : (vecMulVec e (star e)).det = 0 := by
    rw [det_fin_two]
    simp [vecMulVec_apply]
    ring
  have hpos : 0 < stokes (vecMulVec e (star e)) 0 := by
    have h : e 0 ≠ 0 ∨ e 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact he (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    have h0 := Complex.normSq_nonneg (e 0)
    have h1 := Complex.normSq_nonneg (e 1)
    simp only [stokes, vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj]
    simp only [Matrix.cons_val_zero, Complex.add_re, Complex.ofReal_re]
    rcases h with h | h
    · linarith [Complex.normSq_pos.2 h]
    · linarith [Complex.normSq_pos.2 h]
  unfold degreeOfPolarization
  rw [sum_sq_stokes (posSemidef_vecMulVec_self_star e).1, hdet, Complex.zero_re, mul_zero,
    sub_zero, Real.sqrt_sq hpos.le, div_self hpos.ne']

/-! ### Instances -/

/-- A constant amplitude `e` has the coherency matrix `e e*`; for `e ≠ 0` it is completely
polarized (`degreeOfPolarization_vecMulVec`). -/
theorem hasCoherenceMatrix_const (e : Fin 2 → ℂ) :
    HasCoherenceMatrix (fun _ => e) (vecMulVec e (star e)) := by
  have h : ∀ T : ℝ, T ≠ 0 → coherenceAverage (fun _ => e) T = vecMulVec e (star e) := by
    intro T hT
    have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
    ext i j
    rw [coherenceAverage_apply]
    simp [vecMulVec_apply]
    field_simp
  exact tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT => (h T hT).symm)

/-- The average `(1/T) K ∫₀ᵀ e^{iνt} dt` of an oscillating term tends to zero for `ν ≠ 0`. -/
private lemma tendsto_inv_mul_exp_sub_one (K : ℂ) {ν : ℝ} (hν : ν ≠ 0) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * (K * ((Complex.exp (ν * Complex.I * T) - 1) /
      (ν * Complex.I)))) atTop (𝓝 0) := by
  have hc : (ν : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hν) Complex.I_ne_zero
  have hbound : ∀ T : ℝ, 0 < T → ‖(T : ℂ)⁻¹ * (K * ((Complex.exp (ν * Complex.I * T) - 1) /
      (ν * Complex.I)))‖ ≤ (2 * ‖K‖ / ‖(ν : ℂ) * Complex.I‖) * T⁻¹ := by
    intro T hT
    have he : ‖Complex.exp (ν * Complex.I * T)‖ = 1 := by
      rw [show (ν : ℂ) * Complex.I * T = ((ν * T : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have h2 : ‖Complex.exp (ν * Complex.I * T) - 1‖ ≤ 2 := by
      calc _ ≤ ‖Complex.exp (ν * Complex.I * T)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [he, norm_one]; norm_num
    have hn : 0 < ‖(ν : ℂ) * Complex.I‖ := norm_pos_iff.2 hc
    rw [norm_mul, norm_mul, norm_div, norm_inv, Complex.norm_real, Real.norm_of_nonneg hT.le]
    rw [show 2 * ‖K‖ / ‖(ν : ℂ) * Complex.I‖ * T⁻¹ =
      T⁻¹ * (‖K‖ * (2 / ‖(ν : ℂ) * Complex.I‖)) by ring]
    gcongr
  refine squeeze_zero_norm' ((eventually_gt_atTop 0).mono hbound) ?_
  simpa using tendsto_inv_atTop_zero.const_mul (2 * ‖K‖ / ‖(ν : ℂ) * Complex.I‖)

/-- Components with the amplitudes `a`, `b` whose relative phase drifts uniformly,
`θ₁ − θ₂ = ν t` with `ν ≠ 0`, are incoherent: the coherency matrix is
`diag(|a|², |b|²)`. -/
theorem hasCoherenceMatrix_incoherent (a b : ℂ) {ν : ℝ} (hν : ν ≠ 0) :
    HasCoherenceMatrix (fun t => ![a * Complex.exp (ν * t * Complex.I), b])
      !![(Complex.normSq a : ℂ), 0; 0, (Complex.normSq b : ℂ)] := by
  set E₀ : ℝ → Fin 2 → ℂ := fun t => ![a * Complex.exp (ν * t * Complex.I), b] with hE
  have hc : (ν : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hν) Complex.I_ne_zero
  have hexp : ∀ t : ℝ, Complex.normSq (Complex.exp (ν * t * Complex.I)) = 1 := by
    intro t
    rw [Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hdiag : ∀ (c : ℂ) (f : ℝ → ℂ), (∀ t, f t * star (f t) = c) →
      ∀ᶠ T : ℝ in atTop, (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, f t * star (f t) = c := by
    intro c f hf
    refine (eventually_ne_atTop 0).mono fun T hT => ?_
    have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
    simp only [hf, intervalIntegral.integral_const, sub_zero, Complex.real_smul]
    field_simp
  have h00 : ∀ᶠ T in atTop, coherenceAverage E₀ T 0 0 = Complex.normSq a := by
    simp only [coherenceAverage_apply]
    refine hdiag _ (fun t => E₀ t 0) fun t => ?_
    simp only [hE, Matrix.cons_val_zero, Complex.star_def, Complex.mul_conj, Complex.normSq_mul,
      hexp, mul_one]
  have h11 : ∀ᶠ T in atTop, coherenceAverage E₀ T 1 1 = Complex.normSq b := by
    simp only [coherenceAverage_apply]
    refine hdiag _ (fun t => E₀ t 1) fun t => ?_
    simp [hE, Complex.mul_conj]
  have h01 : Tendsto (fun T => coherenceAverage E₀ T 0 1) atTop (𝓝 0) := by
    refine (tendsto_inv_mul_exp_sub_one (a * star b) hν).congr fun T => ?_
    rw [coherenceAverage_apply]
    congr 1
    have h : ∀ t : ℝ, E₀ t 0 * star (E₀ t 1) =
        a * star b * Complex.exp (ν * Complex.I * t) := by
      intro t
      simp only [hE, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring_nf
    simp only [h, intervalIntegral.integral_const_mul, integral_exp_mul_complex hc,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have h10 : Tendsto (fun T => coherenceAverage E₀ T 1 0) atTop (𝓝 0) := by
    have := h01.star
    rw [star_zero] at this
    exact this.congr fun T => (isHermitian_coherenceAverage E₀ T).apply 1 0
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa using tendsto_const_nhds.congr' (h00.mono fun T hT => hT.symm)
  · simpa using h01
  · simpa using h10
  · simpa using tendsto_const_nhds.congr' (h11.mono fun T hT => hT.symm)

/-- The degree of polarization of `diag(|a|², |b|²)` is `||a|² − |b|²| / (|a|² + |b|²)`. -/
theorem degreeOfPolarization_incoherent (a b : ℂ) :
    degreeOfPolarization !![(Complex.normSq a : ℂ), 0; 0, (Complex.normSq b : ℂ)] =
      |Complex.normSq a - Complex.normSq b| / (Complex.normSq a + Complex.normSq b) := by
  simp [degreeOfPolarization, stokes, Real.sqrt_sq_eq_abs]

/-- Components of equal amplitude with the relative phase `θ₁ − θ₂ = t` give the coherency
matrix `1`: natural, unpolarized light. -/
theorem hasCoherenceMatrix_unpolarized :
    HasCoherenceMatrix (fun t : ℝ => ![Complex.exp (t * Complex.I), 1]) 1 := by
  have h := hasCoherenceMatrix_incoherent 1 1 one_ne_zero
  have h1 : (fun t : ℝ => ![1 * Complex.exp (((1 : ℝ) : ℂ) * t * Complex.I), (1 : ℂ)]) =
      fun t : ℝ => ![Complex.exp (t * Complex.I), 1] := by
    funext t
    simp
  have h2 : !![(Complex.normSq 1 : ℂ), 0; 0, (Complex.normSq 1 : ℂ)] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h1, h2] at h
  exact h

/-- The coherency matrix `1` of natural light has the degree of polarization zero. -/
theorem degreeOfPolarization_one : degreeOfPolarization (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simpa using degreeOfPolarization_smul_one 1

end ProjectAinos.Electrodynamics.Coherence
