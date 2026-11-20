/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.Coherence

/-! Public consumers of partially polarized light (Landau–Lifshitz §50): the time averages of a
complex amplitude, the coherency matrix as their limit with its positivity and its transformation,
the Stokes parameters and the degree of polarization, the decomposition into a polarized and an
unpolarized part, the trace–determinant criterion, and the polarized, partially polarized and
unpolarized instances. Default elaborator options are intentional: these checks must not rely on
the implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section

section Coherence

namespace ProjectAinos.Electrodynamics.Coherence

open Filter Matrix Topology

open scoped ComplexOrder ComplexConjugate

example (E₀ : ℝ → Fin 2 → ℂ) (T : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  coherenceAverage E₀ T

example (E₀ : ℝ → Fin 2 → ℂ) (T : ℝ) (i j : Fin 2) :
    coherenceAverage E₀ T i j = (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, E₀ t i * star (E₀ t j) :=
  coherenceAverage_apply E₀ T i j

example (E₀ : ℝ → Fin 2 → ℂ) (T : ℝ) :
    (coherenceAverage E₀ T).IsHermitian :=
  isHermitian_coherenceAverage E₀ T

example {E₀ : ℝ → Fin 2 → ℂ} (hE : Continuous E₀) (A : Matrix (Fin 2) (Fin 2) ℂ) (T : ℝ) :
    coherenceAverage (fun t => A *ᵥ E₀ t) T = A * coherenceAverage E₀ T * Aᴴ :=
  coherenceAverage_mulVec hE A T

example {E₀ : ℝ → Fin 2 → ℂ} (hE : Continuous E₀) (T : ℝ) (x : Fin 2 → ℂ) :
    star x ⬝ᵥ (coherenceAverage E₀ T *ᵥ x) =
      ((T⁻¹ * ∫ t in (0 : ℝ)..T, Complex.normSq (star x ⬝ᵥ E₀ t) : ℝ) : ℂ) :=
  dotProduct_mulVec_coherenceAverage hE T x

example {E₀ : ℝ → Fin 2 → ℂ} (hE : Continuous E₀) {T : ℝ} (hT : 0 < T) :
    (coherenceAverage E₀ T).PosSemidef :=
  posSemidef_coherenceAverage hE hT

example (E₀ : ℝ → Fin 2 → ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) :
    Prop :=
  HasCoherenceMatrix E₀ J

example {E₀ : ℝ → Fin 2 → ℂ} {J : Matrix (Fin 2) (Fin 2) ℂ} (h : HasCoherenceMatrix E₀ J)
    (hE : Continuous E₀) :
    J.PosSemidef :=
  HasCoherenceMatrix.posSemidef h hE

example {E₀ : ℝ → Fin 2 → ℂ} {J : Matrix (Fin 2) (Fin 2) ℂ} (h : HasCoherenceMatrix E₀ J)
    (hE : Continuous E₀) :
    0 ≤ J.det :=
  HasCoherenceMatrix.det_nonneg h hE

example {E₀ : ℝ → Fin 2 → ℂ} {J : Matrix (Fin 2) (Fin 2) ℂ} (h : HasCoherenceMatrix E₀ J)
    (hE : Continuous E₀) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    HasCoherenceMatrix (fun t => A *ᵥ E₀ t) (A * J * Aᴴ) :=
  HasCoherenceMatrix.mulVec h hE A

example (J : Matrix (Fin 2) (Fin 2) ℂ) :
    Fin 4 → ℝ :=
  stokes J

example {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.IsHermitian) :
    stokes J 1 ^ 2 + stokes J 2 ^ 2 + stokes J 3 ^ 2 = stokes J 0 ^ 2 - 4 * J.det.re :=
  sum_sq_stokes hJ

example {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) :
    0 ≤ stokes J 0 :=
  stokes_zero_nonneg hJ

example {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) :
    stokes J 1 ^ 2 + stokes J 2 ^ 2 + stokes J 3 ^ 2 ≤ stokes J 0 ^ 2 :=
  stokes_sq_le hJ

example (J : Matrix (Fin 2) (Fin 2) ℂ) :
    ℝ :=
  degreeOfPolarization J

example {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.IsHermitian) (h0 : stokes J 0 ≠ 0) :
    degreeOfPolarization J ^ 2 = 1 - 4 * J.det.re / stokes J 0 ^ 2 :=
  degreeOfPolarization_sq hJ h0

example {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) :
    0 ≤ degreeOfPolarization J :=
  degreeOfPolarization_nonneg hJ

example {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) :
    degreeOfPolarization J ≤ 1 :=
  degreeOfPolarization_le_one hJ

example {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (A * J * Aᴴ).PosSemidef :=
  posSemidef_conj hJ A

example {J A : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsUnit A) :
    (A * J * Aᴴ).PosSemidef ↔ J.PosSemidef :=
  posSemidef_conj_iff hA

example {J : Matrix (Fin 2) (Fin 2) ℂ} :
    J.PosSemidef ↔ J.IsHermitian ∧ 0 ≤ J.trace ∧ 0 ≤ J.det :=
  posSemidef_iff_trace_det

example {J : Matrix (Fin 2) (Fin 2) ℂ} (hJ : J.PosSemidef) :
    ∃ e : Fin 2 → ℂ,
      J = (((1 - degreeOfPolarization J) * stokes J 0 / 2 : ℝ) : ℂ) • 1 +
          vecMulVec e (star e) ∧
        stokes (vecMulVec e (star e)) 0 = degreeOfPolarization J * stokes J 0 :=
  exists_decomposition hJ

example (c : ℝ) :
    degreeOfPolarization ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 :=
  degreeOfPolarization_smul_one c

example {e : Fin 2 → ℂ} (he : e ≠ 0) :
    degreeOfPolarization (vecMulVec e (star e)) = 1 :=
  degreeOfPolarization_vecMulVec he

example (e : Fin 2 → ℂ) :
    HasCoherenceMatrix (fun _ => e) (vecMulVec e (star e)) :=
  hasCoherenceMatrix_const e

example (a b : ℂ) {ν : ℝ} (hν : ν ≠ 0) :
    HasCoherenceMatrix (fun t => ![a * Complex.exp (ν * t * Complex.I), b])
      !![(Complex.normSq a : ℂ), 0; 0, (Complex.normSq b : ℂ)] :=
  hasCoherenceMatrix_incoherent a b hν

example (a b : ℂ) :
    degreeOfPolarization !![(Complex.normSq a : ℂ), 0; 0, (Complex.normSq b : ℂ)] =
      |Complex.normSq a - Complex.normSq b| / (Complex.normSq a + Complex.normSq b) :=
  degreeOfPolarization_incoherent a b

example :
    HasCoherenceMatrix (fun t : ℝ => ![Complex.exp (t * Complex.I), 1]) 1 :=
  hasCoherenceMatrix_unpolarized

example :
    degreeOfPolarization (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 :=
  degreeOfPolarization_one

end ProjectAinos.Electrodynamics.Coherence

end Coherence
