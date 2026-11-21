/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Linearized
public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorQuadratic
public import ProjectAinos.SmoothGeometry.Euclidean.SphereIntegral
import Mathlib.Tactic

/-!
# The flux of the pseudotensor of a plane wave and the transverse-traceless part

Space-time has the signature `(−+++)` (`LorentzConvention.timeNegative`) and the Minkowski
coefficients `η = diag(−1, 1, 1, 1)`. A perturbation that depends on `t − ⟨n, x⟩` for a unit
vector `n` has the derivatives `∂_c h_{ab} = k_c ḣ_{ab}` with the null covector `k = (1, −n)`
(`waveCovector`), so its linearized Christoffel symbols are
`δΓ^c_{ab} = ½ η^{cc}(k_a ḣ_{bc} + k_b ḣ_{ca} − k_c ḣ_{ab})` (`planeChristoffel`).

* `planeFlux n A = ½ Σ_α {…}^{0α} n_α`: the radial flux `t^{0α} n_α` of the part of the
  pseudotensor (Landau–Lifshitz, (96.9)) quadratic in these symbols, with the braces
  `pseudoBraces` of `η` and `planeChristoffel (waveCovector n) A`.
* `ttSquare n S = Σ S² − 2|Sn|² + ½(nSn)² − ½(tr S)² + tr S · nSn`, which is `Σ (ΛS)²` for the
  transverse-traceless projection `ΛS = PSP − ½ P tr(PS)`, `P = 1 − n nᵀ`
  (`transverseTraceless`, `sum_sq_transverseTraceless`).
* `planeFlux_eq`: **the flux of a plane wave** is `¼ ttSquare n S + ⅛ (tr S − nSn)(2A₀₀ − 3 tr S +
  nSn)` for a symmetric `A` with the spatial part `S`; the components `A₀α` do not enter, and
  `A₀₀` enters only through the last term. `planeFlux_traceReverse`: for the trace reverse
  `A = Ā − ½ η tr Ā` of an amplitude in harmonic gauge, `Ā₀ᵦ = −Σ_α n_α Ā_{αb}`, the last term
  vanishes and the flux is `¼ ttSquare n S̄` (Landau–Lifshitz, §107:
  `t^{01} = ḣ₂₃² + ¼(ḣ₂₂ − ḣ₃₃)²` up to the factor `c²/16πk`, which is `1/2κ` here).
* `integral_ttSquare`: **the angular integral** `∫ ttSquare n S dσ = (8π/45) Σ D²` with
  `D = 3S − δ tr S` (`quadrupoleOf`), from the second and fourth moments of the sphere.
* Analysis: `continuous_pseudoBraces`, `continuous_planeFlux`, the homogeneity
  `pseudoBraces_mul` and `ttSquare_mul`, and the bound `abs_ttSquare_sub_le` of the difference
  of two transverse-traceless squares through the polarization `ttBilinear`.

The identities `planeFlux_eq` and `sum_sq_transverseTraceless` were found and checked with SymPy;
in Lean they are the identities of polynomials modulo `‖n‖² = 1` that `linear_combination`
certifies.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real

namespace ProjectAinos.SmoothGeometry.Wave

open Sphere CoordinateMetric

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Plane waves -/

/-- The null covector `k = (1, −n)` of a wave going out in the direction `n`:
`∂_c f(t − ⟨n, x⟩) = k_c f'`. -/
def waveCovector (n : E3) : Fin 4 → ℝ := ![1, -n 0, -n 1, -n 2]

/-- The linearized Christoffel symbols `δΓ^c_{ab} = ½ η^{cc}(k_a A_{bc} + k_b A_{ca} − k_c A_{ab})`
of a perturbation with the derivatives `∂_c h_{ab} = k_c A_{ab}`, in the index order of
`CoordinateMetric.linearizedChristoffel`. -/
def planeChristoffel (k : Fin 4 → ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) (c a b : Fin 4) : ℝ :=
  lorentzSign (d := 3) .timeNegative c * (k a * A b c + k b * A c a - k c * A a b) / 2

/-- The radial flux `t^{0α} n_α = ½ Σ_α {…}^{0α} n_α` of the quadratic pseudotensor of a plane
wave with the amplitude `A` of `∂_c h = k_c A`. -/
def planeFlux (n : E3) (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (∑ α : Fin 3, pseudoBraces (fun a b : Fin 4 => Minkowski.metricMatrix .timeNegative 3 a b)
    (planeChristoffel (waveCovector n) A) 0 α.succ * n α) / 2

/-- The square `Σ (ΛS)²` of the transverse-traceless part of a symmetric matrix, written as
`Σ S² − 2|Sn|² + ½(nSn)² − ½(tr S)² + tr S · nSn`. -/
def ttSquare (n : E3) (S : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, S i j ^ 2 - 2 * ∑ i, (∑ j, S i j * n j) ^ 2 +
    (∑ i, ∑ j, n i * S i j * n j) ^ 2 / 2 - (∑ i, S i i) ^ 2 / 2 +
    (∑ i, S i i) * ∑ i, ∑ j, n i * S i j * n j

/-- The transverse-traceless projection `ΛS = PSP − ½ P tr(PS)` with `P = 1 − n nᵀ`. -/
def transverseTraceless (n : E3) (S : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  ∑ a, ∑ b, ((if i = a then 1 else 0) - n i * n a) * S a b * ((if b = j then 1 else 0) - n b * n j)
    - ((if i = j then 1 else 0) - n i * n j) / 2 *
      ∑ a, ∑ b, ((if a = b then 1 else 0) - n a * n b) * S b a

/-- The quadrupole tensor `D = 3S − δ tr S` of a symmetric matrix `S` of second moments. -/
def quadrupoleOf (S : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  3 * S i j - if i = j then ∑ l, S l l else 0

/-- The sum of the squares of the components of a unit vector is `1`. -/
theorem sum_sq_eq_one {n : E3} (hn : ‖n‖ = 1) : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq n
  rw [hn, Fin.sum_univ_three] at h
  rw [← h]
  norm_num

private theorem lorentzSign_zero' : lorentzSign (d := 3) .timeNegative 0 = -1 := by
  simp [lorentzSign]

private theorem lorentzSign_one' : lorentzSign (d := 3) .timeNegative 1 = 1 := by
  simp [lorentzSign]

private theorem lorentzSign_two' : lorentzSign (d := 3) .timeNegative 2 = 1 := by
  simp [lorentzSign]

private theorem lorentzSign_three' : lorentzSign (d := 3) .timeNegative 3 = 1 := by
  simp [lorentzSign]

private theorem flatTrace_four (A : Matrix (Fin 4) (Fin 4) ℝ) :
    flatTrace .timeNegative A = -A 0 0 + A 1 1 + A 2 2 + A 3 3 := by
  simp only [flatTrace, Fin.sum_univ_succ, Fin.sum_univ_zero, lorentzSign, Fin.succ_ne_zero,
    ite_true, ite_false]
  simp
  ring

/-- **The flux of a plane wave**: for a unit vector `n` and a symmetric amplitude `A` with the
spatial part `S`, `t^{0α} n_α = ¼ ttSquare n S + ⅛ (tr S − nSn)(2A₀₀ − 3 tr S + nSn)`. -/
theorem planeFlux_eq {n : E3} (hn : ‖n‖ = 1) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : ∀ a b, A a b = A b a) :
    planeFlux n A = ttSquare n (fun i j => A i.succ j.succ) / 4 +
      ((∑ i : Fin 3, A i.succ i.succ) - ∑ i : Fin 3, ∑ j : Fin 3, n i * A i.succ j.succ * n j) *
        (2 * A 0 0 - 3 * (∑ i : Fin 3, A i.succ i.succ) +
          ∑ i : Fin 3, ∑ j : Fin 3, n i * A i.succ j.succ * n j) / 8 := by
  have hn' := sum_sq_eq_one hn
  have h10 := hA 1 0
  have h20 := hA 2 0
  have h30 := hA 3 0
  have h21 := hA 2 1
  have h31 := hA 3 1
  have h32 := hA 3 2
  have k0 : waveCovector n 0 = 1 := rfl
  have k1 : waveCovector n 1 = -n 0 := rfl
  have k2 : waveCovector n 2 = -n 1 := rfl
  have k3 : waveCovector n 3 = -n 2 := rfl
  simp only [planeFlux, pseudoBraces, Fin.sum_univ_four, Fin.sum_univ_three, metricMatrix_apply,
    planeChristoffel, k0, k1, k2, k3, ttSquare, lorentzSign_zero', lorentzSign_one',
    lorentzSign_two', lorentzSign_three']
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceEq, ite_true,
    ite_false, Fin.reduceSucc, h10, h20, h30, h21, h31, h32, k1, k2, k3, lorentzSign_one',
    lorentzSign_two', lorentzSign_three', mul_zero, zero_mul, add_zero, zero_add, sub_zero, mul_one,
    one_mul]
  linear_combination (A 0 0 * A 1 1 + A 0 0 * A 2 2 + A 0 0 * A 3 3 - A 1 1 ^ 2 -
    4 * A 1 1 * A 2 2 - 4 * A 1 1 * A 3 3 + 2 * A 1 2 ^ 2 + 2 * A 1 3 ^ 2 - A 2 2 ^ 2 -
    4 * A 2 2 * A 3 3 + 2 * A 2 3 ^ 2 - A 3 3 ^ 2) / 4 * hn'

/-- The trace reverse of a symmetric matrix is symmetric. -/
theorem traceReverse_symm {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a) (a b : Fin 4) :
    traceReverse .timeNegative A a b = traceReverse .timeNegative A b a := by
  rw [traceReverse_apply, traceReverse_apply, hA a b, metricMatrix_apply, metricMatrix_apply]
  by_cases h : a = b
  · subst h
    rfl
  · simp [h, Ne.symm h]

/-- **The flux of a wave in harmonic gauge** (Landau–Lifshitz, §107): if the amplitude `Ā` of
the trace-reversed perturbation is symmetric and in harmonic gauge, `Ā₀ᵦ = −Σ_α n_α Ā_{αb}`, the
flux of the trace reverse `A = Ā − ½ η tr Ā` is `¼ ttSquare n S̄`, with the spatial part `S̄` of
`Ā`. -/
theorem planeFlux_traceReverse {n : E3} (hn : ‖n‖ = 1) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : ∀ a b, A a b = A b a) (hg : ∀ b, A 0 b = -∑ α : Fin 3, n α * A α.succ b) :
    planeFlux n (traceReverse .timeNegative A) = ttSquare n (fun i j => A i.succ j.succ) / 4 := by
  have hn' := sum_sq_eq_one hn
  rw [planeFlux_eq hn (traceReverse_symm hA)]
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  have h3 := hg 3
  have h10 := hA 1 0
  have h20 := hA 2 0
  have h30 := hA 3 0
  have h21 := hA 2 1
  have h31 := hA 3 1
  have h32 := hA 3 2
  simp only [ttSquare, traceReverse_apply, flatTrace_four, Fin.sum_univ_three, metricMatrix_apply,
    Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Fin.reduceEq,
    ite_true, ite_false, lorentzSign_zero', lorentzSign_one', lorentzSign_two', lorentzSign_three',
    h10, h20, h30, h21, h31, h32] at h0 h1 h2 h3 ⊢
  linear_combination (((-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2) * (2 * (n 0 * A 1 1 * n 0 +
    n 0 * A 1 2 * n 1 + n 0 * A 1 3 * n 2 + n 1 * A 1 2 * n 0 + n 1 * A 2 2 * n 1 +
    n 1 * A 2 3 * n 2 + n 2 * A 1 3 * n 0 + n 2 * A 2 3 * n 1 + n 2 * A 3 3 * n 2) + 2 * (A 1 1 +
    A 2 2 + A 3 3) + (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2) * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) +
    3 * (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2)) / 2) / 4 - (-(-A 0 0 + A 1 1 + A 2 2 +
    A 3 3) / 2) * (2 * (A 0 0 - (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2)) - 3 * ((A 1 1 + A 2 2 +
    A 3 3) + 3 * (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2)) + (n 0 * A 1 1 * n 0 + n 0 * A 1 2 * n 1
    + n 0 * A 1 3 * n 2 + n 1 * A 1 2 * n 0 + n 1 * A 2 2 * n 1 + n 1 * A 2 3 * n 2 +
    n 2 * A 1 3 * n 0 + n 2 * A 2 3 * n 1 + n 2 * A 3 3 * n 2) + (-(-A 0 0 + A 1 1 + A 2 2 +
    A 3 3) / 2) * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2)) / 8) * hn' + (2 * (A 0 0 - (-(-A 0 0 + A 1 1 +
    A 2 2 + A 3 3) / 2)) - 3 * ((A 1 1 + A 2 2 + A 3 3) + 3 * (-(-A 0 0 + A 1 1 + A 2 2 +
    A 3 3) / 2)) + (n 0 * A 1 1 * n 0 + n 0 * A 1 2 * n 1 + n 0 * A 1 3 * n 2 + n 1 * A 1 2 * n 0 +
    n 1 * A 2 2 * n 1 + n 1 * A 2 3 * n 2 + n 2 * A 1 3 * n 0 + n 2 * A 2 3 * n 1 +
    n 2 * A 3 3 * n 2) + (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2) * (n 0 ^ 2 + n 1 ^ 2 +
    n 2 ^ 2)) / 8 * h0 - (2 * (A 0 0 - (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2)) - 3 * ((A 1 1 +
    A 2 2 + A 3 3) + 3 * (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2)) + (n 0 * A 1 1 * n 0 +
    n 0 * A 1 2 * n 1 + n 0 * A 1 3 * n 2 + n 1 * A 1 2 * n 0 + n 1 * A 2 2 * n 1 +
    n 1 * A 2 3 * n 2 + n 2 * A 1 3 * n 0 + n 2 * A 2 3 * n 1 + n 2 * A 3 3 * n 2) + (-(-A 0 0 +
    A 1 1 + A 2 2 + A 3 3) / 2) * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2)) / 8 * n 0 * h1 - (2 * (A 0 0 -
    (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2)) - 3 * ((A 1 1 + A 2 2 + A 3 3) + 3 * (-(-A 0 0 + A 1 1
    + A 2 2 + A 3 3) / 2)) + (n 0 * A 1 1 * n 0 + n 0 * A 1 2 * n 1 + n 0 * A 1 3 * n 2 +
    n 1 * A 1 2 * n 0 + n 1 * A 2 2 * n 1 + n 1 * A 2 3 * n 2 + n 2 * A 1 3 * n 0 +
    n 2 * A 2 3 * n 1 + n 2 * A 3 3 * n 2) + (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2) * (n 0 ^ 2 +
    n 1 ^ 2 + n 2 ^ 2)) / 8 * n 1 * h2 - (2 * (A 0 0 - (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2)) -
    3 * ((A 1 1 + A 2 2 + A 3 3) + 3 * (-(-A 0 0 + A 1 1 + A 2 2 + A 3 3) / 2)) + (n 0 * A 1 1 * n 0
    + n 0 * A 1 2 * n 1 + n 0 * A 1 3 * n 2 + n 1 * A 1 2 * n 0 + n 1 * A 2 2 * n 1 +
    n 1 * A 2 3 * n 2 + n 2 * A 1 3 * n 0 + n 2 * A 2 3 * n 1 + n 2 * A 3 3 * n 2) + (-(-A 0 0 +
    A 1 1 + A 2 2 + A 3 3) / 2) * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2)) / 8 * n 2 * h3

/-- The square of the transverse-traceless part is homogeneous of degree two. -/
theorem ttSquare_mul (n : E3) (S : Fin 3 → Fin 3 → ℝ) (c : ℝ) :
    ttSquare n (fun i j => c * S i j) = c ^ 2 * ttSquare n S := by
  simp only [ttSquare, Fin.sum_univ_three]
  ring

/-- **The transverse-traceless projection**: for a unit vector `n` and a symmetric `S`,
`Σ (ΛS)² = ttSquare n S`. -/
theorem sum_sq_transverseTraceless {n : E3} (hn : ‖n‖ = 1) {S : Fin 3 → Fin 3 → ℝ}
    (hS : ∀ i j, S i j = S j i) :
    ∑ i, ∑ j, transverseTraceless n S i j ^ 2 = ttSquare n S := by
  have hn' := sum_sq_eq_one hn
  have h10 := hS 1 0
  have h20 := hS 2 0
  have h21 := hS 2 1
  simp only [transverseTraceless, ttSquare, Fin.sum_univ_three, Fin.isValue, Fin.reduceEq,
    ite_true, ite_false, h10, h20, h21]
  linear_combination ((S 0 0)^2*(n 0)^6/4 + (S 0 0)^2*(n 0)^4*(n 1)^2/4 +
    (S 0 0)^2*(n 0)^4*(n 2)^2/4 - 3*(S 0 0)^2*(n 0)^4/4 + (S 0 0)^2*(n 0)^2*(n 1)^2/2 +
    (S 0 0)^2*(n 0)^2*(n 2)^2/2 + 3*(S 0 0)^2*(n 0)^2/4 + (S 0 0)^2*(n 1)^2/4 + (S 0 0)^2*(n 2)^2/4
    - (S 0 0)^2/4 + (S 0 0)*(S 0 1)*(n 0)^5*(n 1) + (S 0 0)*(S 0 1)*(n 0)^3*(n 1)^3 +
    (S 0 0)*(S 0 1)*(n 0)^3*(n 1)*(n 2)^2 - 4*(S 0 0)*(S 0 1)*(n 0)^3*(n 1) +
    (S 0 0)*(S 0 1)*(n 0)*(n 1)^3 + (S 0 0)*(S 0 1)*(n 0)*(n 1)*(n 2)^2 +
    (S 0 0)*(S 0 1)*(n 0)*(n 1) + (S 0 0)*(S 0 2)*(n 0)^5*(n 2) +
    (S 0 0)*(S 0 2)*(n 0)^3*(n 1)^2*(n 2) + (S 0 0)*(S 0 2)*(n 0)^3*(n 2)^3 -
    4*(S 0 0)*(S 0 2)*(n 0)^3*(n 2) + (S 0 0)*(S 0 2)*(n 0)*(n 1)^2*(n 2) +
    (S 0 0)*(S 0 2)*(n 0)*(n 2)^3 + (S 0 0)*(S 0 2)*(n 0)*(n 2) + (S 0 0)*(S 1 1)*(n 0)^4*(n 1)^2/2
    + (S 0 0)*(S 1 1)*(n 0)^4/2 + (S 0 0)*(S 1 1)*(n 0)^2*(n 1)^4/2 +
    (S 0 0)*(S 1 1)*(n 0)^2*(n 1)^2*(n 2)^2/2 - 3*(S 0 0)*(S 1 1)*(n 0)^2*(n 1)^2/2 +
    (S 0 0)*(S 1 1)*(n 0)^2*(n 2)^2/2 - (S 0 0)*(S 1 1)*(n 0)^2 + (S 0 0)*(S 1 1)*(n 1)^4/2 +
    (S 0 0)*(S 1 1)*(n 1)^2*(n 2)^2/2 - (S 0 0)*(S 1 1)*(n 1)^2 + (S 0 0)*(S 1 1)*(n 2)^2/2 -
    (S 0 0)*(S 1 1)/2 + (S 0 0)*(S 1 2)*(n 0)^4*(n 1)*(n 2) + (S 0 0)*(S 1 2)*(n 0)^2*(n 1)^3*(n 2)
    + (S 0 0)*(S 1 2)*(n 0)^2*(n 1)*(n 2)^3 - 4*(S 0 0)*(S 1 2)*(n 0)^2*(n 1)*(n 2) +
    (S 0 0)*(S 1 2)*(n 1)^3*(n 2) + (S 0 0)*(S 1 2)*(n 1)*(n 2)^3 - 3*(S 0 0)*(S 1 2)*(n 1)*(n 2) +
    (S 0 0)*(S 2 2)*(n 0)^4*(n 2)^2/2 + (S 0 0)*(S 2 2)*(n 0)^4/2 +
    (S 0 0)*(S 2 2)*(n 0)^2*(n 1)^2*(n 2)^2/2 + (S 0 0)*(S 2 2)*(n 0)^2*(n 1)^2/2 +
    (S 0 0)*(S 2 2)*(n 0)^2*(n 2)^4/2 - 3*(S 0 0)*(S 2 2)*(n 0)^2*(n 2)^2/2 -
    (S 0 0)*(S 2 2)*(n 0)^2 + (S 0 0)*(S 2 2)*(n 1)^2*(n 2)^2/2 + (S 0 0)*(S 2 2)*(n 1)^2/2 +
    (S 0 0)*(S 2 2)*(n 2)^4/2 - (S 0 0)*(S 2 2)*(n 2)^2 - (S 0 0)*(S 2 2)/2 +
    (S 0 1)^2*(n 0)^4*(n 1)^2 + (S 0 1)^2*(n 0)^2*(n 1)^4 + (S 0 1)^2*(n 0)^2*(n 1)^2*(n 2)^2 -
    5*(S 0 1)^2*(n 0)^2*(n 1)^2 + 2*(S 0 1)^2*(n 0)^2 + 2*(S 0 1)^2*(n 1)^2 +
    2*(S 0 1)*(S 0 2)*(n 0)^4*(n 1)*(n 2) + 2*(S 0 1)*(S 0 2)*(n 0)^2*(n 1)^3*(n 2) +
    2*(S 0 1)*(S 0 2)*(n 0)^2*(n 1)*(n 2)^3 - 10*(S 0 1)*(S 0 2)*(n 0)^2*(n 1)*(n 2) +
    4*(S 0 1)*(S 0 2)*(n 1)*(n 2) + (S 0 1)*(S 1 1)*(n 0)^3*(n 1)^3 + (S 0 1)*(S 1 1)*(n 0)^3*(n 1)
    + (S 0 1)*(S 1 1)*(n 0)*(n 1)^5 + (S 0 1)*(S 1 1)*(n 0)*(n 1)^3*(n 2)^2 -
    4*(S 0 1)*(S 1 1)*(n 0)*(n 1)^3 + (S 0 1)*(S 1 1)*(n 0)*(n 1)*(n 2)^2 +
    (S 0 1)*(S 1 1)*(n 0)*(n 1) + 2*(S 0 1)*(S 1 2)*(n 0)^3*(n 1)^2*(n 2) +
    2*(S 0 1)*(S 1 2)*(n 0)*(n 1)^4*(n 2) + 2*(S 0 1)*(S 1 2)*(n 0)*(n 1)^2*(n 2)^3 -
    10*(S 0 1)*(S 1 2)*(n 0)*(n 1)^2*(n 2) + 4*(S 0 1)*(S 1 2)*(n 0)*(n 2) +
    (S 0 1)*(S 2 2)*(n 0)^3*(n 1)*(n 2)^2 + (S 0 1)*(S 2 2)*(n 0)^3*(n 1) +
    (S 0 1)*(S 2 2)*(n 0)*(n 1)^3*(n 2)^2 + (S 0 1)*(S 2 2)*(n 0)*(n 1)^3 +
    (S 0 1)*(S 2 2)*(n 0)*(n 1)*(n 2)^4 - 4*(S 0 1)*(S 2 2)*(n 0)*(n 1)*(n 2)^2 -
    3*(S 0 1)*(S 2 2)*(n 0)*(n 1) + (S 0 2)^2*(n 0)^4*(n 2)^2 + (S 0 2)^2*(n 0)^2*(n 1)^2*(n 2)^2 +
    (S 0 2)^2*(n 0)^2*(n 2)^4 - 5*(S 0 2)^2*(n 0)^2*(n 2)^2 + 2*(S 0 2)^2*(n 0)^2 +
    2*(S 0 2)^2*(n 2)^2 + (S 0 2)*(S 1 1)*(n 0)^3*(n 1)^2*(n 2) + (S 0 2)*(S 1 1)*(n 0)^3*(n 2) +
    (S 0 2)*(S 1 1)*(n 0)*(n 1)^4*(n 2) + (S 0 2)*(S 1 1)*(n 0)*(n 1)^2*(n 2)^3 -
    4*(S 0 2)*(S 1 1)*(n 0)*(n 1)^2*(n 2) + (S 0 2)*(S 1 1)*(n 0)*(n 2)^3 -
    3*(S 0 2)*(S 1 1)*(n 0)*(n 2) + 2*(S 0 2)*(S 1 2)*(n 0)^3*(n 1)*(n 2)^2 +
    2*(S 0 2)*(S 1 2)*(n 0)*(n 1)^3*(n 2)^2 + 2*(S 0 2)*(S 1 2)*(n 0)*(n 1)*(n 2)^4 -
    10*(S 0 2)*(S 1 2)*(n 0)*(n 1)*(n 2)^2 + 4*(S 0 2)*(S 1 2)*(n 0)*(n 1) +
    (S 0 2)*(S 2 2)*(n 0)^3*(n 2)^3 + (S 0 2)*(S 2 2)*(n 0)^3*(n 2) +
    (S 0 2)*(S 2 2)*(n 0)*(n 1)^2*(n 2)^3 + (S 0 2)*(S 2 2)*(n 0)*(n 1)^2*(n 2) +
    (S 0 2)*(S 2 2)*(n 0)*(n 2)^5 - 4*(S 0 2)*(S 2 2)*(n 0)*(n 2)^3 + (S 0 2)*(S 2 2)*(n 0)*(n 2) +
    (S 1 1)^2*(n 0)^2*(n 1)^4/4 + (S 1 1)^2*(n 0)^2*(n 1)^2/2 + (S 1 1)^2*(n 0)^2/4 +
    (S 1 1)^2*(n 1)^6/4 + (S 1 1)^2*(n 1)^4*(n 2)^2/4 - 3*(S 1 1)^2*(n 1)^4/4 +
    (S 1 1)^2*(n 1)^2*(n 2)^2/2 + 3*(S 1 1)^2*(n 1)^2/4 + (S 1 1)^2*(n 2)^2/4 - (S 1 1)^2/4 +
    (S 1 1)*(S 1 2)*(n 0)^2*(n 1)^3*(n 2) + (S 1 1)*(S 1 2)*(n 0)^2*(n 1)*(n 2) +
    (S 1 1)*(S 1 2)*(n 1)^5*(n 2) + (S 1 1)*(S 1 2)*(n 1)^3*(n 2)^3 -
    4*(S 1 1)*(S 1 2)*(n 1)^3*(n 2) + (S 1 1)*(S 1 2)*(n 1)*(n 2)^3 + (S 1 1)*(S 1 2)*(n 1)*(n 2) +
    (S 1 1)*(S 2 2)*(n 0)^2*(n 1)^2*(n 2)^2/2 + (S 1 1)*(S 2 2)*(n 0)^2*(n 1)^2/2 +
    (S 1 1)*(S 2 2)*(n 0)^2*(n 2)^2/2 + (S 1 1)*(S 2 2)*(n 0)^2/2 +
    (S 1 1)*(S 2 2)*(n 1)^4*(n 2)^2/2 + (S 1 1)*(S 2 2)*(n 1)^4/2 +
    (S 1 1)*(S 2 2)*(n 1)^2*(n 2)^4/2 - 3*(S 1 1)*(S 2 2)*(n 1)^2*(n 2)^2/2 -
    (S 1 1)*(S 2 2)*(n 1)^2 + (S 1 1)*(S 2 2)*(n 2)^4/2 - (S 1 1)*(S 2 2)*(n 2)^2 -
    (S 1 1)*(S 2 2)/2 + (S 1 2)^2*(n 0)^2*(n 1)^2*(n 2)^2 + (S 1 2)^2*(n 1)^4*(n 2)^2 +
    (S 1 2)^2*(n 1)^2*(n 2)^4 - 5*(S 1 2)^2*(n 1)^2*(n 2)^2 + 2*(S 1 2)^2*(n 1)^2 +
    2*(S 1 2)^2*(n 2)^2 + (S 1 2)*(S 2 2)*(n 0)^2*(n 1)*(n 2)^3 +
    (S 1 2)*(S 2 2)*(n 0)^2*(n 1)*(n 2) + (S 1 2)*(S 2 2)*(n 1)^3*(n 2)^3 +
    (S 1 2)*(S 2 2)*(n 1)^3*(n 2) + (S 1 2)*(S 2 2)*(n 1)*(n 2)^5 - 4*(S 1 2)*(S 2 2)*(n 1)*(n 2)^3
    + (S 1 2)*(S 2 2)*(n 1)*(n 2) + (S 2 2)^2*(n 0)^2*(n 2)^4/4 + (S 2 2)^2*(n 0)^2*(n 2)^2/2 +
    (S 2 2)^2*(n 0)^2/4 + (S 2 2)^2*(n 1)^2*(n 2)^4/4 + (S 2 2)^2*(n 1)^2*(n 2)^2/2 +
    (S 2 2)^2*(n 1)^2/4 + (S 2 2)^2*(n 2)^6/4 - 3*(S 2 2)^2*(n 2)^4/4 + 3*(S 2 2)^2*(n 2)^2/4 -
    (S 2 2)^2/4) * hn'

/-! ### The angular integral -/

/-- **The angular integral of the transverse-traceless square**:
`∫ ttSquare n S dσ = (8π/5)(Σ S² − ⅓(tr S)²) = (8π/45) Σ D²` with `D = 3S − δ tr S`, for a
symmetric `S`. -/
theorem integral_ttSquare {S : Fin 3 → Fin 3 → ℝ} (hS : ∀ i j, S i j = S j i) :
    ∫ n : sphere (0 : E3) 1, ttSquare (n : E3) S ∂sphereMeasure =
      8 * π / 45 * ∑ i, ∑ j, quadrupoleOf S i j ^ 2 := by
  set e : Fin 3 → E3 := fun i => EuclideanSpace.single i 1 with he
  have hc : ∀ (n : E3) (i : Fin 3), n i = inner ℝ n (e i) := fun n i => by
    simp [he, EuclideanSpace.inner_single_right]
  have hee : ∀ i j : Fin 3, inner ℝ (e i) (e j) = if i = j then 1 else 0 := fun i j => by
    by_cases h : i = j
    · subst h
      simp [he]
    · simp only [he, EuclideanSpace.inner_single_left, map_one, PiLp.single_apply, h, ite_false,
        mul_zero]
  set C₀ : ℝ := ∑ i, ∑ j, S i j ^ 2 - (∑ i, S i i) ^ 2 / 2 with hC₀
  set a : Fin 3 → Fin 3 → ℝ := fun j k => S j k * ∑ i, S i i - 2 * ∑ i, S i j * S i k with ha
  set b : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k l => S i j * S k l / 2 with hb
  have hexp : ∀ n : E3, ttSquare n S = C₀ +
      ∑ j, ∑ k, a j k * (inner ℝ n (e j) * inner ℝ n (e k)) +
      ∑ i, ∑ j, ∑ k, ∑ l, b i j k l *
        (inner ℝ n (e i) * inner ℝ n (e j) * inner ℝ n (e k) * inner ℝ n (e l)) := by
    intro n
    simp only [ttSquare, ← hc, Fin.sum_univ_three, hC₀, ha, hb]
    ring
  have i2 : ∀ j k : Fin 3, ∫ n : sphere (0 : E3) 1, a j k *
      (inner ℝ (n : E3) (e j) * inner ℝ (n : E3) (e k)) ∂sphereMeasure =
        a j k * (4 * π / 3 * if j = k then 1 else 0) := fun j k => by
    rw [integral_const_mul, integral_inner_mul_inner, hee]
  have i4 : ∀ i j k l : Fin 3, ∫ n : sphere (0 : E3) 1, b i j k l *
      (inner ℝ (n : E3) (e i) * inner ℝ (n : E3) (e j) * inner ℝ (n : E3) (e k) *
        inner ℝ (n : E3) (e l)) ∂sphereMeasure =
        b i j k l * (4 * π / 15 * ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = k then 1 else 0) * (if j = l then 1 else 0) +
          (if i = l then 1 else 0) * (if j = k then 1 else 0))) := fun i j k l => by
    rw [integral_const_mul, integral_inner_mul_inner_mul_inner_mul_inner, hee, hee, hee, hee,
      hee, hee]
  have hA2 : ∫ n : sphere (0 : E3) 1, ∑ j, ∑ k, a j k *
      (inner ℝ (n : E3) (e j) * inner ℝ (n : E3) (e k)) ∂sphereMeasure =
        ∑ j, ∑ k, a j k * (4 * π / 3 * if j = k then 1 else 0) := by
    rw [integral_finsetSum _ fun j _ => integrable_of_continuous (by fun_prop)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => integrable_of_continuous (by fun_prop)]
    exact Finset.sum_congr rfl fun k _ => i2 j k
  have hA4 : ∫ n : sphere (0 : E3) 1, ∑ i, ∑ j, ∑ k, ∑ l, b i j k l *
      (inner ℝ (n : E3) (e i) * inner ℝ (n : E3) (e j) * inner ℝ (n : E3) (e k) *
        inner ℝ (n : E3) (e l)) ∂sphereMeasure =
        ∑ i, ∑ j, ∑ k, ∑ l, b i j k l * (4 * π / 15 *
          ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = k then 1 else 0) * (if j = l then 1 else 0) +
          (if i = l then 1 else 0) * (if j = k then 1 else 0))) := by
    rw [integral_finsetSum _ fun i _ => integrable_of_continuous (by fun_prop)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_of_continuous (by fun_prop)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => integrable_of_continuous (by fun_prop)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => integrable_of_continuous (by fun_prop)]
    exact Finset.sum_congr rfl fun l _ => i4 i j k l
  simp_rw [hexp]
  rw [integral_add (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop)),
    integral_add (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop)),
    integral_const, sphereMeasure_real_univ, smul_eq_mul, hA2, hA4]
  have h10 := hS 1 0
  have h20 := hS 2 0
  have h21 := hS 2 1
  simp only [hC₀, ha, hb, quadrupoleOf, Fin.sum_univ_three, Fin.isValue, Fin.reduceEq, ite_true,
    ite_false, h10, h20, h21]
  ring

/-! ### The braces as a function of the Christoffel symbols -/

/-- The braces are continuous in the Christoffel symbols. -/
theorem continuous_pseudoBraces {m : ℕ} (G : Fin m → Fin m → ℝ) (i k : Fin m) :
    Continuous fun Γ : Fin m → Fin m → Fin m → ℝ => pseudoBraces G Γ i k := by
  unfold pseudoBraces
  fun_prop

/-- The braces are homogeneous of degree two in the Christoffel symbols. -/
theorem pseudoBraces_mul {m : ℕ} (G : Fin m → Fin m → ℝ) (Γ : Fin m → Fin m → Fin m → ℝ)
    (r : ℝ) (i k : Fin m) :
    pseudoBraces G (fun a b c => r * Γ a b c) i k = r ^ 2 * pseudoBraces G Γ i k := by
  simp only [pseudoBraces, mul_add, Finset.mul_sum]
  congr 1
  · congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_congr rfl fun b _ => by ring
    · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
        Finset.sum_congr rfl fun a _ => ?_
      exact Finset.sum_congr rfl fun b _ => by ring
  · exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The plane flux is continuous in the amplitude. -/
theorem continuous_planeFlux (n : E3) : Continuous fun A : Matrix (Fin 4) (Fin 4) ℝ =>
    planeFlux n A := by
  unfold planeFlux planeChristoffel
  have h : ∀ α : Fin 4, Continuous fun A : Matrix (Fin 4) (Fin 4) ℝ =>
      pseudoBraces (fun a b : Fin 4 => Minkowski.metricMatrix .timeNegative 3 a b)
        (fun c a b => lorentzSign (d := 3) .timeNegative c *
          (waveCovector n a * A b c + waveCovector n b * A c a - waveCovector n c * A a b) / 2)
        0 α := fun α =>
    (continuous_pseudoBraces _ 0 α).comp (by fun_prop)
  fun_prop

/-! ### Bounds -/

/-- The polarization of `ttSquare`: `ttSquare n X − ttSquare n Y = B(X − Y, X + Y)`. -/
def ttBilinear (n : E3) (U W : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, U i j * W i j - 2 * ∑ i, (∑ j, U i j * n j) * (∑ j, W i j * n j) +
    (∑ i, ∑ j, n i * U i j * n j) * (∑ i, ∑ j, n i * W i j * n j) / 2 -
    (∑ i, U i i) * (∑ i, W i i) / 2 +
    ((∑ i, U i i) * (∑ i, ∑ j, n i * W i j * n j) +
      (∑ i, W i i) * (∑ i, ∑ j, n i * U i j * n j)) / 2

theorem ttSquare_sub (n : E3) (X Y : Fin 3 → Fin 3 → ℝ) :
    ttSquare n X - ttSquare n Y = ttBilinear n (fun i j => X i j - Y i j)
      (fun i j => X i j + Y i j) := by
  simp only [ttSquare, ttBilinear, Fin.sum_univ_three]
  ring

private theorem abs_sum_three_le {f : Fin 3 → ℝ} {M : ℝ} (h : ∀ i, |f i| ≤ M) :
    |∑ i, f i| ≤ 3 * M := by
  rw [Fin.sum_univ_three]
  have h0 := abs_le.mp (h 0)
  have h1 := abs_le.mp (h 1)
  have h2 := abs_le.mp (h 2)
  rw [abs_le]
  constructor <;> linarith

private theorem abs_mul_le_mul' {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- A bound of the polarization: `|B(U, W)| ≤ 135 u w` for `|nᵢ| ≤ 1`, `|U_ij| ≤ u` and
`|W_ij| ≤ w`. -/
theorem abs_ttBilinear_le {n : E3} (hn : ∀ i, |n i| ≤ 1) {U W : Fin 3 → Fin 3 → ℝ} {u w : ℝ}
    (hU : ∀ i j, |U i j| ≤ u) (hW : ∀ i j, |W i j| ≤ w) :
    |ttBilinear n U W| ≤ 135 * u * w := by
  have hu : 0 ≤ u := (abs_nonneg _).trans (hU 0 0)
  have hw : 0 ≤ w := (abs_nonneg _).trans (hW 0 0)
  have hUn : ∀ i, |∑ j, U i j * n j| ≤ 3 * u := fun i =>
    abs_sum_three_le fun j => (abs_mul_le_mul' (hU i j) (hn j)).trans_eq (mul_one u)
  have hWn : ∀ i, |∑ j, W i j * n j| ≤ 3 * w := fun i =>
    abs_sum_three_le fun j => (abs_mul_le_mul' (hW i j) (hn j)).trans_eq (mul_one w)
  have hnUn : |∑ i, ∑ j, n i * U i j * n j| ≤ 9 * u := by
    have := abs_sum_three_le (M := 3 * u) fun i => abs_sum_three_le fun j =>
      (abs_mul_le_mul' (abs_mul_le_mul' (hn i) (hU i j)) (hn j)).trans_eq (by ring)
    linarith
  have hnWn : |∑ i, ∑ j, n i * W i j * n j| ≤ 9 * w := by
    have := abs_sum_three_le (M := 3 * w) fun i => abs_sum_three_le fun j =>
      (abs_mul_le_mul' (abs_mul_le_mul' (hn i) (hW i j)) (hn j)).trans_eq (by ring)
    linarith
  have htU : |∑ i, U i i| ≤ 3 * u := abs_sum_three_le fun i => hU i i
  have htW : |∑ i, W i i| ≤ 3 * w := abs_sum_three_le fun i => hW i i
  have h1 : |∑ i, ∑ j, U i j * W i j| ≤ 9 * (u * w) := by
    have := abs_sum_three_le (M := 3 * (u * w)) fun i => abs_sum_three_le fun j =>
      abs_mul_le_mul' (hU i j) (hW i j)
    linarith
  have h2 : |∑ i, (∑ j, U i j * n j) * (∑ j, W i j * n j)| ≤ 3 * (3 * u * (3 * w)) :=
    abs_sum_three_le fun i => abs_mul_le_mul' (hUn i) (hWn i)
  have h3 := abs_mul_le_mul' hnUn hnWn
  have h4 := abs_mul_le_mul' htU htW
  have h5 := abs_mul_le_mul' htU hnWn
  have h6 := abs_mul_le_mul' htW hnUn
  unfold ttBilinear
  set A1 := ∑ i, ∑ j, U i j * W i j
  set A2 := ∑ i, (∑ j, U i j * n j) * (∑ j, W i j * n j)
  set A3 := (∑ i, ∑ j, n i * U i j * n j) * (∑ i, ∑ j, n i * W i j * n j)
  set A4 := (∑ i, U i i) * (∑ i, W i i)
  set A5 := (∑ i, U i i) * (∑ i, ∑ j, n i * W i j * n j)
  set A6 := (∑ i, W i i) * (∑ i, ∑ j, n i * U i j * n j)
  rw [abs_le] at h1 h2 h3 h4 h5 h6 ⊢
  constructor <;> linarith [mul_nonneg hu hw]

/-- **The difference of two transverse-traceless squares**: `|ttSquare n X − ttSquare n Y| ≤
270 B δ` for `|nᵢ| ≤ 1`, `|X_ij|, |Y_ij| ≤ B` and `|X_ij − Y_ij| ≤ δ`. -/
theorem abs_ttSquare_sub_le {n : E3} (hn : ∀ i, |n i| ≤ 1) {X Y : Fin 3 → Fin 3 → ℝ} {B δ : ℝ}
    (hX : ∀ i j, |X i j| ≤ B) (hY : ∀ i j, |Y i j| ≤ B) (hXY : ∀ i j, |X i j - Y i j| ≤ δ) :
    |ttSquare n X - ttSquare n Y| ≤ 270 * B * δ := by
  rw [ttSquare_sub]
  have h := abs_ttBilinear_le hn hXY (W := fun i j => X i j + Y i j) (w := 2 * B) fun i j => by
    have := abs_add_le (X i j) (Y i j)
    linarith [hX i j, hY i j]
  linarith

end ProjectAinos.SmoothGeometry.Wave
