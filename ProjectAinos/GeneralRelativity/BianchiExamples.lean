/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.BianchiClassA
public import ProjectAinos.GeneralRelativity.BianchiFrames
public import ProjectAinos.GeneralRelativity.Kasner
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Diagonal homogeneous models of types I and IX

Landau–Lifshitz, §§116–118. The diagonal models of `BianchiClassA.lean` on the invariant frames
of `BianchiFrames.lean`.

* `bianchiI_eq_diagonal`, `bianchiII_eq_diagonal`, `bianchiIX_eq_diagonal`: the canonical
  structure constants of the types I, II and IX are of the diagonal form `ε_{abc} n_c` with
  `n = 0`, `n = (1, 0, 0)` and `n = (1, 1, 1)`.
* `ricci_eq_zero_iff_bianchiIX`: **the vacuum equations of the diagonal type IX models**
  (L&L §118) are
  `ä₁/a₁ + ä₂/a₂ + ä₃/a₃ = 0` and
  `ä_i/a_i + (ȧ_i/a_i)(ȧ_j/a_j + ȧ_k/a_k) + (a_i⁴ − (a_j² − a_k²)²)/(2 (a₁a₂a₃)²) = 0`.
* `kasnerModel`, `ricci_kasnerModel_eq_zero`: the Kasner metric with `Σp = Σp² = 1` is a vacuum
  solution of type I through the frame reduction, independently of the co-ordinate computation
  of `Kasner.lean`.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace ProjectAinos.GeneralRelativity.HomogeneousSpace

open SmoothGeometry CoordinateMetric LorentzMetric StructureConstants

/-- The structure constants of type I are those of `n = 0`. -/
theorem bianchiI_eq_diagonal : StructureConstants.bianchiI = ofBianchi (Matrix.diagonal 0) 0 := by
  funext c a b
  simp [StructureConstants.bianchiI, ofBianchi]

/-- The structure constants of type II are those of `n = (1, 0, 0)`. -/
theorem bianchiII_eq_diagonal :
    StructureConstants.bianchiII = ofBianchi (Matrix.diagonal ![1, 0, 0]) 0 := rfl

/-- The structure constants of type IX are those of `n = (1, 1, 1)`. -/
theorem bianchiIX_eq_diagonal :
    StructureConstants.bianchiIX = ofBianchi (Matrix.diagonal fun _ => 1) 0 := by
  rw [Matrix.diagonal_one]
  rfl

/-- **The vacuum equations of a diagonal model of type IX** (L&L §118). -/
theorem ricci_eq_zero_iff_bianchiIX {I : Set ℝ} {hI : IsOpen I} {a : Fin 3 → ℝ → ℝ}
    {ha : ∀ i, ContDiffOn ℝ ∞ (a i) I} {hpos : ∀ i, ∀ t ∈ I, 0 < a i t} :
    (∀ y : (Data.diagonal InvariantFrame.bianchiIX I hI a ha hpos).domain,
        (Data.diagonal InvariantFrame.bianchiIX I hI a ha hpos).metric.toLorentzMetric.ricci y =
          0) ↔
      ∀ t ∈ I,
        deriv (deriv (a 0)) t / a 0 t + deriv (deriv (a 1)) t / a 1 t +
            deriv (deriv (a 2)) t / a 2 t = 0 ∧
        deriv (deriv (a 0)) t / a 0 t +
            deriv (a 0) t / a 0 t * (deriv (a 1) t / a 1 t + deriv (a 2) t / a 2 t) +
            ((a 0 t ^ 2) ^ 2 - (a 1 t ^ 2 - a 2 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 ∧
        deriv (deriv (a 1)) t / a 1 t +
            deriv (a 1) t / a 1 t * (deriv (a 0) t / a 0 t + deriv (a 2) t / a 2 t) +
            ((a 1 t ^ 2) ^ 2 - (a 0 t ^ 2 - a 2 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 ∧
        deriv (deriv (a 2)) t / a 2 t +
            deriv (a 2) t / a 2 t * (deriv (a 0) t / a 0 t + deriv (a 1) t / a 1 t) +
            ((a 2 t ^ 2) ^ 2 - (a 0 t ^ 2 - a 1 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 := by
  simpa only [one_mul] using Data.ricci_eq_zero_iff_diagonal (n := fun _ => 1)
    (InvariantFrame.bianchiIX_C.trans bianchiIX_eq_diagonal)

/-- **The Kasner metric as a diagonal model of type I**: the scale factors `a_α = t^{p_α}` on
the times `t > 0`. -/
def kasnerModel (p : Fin 3 → ℝ) : Data :=
  Data.diagonal InvariantFrame.bianchiI (Ioi 0) isOpen_Ioi (Kasner.kasner p).a
    (Kasner.kasner p).contDiffOn_a (Kasner.kasner p).a_pos

/-- **The Kasner metric is a vacuum solution of type I**, from the frame reduction. -/
theorem ricci_kasnerModel_eq_zero {p : Fin 3 → ℝ} (h : ∑ α, p α = 1 ∧ ∑ α, p α ^ 2 = 1) :
    ∀ y : (kasnerModel p).domain, (kasnerModel p).metric.toLorentzMetric.ricci y = 0 := by
  refine (Data.ricci_eq_zero_iff_diagonal (n := 0)
    (InvariantFrame.bianchiI_C.trans bianchiI_eq_diagonal)).mpr fun t ht => ?_
  have htp : 0 < t := ht
  have hH (α : Fin 3) : deriv ((Kasner.kasner p).a α) t / (Kasner.kasner p).a α t = p α / t :=
    Kasner.hubble_kasner p α htp
  have hA (α : Fin 3) : deriv (deriv ((Kasner.kasner p).a α)) t / (Kasner.kasner p).a α t =
      p α * (p α - 1) / t ^ 2 :=
    Kasner.accel_kasner p α htp
  obtain ⟨h1, h2⟩ := h
  simp only [Fin.sum_univ_three] at h1 h2
  simp only [hH, hA, Pi.zero_apply, zero_mul, sub_zero, zero_pow two_ne_zero, zero_div, add_zero]
  have ht0 := htp.ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp
  · linear_combination h2 - h1
  · linear_combination p 0 * h1
  · linear_combination p 1 * h1
  · linear_combination p 2 * h1

end ProjectAinos.GeneralRelativity.HomogeneousSpace
