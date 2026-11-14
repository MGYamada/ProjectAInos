/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rutherford's formula

Landau–Lifshitz §19. For the field `U = α/r` the orbit is a hyperbola with
the eccentricity `e`, `e² − 1 = 2 E M²/m α²`, and the angle of deflection
satisfies `sin (χ/2) = 1/e`.

* `eccentricity_sq_sub_one`: with `E = ½ m v²` and `M = m ρ v`,
  `e² − 1 = (m v² ρ/α)²`.
* `cot_half_eq`: `cot (χ/2) = m v² ρ/α` (Landau–Lifshitz (19.1)).
* `hasDerivAt_impactParameter`, `rutherford`: for
  `ρ(χ) = (α/m v²) cot (χ/2)`, `ρ |dρ/dχ| / sin χ = (α/2 m v²)² / sin⁴ (χ/2)`
  (Landau–Lifshitz (19.3)).

The angle of deflection as a limit of the direction of the motion, and the
cross-section as a measure, are not defined here.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.Rutherford

open Real

/-- The eccentricity of the orbit with the speed `v` at infinity and the
impact parameter `ρ`: `2 E M²/m α² = (m v² ρ/α)²` for `E = ½ m v²` and
`M = m ρ v`. -/
theorem eccentricity_sq_sub_one {m α : ℝ} (hm : m ≠ 0) (hα : α ≠ 0) (v ρ : ℝ) :
    2 * (m * v ^ 2 / 2) * (m * ρ * v) ^ 2 / (m * α ^ 2) = (m * v ^ 2 * ρ / α) ^ 2 := by
  field_simp

/-- If `sin (χ/2) = 1/e` for an angle `0 < χ < π` and `e² − 1 = k²` with
`k ≥ 0`, then `cot (χ/2) = k` (Landau–Lifshitz (19.1) with
`k = m v² ρ/α`). -/
theorem cot_half_eq {χ e k : ℝ} (hχ : 0 < χ) (hχπ : χ < π) (he : sin (χ / 2) = 1 / e)
    (hk : 0 ≤ k) (hek : e ^ 2 - 1 = k ^ 2) : cos (χ / 2) / sin (χ / 2) = k := by
  have hs : 0 < sin (χ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc : 0 < cos (χ / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have he0 : 0 < e := by
    rw [he] at hs
    exact one_div_pos.mp hs
  have hsq := sin_sq_add_cos_sq (χ / 2)
  have hc2 : cos (χ / 2) ^ 2 = (k / e) ^ 2 := by
    rw [he] at hsq
    have : (1 / e) ^ 2 + (k / e) ^ 2 = 1 := by
      field_simp
      linarith
    linarith
  have hce : cos (χ / 2) = k / e := by
    have h1 : 0 ≤ k / e := div_nonneg hk he0.le
    nlinarith [sq_nonneg (cos (χ / 2) - k / e), sq_nonneg (cos (χ / 2) + k / e)]
  rw [hce, he]
  field_simp

/-- The derivative of the impact parameter `ρ(χ) = a cot (χ/2)`. -/
theorem hasDerivAt_impactParameter (a : ℝ) {χ : ℝ} (hs : sin (χ / 2) ≠ 0) :
    HasDerivAt (fun x => a * (cos (x / 2) / sin (x / 2))) (-(a / (2 * sin (χ / 2) ^ 2))) χ := by
  have hhalf : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) χ := (hasDerivAt_id χ).div_const 2
  have hcos' := (hasDerivAt_cos (χ / 2)).comp χ hhalf
  have hsin' := (hasDerivAt_sin (χ / 2)).comp χ hhalf
  have hcos : HasDerivAt (fun x => cos (x / 2)) (-sin (χ / 2) * (1 / 2)) χ := hcos'
  have hsin : HasDerivAt (fun x => sin (x / 2)) (cos (χ / 2) * (1 / 2)) χ := hsin'
  have h := (hcos.div hsin hs).const_mul a
  have hsq := sin_sq_add_cos_sq (χ / 2)
  have hval : a * ((-sin (χ / 2) * (1 / 2) * sin (χ / 2) -
      cos (χ / 2) * (cos (χ / 2) * (1 / 2))) / sin (χ / 2) ^ 2) =
        -(a / (2 * sin (χ / 2) ^ 2)) := by
    have h1 : -sin (χ / 2) * (1 / 2) * sin (χ / 2) - cos (χ / 2) * (cos (χ / 2) * (1 / 2)) =
        -(1 / 2) := by linear_combination (-(1 / 2 : ℝ)) * hsq
    rw [h1]
    field_simp
  rw [← hval]
  exact h

/-- Rutherford's formula (Landau–Lifshitz (19.3)): with
`ρ(χ) = a cot (χ/2)` and `a = α/m v²`,
`ρ |dρ/dχ| / sin χ = (a/2)² / sin⁴ (χ/2)`. -/
theorem rutherford (a : ℝ) {χ : ℝ} (hs : sin (χ / 2) ≠ 0) (hc : cos (χ / 2) ≠ 0) :
    a * (cos (χ / 2) / sin (χ / 2)) * (a / (2 * sin (χ / 2) ^ 2)) / sin χ =
      (a / 2) ^ 2 / sin (χ / 2) ^ 4 := by
  have h2 : sin χ = 2 * sin (χ / 2) * cos (χ / 2) := by
    have h := sin_two_mul (χ / 2)
    rwa [mul_div_cancel₀ χ (two_ne_zero)] at h
  rw [h2]
  field_simp

end ProjectAInos.Mechanics.Rutherford
