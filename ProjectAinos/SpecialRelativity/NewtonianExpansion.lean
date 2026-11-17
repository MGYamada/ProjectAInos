/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The expansion in `1/c` of the energy of a free particle

The other files of special relativity use units with `c = 1`. Here the speed of light `c` is a
parameter (Landau–Lifshitz, *The Classical Theory of Fields*, §§8–9). For a velocity `v` in `d`
space dimensions, with `x = Σ vᵢ²/c²`:

* `Newtonian.energy m c v = m c²/√(1 − x)`,
* `Newtonian.lagrangian m c v = −m c² √(1 − x)`,
* `Newtonian.momentum m c v i = m vᵢ/√(1 − x)`,
* `Newtonian.clockRate c v = √(1 − x)`.

The two elementary estimates are exact consequences of `s² = 1 − x` for `s = √(1 − x)`: for
`0 ≤ x ≤ 1/4`,

* `sqrt_one_sub_bounds`: `0 ≤ 1 − x/2 − √(1 − x) ≤ x²/2`,
* `inv_sqrt_one_sub_bounds`: `0 ≤ 1/√(1 − x) − 1 − x/2 ≤ x²/2`.

For a bound `V` on the speed, `Σ vᵢ² ≤ V²`, and `c ≥ 2V`, `c > 0`, the remainders are uniform:

* `abs_energy_sub_le`: `|E − m c² − ½ m Σ vᵢ²| ≤ |m| V⁴/(2c²)`,
* `abs_lagrangian_sub_le`: `|L + m c² − ½ m Σ vᵢ²| ≤ |m| V⁴/(2c²)`,
* `abs_momentum_sub_le`: `|pᵢ − m vᵢ| ≤ |m| V³/c²`,
* `abs_clockRate_sub_le`: `|√(1 − x) − (1 − Σ vᵢ²/(2c²))| ≤ V⁴/(2c⁴)`.

These are estimates for functions of the velocity. They do not state that the trajectories of
the relativistic particle converge to those of the Newtonian one.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SpecialRelativity.Newtonian

/-! ### Two elementary estimates -/

/-- `0 ≤ 1 − x/2 − √(1 − x) ≤ x²/2` for `0 ≤ x ≤ 1/4`. -/
theorem sqrt_one_sub_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) :
    0 ≤ 1 - x / 2 - Real.sqrt (1 - x) ∧ 1 - x / 2 - Real.sqrt (1 - x) ≤ x ^ 2 / 2 := by
  have hs0 : 0 ≤ Real.sqrt (1 - x) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  constructor
  · have h : Real.sqrt (1 - x) ≤ 1 - x / 2 := by
      refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
      nlinarith [sq_nonneg x]
    linarith
  · have h : 1 - x / 2 - x ^ 2 / 2 ≤ Real.sqrt (1 - x) := by
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith [sq_nonneg x, mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]
    linarith

private theorem mul_one_add_half (s : ℝ) :
    s * (1 + (1 - s ^ 2) / 2) = 1 - (1 - s) ^ 2 * (2 + s) / 2 := by ring

private theorem mul_one_add_half_add_sq (s : ℝ) :
    s * (1 + (1 - s ^ 2) / 2 + (1 - s ^ 2) ^ 2 / 2) =
      1 + (1 - s) ^ 2 * (s ^ 2 + s ^ 3 / 2 - 1) := by ring

/-- `0 ≤ 1/√(1 − x) − 1 − x/2 ≤ x²/2` for `0 ≤ x ≤ 1/4`. -/
theorem inv_sqrt_one_sub_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) :
    0 ≤ (Real.sqrt (1 - x))⁻¹ - 1 - x / 2 ∧ (Real.sqrt (1 - x))⁻¹ - 1 - x / 2 ≤ x ^ 2 / 2 := by
  have hs2 : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  have hs : (4 : ℝ) / 5 ≤ Real.sqrt (1 - x) := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hpos : 0 < Real.sqrt (1 - x) := by linarith
  have hx : 1 - Real.sqrt (1 - x) ^ 2 = x := by linarith
  have hle1 : Real.sqrt (1 - x) ≤ 1 := by
    refine Real.sqrt_le_iff.mpr ⟨zero_le_one, by linarith⟩
  constructor
  · have h : 1 + x / 2 ≤ (Real.sqrt (1 - x))⁻¹ := by
      rw [le_inv_comm₀ (by linarith) hpos]
      rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
      have hid : Real.sqrt (1 - x) * (1 + x / 2) =
          1 - (1 - Real.sqrt (1 - x)) ^ 2 * (2 + Real.sqrt (1 - x)) / 2 := by
        have h := mul_one_add_half (Real.sqrt (1 - x))
        rwa [hx] at h
      rw [hid]
      have hnn : 0 ≤ (1 - Real.sqrt (1 - x)) ^ 2 * (2 + Real.sqrt (1 - x)) / 2 := by positivity
      linarith
    linarith
  · have h : (Real.sqrt (1 - x))⁻¹ ≤ 1 + x / 2 + x ^ 2 / 2 := by
      rw [inv_le_comm₀ hpos (by positivity)]
      rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
      have hid : Real.sqrt (1 - x) * (1 + x / 2 + x ^ 2 / 2) =
          1 + (1 - Real.sqrt (1 - x)) ^ 2 *
            (Real.sqrt (1 - x) ^ 2 + Real.sqrt (1 - x) ^ 3 / 2 - 1) := by
        have h := mul_one_add_half_add_sq (Real.sqrt (1 - x))
        rwa [hx] at h
      rw [hid]
      have hcube : (3 : ℝ) / 5 ≤ Real.sqrt (1 - x) ^ 3 := by
        have h3 : Real.sqrt (1 - x) ^ 3 = Real.sqrt (1 - x) * Real.sqrt (1 - x) ^ 2 := by ring
        rw [h3, hs2]
        nlinarith
      have hfac : 0 ≤ Real.sqrt (1 - x) ^ 2 + Real.sqrt (1 - x) ^ 3 / 2 - 1 := by
        rw [hs2]
        linarith
      have hnn := mul_nonneg (sq_nonneg (1 - Real.sqrt (1 - x))) hfac
      linarith
    linarith

/-! ### The functions of the velocity, with the speed of light -/

variable {d : ℕ}

/-- `Σ vᵢ²/c²`. -/
def betaSq (c : ℝ) (v : Fin d → ℝ) : ℝ := (∑ i, v i ^ 2) / c ^ 2

/-- The energy `m c²/√(1 − v²/c²)`. -/
def energy (m c : ℝ) (v : Fin d → ℝ) : ℝ := m * c ^ 2 * (Real.sqrt (1 - betaSq c v))⁻¹

/-- The Lagrangian `−m c² √(1 − v²/c²)`. -/
def lagrangian (m c : ℝ) (v : Fin d → ℝ) : ℝ := -(m * c ^ 2) * Real.sqrt (1 - betaSq c v)

/-- The momentum `m v/√(1 − v²/c²)`. -/
def momentum (m c : ℝ) (v : Fin d → ℝ) (i : Fin d) : ℝ :=
  m * (Real.sqrt (1 - betaSq c v))⁻¹ * v i

/-- The rate `√(1 − v²/c²)` of a moving clock. -/
def clockRate (c : ℝ) (v : Fin d → ℝ) : ℝ := Real.sqrt (1 - betaSq c v)

theorem betaSq_nonneg (c : ℝ) (v : Fin d → ℝ) : 0 ≤ betaSq c v :=
  div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (v i)) (sq_nonneg c)

theorem betaSq_mul (c : ℝ) (hc : c ≠ 0) (v : Fin d → ℝ) :
    c ^ 2 * betaSq c v = ∑ i, v i ^ 2 := by
  rw [betaSq]
  field_simp

variable {V c : ℝ} {v : Fin d → ℝ}

/-- `v²/c² ≤ V²/c²` under the bound on the speed. -/
theorem betaSq_le_div (hv : ∑ i, v i ^ 2 ≤ V ^ 2) :
    betaSq c v ≤ V ^ 2 / c ^ 2 :=
  div_le_div_of_nonneg_right hv (sq_nonneg c)

/-- `v²/c² ≤ 1/4` when `c ≥ 2V`. -/
theorem betaSq_le_quarter (hV : 0 ≤ V) (hc : 0 < c) (hVc : 2 * V ≤ c)
    (hv : ∑ i, v i ^ 2 ≤ V ^ 2) : betaSq c v ≤ 1 / 4 := by
  refine (betaSq_le_div hv).trans ?_
  rw [div_le_iff₀ (pow_pos hc 2)]
  nlinarith

/-- `(v²/c²)² ≤ V⁴/c⁴`. -/
theorem betaSq_sq_le (hv : ∑ i, v i ^ 2 ≤ V ^ 2) :
    betaSq c v ^ 2 ≤ V ^ 4 / c ^ 4 := by
  have h := pow_le_pow_left₀ (betaSq_nonneg c v) (betaSq_le_div hv) 2
  have he : (V ^ 2 / c ^ 2) ^ 2 = V ^ 4 / c ^ 4 := by
    rw [div_pow]
    ring
  rwa [he] at h

/-! ### Uniform remainders -/

/-- The energy is `m c² + ½ m v²` up to `|m| V⁴/(2c²)`. -/
theorem abs_energy_sub_le (m : ℝ) (hV : 0 ≤ V) (hc : 0 < c) (hVc : 2 * V ≤ c)
    (hv : ∑ i, v i ^ 2 ≤ V ^ 2) :
    |energy m c v - m * c ^ 2 - m / 2 * ∑ i, v i ^ 2| ≤ |m| * V ^ 4 / (2 * c ^ 2) := by
  have hb := inv_sqrt_one_sub_bounds (betaSq_nonneg c v) (betaSq_le_quarter hV hc hVc hv)
  have hid : energy m c v - m * c ^ 2 - m / 2 * ∑ i, v i ^ 2 =
      m * c ^ 2 * ((Real.sqrt (1 - betaSq c v))⁻¹ - 1 - betaSq c v / 2) := by
    rw [energy, ← betaSq_mul c hc.ne' v]
    ring
  have hsq := betaSq_sq_le (c := c) hv
  rw [hid, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c), abs_of_nonneg hb.1]
  calc |m| * c ^ 2 * ((Real.sqrt (1 - betaSq c v))⁻¹ - 1 - betaSq c v / 2)
      ≤ |m| * c ^ 2 * (V ^ 4 / c ^ 4 / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg m) (sq_nonneg c))
        linarith [hb.2]
    _ = |m| * V ^ 4 / (2 * c ^ 2) := by
        field_simp

/-- The Lagrangian is `−m c² + ½ m v²` up to `|m| V⁴/(2c²)`. -/
theorem abs_lagrangian_sub_le (m : ℝ) (hV : 0 ≤ V) (hc : 0 < c) (hVc : 2 * V ≤ c)
    (hv : ∑ i, v i ^ 2 ≤ V ^ 2) :
    |lagrangian m c v + m * c ^ 2 - m / 2 * ∑ i, v i ^ 2| ≤ |m| * V ^ 4 / (2 * c ^ 2) := by
  have hb := sqrt_one_sub_bounds (betaSq_nonneg c v) (betaSq_le_quarter hV hc hVc hv)
  have hid : lagrangian m c v + m * c ^ 2 - m / 2 * ∑ i, v i ^ 2 =
      m * c ^ 2 * (1 - betaSq c v / 2 - Real.sqrt (1 - betaSq c v)) := by
    rw [lagrangian, ← betaSq_mul c hc.ne' v]
    ring
  have hsq := betaSq_sq_le (c := c) hv
  rw [hid, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c), abs_of_nonneg hb.1]
  calc |m| * c ^ 2 * (1 - betaSq c v / 2 - Real.sqrt (1 - betaSq c v))
      ≤ |m| * c ^ 2 * (V ^ 4 / c ^ 4 / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg m) (sq_nonneg c))
        linarith [hb.2]
    _ = |m| * V ^ 4 / (2 * c ^ 2) := by
        field_simp

/-- A component of the velocity is at most the bound on the speed. -/
theorem abs_le_of_sum_sq_le (hV : 0 ≤ V) (hv : ∑ i, v i ^ 2 ≤ V ^ 2) (i : Fin d) :
    |v i| ≤ V := by
  exact abs_le.mpr (abs_le_of_sq_le_sq' ((Finset.single_le_sum (f := fun j => v j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans hv) hV)

/-- The momentum is `m v` up to `|m| V³/c²`. -/
theorem abs_momentum_sub_le (m : ℝ) (hV : 0 ≤ V) (hc : 0 < c) (hVc : 2 * V ≤ c)
    (hv : ∑ i, v i ^ 2 ≤ V ^ 2) (i : Fin d) :
    |momentum m c v i - m * v i| ≤ |m| * V ^ 3 / c ^ 2 := by
  have hx0 := betaSq_nonneg c v
  have hx1 := betaSq_le_quarter hV hc hVc hv
  have hb := inv_sqrt_one_sub_bounds hx0 hx1
  have hg0 : 0 ≤ (Real.sqrt (1 - betaSq c v))⁻¹ - 1 := by linarith [hb.1]
  have hg1 : (Real.sqrt (1 - betaSq c v))⁻¹ - 1 ≤ V ^ 2 / c ^ 2 := by
    have hxx : betaSq c v ^ 2 / 2 ≤ betaSq c v / 2 := by nlinarith
    linarith [hb.2, betaSq_le_div (c := c) hv]
  have hid : momentum m c v i - m * v i = m * ((Real.sqrt (1 - betaSq c v))⁻¹ - 1) * v i := by
    rw [momentum]
    ring
  rw [hid, abs_mul, abs_mul, abs_of_nonneg hg0]
  calc |m| * ((Real.sqrt (1 - betaSq c v))⁻¹ - 1) * |v i|
      ≤ |m| * (V ^ 2 / c ^ 2) * V :=
        mul_le_mul (mul_le_mul_of_nonneg_left hg1 (abs_nonneg m))
          (abs_le_of_sum_sq_le hV hv i) (abs_nonneg _)
          (mul_nonneg (abs_nonneg m) (by positivity))
    _ = |m| * V ^ 3 / c ^ 2 := by ring

/-- The rate of a moving clock is `1 − v²/(2c²)` up to `V⁴/(2c⁴)`. -/
theorem abs_clockRate_sub_le (hV : 0 ≤ V) (hc : 0 < c) (hVc : 2 * V ≤ c)
    (hv : ∑ i, v i ^ 2 ≤ V ^ 2) :
    |clockRate c v - (1 - (∑ i, v i ^ 2) / (2 * c ^ 2))| ≤ V ^ 4 / (2 * c ^ 4) := by
  have hb := sqrt_one_sub_bounds (betaSq_nonneg c v) (betaSq_le_quarter hV hc hVc hv)
  have hid : clockRate c v - (1 - (∑ i, v i ^ 2) / (2 * c ^ 2)) =
      -(1 - betaSq c v / 2 - Real.sqrt (1 - betaSq c v)) := by
    rw [clockRate, betaSq]
    field_simp
    ring
  have hsq := betaSq_sq_le (c := c) hv
  rw [hid, abs_neg, abs_of_nonneg hb.1]
  calc 1 - betaSq c v / 2 - Real.sqrt (1 - betaSq c v) ≤ V ^ 4 / c ^ 4 / 2 := by
        linarith [hb.2]
    _ = V ^ 4 / (2 * c ^ 4) := by ring

end ProjectAinos.SpecialRelativity.Newtonian
