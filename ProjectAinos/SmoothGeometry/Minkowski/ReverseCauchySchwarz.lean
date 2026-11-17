/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Minkowski.Observer
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The reverse Cauchy–Schwarz inequality on the future cone

For vectors `v` and `w` of the closed future cone of Minkowski space, with the normalized
pairing `pair v w = v⁰ w⁰ − ⟨𝐯, 𝐰⟩` and the quadratic form `Q`,

* `pair_nonneg_of_futureCausal`: `0 ≤ pair v w`,
* `intervalQuadratic_mul_le_pair_sq`: `Q(v) Q(w) ≤ (pair v w)²`,
* `sqrt_mul_sqrt_le_pair`: `√Q(v) √Q(w) ≤ pair v w`,
* `sqrt_add_sqrt_le`: `√Q(v) + √Q(w) ≤ √Q(v + w)`, the reverse triangle inequality.

For an observer `u`, `Observer.intervalQuadratic_eq` is the split
`Q(w) = (u.clock w)² − restForm(w⊥, w⊥)`, and `Observer.eq_smul_of_clock_eq_sqrt` is the case
of equality: if `u.clock w = √Q(w)` then `w = (u.clock w) • u`.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SmoothGeometry.Minkowski

variable {d : ℕ}

/-- The pairing of two vectors of the closed future cone is not negative. -/
theorem pair_nonneg_of_futureCausal {v w : MinkowskiModel d} (hv : FutureCausal v)
    (hw : FutureCausal w) : 0 ≤ pair v w := by
  rw [pair_apply]
  have h1 := real_inner_le_norm (space v) (space w)
  have h2 : ‖space v‖ * ‖space w‖ ≤ time v * time w :=
    mul_le_mul hv hw (norm_nonneg _) ((norm_nonneg _).trans hv)
  linarith

/-- The reverse Cauchy–Schwarz inequality on the closed future cone. -/
theorem intervalQuadratic_mul_le_pair_sq {v w : MinkowskiModel d} (hv : FutureCausal v)
    (hw : FutureCausal w) : intervalQuadratic v * intervalQuadratic w ≤ pair v w ^ 2 := by
  rw [intervalQuadratic_coordinates, intervalQuadratic_coordinates, pair_apply]
  have h1 := real_inner_le_norm (space v) (space w)
  have hb := norm_nonneg (space v)
  have he := norm_nonneg (space w)
  have h2 : ‖space v‖ * ‖space w‖ ≤ time v * time w :=
    mul_le_mul hv hw he (hb.trans hv)
  have h3 : (time v ^ 2 - ‖space v‖ ^ 2) * (time w ^ 2 - ‖space w‖ ^ 2) ≤
      (time v * time w - ‖space v‖ * ‖space w‖) ^ 2 := by
    have h := sq_nonneg (time v * ‖space w‖ - ‖space v‖ * time w)
    linarith [h, show (time v * time w - ‖space v‖ * ‖space w‖) ^ 2 -
      (time v ^ 2 - ‖space v‖ ^ 2) * (time w ^ 2 - ‖space w‖ ^ 2) =
      (time v * ‖space w‖ - ‖space v‖ * time w) ^ 2 by ring]
  refine h3.trans (pow_le_pow_left₀ (sub_nonneg.mpr h2) ?_ 2)
  linarith

/-- The reverse Cauchy–Schwarz inequality with square roots. -/
theorem sqrt_mul_sqrt_le_pair {v w : MinkowskiModel d} (hv : FutureCausal v)
    (hw : FutureCausal w) :
    Real.sqrt (intervalQuadratic v) * Real.sqrt (intervalQuadratic w) ≤ pair v w := by
  have hQv : 0 ≤ intervalQuadratic v := ((futureCausal_iff v).mp hv).1
  rw [← Real.sqrt_mul hQv]
  exact (Real.sqrt_le_sqrt (intervalQuadratic_mul_le_pair_sq hv hw)).trans_eq
    (Real.sqrt_sq (pair_nonneg_of_futureCausal hv hw))

/-- The quadratic form of a sum. -/
theorem intervalQuadratic_add (v w : MinkowskiModel d) :
    intervalQuadratic (v + w) = intervalQuadratic v + 2 * pair v w + intervalQuadratic w := by
  simp only [intervalQuadratic_apply, map_add, add_apply, pair_comm w v]
  ring

/-- The reverse triangle inequality on the closed future cone. -/
theorem sqrt_add_sqrt_le {v w : MinkowskiModel d} (hv : FutureCausal v) (hw : FutureCausal w) :
    Real.sqrt (intervalQuadratic v) + Real.sqrt (intervalQuadratic w) ≤
      Real.sqrt (intervalQuadratic (v + w)) := by
  have hQv : 0 ≤ intervalQuadratic v := ((futureCausal_iff v).mp hv).1
  have hQw : 0 ≤ intervalQuadratic w := ((futureCausal_iff w).mp hw).1
  refine Real.le_sqrt_of_sq_le ?_
  rw [intervalQuadratic_add]
  have h := sqrt_mul_sqrt_le_pair hv hw
  nlinarith [Real.sq_sqrt hQv, Real.sq_sqrt hQw]

namespace Observer

variable (u : Observer d)

/-- The split of the quadratic form by an observer: `Q(w) = (u.clock w)² − restForm(w⊥, w⊥)`. -/
theorem intervalQuadratic_eq (w : MinkowskiModel d) :
    intervalQuadratic w = u.clock w ^ 2 - u.restForm (u.project w) (u.project w) := by
  have h := u.decomposition w
  have hQ : intervalQuadratic w = intervalQuadratic
      (u.clock w • u.velocity + (u.project w : MinkowskiModel d)) := by rw [h]
  have hrest : pair u.velocity (u.project w : MinkowskiModel d) = 0 := u.clock_rest (u.project w)
  have hform : u.restForm (u.project w) (u.project w) =
      -intervalQuadratic (u.project w : MinkowskiModel d) := rfl
  rw [hQ, intervalQuadratic_add, hform, QuadraticMap.map_smul, u.unit, map_smul, smul_apply,
    hrest]
  simp only [smul_eq_mul]
  ring

/-- The time measured by an observer is at least the proper length: `√Q(w) ≤ u.clock w` for a
future causal `w`. -/
theorem sqrt_le_clock {w : MinkowskiModel d} (hw : FutureCausal w) :
    Real.sqrt (intervalQuadratic w) ≤ u.clock w := by
  have hu : FutureCausal u.velocity := by
    refine (futureCausal_iff _).mpr ⟨?_, u.future.le⟩
    change 0 ≤ intervalQuadratic u.velocity
    rw [u.unit]
    exact zero_le_one
  have h := sqrt_mul_sqrt_le_pair hu hw
  rwa [u.unit, Real.sqrt_one, one_mul] at h

/-- The case of equality: a vector whose proper length is the time measured by the observer is
a multiple of the velocity of the observer. -/
theorem eq_smul_of_clock_eq_sqrt {w : MinkowskiModel d}
    (h : u.clock w = Real.sqrt (intervalQuadratic w)) (hw : 0 ≤ intervalQuadratic w) :
    w = u.clock w • u.velocity := by
  have hsplit := u.intervalQuadratic_eq w
  have hsq : u.clock w ^ 2 = intervalQuadratic w := by rw [h, Real.sq_sqrt hw]
  have hzero : u.restForm (u.project w) (u.project w) = 0 := by linarith
  have hproj : u.project w = 0 := by
    by_contra hne
    exact (u.restForm_posDef (u.project w) hne).ne' hzero
  have hd := u.decomposition w
  rw [hproj] at hd
  simpa using hd.symm

end Observer

end ProjectAinos.SmoothGeometry.Minkowski
