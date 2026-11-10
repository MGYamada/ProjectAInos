/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Operations
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Smooth inverses near a nonzero real number -/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open scoped ContDiff
open Metric

/-- A globally smooth inverse on the support of a smaller cutoff. This identity
constructs inverses in the localization at a real point without postulating a
smooth structure on an ordinary ring localization. -/
theorem exists_localInverse (r : ℝ) (hr : r ≠ 0) :
    ∃ f g : SmoothOperation 1, g ![r] = 1 ∧
      (SmoothOperation.proj 0 * f - 1) * g = 0 := by
  have hpos : 0 < |r| := abs_pos.mpr hr
  let b : ContDiffBump r := ⟨|r| / 4, |r| / 2, by positivity, by linarith⟩
  let c : ContDiffBump r := ⟨|r| / 8, |r| / 4, by positivity, by linarith⟩
  have hb0 : b 0 = 0 := by
    apply b.zero_of_le_dist
    simp only [Real.dist_eq, zero_sub, abs_neg]
    dsimp [b]
    linarith
  have hd (t : ℝ) : t ^ 2 + (1 - b t) ^ 2 ≠ 0 := by
    by_cases ht : t = 0
    · simp [ht, hb0]
    · have : 0 < t ^ 2 := sq_pos_of_ne_zero ht
      nlinarith [sq_nonneg (1 - b t)]
  let f : ℝ → ℝ := fun t => t / (t ^ 2 + (1 - b t) ^ 2)
  have hf : ContDiff ℝ ∞ f :=
    contDiff_id.div ((contDiff_id.pow 2).add ((contDiff_const.sub b.contDiff).pow 2)) hd
  refine ⟨SmoothOperation.ofContDiff (fun x => f (x 0))
      (hf.comp (contDiff_apply ℝ (fun _ => ℝ) 0)),
    SmoothOperation.ofContDiff (fun x => c (x 0))
      (c.contDiff.comp (contDiff_apply ℝ (fun _ => ℝ) 0)), ?_, ?_⟩
  · exact c.one_of_mem_closedBall (mem_closedBall_self c.rIn_pos.le)
  · ext x
    change (x 0 * f (x 0) - 1) * c (x 0) = 0
    by_cases hc : c (x 0) = 0
    · rw [hc, mul_zero]
    · have hxc : dist (x 0) r < |r| / 4 := by
        have hxmem : x 0 ∈ Function.support c := hc
        rw [c.support_eq] at hxmem
        exact hxmem
      have hb : b (x 0) = 1 := b.one_of_mem_closedBall hxc.le
      have hx : x 0 ≠ 0 := by
        intro h
        simp only [h, Real.dist_eq, zero_sub, abs_neg] at hxc
        linarith
      dsimp [f]
      simp only [hb, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]
      field_simp
      ring

end ProjectAInos.SmoothAlgebra
