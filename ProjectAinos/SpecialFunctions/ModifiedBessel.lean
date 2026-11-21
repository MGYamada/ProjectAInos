/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Bessel
import Mathlib.Tactic

/-! # Modified Bessel functions of the first kind

The normalized ₀F₁ series gives the principal branch at every complex order, including
negative integral orders where individual reciprocal gamma coefficients vanish.
-/

@[expose] public section
noncomputable section

open Complex Filter
open scoped Topology

namespace ProjectAinos.SpecialFunctions.Bessel

/-- The modified Bessel function of the first kind at complex order. -/
def modifiedI (a z : ℂ) : ℂ := (z / 2) ^ a * regularizedHGFun 0 {a + 1} ((z / 2) ^ 2)

private theorem slit_half {z : ℂ} (hz : z ∈ slitPlane) : z / 2 ∈ slitPlane := by
  simpa [mem_slitPlane_iff, div_ofNat_re, div_ofNat_im] using hz

/-- Differentiation of the regular modified solution on the principal slit plane. -/
theorem hasDerivAt_modifiedI (a z : ℂ) (hz : z ∈ slitPlane) :
    HasDerivAt (modifiedI a) (a / z * modifiedI a z + modifiedI (a + 1) z) z := by
  have ht := (hasDerivAt_id z).div_const (2 : ℂ)
  have h₁ := ht.cpow_const (c := a) (slit_half hz)
  have h₂ := (hasDerivAt_zeroFone (a + 1) ((z / 2) ^ 2)).comp z (ht.pow 2)
  convert h₁.mul h₂ using 1
  · rfl
  unfold modifiedI
  simp only [id_eq, cpow_add _ _ (slitPlane_ne_zero (slit_half hz)),
    cpow_sub _ _ (slitPlane_ne_zero (slit_half hz)), cpow_one, Nat.cast_ofNat,
    Function.comp_apply, Pi.pow_apply]
  field_simp [slitPlane_ne_zero hz]
  ring

/-- The difference of two adjacent order shifts of the first modified function. -/
theorem modifiedI_recurrence (a z : ℂ) (hz : z ∈ slitPlane) :
    modifiedI (a - 1) z - modifiedI (a + 1) z = 2 * a / z * modifiedI a z := by
  unfold modifiedI
  simp only [sub_add_cancel, cpow_sub _ _ (slitPlane_ne_zero (slit_half hz)),
    cpow_add _ _ (slitPlane_ne_zero (slit_half hz)), cpow_one]
  rw [zeroFone_contiguous a ((z / 2) ^ 2)]
  field_simp [slitPlane_ne_zero hz]
  ring

/-- The first modified Bessel function satisfies the modified Bessel equation. -/
theorem modifiedI_equation (a z : ℂ) (hz : z ∈ slitPlane) :
    z ^ 2 * deriv (deriv (modifiedI a)) z + z * deriv (modifiedI a) z -
      (z ^ 2 + a ^ 2) * modifiedI a z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  have hd := hasDerivAt_modifiedI a z hz
  have he := (((hasDerivAt_const z a).div (hasDerivAt_id z) hz0).mul hd).add
    (hasDerivAt_modifiedI (a + 1) z hz)
  have hf : deriv (modifiedI a) =ᶠ[𝓝 z] (fun w => a / w * modifiedI a w + modifiedI (a + 1) w) :=
    eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw =>
      (hasDerivAt_modifiedI a w hw).deriv
  rw [(he.congr_of_eventuallyEq hf).deriv, hd.deriv]
  have hr := modifiedI_recurrence (a + 1) z hz
  rw [add_sub_cancel_right] at hr
  dsimp only [id_eq, Pi.div_apply]
  field_simp [hz0] at hr ⊢
  linear_combination -z * hr

end ProjectAinos.SpecialFunctions.Bessel
