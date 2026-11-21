/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.ScalarFlow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Jacobi's elliptic functions

For a modulus `k` with `k² < 1` the amplitude `am k` is the solution of

`φ′ = √(1 − k² sin² φ)`, `φ(0) = 0`,

which is the flow of a smooth, positive and bounded field on the line. Jacobi's
functions are `sn = sin ∘ am`, `cn = cos ∘ am` and `dn = √(1 − k² sn²)`. Mathlib
has Weierstrass's `℘` and no Jacobi functions.

* `hasDerivAt_sn`, `hasDerivAt_cn`, `hasDerivAt_dn`: `sn′ = cn dn`,
  `cn′ = −sn dn`, `dn′ = −k² sn cn`.
* `sn_sq_add_cn_sq`, `dn_sq`: `sn² + cn² = 1` and `dn² + k² sn² = 1`.
* `am_surjective`: the amplitude takes every real value, so `(cn, sn)` runs
  over the whole circle.
* `am_add_halfPeriod`: the amplitude increases by `π` in the time
  `halfPeriod k = ∫₀^π dφ / √(1 − k² sin² φ)`, which is `2K`; hence
  `sn (u + 2K) = −sn u`, `cn (u + 2K) = −cn u` and `dn (u + 2K) = dn u`.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Real ContDiff

namespace ProjectAinos.SpecialFunctions.JacobiElliptic

open SmoothGeometry SmoothGeometry.NonlinearODE

variable {k : ℝ}

/-- The field `√(1 − k² sin² φ)` of the amplitude. -/
def amplitudeField (k φ : ℝ) : ℝ := √(1 - k ^ 2 * Real.sin φ ^ 2)

theorem one_sub_pos (hk : k ^ 2 < 1) (φ : ℝ) : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := by
  have h1 : Real.sin φ ^ 2 ≤ 1 := Real.sin_sq_le_one φ
  nlinarith [sq_nonneg k, sq_nonneg (Real.sin φ)]

theorem amplitudeField_pos (hk : k ^ 2 < 1) (φ : ℝ) : 0 < amplitudeField k φ :=
  Real.sqrt_pos.mpr (one_sub_pos hk φ)

theorem amplitudeField_sq (hk : k ^ 2 < 1) (φ : ℝ) :
    amplitudeField k φ ^ 2 = 1 - k ^ 2 * Real.sin φ ^ 2 :=
  Real.sq_sqrt (one_sub_pos hk φ).le

theorem abs_amplitudeField_le (k φ : ℝ) : |amplitudeField k φ| ≤ 1 := by
  rw [amplitudeField, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
  nlinarith [sq_nonneg (k * Real.sin φ)]

theorem amplitudeField_add_pi (k φ : ℝ) : amplitudeField k (φ + π) = amplitudeField k φ := by
  simp [amplitudeField, Real.sin_add_pi]

theorem contDiff_amplitudeField (hk : k ^ 2 < 1) : ContDiff ℝ ∞ (amplitudeField k) := by
  have h : ContDiff ℝ ∞ fun φ : ℝ => 1 - k ^ 2 * Real.sin φ ^ 2 :=
    contDiff_const.sub (contDiff_const.mul (Real.contDiff_sin.pow 2))
  exact h.sqrt fun φ => (one_sub_pos hk φ).ne'

theorem hasDerivAt_amplitudeField (hk : k ^ 2 < 1) (φ : ℝ) :
    HasDerivAt (amplitudeField k)
      (-(k ^ 2 * Real.sin φ * Real.cos φ) / amplitudeField k φ) φ := by
  have h1 : HasDerivAt (fun φ : ℝ => 1 - k ^ 2 * Real.sin φ ^ 2)
      (-(k ^ 2 * (2 * Real.sin φ * Real.cos φ))) φ := by
    have h := (((Real.hasDerivAt_sin φ).pow 2).const_mul (k ^ 2)).const_sub 1
    refine h.congr_deriv ?_
    simp
  have h2 := h1.sqrt (one_sub_pos hk φ).ne'
  refine h2.congr_deriv ?_
  have hne : √(1 - k ^ 2 * Real.sin φ ^ 2) ≠ 0 := (amplitudeField_pos hk φ).ne'
  rw [amplitudeField]
  field_simp

/-- The amplitude: the solution of `φ′ = √(1 − k² sin² φ)` through `0`. -/
def am (k u : ℝ) : ℝ := flow (amplitudeField k) (u, 0)

/-- Jacobi's `sn`. -/
def sn (k u : ℝ) : ℝ := Real.sin (am k u)

/-- Jacobi's `cn`. -/
def cn (k u : ℝ) : ℝ := Real.cos (am k u)

/-- Jacobi's `dn`. -/
def dn (k u : ℝ) : ℝ := amplitudeField k (am k u)

/-- The time `2K = ∫₀^π dφ / √(1 − k² sin² φ)` in which the amplitude increases
by `π`. -/
def halfPeriod (k : ℝ) : ℝ := scalarTime (amplitudeField k) π

@[simp] theorem am_zero (k : ℝ) : am k 0 = 0 := flow_zero _ _

@[simp] theorem sn_zero (k : ℝ) : sn k 0 = 0 := by simp [sn]

@[simp] theorem cn_zero (k : ℝ) : cn k 0 = 1 := by simp [cn]

@[simp] theorem dn_zero (k : ℝ) : dn k 0 = 1 := by simp [dn, amplitudeField]

theorem sn_sq_add_cn_sq (k u : ℝ) : sn k u ^ 2 + cn k u ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq (am k u)

theorem dn_sq (hk : k ^ 2 < 1) (u : ℝ) : dn k u ^ 2 = 1 - k ^ 2 * sn k u ^ 2 :=
  amplitudeField_sq hk (am k u)

theorem dn_pos (hk : k ^ 2 < 1) (u : ℝ) : 0 < dn k u := amplitudeField_pos hk (am k u)

theorem hasDerivAt_am (hk : k ^ 2 < 1) (u : ℝ) : HasDerivAt (am k) (dn k u) u :=
  hasDerivAt_flow_zero (contDiff_amplitudeField hk) (abs_amplitudeField_le k) u

theorem hasDerivAt_sn (hk : k ^ 2 < 1) (u : ℝ) : HasDerivAt (sn k) (cn k u * dn k u) u :=
  (Real.hasDerivAt_sin (am k u)).comp u (hasDerivAt_am hk u)

theorem hasDerivAt_cn (hk : k ^ 2 < 1) (u : ℝ) :
    HasDerivAt (cn k) (-(sn k u * dn k u)) u := by
  have h := (Real.hasDerivAt_cos (am k u)).comp u (hasDerivAt_am hk u)
  refine h.congr_deriv ?_
  rw [sn]
  ring

theorem hasDerivAt_dn (hk : k ^ 2 < 1) (u : ℝ) :
    HasDerivAt (dn k) (-(k ^ 2 * sn k u * cn k u)) u := by
  have h := (hasDerivAt_amplitudeField hk (am k u)).comp u (hasDerivAt_am hk u)
  refine h.congr_deriv ?_
  have hne : amplitudeField k (am k u) ≠ 0 := (amplitudeField_pos hk _).ne'
  rw [dn, sn, cn]
  field_simp

theorem contDiff_am (hk : k ^ 2 < 1) : ContDiff ℝ ∞ (am k) := by
  have hflow : ContDiff ℝ ∞ (flow (amplitudeField k)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_flow (contDiff_amplitudeField hk) (by
      rw [flowDomain_eq_univ_of_abs_le (contDiff_amplitudeField hk) (abs_amplitudeField_le k)]
      exact mem_univ _)
  exact hflow.comp (contDiff_id.prodMk contDiff_const)

theorem contDiff_sn (hk : k ^ 2 < 1) : ContDiff ℝ ∞ (sn k) :=
  Real.contDiff_sin.comp (contDiff_am hk)

theorem contDiff_cn (hk : k ^ 2 < 1) : ContDiff ℝ ∞ (cn k) :=
  Real.contDiff_cos.comp (contDiff_am hk)

theorem contDiff_dn (hk : k ^ 2 < 1) : ContDiff ℝ ∞ (dn k) :=
  (contDiff_amplitudeField hk).comp (contDiff_am hk)

/-- The amplitude takes every real value. -/
theorem am_surjective (hk : k ^ 2 < 1) : Function.Surjective (am k) := fun φ =>
  ⟨scalarTime (amplitudeField k) φ,
    flow_scalarTime (contDiff_amplitudeField hk) (amplitudeField_pos hk)
      (abs_amplitudeField_le k) φ⟩

theorem strictMono_am (hk : k ^ 2 < 1) : StrictMono (am k) :=
  strictMono_flow_zero (contDiff_amplitudeField hk) (amplitudeField_pos hk)
    (abs_amplitudeField_le k)

theorem halfPeriod_pos (hk : k ^ 2 < 1) : 0 < halfPeriod k := by
  have h := strictMono_scalarTime (contDiff_amplitudeField hk).continuous
    (amplitudeField_pos hk) Real.pi_pos
  rwa [scalarTime_zero] at h

/-- The amplitude increases by `π` in the time `2K`. -/
theorem am_add_halfPeriod (hk : k ^ 2 < 1) (u : ℝ) :
    am k (u + halfPeriod k) = am k u + π :=
  flow_add_scalarTime_of_periodic (contDiff_amplitudeField hk) (amplitudeField_pos hk)
    (abs_amplitudeField_le k) (amplitudeField_add_pi k) u

theorem sn_add_halfPeriod (hk : k ^ 2 < 1) (u : ℝ) : sn k (u + halfPeriod k) = -sn k u := by
  rw [sn, am_add_halfPeriod hk, Real.sin_add_pi, sn]

theorem cn_add_halfPeriod (hk : k ^ 2 < 1) (u : ℝ) : cn k (u + halfPeriod k) = -cn k u := by
  rw [cn, am_add_halfPeriod hk, Real.cos_add_pi, cn]

theorem dn_add_halfPeriod (hk : k ^ 2 < 1) (u : ℝ) : dn k (u + halfPeriod k) = dn k u := by
  rw [dn, am_add_halfPeriod hk, amplitudeField_add_pi, dn]

end ProjectAinos.SpecialFunctions.JacobiElliptic
