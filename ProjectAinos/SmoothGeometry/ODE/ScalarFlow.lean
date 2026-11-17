/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.FlowComplete

/-!
# The flow of a positive bounded field on the line

For a smooth field `g` on `ℝ` with `0 < g ≤ C`, the equation `φ′ = g(φ)` is
solved by quadrature: the time `τ(φ) = ∫₀^φ ds / g(s)` (`scalarTime`) is a
strictly increasing function, and the solution through `0` is its inverse.

* `flowDomain_eq_univ_of_abs_le`: the flow of a bounded smooth field is
  defined for all times and points.
* `scalarTime_flow`, `flow_scalarTime`: the flow through `0` and the time are
  inverse to each other, so the solution through `0` is a bijection of the
  line.
* `flow_add_scalarTime_of_periodic`: if `g` has the period `P`, the solution
  advances by `P` in the time `τ(P)`.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace ProjectAinos.SmoothGeometry.NonlinearODE

variable {g : ℝ → ℝ}

/-- A bounded smooth field on the line has a flow defined for all times and
points. -/
theorem flowDomain_eq_univ_of_abs_le (hg : ContDiff ℝ ∞ g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    flowDomain g = univ :=
  flowDomain_eq_univ_of_norm_le hg (a := C) (b := 0) fun x => by
    rw [zero_mul, add_zero, Real.norm_eq_abs]
    exact hC x

/-- The time `∫₀^φ ds / g(s)` at which the solution through `0` reaches `φ`. -/
def scalarTime (g : ℝ → ℝ) (φ : ℝ) : ℝ := ∫ s in (0 : ℝ)..φ, (g s)⁻¹

theorem hasDerivAt_scalarTime (hg : Continuous g) (hpos : ∀ x, 0 < g x) (φ : ℝ) :
    HasDerivAt (scalarTime g) (g φ)⁻¹ φ :=
  ((hg.inv₀ fun x => (hpos x).ne').integral_hasStrictDerivAt 0 φ).hasDerivAt

theorem strictMono_scalarTime (hg : Continuous g) (hpos : ∀ x, 0 < g x) :
    StrictMono (scalarTime g) :=
  strictMono_of_deriv_pos fun φ => by
    rw [(hasDerivAt_scalarTime hg hpos φ).deriv]
    exact inv_pos.mpr (hpos φ)

@[simp] theorem scalarTime_zero (g : ℝ → ℝ) : scalarTime g 0 = 0 := by
  simp [scalarTime]

/-- The solution through `0` of a positive bounded field, at every time. -/
theorem hasDerivAt_flow_zero (hg : ContDiff ℝ ∞ g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) (u : ℝ) :
    HasDerivAt (fun u => flow g (u, 0)) (g (flow g (u, 0))) u :=
  hasDerivAt_flow hg (by rw [flowDomain_eq_univ_of_abs_le hg hC]; exact mem_univ _)

/-- The time of the point reached at the time `u` is `u`. -/
theorem scalarTime_flow (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (u : ℝ) : scalarTime g (flow g (u, 0)) = u := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s => scalarTime g (flow g (s, 0)) - s) 0 s := by
    intro s
    have h1 := (hasDerivAt_scalarTime hg.continuous hpos (flow g (s, 0))).comp s
      (hasDerivAt_flow_zero hg hC s)
    have h2 := h1.sub (hasDerivAt_id s)
    refine h2.congr_deriv ?_
    rw [inv_mul_cancel₀ (hpos _).ne', sub_self]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) u 0
  have h0 : scalarTime g (flow g (0, 0)) - 0 = 0 := by simp
  linarith

/-- The point reached at the time of `φ` is `φ`. -/
theorem flow_scalarTime (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (φ : ℝ) : flow g (scalarTime g φ, 0) = φ :=
  (strictMono_scalarTime hg.continuous hpos).injective (scalarTime_flow hg hpos hC _)

/-- The solution through `0` is strictly increasing. -/
theorem strictMono_flow_zero (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) : StrictMono fun u => flow g (u, 0) :=
  strictMono_of_deriv_pos fun u => by
    rw [(hasDerivAt_flow_zero hg hC u).deriv]
    exact hpos _

/-- For a periodic field the time increases by the same amount in each period. -/
theorem scalarTime_add_of_periodic (hg : Continuous g) (hpos : ∀ x, 0 < g x) {P : ℝ}
    (hP : ∀ x, g (x + P) = g x) (φ : ℝ) :
    scalarTime g (φ + P) = scalarTime g φ + scalarTime g P := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s => scalarTime g (s + P) - scalarTime g s) 0 s := by
    intro s
    have h1 := (hasDerivAt_scalarTime hg hpos (s + P)).comp_add_const s P
    have h2 := h1.sub (hasDerivAt_scalarTime hg hpos s)
    refine h2.congr_deriv ?_
    rw [hP, sub_self]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) φ 0
  have h0 : scalarTime g (0 + P) - scalarTime g 0 = scalarTime g P := by simp
  linarith

/-- For a field of period `P` the solution through `0` advances by `P` in the
time `τ(P)`. -/
theorem flow_add_scalarTime_of_periodic (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) {P : ℝ} (hP : ∀ x, g (x + P) = g x) (u : ℝ) :
    flow g (u + scalarTime g P, 0) = flow g (u, 0) + P := by
  apply (strictMono_scalarTime hg.continuous hpos).injective
  rw [scalarTime_flow hg hpos hC, scalarTime_add_of_periodic hg.continuous hpos hP,
    scalarTime_flow hg hpos hC]

end ProjectAinos.SmoothGeometry.NonlinearODE
