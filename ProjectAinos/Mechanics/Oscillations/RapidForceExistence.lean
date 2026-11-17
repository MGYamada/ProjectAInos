/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Oscillations.RapidForce
public import ProjectAinos.SmoothGeometry.ODE.FlowComplete

/-!
# Existence of the motions in a rapidly oscillating field

The theorems of `RapidForce` compare a given motion under the oscillating
force with a given motion in the effective potential. Under the same bounds
both exist for all times and all initial values, as flows of smooth vector
fields of linear growth; the time is a third co-ordinate for the first one.

* `exists_isRapidMotion`: a motion under the force with a given initial
  position and velocity.
* `exists_isSlowMotion`: a motion in the effective potential with a given
  initial position and velocity.
* `exists_forall_exists_abs_sub_le`: hence, for every frequency and all
  initial values with a bounded velocity, there are a motion and a motion in
  the effective potential that differ by at most `C/ω` on `[0, L]`.
-/

@[expose] public section
noncomputable section

open Set
open scoped ContDiff

namespace ProjectAinos.Mechanics.RapidForce

open SmoothGeometry.NonlinearODE

variable {m Ω A B : ℝ} {U g : ℝ → ℝ}

/-- The field of the motion under the force, with the time as a third
co-ordinate. -/
def extendedField (m Ω : ℝ) (U g : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.2.1, (-deriv U p.1 + Ω * g p.1 * Real.cos (Ω * p.2.2)) / m, 1)

theorem contDiff_extendedField (hb : RapidBounds U g A B) (m Ω : ℝ) :
    ContDiff ℝ ∞ (extendedField m Ω U g) := by
  have hU' : ContDiff ℝ ∞ (deriv U) := hb.contDiff_potential.iterate_deriv 1
  have hg := hb.contDiff_amplitude
  have h1 : ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ => p.2.1 := contDiff_snd.fst
  have h2 : ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ =>
      (-deriv U p.1 + Ω * g p.1 * Real.cos (Ω * p.2.2)) / m :=
    (((hU'.comp contDiff_fst).neg).add ((contDiff_const.mul (hg.comp contDiff_fst)).mul
      (Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd.snd)))).div_const m
  exact h1.prodMk (h2.prodMk contDiff_const)

theorem norm_extendedField_le (hb : RapidBounds U g A B) (hm : 0 < m) (Ω : ℝ)
    (p : ℝ × ℝ × ℝ) :
    ‖extendedField m Ω U g p‖ ≤ ((A + |Ω| * B) / m + 1) + 1 * ‖p‖ := by
  have hA := hb.nonneg_potential
  have hB := hb.nonneg_amplitude
  have hacc : |(-deriv U p.1 + Ω * g p.1 * Real.cos (Ω * p.2.2)) / m| ≤ (A + |Ω| * B) / m := by
    rw [abs_div, abs_of_pos hm]
    refine div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add ?_ ?_)) hm.le
    · rw [abs_neg]
      exact hb.deriv_potential _
    · rw [abs_mul, abs_mul]
      calc |Ω| * |g p.1| * |Real.cos (Ω * p.2.2)| ≤ |Ω| * B * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hb.amplitude _) (abs_nonneg _))
              (Real.abs_cos_le_one _) (abs_nonneg _) (mul_nonneg (abs_nonneg _) hB)
        _ = |Ω| * B := mul_one _
  have hc : 0 ≤ (A + |Ω| * B) / m :=
    div_nonneg (add_nonneg hA (mul_nonneg (abs_nonneg _) hB)) hm.le
  have h1 : |p.2.1| ≤ ‖p‖ := by
    rw [← Real.norm_eq_abs]
    exact (norm_fst_le p.2).trans (norm_snd_le p)
  have hp := norm_nonneg p
  simp only [extendedField, Prod.norm_mk, max_le_iff, Real.norm_eq_abs, abs_one]
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-- A motion under the oscillating force exists for all times, with a given
initial position and velocity. -/
theorem exists_isRapidMotion (hb : RapidBounds U g A B) (hm : 0 < m) (Ω x₀ v₀ : ℝ) :
    ∃ x v : ℝ → ℝ, IsRapidMotion m Ω U g x v ∧ x 0 = x₀ ∧ v 0 = v₀ := by
  have hX := contDiff_extendedField hb m Ω
  have hdom : flowDomain (extendedField m Ω U g) = univ :=
    flowDomain_eq_univ_of_norm_le hX (norm_extendedField_le hb hm Ω)
  let γ : ℝ → ℝ × ℝ × ℝ := fun t => flow (extendedField m Ω U g) (t, (x₀, v₀, 0))
  have hγ : ∀ t, HasDerivAt γ (extendedField m Ω U g (γ t)) t := fun t =>
    hasDerivAt_flow hX (by rw [hdom]; exact mem_univ _)
  have hγ0 : γ 0 = (x₀, v₀, 0) := flow_zero _ _
  have h1 : ∀ t, HasDerivAt (fun s => (γ s).1) ((γ t).2.1) t := fun t =>
    (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t (hγ t)
  have hsnd : ∀ t, HasDerivAt (fun s => (γ s).2) ((extendedField m Ω U g (γ t)).2) t :=
    fun t => (hasFDerivAt_snd (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t (hγ t)
  have h2' : ∀ t, HasDerivAt (fun s => (γ s).2.1) ((extendedField m Ω U g (γ t)).2.1) t :=
    fun t => HasFDerivAt.comp_hasDerivAt (l := Prod.fst) (f := fun s => (γ s).2) t
      hasFDerivAt_fst (hsnd t)
  have h3' : ∀ t, HasDerivAt (fun s => (γ s).2.2) ((extendedField m Ω U g (γ t)).2.2) t :=
    fun t => HasFDerivAt.comp_hasDerivAt (l := Prod.snd) (f := fun s => (γ s).2) t
      hasFDerivAt_snd (hsnd t)
  have h2 : ∀ t, HasDerivAt (fun s => (γ s).2.1)
      ((-deriv U (γ t).1 + Ω * g (γ t).1 * Real.cos (Ω * (γ t).2.2)) / m) t := h2'
  have h3 : ∀ t, HasDerivAt (fun s => (γ s).2.2) 1 t := h3'
  have htime : ∀ t, (γ t).2.2 = t := by
    have hd : ∀ t, HasDerivAt (fun s => (γ s).2.2 - s) 0 t := fun t => by
      have h := (h3 t).sub (hasDerivAt_id t)
      rwa [sub_self] at h
    intro t
    have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    have h0 : (γ 0).2.2 - 0 = 0 := by rw [hγ0, sub_zero]
    linarith
  refine ⟨fun t => (γ t).1, fun t => (γ t).2.1, ⟨h1, fun t => ?_⟩, ?_, ?_⟩
  · have h := h2 t
    rwa [htime t] at h
  · change (γ 0).1 = x₀
    rw [hγ0]
  · change (γ 0).2.1 = v₀
    rw [hγ0]

theorem contDiff_slowField (hb : RapidBounds U g A B) (m : ℝ) :
    ContDiff ℝ ∞ (slowField m U g) := by
  have hU' : ContDiff ℝ ∞ (deriv U) := hb.contDiff_potential.iterate_deriv 1
  have hg := hb.contDiff_amplitude
  have hg' : ContDiff ℝ ∞ (deriv g) := hg.iterate_deriv 1
  have h2 : ContDiff ℝ ∞ fun p : ℝ × ℝ =>
      -(deriv U p.1 + g p.1 * deriv g p.1 / (2 * m)) / m :=
    (((hU'.comp contDiff_fst).add (((hg.comp contDiff_fst).mul
      (hg'.comp contDiff_fst)).div_const (2 * m))).neg).div_const m
  exact contDiff_snd.prodMk h2

theorem norm_slowField_le (hb : RapidBounds U g A B) (hm : 0 < m) (p : ℝ × ℝ) :
    ‖slowField m U g p‖ ≤ (A + B * B / (2 * m)) / m + 1 * ‖p‖ := by
  have hA := hb.nonneg_potential
  have hB := hb.nonneg_amplitude
  have h2m : (0 : ℝ) < 2 * m := by positivity
  have hacc : |-(deriv U p.1 + g p.1 * deriv g p.1 / (2 * m)) / m| ≤
      (A + B * B / (2 * m)) / m := by
    rw [abs_div, abs_neg, abs_of_pos hm]
    refine div_le_div_of_nonneg_right ((abs_add_le _ _).trans
      (add_le_add (hb.deriv_potential _) ?_)) hm.le
    rw [abs_div, abs_of_pos h2m, abs_mul]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (hb.amplitude _) (hb.deriv_amplitude _) (abs_nonneg _) hB) h2m.le
  have hc : 0 ≤ (A + B * B / (2 * m)) / m :=
    div_nonneg (add_nonneg hA (div_nonneg (mul_nonneg hB hB) h2m.le)) hm.le
  have h1 : |p.2| ≤ ‖p‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_snd_le p
  have hp := norm_nonneg p
  simp only [slowField, Prod.norm_mk, max_le_iff, Real.norm_eq_abs]
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- A motion in the effective potential exists for all times, with a given
initial position and velocity. -/
theorem exists_isSlowMotion (hb : RapidBounds U g A B) (hm : 0 < m) (x₀ v₀ : ℝ) :
    ∃ X W : ℝ → ℝ, IsSlowMotion m U g X W ∧ X 0 = x₀ ∧ W 0 = v₀ := by
  have hX := contDiff_slowField hb m
  have hdom : flowDomain (slowField m U g) = univ :=
    flowDomain_eq_univ_of_norm_le hX (norm_slowField_le hb hm)
  let γ : ℝ → ℝ × ℝ := fun t => flow (slowField m U g) (t, (x₀, v₀))
  have hγ : ∀ t, HasDerivAt γ (slowField m U g (γ t)) t := fun t =>
    hasDerivAt_flow hX (by rw [hdom]; exact mem_univ _)
  have hγ0 : γ 0 = (x₀, v₀) := flow_zero _ _
  refine ⟨fun t => (γ t).1, fun t => (γ t).2, ⟨fun t => ?_, fun t => ?_⟩, ?_, ?_⟩
  · exact (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t (hγ t)
  · exact (hasFDerivAt_snd (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t (hγ t)
  · change (γ 0).1 = x₀
    rw [hγ0]
  · change (γ 0).2 = v₀
    rw [hγ0]

/-- The motion in the effective potential as the limit of large frequencies:
for all initial values with a bounded velocity and every frequency there are a
motion under the force and a motion in the effective potential, from these
initial values, which differ by at most `C/ω` on `[0, L]`. -/
theorem exists_forall_exists_abs_sub_le (hm : 0 < m) (hb : RapidBounds U g A B) (V₀ L : ℝ) :
    ∃ C : ℝ, ∀ Ω : ℝ, 0 < Ω → ∀ x₀ v₀ : ℝ, |v₀| ≤ V₀ → ∃ x v X W : ℝ → ℝ,
      IsRapidMotion m Ω U g x v ∧ IsSlowMotion m U g X W ∧ x 0 = x₀ ∧ v 0 = v₀ ∧ X 0 = x₀ ∧
        W 0 = v₀ ∧ ∀ t ∈ Icc 0 L, |x t - X t| ≤ C / Ω := by
  obtain ⟨C, hC⟩ := exists_forall_abs_sub_le_of_initial hm hb V₀ L
  refine ⟨C, fun Ω hΩ x₀ v₀ hv₀ => ?_⟩
  obtain ⟨x, v, hxv, hx0, hv0⟩ := exists_isRapidMotion hb hm Ω x₀ v₀
  obtain ⟨X, W, hXW, hX0, hW0⟩ := exists_isSlowMotion hb hm x₀ v₀
  exact ⟨x, v, X, W, hxv, hXW, hx0, hv0, hX0, hW0,
    hC Ω hΩ x v X W hxv hXW (hx0.trans hX0.symm) (hv0.trans hW0.symm) (hv0 ▸ hv₀)⟩

end ProjectAinos.Mechanics.RapidForce
