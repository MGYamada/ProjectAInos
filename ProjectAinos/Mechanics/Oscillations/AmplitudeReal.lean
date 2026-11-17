/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Oscillations.AmplitudeDeformation
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The amplitude system on the real line

On the real line the two entries of the coefficient are complex conjugates,
`u′ = a w`, `w′ = ā u`. Then

* the propagator is complex linear (`propagator_cmul`) and commutes with
  `(u, w) ↦ (w̄, ū)` (`propagator_swapConj`), so the solutions with `w = ū`
  stay of this form;
* `|u|² − |w|²` is constant along a solution (`normSq_sub_normSq_propagator`).

For the solution with the initial value `(B₀, B̄₀)` this gives
(`abs_normSq_fst_propagator_sub_le`)

`| |u(s₁)|² − |B₀|² | ≤ |B₀|² |β| (4 |β| + 2)`,

where `β` is the first component of the solution with the initial value
`(0, 1)`: the change of the action is controlled by one entry of the
propagator.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ComplexConjugate

namespace ProjectAinos.Mechanics.AdiabaticAmplitude

open Complex (I)
open SmoothGeometry.LinearODE

/-- The multiplication of both unknowns by a complex number. -/
def cmul (c : ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ c).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).prod
    ((ContinuousLinearMap.mul ℝ ℂ c).comp (ContinuousLinearMap.snd ℝ ℂ ℂ))

theorem cmul_apply (c : ℂ) (y : ℂ × ℂ) : cmul c y = (c * y.1, c * y.2) := rfl

theorem offDiag_cmul (a b c : ℂ) (y : ℂ × ℂ) :
    offDiag a b (cmul c y) = cmul c (offDiag a b y) := by
  rw [offDiag_apply, cmul_apply, cmul_apply, offDiag_apply]
  exact Prod.ext (by ring) (by ring)

/-- The map `(u, w) ↦ (w̄, ū)`. -/
def swapConj : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ℂ ℂ)).prod
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.fst ℝ ℂ ℂ))

theorem swapConj_apply (y : ℂ × ℂ) : swapConj y = (conj y.2, conj y.1) := rfl

theorem offDiag_swapConj (a : ℂ) (y : ℂ × ℂ) :
    offDiag a (conj a) (swapConj y) = swapConj (offDiag a (conj a) y) := by
  rw [offDiag_apply, swapConj_apply, swapConj_apply, offDiag_apply, Prod.mk.injEq]
  constructor
  · change a * conj y.1 = conj (conj a * y.1)
    rw [map_mul, Complex.conj_conj]
  · change conj a * conj y.2 = conj (a * y.2)
    rw [map_mul]

section RealLine

variable {a : ℝ → ℂ} (ha : Continuous a) (hb : Continuous fun s => conj (a s))

/-- The propagator is complex linear. -/
theorem propagator_cmul {b : ℝ → ℂ} (hb' : Continuous b) (c : ℂ) (s₁ s₀ : ℝ) (y : ℂ × ℂ) :
    propagator (offDiagCurve a b ha hb') s₁ s₀ (cmul c y) =
      cmul c (propagator (offDiagCurve a b ha hb') s₁ s₀ y) :=
  propagator_apply_comm _ (cmul c) (fun r y => offDiag_cmul (a r) (b r) c y) s₁ s₀ y

/-- On the real line the propagator commutes with `(u, w) ↦ (w̄, ū)`. -/
theorem propagator_swapConj (s₁ s₀ : ℝ) (y : ℂ × ℂ) :
    propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ (swapConj y) =
      swapConj (propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ y) :=
  propagator_apply_comm _ swapConj (fun r y => offDiag_swapConj (a r) y) s₁ s₀ y

/-- On the real line `|u|² − |w|²` is constant along a solution. -/
theorem normSq_sub_normSq_propagator (s₁ s₀ : ℝ) (y : ℂ × ℂ) :
    Complex.normSq (propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ y).1 -
        Complex.normSq (propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ y).2 =
      Complex.normSq y.1 - Complex.normSq y.2 := by
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ → ℂ × ℂ, Y = fun s =>
      propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s s₀ y := ⟨_, rfl⟩
  have hY : ∀ s : ℝ, HasDerivAt Y (a s * (Y s).2, conj (a s) * (Y s).1) s := fun s => by
    rw [hYdef]
    exact hasDerivAt_propagator_apply _ s s₀ y
  have hu : ∀ s : ℝ, HasDerivAt (fun s => (Y s).1) (a s * (Y s).2) s := fun s =>
    (hasFDerivAt_fst (𝕜 := ℝ) (p := Y s)).comp_hasDerivAt s (hY s)
  have hw : ∀ s : ℝ, HasDerivAt (fun s => (Y s).2) (conj (a s) * (Y s).1) s := fun s =>
    (hasFDerivAt_snd (𝕜 := ℝ) (p := Y s)).comp_hasDerivAt s (hY s)
  have hP : ∀ s : ℝ, HasDerivAt
      (fun s => (Y s).1 * conj (Y s).1 - (Y s).2 * conj (Y s).2) 0 s := by
    intro s
    have h1 := ((hu s).mul (hu s).star).sub ((hw s).mul (hw s).star)
    refine h1.congr_deriv ?_
    simp only [Complex.star_def, map_mul, Complex.conj_conj]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hP s).differentiableAt)
    (fun s => (hP s).deriv) s₁ s₀
  have hY0 : Y s₀ = y := by
    rw [hYdef]
    change propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₀ s₀ y = y
    rw [propagator_self]
    rfl
  have h2 : ((Complex.normSq (Y s₁).1 - Complex.normSq (Y s₁).2 : ℝ) : ℂ) =
      ((Complex.normSq y.1 - Complex.normSq y.2 : ℝ) : ℂ) := by
    have h3 : (Y s₁).1 * conj (Y s₁).1 - (Y s₁).2 * conj (Y s₁).2 =
        (Y s₀).1 * conj (Y s₀).1 - (Y s₀).2 * conj (Y s₀).2 := hconst
    rw [hY0] at h3
    simp only [Complex.mul_conj] at h3
    push_cast
    exact h3
  have h4 := Complex.ofReal_injective h2
  rw [hYdef] at h4
  exact h4

/-- A bound for the change of the square of a norm between two triangle
inequalities, when `A² − c² = 1`. -/
theorem abs_sq_sub_sq_le {n₁ n₀ A c : ℝ} (hn₁ : 0 ≤ n₁) (hn₀ : 0 ≤ n₀) (hA : 0 ≤ A)
    (hc : 0 ≤ c) (hsq : A ^ 2 - c ^ 2 = 1) (h1 : n₁ ≤ n₀ * A + n₀ * c)
    (h2 : n₀ * A ≤ n₁ + n₀ * c) : |n₁ ^ 2 - n₀ ^ 2| ≤ n₀ ^ 2 * (c * (4 * c + 2)) := by
  have hA1 : A ≤ 1 + c := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hcA : c ≤ A := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hn₀2 : 0 ≤ n₀ ^ 2 := sq_nonneg _
  have hsq' : n₀ ^ 2 * A ^ 2 = n₀ ^ 2 * (1 + c ^ 2) := by
    rw [← hsq]
    ring
  have e1 : (n₀ * A + n₀ * c) ^ 2 = n₀ ^ 2 * (1 + 2 * c ^ 2) + 2 * (n₀ ^ 2 * c * A) := by
    have e : (n₀ * A + n₀ * c) ^ 2 = n₀ ^ 2 * A ^ 2 + n₀ ^ 2 * c ^ 2 + 2 * (n₀ ^ 2 * c * A) := by
      ring
    rw [e, hsq']
    ring
  have e2 : (n₀ * A - n₀ * c) ^ 2 = n₀ ^ 2 * (1 + 2 * c ^ 2) - 2 * (n₀ ^ 2 * c * A) := by
    have e : (n₀ * A - n₀ * c) ^ 2 = n₀ ^ 2 * A ^ 2 + n₀ ^ 2 * c ^ 2 - 2 * (n₀ ^ 2 * c * A) := by
      ring
    rw [e, hsq']
    ring
  have hup : n₁ ^ 2 ≤ (n₀ * A + n₀ * c) ^ 2 := pow_le_pow_left₀ hn₁ h1 2
  have hlow : (n₀ * A - n₀ * c) ^ 2 ≤ n₁ ^ 2 :=
    pow_le_pow_left₀ (by nlinarith [mul_nonneg hn₀ (sub_nonneg.mpr hcA)]) (by linarith) 2
  rw [e1] at hup
  rw [e2] at hlow
  have h3 : n₀ ^ 2 * c * A ≤ n₀ ^ 2 * c * (1 + c) :=
    mul_le_mul_of_nonneg_left hA1 (mul_nonneg hn₀2 hc)
  have h4 : 0 ≤ n₀ ^ 2 * c * A := mul_nonneg (mul_nonneg hn₀2 hc) hA
  have h5 : 0 ≤ n₀ ^ 2 * c ^ 2 := mul_nonneg hn₀2 (sq_nonneg c)
  have h6 : 0 ≤ n₀ ^ 2 * c := mul_nonneg hn₀2 hc
  rw [abs_le]
  constructor <;> nlinarith

/-- The change of `|u|²` along a solution with `w = ū`, through the entry of
the propagator from the second unknown to the first. -/
theorem abs_normSq_fst_propagator_sub_le (s₁ s₀ : ℝ) (B₀ : ℂ) :
    |Complex.normSq (propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀
          (B₀, conj B₀)).1 - Complex.normSq B₀| ≤
      Complex.normSq B₀ *
        (‖(propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ (0, 1)).1‖ *
          (4 * ‖(propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ (0, 1)).1‖ +
            2)) := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ × ℂ →L[ℝ] ℂ × ℂ,
      Φ = propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ := ⟨_, rfl⟩
  rw [← hΦ]
  have he2 : ((0 : ℂ), (1 : ℂ)) = swapConj (1, 0) := by
    rw [swapConj_apply]
    simp
  have hΦ2 : Φ (0, 1) = swapConj (Φ (1, 0)) := by
    rw [he2, hΦ]
    exact propagator_swapConj ha hb s₁ s₀ _
  have hy : ((B₀, conj B₀) : ℂ × ℂ) = cmul B₀ (1, 0) + cmul (conj B₀) (0, 1) := by
    rw [cmul_apply, cmul_apply]
    simp
  have hΦy : Φ (B₀, conj B₀) = cmul B₀ (Φ (1, 0)) + cmul (conj B₀) (Φ (0, 1)) := by
    rw [hy, map_add, hΦ, propagator_cmul ha hb, propagator_cmul ha hb]
  have hcons : Complex.normSq (Φ (1, 0)).1 - Complex.normSq (Φ (1, 0)).2 = 1 := by
    have h := normSq_sub_normSq_propagator ha hb s₁ s₀ ((1 : ℂ), (0 : ℂ))
    rw [← hΦ] at h
    simpa using h
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = (Φ (1, 0)).1 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℂ, γ = (Φ (1, 0)).2 := ⟨_, rfl⟩
  have hβ : (Φ (0, 1)).1 = conj γ := by
    rw [hΦ2, swapConj_apply, hγ]
  have hu : (Φ (B₀, conj B₀)).1 = B₀ * α + conj B₀ * conj γ := by
    rw [hΦy, Prod.fst_add, cmul_apply, cmul_apply, hβ, hα]
  rw [← hα, ← hγ] at hcons
  rw [hu, hβ, RCLike.norm_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hcons
  have h1 : ‖B₀ * α + conj B₀ * conj γ‖ ≤ ‖B₀‖ * ‖α‖ + ‖B₀‖ * ‖γ‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
  have h2 : ‖B₀‖ * ‖α‖ ≤ ‖B₀ * α + conj B₀ * conj γ‖ + ‖B₀‖ * ‖γ‖ := by
    have h3 : B₀ * α = (B₀ * α + conj B₀ * conj γ) - conj B₀ * conj γ := by ring
    have h4 := norm_sub_le (B₀ * α + conj B₀ * conj γ) (conj B₀ * conj γ)
    rw [← h3, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj] at h4
    exact h4
  exact abs_sq_sub_sq_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hcons
    h1 h2

end RealLine

end ProjectAinos.Mechanics.AdiabaticAmplitude
