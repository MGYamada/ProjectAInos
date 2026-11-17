/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.PropagatorBound
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The propagator of a coefficient that is deformed along a complex direction

Let the coefficient `A(p, s)` of a linear equation in the time `s` depend on a
parameter `p`, and let `J` be a continuous linear map that commutes with
`A(p, s)`. Suppose that `∂A/∂p = c(p) J ∂A/∂s`. This is the Cauchy–Riemann
equation of a coefficient `A(p, s) = a(s + i η(p))` with a holomorphic `a`,
where `J` is the multiplication by `i` and `c = η′`.

* `hasDerivAt_propagator_apply_param`: the derivative of the solution in the
  parameter is
  `∂/∂p Φ_p(s₁, s₀) y₀ = c(p) J (A(p, s₁) Φ_p(s₁, s₀) y₀ − Φ_p(s₁, s₀) A(p, s₀) y₀)`.
  Only the values of the coefficient at the two ends enter: the propagator
  along a line parallel to the real axis depends on the line only through
  its ends.
* `norm_propagator_apply_sub_le_of_deformation`: the resulting bound for the
  difference of the propagators of two parameters.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.LinearODE

section Lines

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The derivative of a function of two real variables in the first variable. -/
theorem hasDerivAt_fst_line {F : ℝ × ℝ → G} {p s : ℝ} (h : DifferentiableAt ℝ F (p, s)) :
    HasDerivAt (fun p' => F (p', s)) (fderiv ℝ F (p, s) (1, 0)) p := by
  have h1 : HasDerivAt (fun p' : ℝ => (p', s)) ((1 : ℝ), (0 : ℝ)) p :=
    (hasDerivAt_id p).prodMk (hasDerivAt_const p s)
  exact HasFDerivAt.comp_hasDerivAt (f := fun p' : ℝ => (p', s)) p h.hasFDerivAt h1

/-- The derivative of a function of two real variables in the second variable. -/
theorem hasDerivAt_snd_line {F : ℝ × ℝ → G} {p s : ℝ} (h : DifferentiableAt ℝ F (p, s)) :
    HasDerivAt (fun s' => F (p, s')) (fderiv ℝ F (p, s) (0, 1)) s := by
  have h1 : HasDerivAt (fun s' : ℝ => (p, s')) ((0 : ℝ), (1 : ℝ)) s :=
    (hasDerivAt_const s p).prodMk (hasDerivAt_id s)
  exact HasFDerivAt.comp_hasDerivAt (f := fun s' : ℝ => (p, s')) s h.hasFDerivAt h1

end Lines

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The solution with the value `y₀` at the time `s₀`, as a function of the
parameter and the time. -/
def paramSolution (A : ℝ × ℝ → V →L[ℝ] V) (hA : Continuous A) (s₀ : ℝ) (y₀ : V)
    (q : ℝ × ℝ) : V :=
  propagator (coefficientCurve A hA q.1) q.2 s₀ y₀

theorem contDiff_paramSolution {A : ℝ × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) (s₀ : ℝ)
    (y₀ : V) : ContDiff ℝ ∞ (paramSolution A hA.continuous s₀ y₀) :=
  ContDiff.comp
    (g := fun q : (ℝ × ℝ × ℝ) × V =>
      propagator (coefficientCurve A hA.continuous q.1.1) q.1.2.1 q.1.2.2 q.2)
    (f := fun q : ℝ × ℝ => (((q.1, q.2, s₀), y₀) : (ℝ × ℝ × ℝ) × V))
    (propagator_apply_contDiff hA)
    ((contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).prodMk contDiff_const)

theorem hasDerivAt_paramSolution (A : ℝ × ℝ → V →L[ℝ] V) (hA : Continuous A) (s₀ : ℝ)
    (y₀ : V) (p s : ℝ) :
    HasDerivAt (fun s' => paramSolution A hA s₀ y₀ (p, s'))
      (A (p, s) (paramSolution A hA s₀ y₀ (p, s))) s :=
  hasDerivAt_propagator_apply (coefficientCurve A hA p) s s₀ y₀

theorem paramSolution_self (A : ℝ × ℝ → V →L[ℝ] V) (hA : Continuous A) (s₀ : ℝ) (y₀ : V)
    (p : ℝ) : paramSolution A hA s₀ y₀ (p, s₀) = y₀ := by
  rw [paramSolution, propagator_self]
  rfl

theorem fderiv_paramSolution_time {A : ℝ × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) (s₀ : ℝ)
    (y₀ : V) (p s : ℝ) :
    fderiv ℝ (paramSolution A hA.continuous s₀ y₀) (p, s) (0, 1) =
      A (p, s) (paramSolution A hA.continuous s₀ y₀ (p, s)) :=
  (hasDerivAt_snd_line ((contDiff_paramSolution hA s₀ y₀).differentiable (by simp)
    (p, s))).unique (hasDerivAt_paramSolution A hA.continuous s₀ y₀ p s)

/-- The equation of the derivative of the solution in the parameter. -/
theorem hasDerivAt_fderiv_paramSolution {A : ℝ × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A)
    (s₀ : ℝ) (y₀ : V) (p s : ℝ) :
    HasDerivAt (fun s' => fderiv ℝ (paramSolution A hA.continuous s₀ y₀) (p, s') (1, 0))
      (fderiv ℝ A (p, s) (1, 0) (paramSolution A hA.continuous s₀ y₀ (p, s)) +
        A (p, s) (fderiv ℝ (paramSolution A hA.continuous s₀ y₀) (p, s) (1, 0))) s := by
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ × ℝ → V, F = paramSolution A hA.continuous s₀ y₀ := ⟨_, rfl⟩
  rw [← hFdef]
  have hF : ContDiff ℝ ∞ F := by
    rw [hFdef]
    exact contDiff_paramSolution hA s₀ y₀
  have hFd : ∀ q, DifferentiableAt ℝ F q := fun q => hF.differentiable (by simp) q
  have hF' : ∀ q, DifferentiableAt ℝ (fderiv ℝ F) q := fun q =>
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) q
  have hAd : ∀ q, DifferentiableAt ℝ A q := fun q => hA.differentiable (by simp) q
  have h1 : HasDerivAt (fun s' => fderiv ℝ F (p, s') (1, 0))
      (fderiv ℝ (fderiv ℝ F) (p, s) (0, 1) (1, 0)) s := by
    have h := (hasDerivAt_snd_line (hF' (p, s))).clm_apply
      (hasDerivAt_const s ((1 : ℝ), (0 : ℝ)))
    simpa using h
  have h2 : HasDerivAt (fun p' => fderiv ℝ F (p', s) (0, 1))
      (fderiv ℝ (fderiv ℝ F) (p, s) (1, 0) (0, 1)) p := by
    have h := (hasDerivAt_fst_line (hF' (p, s))).clm_apply
      (hasDerivAt_const p ((0 : ℝ), (1 : ℝ)))
    simpa using h
  have h3 : HasDerivAt (fun p' => A (p', s) (F (p', s)))
      (fderiv ℝ A (p, s) (1, 0) (F (p, s)) + A (p, s) (fderiv ℝ F (p, s) (1, 0))) p :=
    (hasDerivAt_fst_line (hAd (p, s))).clm_apply (hasDerivAt_fst_line (hFd (p, s)))
  have e : (fun p' => fderiv ℝ F (p', s) (0, 1)) = fun p' => A (p', s) (F (p', s)) :=
    funext fun p' => by
      rw [hFdef]
      exact fderiv_paramSolution_time hA s₀ y₀ p' s
  rw [e] at h2
  have hsymm := ((hF.contDiffAt (x := (p, s))).isSymmSndFDerivAt (by simp)) ((0 : ℝ), (1 : ℝ))
    ((1 : ℝ), (0 : ℝ))
  rw [hsymm, h2.unique h3] at h1
  exact h1

/-- The derivative of a solution in the parameter of a deformation of the
coefficient along a complex direction. -/
theorem hasDerivAt_propagator_apply_param {A : ℝ × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A)
    (J : V →L[ℝ] V) (c : ℝ → ℝ) (hJ : ∀ (q : ℝ × ℝ) (v : V), A q (J v) = J (A q v))
    (hCR : ∀ (q : ℝ × ℝ) (v : V),
      fderiv ℝ A q (1, 0) v = c q.1 • J (fderiv ℝ A q (0, 1) v))
    (p s₀ s₁ : ℝ) (y₀ : V) :
    HasDerivAt (fun p' => propagator (coefficientCurve A hA.continuous p') s₁ s₀ y₀)
      (c p • J (A (p, s₁) (propagator (coefficientCurve A hA.continuous p) s₁ s₀ y₀) -
        propagator (coefficientCurve A hA.continuous p) s₁ s₀ (A (p, s₀) y₀))) p := by
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ × ℝ → V, F = paramSolution A hA.continuous s₀ y₀ := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂def⟩ : ∃ F₂ : ℝ → V, F₂ = fun s =>
      propagator (coefficientCurve A hA.continuous p) s s₀ (A (p, s₀) y₀) := ⟨_, rfl⟩
  have hFd : ∀ q, DifferentiableAt ℝ F q := fun q => by
    rw [hFdef]
    exact (contDiff_paramSolution hA s₀ y₀).differentiable (by simp) q
  have hAd : ∀ q, DifferentiableAt ℝ A q := fun q => hA.differentiable (by simp) q
  have hFs : ∀ s : ℝ, HasDerivAt (fun s' => F (p, s')) (A (p, s) (F (p, s))) s := fun s => by
    rw [hFdef]
    exact hasDerivAt_paramSolution A hA.continuous s₀ y₀ p s
  have hD : ∀ s : ℝ, HasDerivAt (fun s' => fderiv ℝ F (p, s') (1, 0))
      (fderiv ℝ A (p, s) (1, 0) (F (p, s)) + A (p, s) (fderiv ℝ F (p, s) (1, 0))) s :=
    fun s => by
      rw [hFdef]
      exact hasDerivAt_fderiv_paramSolution hA s₀ y₀ p s
  have hF2 : ∀ s : ℝ, HasDerivAt F₂ (A (p, s) (F₂ s)) s := fun s => by
    rw [hF₂def]
    exact hasDerivAt_propagator_apply (coefficientCurve A hA.continuous p) s s₀ _
  have hW : ∀ s : ℝ, HasDerivAt (fun s' => c p • J (A (p, s') (F (p, s')) - F₂ s'))
      (c p • J (fderiv ℝ A (p, s) (0, 1) (F (p, s)) + A (p, s) (A (p, s) (F (p, s))) -
        A (p, s) (F₂ s))) s := by
    intro s
    have h1 : HasDerivAt (fun s' => A (p, s') (F (p, s')))
        (fderiv ℝ A (p, s) (0, 1) (F (p, s)) + A (p, s) (A (p, s) (F (p, s)))) s :=
      (hasDerivAt_snd_line (hAd (p, s))).clm_apply (hFs s)
    exact (J.hasFDerivAt.comp_hasDerivAt s (h1.sub (hF2 s))).const_smul (c p)
  -- the difference solves the equation and vanishes at the initial time
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ → V, Z = fun s => fderiv ℝ F (p, s) (1, 0) -
      c p • J (A (p, s) (F (p, s)) - F₂ s) := ⟨_, rfl⟩
  have hZ : ∀ s : ℝ, HasDerivAt Z (coefficientCurve A hA.continuous p s (Z s)) s := by
    intro s
    rw [hZdef]
    refine ((hD s).sub (hW s)).congr_deriv ?_
    change _ = A (p, s) (fderiv ℝ F (p, s) (1, 0) - c p • J (A (p, s) (F (p, s)) - F₂ s))
    rw [hCR]
    simp only [map_sub, map_add, map_smul, smul_sub, smul_add, hJ]
    abel
  have hF0 : ∀ p' : ℝ, F (p', s₀) = y₀ := fun p' => by
    rw [hFdef]
    exact paramSolution_self A hA.continuous s₀ y₀ p'
  have hZ0 : Z s₀ = 0 := by
    have hD0 : fderiv ℝ F (p, s₀) (1, 0) = 0 := by
      have h1 := hasDerivAt_fst_line (hFd (p, s₀))
      have e : (fun p' => F (p', s₀)) = fun _ => y₀ := funext hF0
      rw [e] at h1
      exact h1.unique (hasDerivAt_const p y₀)
    have hF20 : F₂ s₀ = A (p, s₀) y₀ := by
      rw [hF₂def]
      change propagator (coefficientCurve A hA.continuous p) s₀ s₀ (A (p, s₀) y₀) = _
      rw [propagator_self]
      rfl
    rw [hZdef]
    change fderiv ℝ F (p, s₀) (1, 0) - c p • J (A (p, s₀) (F (p, s₀)) - F₂ s₀) = 0
    rw [hD0, hF0, hF20, sub_self, map_zero, smul_zero, sub_zero]
  have hZ1 : Z s₁ = 0 := by
    have h := eq_propagator_apply_of_hasDerivAt (coefficientCurve A hA.continuous p) (f := Z)
      (s := s₀) (t := s₁)
      (continuous_iff_continuousAt.mpr fun s => (hZ s).continuousAt).continuousOn
      (fun s _ => hZ s)
    rw [h, hZ0, map_zero]
  have hmain := hasDerivAt_fst_line (hFd (p, s₁))
  have hval : fderiv ℝ F (p, s₁) (1, 0) = c p • J (A (p, s₁) (F (p, s₁)) - F₂ s₁) := by
    have h := hZ1
    rw [hZdef] at h
    exact sub_eq_zero.mp h
  rw [hval, hFdef, hF₂def] at hmain
  exact hmain

/-- The difference of the solutions for two parameters is bounded by the
coefficient at the two ends. -/
theorem norm_propagator_apply_sub_le_of_deformation {A : ℝ × ℝ → V →L[ℝ] V}
    (hA : ContDiff ℝ ∞ A) (J : V →L[ℝ] V) (c : ℝ → ℝ)
    (hJ : ∀ (q : ℝ × ℝ) (v : V), A q (J v) = J (A q v))
    (hCR : ∀ (q : ℝ × ℝ) (v : V),
      fderiv ℝ A q (1, 0) v = c q.1 • J (fderiv ℝ A q (0, 1) v))
    {p₀ p₁ s₀ s₁ C K M₀ M₁ : ℝ} (hp : p₀ ≤ p₁) (hK0 : 0 ≤ K) (hJn : ∀ v : V, ‖J v‖ ≤ ‖v‖)
    (hc : ∀ p ∈ Icc p₀ p₁, |c p| ≤ C)
    (hK : ∀ p ∈ Icc p₀ p₁, ∀ y : V,
      ‖propagator (coefficientCurve A hA.continuous p) s₁ s₀ y‖ ≤ K * ‖y‖)
    (hM₀ : ∀ p ∈ Icc p₀ p₁, ‖A (p, s₀)‖ ≤ M₀) (hM₁ : ∀ p ∈ Icc p₀ p₁, ‖A (p, s₁)‖ ≤ M₁)
    (y₀ : V) :
    ‖propagator (coefficientCurve A hA.continuous p₁) s₁ s₀ y₀ -
        propagator (coefficientCurve A hA.continuous p₀) s₁ s₀ y₀‖ ≤
      C * (K * (M₁ + M₀) * ‖y₀‖) * (p₁ - p₀) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hc p₀ (left_mem_Icc.mpr hp))
  refine norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun p => propagator (coefficientCurve A hA.continuous p) s₁ s₀ y₀)
    (fun p _ => (hasDerivAt_propagator_apply_param hA J c hJ hCR p s₀ s₁ y₀).hasDerivWithinAt)
    (fun p hp' => ?_) p₁ (right_mem_Icc.mpr hp)
  have hpI : p ∈ Icc p₀ p₁ := ⟨hp'.1, hp'.2.le⟩
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul (hc p hpI) ?_ (norm_nonneg _) hC
  refine (hJn _).trans ((norm_sub_le _ _).trans ?_)
  have h1 : ‖A (p, s₁) (propagator (coefficientCurve A hA.continuous p) s₁ s₀ y₀)‖ ≤
      M₁ * (K * ‖y₀‖) :=
    ((A (p, s₁)).le_opNorm _).trans (mul_le_mul (hM₁ p hpI) (hK p hpI y₀) (norm_nonneg _)
      ((norm_nonneg _).trans (hM₁ p hpI)))
  have h2 : ‖propagator (coefficientCurve A hA.continuous p) s₁ s₀ (A (p, s₀) y₀)‖ ≤
      K * (M₀ * ‖y₀‖) :=
    (hK p hpI _).trans (mul_le_mul_of_nonneg_left
      (((A (p, s₀)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hM₀ p hpI) (norm_nonneg _)))
      hK0)
  nlinarith [h1, h2]

end ProjectAinos.SmoothGeometry.LinearODE
