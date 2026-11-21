/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! # Nonstationary phase on Euclidean space

Integrating by parts along the gradient divided by its squared norm gains one power of
the wavelength. Multiplication by the compactly supported amplitude localizes this vector
field, so the phase may have critical points outside the closed support.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory Filter Set
open scoped ContDiff Topology
namespace ProjectAinos.SpecialFunctions.Oscillatory

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev e {d : ℕ} (j : Fin d) := EuclideanSpace.single j (1 : ℝ)

private def p {d : ℕ} (ψ : E d → ℝ) (j : Fin d) (x : E d) := fderiv ℝ ψ x (e j)
private def q {d : ℕ} (ψ : E d → ℝ) (x : E d) := ∑ j, p ψ j x ^ 2

private theorem smooth_p {d : ℕ} {ψ : E d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : Fin d) :
    ContDiff ℝ ∞ (p ψ j) :=
  (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem q_ne {d : ℕ} {ψ : E d → ℝ} {x : E d} (h : fderiv ℝ ψ x ≠ 0) :
    q ψ x ≠ 0 := by
  intro hq
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (p ψ i x))).mp hq
  apply h
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
  intro i
  simpa [p, EuclideanSpace.basisFun_apply] using (sq_eq_zero_iff.mp (hz i (Finset.mem_univ i)))

private def phase {d : ℕ} (ψ : E d → ℝ) (ε : ℝ) (x : E d) := exp (I / ε * ψ x)

private theorem norm_phase {d : ℕ} (ψ : E d → ℝ) (ε : ℝ) (x : E d) : ‖phase ψ ε x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.div_ofReal_re]

private theorem smooth_phase {d : ℕ} {ψ : E d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (ε : ℝ) :
    ContDiff ℝ ∞ (phase ψ ε) :=
  (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hψ)).cexp

private theorem d_phase {d : ℕ} {ψ : E d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (ε : ℝ) (j : Fin d) (x : E d) :
    fderiv ℝ (phase ψ ε) x (e j) = (I / ε) * (p ψ j x : ℂ) * phase ψ ε x := by
  have hl := (Complex.ofRealCLM.hasFDerivAt.comp x ((hψ.differentiable (by simp)) x).hasFDerivAt)
  have h := (hl.const_mul (I / (ε : ℂ))).cexp
  change HasFDerivAt (phase ψ ε) _ x at h
  rw [h.fderiv]
  simp [p, phase, smul_eq_mul, mul_assoc, mul_left_comm]
  exact Or.inl (mul_comm ..)

private def part {d : ℕ} (ψ : E d → ℝ) (g : E d → ℂ) (j : Fin d) (x : E d) :=
  g x * ((p ψ j x / q ψ x : ℝ) : ℂ)

private theorem support_part {d : ℕ} (ψ : E d → ℝ) (g : E d → ℂ) (j : Fin d) :
    tsupport (part ψ g j) ⊆ tsupport g := tsupport_mul_subset_left

private theorem smooth_part {d : ℕ} {ψ : E d → ℝ} {g : E d → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hn : ∀ x ∈ tsupport g, fderiv ℝ ψ x ≠ 0) (j : Fin d) : ContDiff ℝ ∞ (part ψ g j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport g
  · have hq : ContDiff ℝ ∞ (q ψ) := ContDiff.sum fun i _ => (smooth_p hψ i).pow 2
    exact hg.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((smooth_p hψ j).contDiffAt.div hq.contDiffAt (q_ne (hn x hx))))
  · have hu : x ∉ tsupport (part ψ g j) := fun h => hx (support_part ψ g j h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hu)

private def adjoint {d : ℕ} (ψ : E d → ℝ) (g : E d → ℂ) (x : E d) :=
  -∑ j, fderiv ℝ (part ψ g j) x (e j)

private theorem regular_adjoint {d : ℕ} {ψ : E d → ℝ} {g : E d → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g) (hn : ∀ x ∈ tsupport g, fderiv ℝ ψ x ≠ 0) :
    ContDiff ℝ ∞ (adjoint ψ g) ∧ tsupport (adjoint ψ g) ⊆ tsupport g := by
  constructor
  · exact (ContDiff.sum fun j _ =>
      ((smooth_part hψ hg hn j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).neg
  · apply closure_minimal _ (isClosed_tsupport g)
    intro x hx
    by_contra h
    apply hx
    have he j : x ∉ tsupport (part ψ g j) := fun hx => h (support_part ψ g j hx)
    simp [adjoint, fun j => fderiv_of_notMem_tsupport ℝ (he j)]

private theorem integrate {d : ℕ} {ψ : E d → ℝ} {g : E d → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hn : ∀ x ∈ tsupport g, fderiv ℝ ψ x ≠ 0) (ε : ℝ) :
    (I / ε) * ∫ x, g x * phase ψ ε x = ∫ x, adjoint ψ g x * phase ψ ε x := by
  let b := part ψ g
  let h := phase ψ ε
  let D (j : Fin d) (x : E d) := fderiv ℝ (b j) x (e j)
  have hb j : ContDiff ℝ ∞ (b j) := smooth_part hψ hg hn j
  have hc' j : HasCompactSupport (b j) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (support_part ψ g j)
  have hh : ContDiff ℝ ∞ h := smooth_phase hψ ε
  have hi j : Integrable (fun x => D j x * h x) :=
    (((hb j).continuous_fderiv (by simp)).clm_apply continuous_const |>.mul hh.continuous)
      |>.integrable_of_hasCompactSupport ((hc' j).fderiv_apply (𝕜 := ℝ) (e j)).mul_right
  have hi' j : Integrable (fun x => b j x * fderiv ℝ h x (e j)) :=
    ((hb j).continuous.mul ((hh.continuous_fderiv (by simp)).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport (hc' j).mul_right
  have ib j : ∫ x, b j x * fderiv ℝ h x (e j) = -∫ x, D j x * h x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hi j) (hi' j)
      (((hb j).continuous.mul hh.continuous).integrable_of_hasCompactSupport (hc' j).mul_right)
      (fun x _ => (hb j).differentiable (by simp) x) (fun x _ => hh.differentiable (by simp) x)
  have he x : (I / ε) * (g x * h x) = ∑ j, b j x * fderiv ℝ h x (e j) := by
    have he j : b j x * fderiv ℝ h x (e j) =
        (I / ε * (g x * h x) / (q ψ x : ℂ)) * (p ψ j x : ℂ) ^ 2 := by
      simp only [b, h, part, d_phase hψ, Complex.ofReal_div]
      ring
    simp_rw [he, ← Finset.mul_sum, ← Complex.ofReal_pow, ← Complex.ofReal_sum]
    by_cases hx : x ∈ tsupport g
    · exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (q_ne (hn x hx)))).symm
    · simp [image_eq_zero_of_notMem_tsupport hx]
  calc
    _ = ∫ x, (I / ε) * (g x * h x) := (integral_const_mul ..).symm
    _ = ∫ x, ∑ j, b j x * fderiv ℝ h x (e j) :=
      integral_congr_ae (ae_of_all _ he)
    _ = -∫ x, ∑ j, D j x * h x := by
      rw [integral_finsetSum _ fun j _ => hi' j, integral_finsetSum _ fun j _ => hi j]
      simp only [ib, Finset.sum_neg_distrib]
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by simp only [adjoint, D, b, h, neg_mul, Finset.sum_mul]

/-- Nonstationary phase in every finite dimension, to arbitrary order. The bound is uniform in
the nonzero real wavelength, and only the closed support of the smooth amplitude matters. -/
theorem nonstationary {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (N : ℕ) {g : EuclideanSpace ℝ (Fin d) → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hn : ∀ x ∈ tsupport g, fderiv ℝ ψ x ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ≠ 0 →
      ‖∫ x, g x * exp (I / ε * ψ x)‖ ≤ C * |ε| ^ N := by
  induction N generalizing g with
  | zero =>
    refine ⟨∫ x, ‖g x‖, integral_nonneg (fun _ => norm_nonneg _), fun ε _ => ?_⟩
    change ‖∫ x, g x * phase ψ ε x‖ ≤ (∫ x, ‖g x‖) * |ε| ^ 0
    simpa only [norm_mul, norm_phase, mul_one, pow_zero] using
      (norm_integral_le_integral_norm (fun x => g x * phase ψ ε x))
  | succ N ih =>
    obtain ⟨hs, hsub⟩ := regular_adjoint hψ hg hn
    obtain ⟨C,hC,h⟩ := ih hs (hc.of_isClosed_subset (isClosed_tsupport _) hsub)
      (fun x hx => hn x (hsub hx))
    refine ⟨C,hC,fun ε hε => ?_⟩
    have he := congrArg norm (integrate hψ hg hc hn ε)
    simp only [norm_mul, norm_div, norm_I, norm_real, Real.norm_eq_abs] at he
    have h' := h ε hε
    change ‖∫ x, adjoint ψ g x * phase ψ ε x‖ ≤ _ at h'
    rw [← he] at h'
    change ‖∫ x, g x * phase ψ ε x‖ ≤ _
    rw [pow_succ]
    calc
      _ = (1 / |ε| * ‖∫ x, g x * phase ψ ε x‖) * |ε| := by field_simp
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h' (abs_nonneg ε)

end ProjectAinos.SpecialFunctions.Oscillatory
