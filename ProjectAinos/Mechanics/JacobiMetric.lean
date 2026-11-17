/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Maupertuis
public import ProjectAinos.Variational.Parameter
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Jacobi metric

For a kinetic energy `T` that is homogeneous of degree two in the velocity, the
Jacobi length `2 √((E − U) T)` is homogeneous of degree one, and
`jacobiEnergy = 2 (E − U) T` is half of the square of the velocity in the
Jacobi metric `2 (E − U) g`, `T = g(q̇, q̇)/2`. A geodesic of the Jacobi metric
with an affine parameter is a curve that satisfies the Euler–Lagrange equation
of `jacobiEnergy`.

* `eulerLagrange_comp`: the Euler–Lagrange expression of a Lagrangian that is
  homogeneous of degree one in the velocity is multiplied by `σ′` under a change
  `σ` of the parameter.
* `eulerLagrange_jacobiEnergy_eq`: along a curve of constant Jacobi length `ℓ₀`
  the Euler–Lagrange expression of `jacobiEnergy` is `ℓ₀` times that of
  `jacobiLength`.
* `eulerLagrange_eq_smul_jacobiEnergy`: if `q = γ ∘ σ` has the energy `E` and
  `σ′ = 2 (E − U)`, then `γ` has the unit velocity in the Jacobi metric and
  the equations of motion of `q` are `σ′` times the equation of geodesics of
  `γ` (Landau–Lifshitz §44).
* `exists_jacobi_parameter`: for a curve of the energy `E` the parameter `σ` and
  the curve `γ` exist. `exists_motion_of_jacobi_geodesic`: for a curve `γ` of
  unit velocity in the Jacobi metric the time `τ` with `dτ = dσ/2 (E − U)`,
  which is (44.12), and the curve `q` of the energy `E` exist.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open ContinuousLinearMap (inl inr fst snd)
open scoped Topology ContDiff

namespace ProjectAinos.Mechanics.Maupertuis

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {T : Q × Q → ℝ} {U : Q → ℝ} {E : ℝ}

/-! ### A change of the parameter -/

/-- A function of the position and the velocity that is positively homogeneous
of degree one in the velocity. -/
def IsHomogeneousOne (Λ : Q × Q → ℝ) : Prop :=
  ∀ (q w : Q) (c : ℝ), 0 < c → Λ (q, c • w) = c * Λ (q, w)

/-- The derivative in the position is homogeneous of degree one and the
derivative in the velocity is homogeneous of degree zero. -/
theorem IsHomogeneousOne.fderiv_smul {Λ : Q × Q → ℝ} (hΛ : IsHomogeneousOne Λ) {q w : Q}
    {c : ℝ} (hc : 0 < c) (hd : DifferentiableAt ℝ Λ (q, c • w)) :
    (fderiv ℝ Λ (q, c • w)).comp (inl ℝ Q Q) = c • (fderiv ℝ Λ (q, w)).comp (inl ℝ Q Q) ∧
      (fderiv ℝ Λ (q, c • w)).comp (inr ℝ Q Q) = (fderiv ℝ Λ (q, w)).comp (inr ℝ Q Q) := by
  obtain ⟨S, hSdef⟩ : ∃ S : Q × Q →L[ℝ] Q × Q, S = (fst ℝ Q Q).prod (c • snd ℝ Q Q) :=
    ⟨_, rfl⟩
  have hSapp : ∀ z : Q × Q, S z = (z.1, c • z.2) := fun z => by
    rw [hSdef]
    rfl
  have hS : HasFDerivAt (fun z : Q × Q => ((z.1, c • z.2) : Q × Q)) S (q, w) := by
    have e : (fun z : Q × Q => ((z.1, c • z.2) : Q × Q)) = S := funext fun z => (hSapp z).symm
    rw [e]
    exact S.hasFDerivAt
  have hcomp : HasFDerivAt (fun z : Q × Q => Λ (z.1, c • z.2))
      ((fderiv ℝ Λ (q, c • w)).comp S) (q, w) :=
    HasFDerivAt.comp (q, w) (g := Λ) (f := fun z : Q × Q => ((z.1, c • z.2) : Q × Q))
      hd.hasFDerivAt hS
  have heq : (fun z : Q × Q => Λ (z.1, c • z.2)) = fun z => c * Λ z :=
    funext fun z => hΛ z.1 z.2 c hc
  rw [heq] at hcomp
  have hΛd : HasFDerivAt Λ (c⁻¹ • (fderiv ℝ Λ (q, c • w)).comp S) (q, w) := by
    have h : HasFDerivAt (fun z : Q × Q => c⁻¹ * (c * Λ z))
        (c⁻¹ • (fderiv ℝ Λ (q, c • w)).comp S) (q, w) := hcomp.const_mul c⁻¹
    have e : (fun z : Q × Q => c⁻¹ * (c * Λ z)) = Λ := funext fun z => by
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    rw [e] at h
    exact h
  have hfd := hΛd.fderiv
  constructor
  · refine ContinuousLinearMap.ext fun v => ?_
    change fderiv ℝ Λ (q, c • w) (v, 0) = c • fderiv ℝ Λ (q, w) (v, 0)
    rw [hfd]
    change _ = c • (c⁻¹ • fderiv ℝ Λ (q, c • w) (S (v, 0)))
    rw [hSapp, smul_zero, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  · refine ContinuousLinearMap.ext fun v => ?_
    change fderiv ℝ Λ (q, c • w) (0, v) = fderiv ℝ Λ (q, w) (0, v)
    rw [hfd]
    change _ = c⁻¹ • fderiv ℝ Λ (q, c • w) (S (0, v))
    have e : S (0, v) = c • ((0 : Q), v) := by
      rw [hSapp, Prod.smul_mk, smul_zero]
    rw [e, map_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

theorem eulerLagrange_congr {L : Lagrangian Q} {q₁ q₂ : ℝ → Q} {t : ℝ}
    (h : q₁ =ᶠ[𝓝 t] q₂) : eulerLagrange L q₁ t = eulerLagrange L q₂ t := by
  have hd : deriv q₁ =ᶠ[𝓝 t] deriv q₂ := h.deriv
  have hm : momentum L q₁ =ᶠ[𝓝 t] momentum L q₂ := by
    filter_upwards [h, hd] with s h1 h2
    simp only [momentum, h1, h2]
  simp only [eulerLagrange, force, h.self_of_nhds, hd.self_of_nhds, hm.deriv_eq]

/-- The Euler–Lagrange expression of a Lagrangian that is homogeneous of degree
one in the velocity, under a change of the parameter. -/
theorem eulerLagrange_comp {Λ : Q × Q → ℝ} (hΛ : IsHomogeneousOne Λ) {γ : ℝ → Q}
    {σ : ℝ → ℝ} {t : ℝ} (hpos : ∀ᶠ s in 𝓝 t, 0 < deriv σ s)
    (hγ : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ γ (σ s))
    (hd : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ Λ (γ (σ s), deriv σ s • deriv γ (σ s)))
    (hm : DifferentiableAt ℝ (momentum (fun _ => Λ) γ) (σ t)) :
    eulerLagrange (fun _ => Λ) (γ ∘ σ) t =
      deriv σ t • eulerLagrange (fun _ => Λ) γ (σ t) := by
  have hσd : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ σ s := hpos.mono fun s hs =>
    differentiableAt_of_deriv_ne_zero hs.ne'
  have hderiv : ∀ᶠ s in 𝓝 t, deriv (γ ∘ σ) s = deriv σ s • deriv γ (σ s) := by
    filter_upwards [hσd, hγ] with s h1 h2
    exact (HasDerivAt.scomp s h2.hasDerivAt h1.hasDerivAt).deriv
  have hfd : ∀ᶠ s in 𝓝 t,
      (fderiv ℝ Λ ((γ ∘ σ) s, deriv (γ ∘ σ) s)).comp (inl ℝ Q Q) =
          deriv σ s • (fderiv ℝ Λ (γ (σ s), deriv γ (σ s))).comp (inl ℝ Q Q) ∧
        (fderiv ℝ Λ ((γ ∘ σ) s, deriv (γ ∘ σ) s)).comp (inr ℝ Q Q) =
          (fderiv ℝ Λ (γ (σ s), deriv γ (σ s))).comp (inr ℝ Q Q) := by
    filter_upwards [hpos, hderiv, hd] with s h1 h2 h3
    rw [h2]
    exact hΛ.fderiv_smul h1 h3
  have hmom : momentum (fun _ => Λ) (γ ∘ σ) =ᶠ[𝓝 t] momentum (fun _ => Λ) γ ∘ σ := by
    filter_upwards [hfd] with s hs
    exact hs.2
  have h1 : deriv (momentum (fun _ => Λ) (γ ∘ σ)) t =
      deriv σ t • deriv (momentum (fun _ => Λ) γ) (σ t) := by
    rw [hmom.deriv_eq]
    exact (HasDerivAt.scomp t hm.hasDerivAt hσd.self_of_nhds.hasDerivAt).deriv
  have h2 : force (fun _ => Λ) (γ ∘ σ) t = deriv σ t • force (fun _ => Λ) γ (σ t) :=
    hfd.self_of_nhds.1
  rw [eulerLagrange, eulerLagrange, h1, h2, smul_sub]

/-! ### The length and the energy of the Jacobi metric -/

theorem isHomogeneousOne_jacobiLength (hT : IsHomogeneousTwo T) (t : ℝ) :
    IsHomogeneousOne (jacobiLength T U E t) := by
  intro q w c hc
  have e : radicand T U E (q, c • w) = c ^ 2 * radicand T U E (q, w) := by
    simp only [radicand, hT q w c]
    ring
  change 2 * √(radicand T U E (q, c • w)) = c * (2 * √(radicand T U E (q, w)))
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  ring

section Derivative

variable {z : Q × Q} {T' : Q × Q →L[ℝ] ℝ} {U' : Q →L[ℝ] ℝ}

theorem hasFDerivAt_jacobiEnergy (hT : HasFDerivAt T T' z) (hU : HasFDerivAt U U' z.1)
    (t : ℝ) :
    HasFDerivAt (jacobiEnergy T U E t)
      ((2 : ℝ) • ((E - U z.1) • T' - T z • U'.comp (fst ℝ Q Q))) z :=
  (hasFDerivAt_radicand hT hU).const_mul 2

/-- The derivative of the energy of the Jacobi metric is the length times the
derivative of the length. -/
theorem fderiv_jacobiEnergy_eq (hT : DifferentiableAt ℝ T z) (hU : DifferentiableAt ℝ U z.1)
    (hpos : 0 < radicand T U E z) (t : ℝ) :
    fderiv ℝ (jacobiEnergy T U E t) z =
      jacobiLength T U E t z • fderiv ℝ (jacobiLength T U E t) z := by
  have hs : 0 < √(radicand T U E z) := Real.sqrt_pos.mpr hpos
  rw [(hasFDerivAt_jacobiEnergy hT.hasFDerivAt hU.hasFDerivAt t).fderiv,
    (hasFDerivAt_jacobiLength hT.hasFDerivAt hU.hasFDerivAt hpos t).fderiv, jacobiLength,
    smul_smul]
  congr 1
  field_simp

end Derivative

/-- Along a curve of constant Jacobi length `ℓ₀` the Euler–Lagrange expression
of the energy of the Jacobi metric is `ℓ₀` times that of the length. -/
theorem eulerLagrange_jacobiEnergy_eq (hT : Differentiable ℝ T) (hU : Differentiable ℝ U)
    {γ : ℝ → Q} {x ℓ₀ : ℝ}
    (hℓ : ∀ᶠ y in 𝓝 x, 0 < radicand T U E (γ y, deriv γ y) ∧
      jacobiLength T U E y (γ y, deriv γ y) = ℓ₀)
    (hm : DifferentiableAt ℝ (momentum (jacobiLength T U E) γ) x) :
    eulerLagrange (jacobiEnergy T U E) γ x =
      ℓ₀ • eulerLagrange (jacobiLength T U E) γ x := by
  have hfd : ∀ᶠ y in 𝓝 x, fderiv ℝ (jacobiEnergy T U E y) (γ y, deriv γ y) =
      ℓ₀ • fderiv ℝ (jacobiLength T U E y) (γ y, deriv γ y) := by
    filter_upwards [hℓ] with y hy
    rw [fderiv_jacobiEnergy_eq (hT _) (hU _) hy.1 y, hy.2]
  have hmom : momentum (jacobiEnergy T U E) γ =ᶠ[𝓝 x]
      fun y => ℓ₀ • momentum (jacobiLength T U E) γ y := by
    filter_upwards [hfd] with y hy
    simp only [momentum, hy]
    rfl
  have h1 : deriv (momentum (jacobiEnergy T U E) γ) x =
      ℓ₀ • deriv (momentum (jacobiLength T U E) γ) x := by
    rw [hmom.deriv_eq]
    exact (hm.hasDerivAt.const_smul ℓ₀).deriv
  have h2 : force (jacobiEnergy T U E) γ x = ℓ₀ • force (jacobiLength T U E) γ x := by
    simp only [force, hfd.self_of_nhds]
    rfl
  rw [eulerLagrange, eulerLagrange, h1, h2, smul_sub]

/-! ### Motions and geodesics -/

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem radicand_pos_of_jacobiLength_eq_one {z : Q × Q} {t : ℝ}
    (h : jacobiLength T U E t z = 1) : 0 < radicand T U E z := by
  by_contra hneg
  have h0 : √(radicand T U E z) = 0 := Real.sqrt_eq_zero_of_nonpos (not_lt.mp hneg)
  rw [jacobiLength, h0] at h
  norm_num at h

section Geodesic

variable {q γ : ℝ → Q} {σ : ℝ → ℝ} {t : ℝ}

/-- In the parameter `σ` with `dσ/dt = 2 (E − U)` a curve of the energy `E` has
the unit velocity in the Jacobi metric. -/
theorem eventually_jacobiLength_eq_one (hT2 : IsHomogeneousTwo T) (hU : Continuous U)
    (hqc : ContinuousAt q t)
    (hE : ∀ᶠ s in 𝓝 t, T (q s, deriv q s) + U (q s) = E ∧ U (q s) < E)
    (hσ : ∀ᶠ s in 𝓝 t, HasDerivAt σ (2 * (E - U (q s))) s)
    (hqγ : ∀ᶠ s in 𝓝 t, q s = γ (σ s))
    (hγ : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ γ (σ s)) :
    ∀ᶠ x in 𝓝 (σ t), jacobiLength T U E x (γ x, deriv γ x) = 1 := by
  have hσ' : ∀ᶠ s in 𝓝 t, deriv σ s = 2 * (E - U (q s)) := hσ.mono fun s hs => hs.deriv
  have hpos : ∀ᶠ s in 𝓝 t, 0 < deriv σ s := by
    filter_upwards [hσ', hE] with s h1 h2
    rw [h1]
    linarith [h2.2]
  have hqeq : q =ᶠ[𝓝 t] γ ∘ σ := hqγ
  have hqd : ∀ᶠ s in 𝓝 t, deriv q s = deriv σ s • deriv γ (σ s) := by
    filter_upwards [hqeq.deriv, hγ, hpos] with s h1 h2 h3
    rw [h1]
    exact (HasDerivAt.scomp s h2.hasDerivAt
      (differentiableAt_of_deriv_ne_zero h3.ne').hasDerivAt).deriv
  have hunit : ∀ᶠ s in 𝓝 t, jacobiLength T U E (σ s) (γ (σ s), deriv γ (σ s)) = 1 := by
    filter_upwards [hE, hσ', hqd, hqγ, hpos] with s h1 h2 h3 h4 h5
    have h6 : jacobiLength T U E s (q s, deriv q s) = deriv σ s := by
      rw [jacobiLength_eq_two_mul (z := (q s, deriv q s)) h1.1 h1.2 s, h2]
      linarith [h1.1]
    rw [h4, h3, isHomogeneousOne_jacobiLength hT2 s _ _ _ h5] at h6
    exact mul_left_cancel₀ h5.ne' (h6.trans (mul_one _).symm)
  have hcont : ContinuousAt (fun s => 2 * (E - U (q s))) t :=
    continuousAt_const.mul (continuousAt_const.sub
      (ContinuousAt.comp (g := U) hU.continuousAt hqc))
  have hstrict : HasStrictDerivAt σ (2 * (E - U (q t))) t :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt hσ hcont
  have hne : 2 * (E - U (q t)) ≠ 0 := by
    have h := hE.self_of_nhds.2
    exact ne_of_gt (by linarith)
  rw [← hstrict.map_nhds_eq hne, eventually_map]
  exact hunit

/-- A motion of the energy `E` is a geodesic of the Jacobi metric in the
parameter `σ` with `dσ/dt = 2 (E − U)`: if `q = γ ∘ σ` near `t`, the
Euler–Lagrange expression of `T − U` along `q` is `σ′` times that of the energy
of the Jacobi metric along `γ`. -/
theorem eulerLagrange_eq_smul_jacobiEnergy (hT2 : IsHomogeneousTwo T) (hT : Differentiable ℝ T)
    (hU : Differentiable ℝ U) (hqc : ContinuousAt q t)
    (hE : ∀ᶠ s in 𝓝 t, T (q s, deriv q s) + U (q s) = E ∧ U (q s) < E)
    (hσ : ∀ᶠ s in 𝓝 t, HasDerivAt σ (2 * (E - U (q s))) s)
    (hqγ : ∀ᶠ s in 𝓝 t, q s = γ (σ s))
    (hγ : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ γ (σ s))
    (hm : DifferentiableAt ℝ (momentum (jacobiLength T U E) γ) (σ t)) :
    eulerLagrange (naturalLagrangian T U) q t =
      (2 * (E - U (q t))) • eulerLagrange (jacobiEnergy T U E) γ (σ t) := by
  have hunit' := eventually_jacobiLength_eq_one hT2 hU.continuous hqc hE hσ hqγ hγ
  have hσ' : ∀ᶠ s in 𝓝 t, deriv σ s = 2 * (E - U (q s)) := hσ.mono fun s hs => hs.deriv
  have hpos : ∀ᶠ s in 𝓝 t, 0 < deriv σ s := by
    filter_upwards [hσ', hE] with s h1 h2
    rw [h1]
    linarith [h2.2]
  have hqeq : q =ᶠ[𝓝 t] γ ∘ σ := hqγ
  have hqd : ∀ᶠ s in 𝓝 t, deriv q s = deriv σ s • deriv γ (σ s) := by
    filter_upwards [hqeq.deriv, hγ, hpos] with s h1 h2 h3
    rw [h1]
    exact (HasDerivAt.scomp s h2.hasDerivAt
      (differentiableAt_of_deriv_ne_zero h3.ne').hasDerivAt).deriv
  have step1 := eulerLagrange_jacobiLength_eq (q := q) hT hU hE
  have step2 : eulerLagrange (jacobiLength T U E) q t =
      eulerLagrange (jacobiLength T U E) (γ ∘ σ) t := eulerLagrange_congr hqeq
  have step3 : eulerLagrange (jacobiLength T U E) (γ ∘ σ) t =
      deriv σ t • eulerLagrange (jacobiLength T U E) γ (σ t) := by
    have hd : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (jacobiLength T U E 0)
        (γ (σ s), deriv σ s • deriv γ (σ s)) := by
      filter_upwards [hE, hqd, hqγ] with s h1 h2 h3
      rw [← h2, ← h3]
      exact (hasFDerivAt_jacobiLength_shell (hT _).hasFDerivAt (hU _).hasFDerivAt h1.1 h1.2
        0).differentiableAt
    exact eulerLagrange_comp (isHomogeneousOne_jacobiLength hT2 0) hpos hγ hd hm
  have step4 : eulerLagrange (jacobiEnergy T U E) γ (σ t) =
      (1 : ℝ) • eulerLagrange (jacobiLength T U E) γ (σ t) := by
    refine eulerLagrange_jacobiEnergy_eq hT hU ?_ hm
    filter_upwards [hunit'] with x hx
    exact ⟨radicand_pos_of_jacobiLength_eq_one hx, hx⟩
  rw [← step1, step2, step3, step4, one_smul, hσ'.self_of_nhds]

end Geodesic

/-! ### The existence of the parameters -/

/-- The momentum of the Jacobi length along a curve is differentiable at a
point where the curve is twice continuously differentiable and the radicand is
positive. -/
theorem differentiableAt_momentum_jacobiLength (hT : ContDiff ℝ 2 T) (hU : ContDiff ℝ 2 U)
    {γ : ℝ → Q} {x : ℝ} (hγ : ContDiffAt ℝ 2 γ x)
    (hpos : 0 < radicand T U E (γ x, deriv γ x)) :
    DifferentiableAt ℝ (momentum (jacobiLength T U E) γ) x := by
  have hΛ : ContDiffAt ℝ 2 (jacobiLength T U E 0) (γ x, deriv γ x) :=
    contDiffAt_const.mul ((contDiff_radicand hT hU).contDiffAt.sqrt hpos.ne')
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ (jacobiLength T U E 0)) (γ x, deriv γ x) := by
    have h2 : ContDiffAt ℝ (1 + 1) (jacobiLength T U E 0) (γ x, deriv γ x) := by
      rw [one_add_one_eq_two]
      exact hΛ
    exact h2.fderiv_right (m := 1) le_rfl
  have hγ' : ContDiffAt ℝ 1 (deriv γ) x := by
    have h2 : ContDiffAt ℝ (1 + 1) γ x := by
      rw [one_add_one_eq_two]
      exact hγ
    exact (h2.fderiv_right (m := 1) le_rfl).clm_apply (contDiffAt_const (c := (1 : ℝ)))
  have hJ : ContDiffAt ℝ 1 (fun y => (γ y, deriv γ y)) x :=
    (hγ.of_le (by norm_num)).prodMk hγ'
  have hcomp : ContDiffAt ℝ 1 (fun y => fderiv ℝ (jacobiLength T U E 0) (γ y, deriv γ y)) x :=
    ContDiffAt.comp x (g := fderiv ℝ (jacobiLength T U E 0)) (f := fun y => (γ y, deriv γ y))
      hfd hJ
  have hmom : ContDiffAt ℝ 1 (momentum (jacobiLength T U E) γ) x :=
    hcomp.clm_comp contDiffAt_const
  exact hmom.differentiableAt one_ne_zero

/-- For a curve of the energy `E` in the region `U < E` there are a parameter
`σ` with `dσ/dt = 2 (E − U)` and a curve `γ` with `q = γ ∘ σ`. The curve `γ` has
the unit velocity in the Jacobi metric, and `q` satisfies the equations of
motion at a time if and only if `γ` satisfies the equation of geodesics of the
Jacobi metric at the corresponding parameter. -/
theorem exists_jacobi_parameter (hT2 : IsHomogeneousTwo T) (hT : ContDiff ℝ 2 T)
    (hU : ContDiff ℝ 2 U) {q : ℝ → Q} (hq : ContDiff ℝ 2 q) {a b : ℝ}
    (hE : ∀ t ∈ Ioo a b, T (q t, deriv q t) + U (q t) = E ∧ U (q t) < E) :
    ∃ (σ : ℝ → ℝ) (γ : ℝ → Q), (∀ t ∈ Ioo a b, HasDerivAt σ (2 * (E - U (q t))) t) ∧
      (∀ t ∈ Ioo a b, γ (σ t) = q t) ∧
      (∀ t ∈ Ioo a b, ∀ᶠ x in 𝓝 (σ t), jacobiLength T U E x (γ x, deriv γ x) = 1) ∧
      ∀ t ∈ Ioo a b, eulerLagrange (naturalLagrangian T U) q t =
        (2 * (E - U (q t))) • eulerLagrange (jacobiEnergy T U E) γ (σ t) := by
  have hf : ContDiff ℝ 1 fun s => 2 * (E - U (q s)) :=
    contDiff_const.mul (contDiff_const.sub ((hU.comp hq).of_le (by norm_num)))
  obtain ⟨hσC, hσd⟩ := Variational.contDiff_primitive hf 0
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ → ℝ, σ = fun x => ∫ y in (0 : ℝ)..x, 2 * (E - U (q y)) :=
    ⟨_, rfl⟩
  rw [← hσdef] at hσC hσd
  have hfpos : ∀ t ∈ Ioo a b, 0 < 2 * (E - U (q t)) := fun t ht => by
    linarith [(hE t ht).2]
  obtain ⟨e, he, hsrc, _, hsymm⟩ := Variational.exists_positive_parameter_chart σ
    hσC.contDiffOn (fun t ht => by rw [(hσd t).deriv]; exact hfpos t ht)
  have hes : ∀ s, e s = σ s := fun s => congrFun he s
  have hleft : ∀ s ∈ Ioo a b, e.symm (σ s) = s := fun s hs => by
    rw [← hes s]
    exact e.left_inv (by rw [hsrc]; exact hs)
  have hγ2 : ∀ s ∈ Ioo a b, ContDiffAt ℝ 2 (q ∘ e.symm) (σ s) := fun s hs => by
    have h1 := (hsymm (e s) (e.map_source (by rw [hsrc]; exact hs))).1
    rw [hes s] at h1
    exact ContDiffAt.comp (σ s) (g := q) (f := e.symm) hq.contDiffAt h1
  have hunit : ∀ t ∈ Ioo a b, ∀ᶠ x in 𝓝 (σ t),
      jacobiLength T U E x ((q ∘ e.symm) x, deriv (q ∘ e.symm) x) = 1 := fun t ht => by
    have hnhds : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    refine eventually_jacobiLength_eq_one hT2 hU.continuous hq.continuous.continuousAt ?_
      (Eventually.of_forall hσd) ?_ ?_
    · filter_upwards [hnhds] with s hs using hE s hs
    · filter_upwards [hnhds] with s hs
      change q s = q (e.symm (σ s))
      rw [hleft s hs]
    · filter_upwards [hnhds] with s hs using (hγ2 s hs).differentiableAt (by norm_num)
  refine ⟨σ, q ∘ e.symm, fun t _ => hσd t, fun t ht => ?_, hunit, fun t ht => ?_⟩
  · change q (e.symm (σ t)) = q t
    rw [hleft t ht]
  · have hnhds : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    refine eulerLagrange_eq_smul_jacobiEnergy hT2 (hT.differentiable (by norm_num))
      (hU.differentiable (by norm_num)) hq.continuous.continuousAt ?_
      (Eventually.of_forall hσd) ?_ ?_ ?_
    · filter_upwards [hnhds] with s hs using hE s hs
    · filter_upwards [hnhds] with s hs
      change q s = q (e.symm (σ s))
      rw [hleft s hs]
    · filter_upwards [hnhds] with s hs using (hγ2 s hs).differentiableAt (by norm_num)
    · exact differentiableAt_momentum_jacobiLength hT hU (hγ2 t ht)
        (radicand_pos_of_jacobiLength_eq_one (hunit t ht).self_of_nhds)

/-- The time along a geodesic of the Jacobi metric (Landau–Lifshitz (44.12)).
For a curve `γ` of unit velocity in the Jacobi metric in the region `U < E`
there are a time `τ` with `dτ/dx = 1/(2 (E − U))` and a curve `q` with
`q ∘ τ = γ`. The curve `q` has the energy `E`, and it satisfies the equations of
motion at a time if and only if `γ` satisfies the equation of geodesics at the
corresponding parameter. -/
theorem exists_motion_of_jacobi_geodesic (hT2 : IsHomogeneousTwo T) (hT : ContDiff ℝ 2 T)
    (hU : ContDiff ℝ 2 U) {γ : ℝ → Q} (hγ : ContDiff ℝ 2 γ) {c d : ℝ}
    (hunit : ∀ x ∈ Ioo c d, jacobiLength T U E x (γ x, deriv γ x) = 1 ∧ U (γ x) < E) :
    ∃ (τ : ℝ → ℝ) (q : ℝ → Q),
      (∀ x ∈ Ioo c d, HasDerivAt τ (1 / (2 * (E - U (γ x)))) x) ∧
      (∀ x ∈ Ioo c d, q (τ x) = γ x) ∧
      (∀ x ∈ Ioo c d, ∀ᶠ s in 𝓝 (τ x), T (q s, deriv q s) + U (q s) = E ∧ U (q s) < E) ∧
      ∀ x ∈ Ioo c d, eulerLagrange (naturalLagrangian T U) q (τ x) =
        (2 * (E - U (γ x))) • eulerLagrange (jacobiEnergy T U E) γ x := by
  have hJ : ContDiff ℝ 1 fun y => (γ y, deriv γ y) := contDiff_positionVelocity hγ
  have hf : ContDiff ℝ 1 fun y => 2 * T (γ y, deriv γ y) :=
    contDiff_const.mul ((hT.of_le (by norm_num)).comp hJ)
  obtain ⟨hτC, hτd⟩ := Variational.contDiff_primitive hf 0
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ → ℝ, τ = fun x => ∫ y in (0 : ℝ)..x, 2 * T (γ y, deriv γ y) :=
    ⟨_, rfl⟩
  rw [← hτdef] at hτC hτd
  -- On the interval `(E − U) T = 1/4`.
  have hquarter : ∀ x ∈ Ioo c d, (E - U (γ x)) * T (γ x, deriv γ x) = 1 / 4 := fun x hx => by
    have h1 := (hunit x hx).1
    have hpos := radicand_pos_of_jacobiLength_eq_one h1
    have h2 : √(radicand T U E (γ x, deriv γ x)) = 1 / 2 := by
      rw [jacobiLength] at h1
      linarith
    have h3 := Real.sq_sqrt hpos.le
    rw [h2] at h3
    change radicand T U E (γ x, deriv γ x) = 1 / 4
    rw [← h3]
    norm_num
  have hrate : ∀ x ∈ Ioo c d, 2 * T (γ x, deriv γ x) = 1 / (2 * (E - U (γ x))) := fun x hx => by
    have hpos : 0 < E - U (γ x) := sub_pos.mpr (hunit x hx).2
    have h := hquarter x hx
    field_simp
    linarith
  have hratepos : ∀ x ∈ Ioo c d, 0 < 2 * T (γ x, deriv γ x) := fun x hx => by
    have hpos : 0 < E - U (γ x) := sub_pos.mpr (hunit x hx).2
    rw [hrate x hx]
    positivity
  obtain ⟨e, he, hsrc, _, hsymm⟩ := Variational.exists_positive_parameter_chart τ
    hτC.contDiffOn (fun x hx => by rw [(hτd x).deriv]; exact hratepos x hx)
  have hes : ∀ x, e x = τ x := fun x => congrFun he x
  have hleft : ∀ x ∈ Ioo c d, e.symm (τ x) = x := fun x hx => by
    rw [← hes x]
    exact e.left_inv (by rw [hsrc]; exact hx)
  -- Facts at the points of the target of the chart.
  have htarget : ∀ s ∈ e.target, e.symm s ∈ Ioo c d := fun s hs => by
    rw [← hsrc]
    exact e.map_target hs
  have hσd : ∀ s ∈ e.target, HasDerivAt e.symm (2 * (E - U (γ (e.symm s)))) s := fun s hs => by
    have h1 := (hsymm s hs).2
    have hx := htarget s hs
    have hpos : 0 < E - U (γ (e.symm s)) := sub_pos.mpr (hunit _ hx).2
    rw [(hτd _).deriv, hrate _ hx] at h1
    refine h1.congr_deriv ?_
    field_simp
  have henergy : ∀ s ∈ e.target, T ((γ ∘ e.symm) s, deriv (γ ∘ e.symm) s) +
      U ((γ ∘ e.symm) s) = E ∧ U ((γ ∘ e.symm) s) < E := fun s hs => by
    have hx := htarget s hs
    have hpos : 0 < E - U (γ (e.symm s)) := sub_pos.mpr (hunit _ hx).2
    have hd : deriv (γ ∘ e.symm) s = (2 * (E - U (γ (e.symm s)))) • deriv γ (e.symm s) :=
      (HasDerivAt.scomp s (hγ.differentiable (by norm_num) _).hasDerivAt (hσd s hs)).deriv
    refine ⟨?_, (hunit _ hx).2⟩
    change T (γ (e.symm s), deriv (γ ∘ e.symm) s) + U (γ (e.symm s)) = E
    rw [hd, hT2]
    have h := hquarter _ hx
    have e1 : (2 * (E - U (γ (e.symm s)))) ^ 2 * T (γ (e.symm s), deriv γ (e.symm s)) =
        4 * (E - U (γ (e.symm s))) * ((E - U (γ (e.symm s))) *
          T (γ (e.symm s), deriv γ (e.symm s))) := by ring
    rw [e1, h]
    ring
  have hmem : ∀ x ∈ Ioo c d, τ x ∈ e.target := fun x hx => by
    rw [← hes x]
    exact e.map_source (by rw [hsrc]; exact hx)
  refine ⟨τ, γ ∘ e.symm, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h := hτd x
    rw [hrate x hx] at h
    exact h
  · change γ (e.symm (τ x)) = γ x
    rw [hleft x hx]
  · filter_upwards [e.open_target.mem_nhds (hmem x hx)] with s hs using henergy s hs
  · have hnhds : e.target ∈ 𝓝 (τ x) := e.open_target.mem_nhds (hmem x hx)
    have hcont : ContinuousAt (γ ∘ e.symm) (τ x) :=
      ContinuousAt.comp (g := γ) hγ.continuous.continuousAt
        (hsymm _ (hmem x hx)).1.continuousAt
    have key := eulerLagrange_eq_smul_jacobiEnergy (q := γ ∘ e.symm) (γ := γ) (σ := e.symm)
      (t := τ x) hT2 (hT.differentiable (by norm_num)) (hU.differentiable (by norm_num)) hcont
      (by filter_upwards [hnhds] with s hs using henergy s hs)
      (by filter_upwards [hnhds] with s hs using hσd s hs)
      (Eventually.of_forall fun s => rfl)
      (Eventually.of_forall fun s => hγ.differentiable (by norm_num) _)
      (by
        rw [hleft x hx]
        exact differentiableAt_momentum_jacobiLength hT hU hγ.contDiffAt
          (radicand_pos_of_jacobiLength_eq_one (hunit x hx).1))
    rw [hleft x hx] at key
    change eulerLagrange (naturalLagrangian T U) (γ ∘ e.symm) (τ x) =
      (2 * (E - U (γ (e.symm (τ x))))) • eulerLagrange (jacobiEnergy T U E) γ x at key
    rw [hleft x hx] at key
    exact key

/-! ### A particle in a Euclidean space -/

section Particle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The kinetic energy `m |q̇|²/2` of a particle. -/
def kineticEnergy (m : ℝ) (z : V × V) : ℝ := m / 2 * ‖z.2‖ ^ 2

theorem contDiff_kineticEnergy (m : ℝ) : ContDiff ℝ 2 (kineticEnergy (V := V) m) :=
  contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd)

theorem isHomogeneousTwo_kineticEnergy (m : ℝ) :
    IsHomogeneousTwo (kineticEnergy (V := V) m) := by
  intro q w c
  simp only [kineticEnergy, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem deriv_line (x₀ v : V) (s : ℝ) : deriv (fun s : ℝ => x₀ + s • v) s = v := by
  have h : HasDerivAt (fun s : ℝ => x₀ + s • v) ((1 : ℝ) • v) s :=
    ((hasDerivAt_id s).smul_const v).const_add x₀
  rw [h.deriv, one_smul]

/-- A uniform motion satisfies the equations of motion of a free particle. -/
theorem eulerLagrange_line (m : ℝ) (x₀ v : V) (t : ℝ) :
    eulerLagrange (naturalLagrangian (kineticEnergy m) fun _ => 0)
      (fun s : ℝ => x₀ + s • v) t = 0 := by
  have hL : ∀ (s : ℝ) (z : V × V),
      HasFDerivAt (naturalLagrangian (kineticEnergy m) (fun _ => 0) s)
        ((m / 2) • ((2 : ℕ) • (innerSL ℝ z.2).comp (snd ℝ V V))) z := fun s z =>
    ((hasFDerivAt_snd.norm_sq).const_mul (m / 2)).sub_const 0
  have hfd : ∀ s : ℝ, fderiv ℝ (naturalLagrangian (kineticEnergy m) (fun _ => 0) s)
      (x₀ + s • v, deriv (fun s : ℝ => x₀ + s • v) s) =
      (m / 2) • ((2 : ℕ) • (innerSL ℝ v).comp (snd ℝ V V)) := fun s => by
    rw [deriv_line, (hL s _).fderiv]
  have hmom : momentum (naturalLagrangian (kineticEnergy m) fun _ => 0)
      (fun s : ℝ => x₀ + s • v) =
      fun _ => ((m / 2) • ((2 : ℕ) • (innerSL ℝ v).comp (snd ℝ V V))).comp (inr ℝ V V) :=
    funext fun s => by rw [momentum, hfd s]
  have hforce : force (naturalLagrangian (kineticEnergy m) fun _ => 0)
      (fun s : ℝ => x₀ + s • v) t = 0 := by
    rw [force, hfd t]
    refine ContinuousLinearMap.ext fun u => ?_
    change m / 2 * ((2 : ℕ) • inner ℝ v (0 : V)) = 0
    rw [inner_zero_right, smul_zero, mul_zero]
  rw [eulerLagrange, hmom, hforce, deriv_const, sub_zero]

/-- A straight line makes the length stationary: Maupertuis' principle for a
free particle. -/
theorem stationary_jacobiLength_line [FiniteDimensional ℝ V] {m : ℝ} (hm : 0 < m) (x₀ : V)
    {v : V} (hv : v ≠ 0) {a b : ℝ} (hab : a < b) :
    Stationary a b (jacobiLength (kineticEnergy m) (fun _ => 0) (m / 2 * ‖v‖ ^ 2))
      fun s : ℝ => x₀ + s • v := by
  have hq : ContDiff ℝ 2 fun s : ℝ => x₀ + s • v :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  refine (stationary_jacobiLength_iff hab (contDiff_kineticEnergy m) contDiff_const hq
    fun t _ => ⟨?_, ?_⟩).mpr fun t _ => eulerLagrange_line m x₀ v t
  · rw [deriv_line, kineticEnergy, add_zero]
  · have h := norm_pos_iff.mpr hv
    positivity

end Particle

end ProjectAinos.Mechanics.Maupertuis
