/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.OpenDomain
public import ProjectAinos.Mechanics.Examples
public import ProjectAinos.Variational.MovingLimits
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The action as a function of its end points

Let `q(s, t)` be a family of paths and let the end times `a(s)`, `b(s)` move
with the parameter. If the path of the parameter `s₀` solves the
Euler–Lagrange equation between its end times, then

`dS/ds = [p · dq/ds − E · dt/ds]` taken between the two ends,

where `dq/ds` is the derivative of the position of the end point `q(s, b(s))`,
`p` is the momentum and `E = p · q̇ − L` is the energy (§43 of Landau–Lifshitz).
The Euler–Lagrange equation is assumed for the reference path only.

The family is given. It is smooth on an open set that contains the reference
segment, and the Lagrangian is smooth on an open set that contains the jet of
the reference path. The examples are the action of a free particle and of the
harmonic oscillator as a function of the end point and of the time of arrival,
the latter away from the conjugate times `sin ΩT = 0`, and a family of motions
of the oscillator with moving amplitudes.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Interval

namespace ProjectAinos.Mechanics

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- The energy `p · q̇ − L` along a path. -/
def pathEnergy (L : Lagrangian Q) (q : ℝ → Q) (t : ℝ) : ℝ :=
  momentum L q t (deriv q t) - L t (q t, deriv q t)

/-! ### Partial derivatives of a family of paths -/

section Family

variable {q : ℝ × ℝ → Q}

/-- The velocity of a path of a family is a partial derivative of the family. -/
theorem deriv_family_time {p : ℝ × ℝ} (hq : DifferentiableAt ℝ q p) :
    deriv (fun t => q (p.1, t)) p.2 = fderiv ℝ q p (0, 1) := by
  have h : HasDerivAt (fun t : ℝ => (p.1, t)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => (p.1, t)) p.2 hq.hasFDerivAt h).deriv

/-- The derivative of a family in its parameter, at a fixed time. -/
theorem hasDerivAt_family_parameter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × ℝ → E} {s₀ t : ℝ} (hg : DifferentiableAt ℝ g (s₀, t)) :
    HasDerivAt (fun s => g (s, t)) (fderiv ℝ g (s₀, t) (1, 0)) s₀ := by
  have h : HasDerivAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ)) s₀ :=
    (hasDerivAt_id s₀).prodMk (hasDerivAt_const s₀ t)
  exact HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, t)) s₀ hg.hasFDerivAt h

/-- The derivative of a family in the time, at a fixed parameter. -/
theorem hasDerivAt_family_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × ℝ → E} {s₀ t : ℝ} (hg : DifferentiableAt ℝ g (s₀, t)) :
    HasDerivAt (fun r => g (s₀, r)) (fderiv ℝ g (s₀, t) (0, 1)) t := by
  have h : HasDerivAt (fun r : ℝ => (s₀, r)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t s₀).prodMk (hasDerivAt_id t)
  exact HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (s₀, r)) t hg.hasFDerivAt h

/-- The derivative of the Lagrangian along a family of paths, in the parameter
of the family: the first variation density for the variation field `∂q/∂s`. -/
theorem hasDerivAt_density_family {L : Lagrangian Q} {s₀ t : ℝ}
    (hq : ContDiffAt ℝ 2 q (s₀, t))
    (hL : DifferentiableAt ℝ (L t) (q (s₀, t), deriv (fun r => q (s₀, r)) t)) :
    HasDerivAt (fun s => L t (q (s, t), deriv (fun r => q (s, r)) t))
      (force L (fun r => q (s₀, r)) t (fderiv ℝ q (s₀, t) (1, 0)) +
        momentum L (fun r => q (s₀, r)) t
          (deriv (fun r => fderiv ℝ q (s₀, r) (1, 0)) t)) s₀ := by
  have hqd : DifferentiableAt ℝ q (s₀, t) := hq.differentiableAt (by simp)
  have hqd' : DifferentiableAt ℝ (fderiv ℝ q) (s₀, t) :=
    (hq.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hev : ∀ᶠ p in 𝓝 (s₀, t), DifferentiableAt ℝ q p :=
    (hq.eventually (by simp)).mono fun p hp => hp.differentiableAt (by simp)
  have hv : deriv (fun r => q (s₀, r)) t = fderiv ℝ q (s₀, t) (0, 1) :=
    deriv_family_time (p := (s₀, t)) hqd
  rw [hv] at hL
  have hz1 := hasDerivAt_family_parameter hqd
  have hz2 : HasDerivAt (fun s : ℝ => fderiv ℝ q (s, t) (0, 1))
      (fderiv ℝ (fderiv ℝ q) (s₀, t) (1, 0) (0, 1)) s₀ := by
    have h := (hasDerivAt_family_parameter hqd').clm_apply
      (hasDerivAt_const s₀ ((0 : ℝ), (1 : ℝ)))
    simpa using h
  have hη : HasDerivAt (fun r : ℝ => fderiv ℝ q (s₀, r) (1, 0))
      (fderiv ℝ (fderiv ℝ q) (s₀, t) (0, 1) (1, 0)) t := by
    have h := (hasDerivAt_family_time hqd').clm_apply
      (hasDerivAt_const t ((1 : ℝ), (0 : ℝ)))
    simpa using h
  have hz : HasDerivAt (fun s : ℝ => (q (s, t), fderiv ℝ q (s, t) (0, 1)))
      (fderiv ℝ q (s₀, t) (1, 0), fderiv ℝ (fderiv ℝ q) (s₀, t) (1, 0) (0, 1)) s₀ :=
    hz1.prodMk hz2
  have hc := HasFDerivAt.comp_hasDerivAt
    (f := fun s : ℝ => (q (s, t), fderiv ℝ q (s, t) (0, 1))) s₀ hL.hasFDerivAt hz
  have heq : (fun s => L t (q (s, t), deriv (fun r => q (s, r)) t)) =ᶠ[𝓝 s₀]
      fun s => L t (q (s, t), fderiv ℝ q (s, t) (0, 1)) := by
    have hc' : Tendsto (fun s : ℝ => (s, t)) (𝓝 s₀) (𝓝 (s₀, t)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    filter_upwards [hc'.eventually hev] with s hs
    rw [deriv_family_time (p := (s, t)) hs]
  refine (hc.congr_of_eventuallyEq heq).congr_deriv ?_
  have hsymm := (hq.isSymmSndFDerivAt (by simp)) (1, 0) (0, 1)
  rw [hη.deriv, ← hsymm]
  simp only [force, momentum, hv]
  change _ = fderiv ℝ (L t) (q (s₀, t), fderiv ℝ q (s₀, t) (0, 1))
      (fderiv ℝ q (s₀, t) (1, 0), 0) +
    fderiv ℝ (L t) (q (s₀, t), fderiv ℝ q (s₀, t) (0, 1))
      (0, fderiv ℝ (fderiv ℝ q) (s₀, t) (1, 0) (0, 1))
  rw [← map_add]
  simp

/-- The derivative of the position of a moving end point. -/
theorem deriv_family_endpoint {s₀ : ℝ} {c : ℝ → ℝ} {c' : ℝ} (hc : HasDerivAt c c' s₀)
    (hq : DifferentiableAt ℝ q (s₀, c s₀)) :
    deriv (fun s => q (s, c s)) s₀ =
      fderiv ℝ q (s₀, c s₀) (1, 0) + c' • deriv (fun r => q (s₀, r)) (c s₀) := by
  have h1 : HasDerivAt (fun s : ℝ => (s, c s)) ((1 : ℝ), c') s₀ :=
    (hasDerivAt_id s₀).prodMk hc
  have h2 := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, c s)) s₀ hq.hasFDerivAt h1
  have h3 : deriv (fun s => q (s, c s)) s₀ = fderiv ℝ q (s₀, c s₀) (1, c') := h2.deriv
  rw [h3, deriv_family_time (p := (s₀, c s₀)) hq]
  have hsplit : ((1 : ℝ), c') = ((1 : ℝ), (0 : ℝ)) + c' • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul]

end Family

/-- The momentum along a path is continuously differentiable where the path and
the Lagrangian are twice continuously differentiable. -/
theorem contDiffAt_momentum {L : Lagrangian Q} {q : ℝ → Q} {t : ℝ}
    (hL : ContDiffAt ℝ 2 (Function.uncurry L) (pathJet q t)) (hq : ContDiffAt ℝ 2 q t) :
    ContDiffAt ℝ 1 (momentum L q) t := by
  have hpv : ContDiffAt ℝ 1 (fun r => (q r, deriv q r)) t :=
    (hq.of_le (by norm_num)).prodMk
      ((hq.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  exact (ContDiffAt.fderiv (f := L) (g := fun r => (q r, deriv q r)) hL hpv
    (by norm_num)).clm_comp contDiffAt_const

/-! ### The derivative of the action -/

/-- The derivative of the action with respect to a parameter that moves the
path and both end times. The family is smooth on an open set `U` and the
Lagrangian on an open set `W` of the jet space. -/
theorem hasDerivAt_action_movingEndpoints_on {L : Lagrangian Q} {W : Set (ℝ × (Q × Q))}
    (hW : IsOpen W) (hL : ContDiffOn ℝ ∞ (Function.uncurry L) W)
    {q : ℝ × ℝ → Q} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    {a b : ℝ → ℝ} {s₀ a' b' : ℝ} (ha : HasDerivAt a a' s₀) (hb : HasDerivAt b b' s₀)
    (hqU : ∀ t ∈ uIcc (a s₀) (b s₀), (s₀, t) ∈ U)
    (hqW : ∀ t ∈ uIcc (a s₀) (b s₀), pathJet (fun t => q (s₀, t)) t ∈ W)
    (hEL : ∀ t ∈ uIcc (a s₀) (b s₀), eulerLagrange L (fun t => q (s₀, t)) t = 0) :
    HasDerivAt (fun s => action (a s) (b s) L fun t => q (s, t))
      (momentum L (fun t => q (s₀, t)) (b s₀) (deriv (fun s => q (s, b s)) s₀) -
          pathEnergy L (fun t => q (s₀, t)) (b s₀) * b' -
        (momentum L (fun t => q (s₀, t)) (a s₀) (deriv (fun s => q (s, a s)) s₀) -
          pathEnergy L (fun t => q (s₀, t)) (a s₀) * a')) s₀ := by
  have hqd : ∀ p ∈ U, DifferentiableAt ℝ q p := fun p hp =>
    (hq.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hq2 : ∀ p ∈ U, ContDiffAt ℝ 2 q p := fun p hp =>
    (hq.contDiffAt (hU.mem_nhds hp)).of_le (by simp)
  -- the integrand is smooth on an open set that contains the reference segment
  have hJ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.2, q p, fderiv ℝ q p (0, 1))) U :=
    contDiffOn_snd.prodMk (hq.prodMk
      ((hq.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const))
  have hO : IsOpen (U ∩ (fun p : ℝ × ℝ => (p.2, q p, fderiv ℝ q p (0, 1))) ⁻¹' W) :=
    hJ.continuousOn.isOpen_inter_preimage hU hW
  have hF : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => L p.2 (q p, deriv (fun t => q (p.1, t)) p.2))
      (U ∩ (fun p : ℝ × ℝ => (p.2, q p, fderiv ℝ q p (0, 1))) ⁻¹' W) := by
    refine (hL.comp (hJ.mono inter_subset_left) fun p hp => hp.2).congr fun p hp => ?_
    change L p.2 (q p, deriv (fun t => q (p.1, t)) p.2) = L p.2 (q p, fderiv ℝ q p (0, 1))
    rw [deriv_family_time (hqd p hp.1)]
  have hKO : ∀ t ∈ uIcc (a s₀) (b s₀),
      (s₀, t) ∈ U ∩ (fun p : ℝ × ℝ => (p.2, q p, fderiv ℝ q p (0, 1))) ⁻¹' W := by
    intro t ht
    refine ⟨hqU t ht, ?_⟩
    have h := hqW t ht
    change (t, q (s₀, t), deriv (fun r => q (s₀, r)) t) ∈ W at h
    rw [deriv_family_time (p := (s₀, t)) (hqd _ (hqU t ht))] at h
    exact h
  have hLat : ∀ t ∈ uIcc (a s₀) (b s₀), ContDiffAt ℝ 2 (Function.uncurry L)
      (t, q (s₀, t), deriv (fun r => q (s₀, r)) t) := fun t ht =>
    (hL.contDiffAt (hW.mem_nhds (hqW t ht))).of_le (by simp)
  have hLt : ∀ t ∈ uIcc (a s₀) (b s₀),
      DifferentiableAt ℝ (L t) (q (s₀, t), deriv (fun r => q (s₀, r)) t) := by
    intro t ht
    have h1 : DifferentiableAt ℝ (Function.uncurry L)
        (t, q (s₀, t), deriv (fun r => q (s₀, r)) t) :=
      (hLat t ht).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (fun z : Q × Q => (t, z))
        (q (s₀, t), deriv (fun r => q (s₀, r)) t) :=
      (differentiableAt_const t).prodMk differentiableAt_id
    exact DifferentiableAt.comp (g := Function.uncurry L) (f := fun z : Q × Q => (t, z))
      _ h1 h2
  have hD : ∀ t ∈ uIcc (a s₀) (b s₀),
      HasDerivAt (fun s => L t (q (s, t), deriv (fun r => q (s, r)) t))
        (force L (fun r => q (s₀, r)) t (fderiv ℝ q (s₀, t) (1, 0)) +
          momentum L (fun r => q (s₀, r)) t
            (deriv (fun r => fderiv ℝ q (s₀, r) (1, 0)) t)) s₀ :=
    fun t ht => hasDerivAt_density_family (hq2 _ (hqU t ht)) (hLt t ht)
  have hmain := Variational.hasDerivAt_intervalIntegral_moving_on
    (F := fun p : ℝ × ℝ => L p.2 (q p, deriv (fun t => q (p.1, t)) p.2))
    (D := fun t => force L (fun r => q (s₀, r)) t (fderiv ℝ q (s₀, t) (1, 0)) +
      momentum L (fun r => q (s₀, r)) t (deriv (fun r => fderiv ℝ q (s₀, r) (1, 0)) t))
    hO hF ha hb hKO hD
  -- integration by parts along the reference path
  have hmom : ∀ t ∈ uIcc (a s₀) (b s₀),
      ContDiffAt ℝ 1 (momentum L fun r => q (s₀, r)) t := by
    intro t ht
    have hq₀ : ContDiffAt ℝ 2 (fun r => q (s₀, r)) t :=
      ContDiffAt.comp (g := q) (f := fun r : ℝ => (s₀, r)) t (hq2 _ (hqU t ht))
        (contDiffAt_const.prodMk contDiffAt_id)
    exact contDiffAt_momentum (hLat t ht) hq₀
  have hη : ∀ t ∈ uIcc (a s₀) (b s₀),
      ContDiffAt ℝ 1 (fun r => fderiv ℝ q (s₀, r) (1, 0)) t := by
    intro t ht
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ q) (s₀, t) :=
      (hq2 _ (hqU t ht)).fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun r : ℝ => fderiv ℝ q (s₀, r)) t :=
      ContDiffAt.comp (g := fderiv ℝ q) (f := fun r : ℝ => (s₀, r)) t h1
        (contDiffAt_const.prodMk contDiffAt_id)
    exact h2.clm_apply contDiffAt_const
  have hP : ∀ t ∈ uIcc (a s₀) (b s₀), ContDiffAt ℝ 1
      (fun r => momentum L (fun r => q (s₀, r)) r (fderiv ℝ q (s₀, r) (1, 0))) t :=
    fun t ht => (hmom t ht).clm_apply (hη t ht)
  have hDc : ContinuousOn
      (fun t => force L (fun r => q (s₀, r)) t (fderiv ℝ q (s₀, t) (1, 0)) +
        momentum L (fun r => q (s₀, r)) t (deriv (fun r => fderiv ℝ q (s₀, r) (1, 0)) t))
      (uIcc (a s₀) (b s₀)) :=
    Variational.continuousOn_parameter_derivative
      (F := fun p : ℝ × ℝ => L p.2 (q p, deriv (fun t => q (p.1, t)) p.2))
      (fun t ht => (hF.contDiffAt (hO.mem_nhds (hKO t ht))).of_le (by simp)) hD
  have hPd : ∀ t ∈ uIcc (a s₀) (b s₀),
      HasDerivAt (fun r => momentum L (fun r => q (s₀, r)) r (fderiv ℝ q (s₀, r) (1, 0)))
        ((fun t => force L (fun r => q (s₀, r)) t (fderiv ℝ q (s₀, t) (1, 0)) +
            momentum L (fun r => q (s₀, r)) t
              (deriv (fun r => fderiv ℝ q (s₀, r) (1, 0)) t)) t -
          (fun _ : ℝ => (0 : ℝ)) t) t := by
    intro t ht
    have h := ((hmom t ht).differentiableAt one_ne_zero).hasDerivAt.clm_apply
      ((hη t ht).differentiableAt one_ne_zero).hasDerivAt
    have hf : force L (fun r => q (s₀, r)) t = deriv (momentum L fun r => q (s₀, r)) t :=
      sub_eq_zero.mp (hEL t ht)
    refine h.congr_deriv ?_
    simp only [hf, sub_zero]
  have hint := Variational.integral_eq_boundary_add_residual hP hDc hPd
  refine hmain.congr_deriv ?_
  rw [hint, deriv_family_endpoint hb (hqd _ (hqU _ right_mem_uIcc)),
    deriv_family_endpoint ha (hqd _ (hqU _ left_mem_uIcc))]
  simp only [pathEnergy, map_add, map_smul, smul_eq_mul, intervalIntegral.integral_zero,
    add_zero]
  ring

/-- The formula for a family and a Lagrangian that are smooth everywhere. -/
theorem hasDerivAt_action_movingEndpoints {L : Lagrangian Q}
    (hL : ContDiff ℝ ∞ (Function.uncurry L)) {q : ℝ × ℝ → Q} (hq : ContDiff ℝ ∞ q)
    {a b : ℝ → ℝ} {s₀ a' b' : ℝ} (ha : HasDerivAt a a' s₀) (hb : HasDerivAt b b' s₀)
    (hEL : ∀ t ∈ uIcc (a s₀) (b s₀), eulerLagrange L (fun t => q (s₀, t)) t = 0) :
    HasDerivAt (fun s => action (a s) (b s) L fun t => q (s, t))
      (momentum L (fun t => q (s₀, t)) (b s₀) (deriv (fun s => q (s, b s)) s₀) -
          pathEnergy L (fun t => q (s₀, t)) (b s₀) * b' -
        (momentum L (fun t => q (s₀, t)) (a s₀) (deriv (fun s => q (s, a s)) s₀) -
          pathEnergy L (fun t => q (s₀, t)) (a s₀) * a')) s₀ :=
  hasDerivAt_action_movingEndpoints_on isOpen_univ hL.contDiffOn isOpen_univ hq.contDiffOn
    ha hb (fun _ _ => mem_univ _) (fun _ _ => mem_univ _) hEL

/-! ### One coordinate with a potential -/

theorem contDiff_natural_of_contDiff (m : ℝ) {V : ℝ → ℝ} {n : WithTop ℕ∞}
    (hV : ContDiff ℝ n V) : ContDiff ℝ n (Function.uncurry (natural m V)) :=
  (contDiff_const.mul ((contDiff_snd.comp contDiff_snd).mul
    (contDiff_snd.comp contDiff_snd))).sub (hV.comp (contDiff_fst.comp contDiff_snd))

/-- The Euler–Lagrange expression of a potential at a time where the velocity is
differentiable. -/
theorem eulerLagrange_natural_of_differentiableAt (m : ℝ) {V : ℝ → ℝ}
    (hV : Differentiable ℝ V) {q : ℝ → ℝ} {t : ℝ} (hq : DifferentiableAt ℝ (deriv q) t) :
    eulerLagrange (natural m V) q t =
      (-deriv V (q t) - m * deriv (deriv q) t) • ContinuousLinearMap.id ℝ ℝ := by
  have hp := ((hq.hasDerivAt.const_mul m).smul_const (ContinuousLinearMap.id ℝ ℝ)).deriv
  have hm : momentum (natural m V) q =
      fun s => (m * deriv q s) • ContinuousLinearMap.id ℝ ℝ :=
    funext (momentum_natural m hV q)
  rw [eulerLagrange, hm, hp, force_natural m hV]
  exact (_root_.sub_smul _ _ _).symm

/-- The energy of a potential: kinetic plus potential energy. -/
theorem pathEnergy_natural (m : ℝ) {V : ℝ → ℝ} (hV : Differentiable ℝ V) (q : ℝ → ℝ)
    (t : ℝ) : pathEnergy (natural m V) q t = m / 2 * deriv q t ^ 2 + V (q t) := by
  rw [pathEnergy, momentum_natural m hV]
  simp only [natural, _root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

/-- The derivative of the action of a particle in a potential, for a family of
paths whose reference path solves Newton's equation. -/
theorem hasDerivAt_action_natural_movingEndpoints_on {m : ℝ} {V : ℝ → ℝ}
    (hV : ContDiff ℝ ∞ V) {q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hq : ContDiffOn ℝ ∞ q U) {a b : ℝ → ℝ} {s₀ a' b' : ℝ} (ha : HasDerivAt a a' s₀)
    (hb : HasDerivAt b b' s₀) (hqU : ∀ t ∈ uIcc (a s₀) (b s₀), (s₀, t) ∈ U)
    (hN : ∀ t ∈ uIcc (a s₀) (b s₀),
      m * deriv (deriv fun t => q (s₀, t)) t = -deriv V (q (s₀, t))) :
    HasDerivAt (fun s => action (a s) (b s) (natural m V) fun t => q (s, t))
      (m * deriv (fun t => q (s₀, t)) (b s₀) * deriv (fun s => q (s, b s)) s₀ -
          (m / 2 * deriv (fun t => q (s₀, t)) (b s₀) ^ 2 + V (q (s₀, b s₀))) * b' -
        (m * deriv (fun t => q (s₀, t)) (a s₀) * deriv (fun s => q (s, a s)) s₀ -
          (m / 2 * deriv (fun t => q (s₀, t)) (a s₀) ^ 2 + V (q (s₀, a s₀))) * a')) s₀ := by
  have hVd : Differentiable ℝ V := hV.differentiable (by simp)
  have hEL : ∀ t ∈ uIcc (a s₀) (b s₀),
      eulerLagrange (natural m V) (fun t => q (s₀, t)) t = 0 := by
    intro t ht
    have hq₀ : ContDiffAt ℝ 2 (fun r => q (s₀, r)) t :=
      ContDiffAt.comp (g := q) (f := fun r : ℝ => (s₀, r)) t
        ((hq.contDiffAt (hU.mem_nhds (hqU t ht))).of_le (by simp))
        (contDiffAt_const.prodMk contDiffAt_id)
    have hdq : DifferentiableAt ℝ (deriv fun r => q (s₀, r)) t :=
      ((hq₀.fderiv_right (m := 1) (by norm_num)).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
    rw [eulerLagrange_natural_of_differentiableAt m hVd hdq]
    change (-deriv V (q (s₀, t)) - m * deriv (deriv fun t => q (s₀, t)) t) •
      ContinuousLinearMap.id ℝ ℝ = 0
    rw [hN t ht, sub_self, zero_smul]
  have h := hasDerivAt_action_movingEndpoints_on isOpen_univ
    (contDiff_natural_of_contDiff m hV).contDiffOn hU hq ha hb hqU
    (fun _ _ => mem_univ _) hEL
  refine h.congr_deriv ?_
  simp only [momentum_natural m hVd, pathEnergy_natural m hVd, _root_.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]

/-! ### Examples -/

/-- The action of a free particle that leaves the origin at time `0` and
reaches `x` at time `T` is `m x² / 2T`. Its derivative for a displacement of the
end point and of the time of arrival is `p dx − E dT`, with `p = m x / T` and
`E = m x² / 2T²`. -/
theorem hasDerivAt_action_free_endpoint (m x ξ T τ : ℝ) (hT : T ≠ 0) :
    HasDerivAt (fun s => action 0 (T + s * τ) (natural m fun _ => 0)
        fun t => (x + s * ξ) * t / (T + s * τ))
      (m * x / T * ξ - m * x ^ 2 / (2 * T ^ 2) * τ) 0 := by
  have hU : IsOpen {p : ℝ × ℝ | T + p.1 * τ ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hq : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (x + p.1 * ξ) * p.2 / (T + p.1 * τ))
      {p : ℝ × ℝ | T + p.1 * τ ≠ 0} :=
    ContDiffOn.div (by fun_prop) (by fun_prop) fun p hp => hp
  have ha : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 := hasDerivAt_const 0 0
  have hb : HasDerivAt (fun s : ℝ => T + s * τ) τ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const τ).const_add T
  have hd₀ : deriv (fun t : ℝ => (x + 0 * ξ) * t / (T + 0 * τ)) = fun _ => x / T := by
    funext t
    have h : HasDerivAt (fun t : ℝ => (x + 0 * ξ) * t / (T + 0 * τ)) (x / T) t := by
      have h1 := ((hasDerivAt_id t).const_mul (x + 0 * ξ)).div_const (T + 0 * τ)
      refine h1.congr_deriv ?_
      simp
    exact h.deriv
  have he : deriv (fun s : ℝ => (x + s * ξ) * (T + s * τ) / (T + s * τ)) 0 = ξ := by
    have hev : (fun s : ℝ => (x + s * ξ) * (T + s * τ) / (T + s * τ)) =ᶠ[𝓝 0]
        fun s => x + s * ξ := by
      have hne : ∀ᶠ s : ℝ in 𝓝 0, T + s * τ ≠ 0 := by
        have hc : ContinuousAt (fun s : ℝ => T + s * τ) 0 := by fun_prop
        exact hc.eventually_ne (by simpa using hT)
      filter_upwards [hne] with s hs
      field_simp
    rw [hev.deriv_eq]
    simp
  have h0 : deriv (fun s : ℝ => (x + s * ξ) * 0 / (T + s * τ)) 0 = 0 := by
    simp
  have h := hasDerivAt_action_natural_movingEndpoints_on (m := m) (V := fun _ => 0)
    contDiff_const hU hq ha hb (fun t _ => by simpa using hT)
    (fun t _ => by
      change m * deriv (deriv fun t : ℝ => (x + 0 * ξ) * t / (T + 0 * τ)) t = _
      rw [hd₀]
      simp)
  refine h.congr_deriv ?_
  simp only [hd₀, he, h0]
  field_simp
  ring

/-- A family of motions of the harmonic oscillator, with the amplitudes and the
time of arrival moving. -/
theorem hasDerivAt_action_oscillator_family (m Ω A B α β T τ : ℝ) :
    HasDerivAt (fun s => action 0 (T + s * τ) (natural m fun x => m * Ω ^ 2 / 2 * x ^ 2)
        fun t => (A + s * α) * Real.cos (Ω * t) + (B + s * β) * Real.sin (Ω * t))
      (m * (Ω * (B * Real.cos (Ω * T) - A * Real.sin (Ω * T))) *
            (α * Real.cos (Ω * T) + β * Real.sin (Ω * T)) +
          (m / 2 * (Ω * (B * Real.cos (Ω * T) - A * Real.sin (Ω * T))) ^ 2 -
            m * Ω ^ 2 / 2 * (A * Real.cos (Ω * T) + B * Real.sin (Ω * T)) ^ 2) * τ -
        m * (Ω * B) * α) 0 := by
  have hq : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      (A + p.1 * α) * Real.cos (Ω * p.2) + (B + p.1 * β) * Real.sin (Ω * p.2)) := by
    fun_prop
  have hV : ContDiff ℝ ∞ (fun x : ℝ => m * Ω ^ 2 / 2 * x ^ 2) := by fun_prop
  have hV' : ∀ y : ℝ, deriv (fun x : ℝ => m * Ω ^ 2 / 2 * x ^ 2) y = m * Ω ^ 2 * y := by
    intro y
    have h : HasDerivAt (fun x : ℝ => m * Ω ^ 2 / 2 * x ^ 2) (m * Ω ^ 2 * y) y := by
      refine (((hasDerivAt_id y).pow 2).const_mul (m * Ω ^ 2 / 2)).congr_deriv ?_
      simp
      ring
    exact h.deriv
  have ha : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 := hasDerivAt_const 0 0
  have hb : HasDerivAt (fun s : ℝ => T + s * τ) τ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const τ).const_add T
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Ω * t) Ω t := fun t => by
    simpa using (hasDerivAt_id t).const_mul Ω
  have hd₀ : deriv (fun t : ℝ =>
      (A + 0 * α) * Real.cos (Ω * t) + (B + 0 * β) * Real.sin (Ω * t)) =
      fun t => Ω * (B * Real.cos (Ω * t) - A * Real.sin (Ω * t)) := by
    funext t
    have h : HasDerivAt (fun t : ℝ =>
        (A + 0 * α) * Real.cos (Ω * t) + (B + 0 * β) * Real.sin (Ω * t))
        (Ω * (B * Real.cos (Ω * t) - A * Real.sin (Ω * t))) t := by
      refine (((hlin t).cos.const_mul (A + 0 * α)).add
        ((hlin t).sin.const_mul (B + 0 * β))).congr_deriv ?_
      ring
    exact h.deriv
  have hdd : ∀ t : ℝ, deriv (fun t : ℝ => Ω * (B * Real.cos (Ω * t) - A * Real.sin (Ω * t)))
      t = -(Ω ^ 2 * (A * Real.cos (Ω * t) + B * Real.sin (Ω * t))) := by
    intro t
    have h : HasDerivAt (fun t : ℝ => Ω * (B * Real.cos (Ω * t) - A * Real.sin (Ω * t)))
        (-(Ω ^ 2 * (A * Real.cos (Ω * t) + B * Real.sin (Ω * t)))) t := by
      refine ((((hlin t).cos.const_mul B).sub
        ((hlin t).sin.const_mul A)).const_mul Ω).congr_deriv ?_
      ring
    exact h.deriv
  have he : deriv (fun s : ℝ => (A + s * α) * Real.cos (Ω * (T + s * τ)) +
      (B + s * β) * Real.sin (Ω * (T + s * τ))) 0 =
      α * Real.cos (Ω * T) + β * Real.sin (Ω * T) +
        τ * (Ω * (B * Real.cos (Ω * T) - A * Real.sin (Ω * T))) := by
    have hl : HasDerivAt (fun s : ℝ => Ω * (T + s * τ)) (Ω * τ) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const τ).const_add T).const_mul Ω
    have hA : HasDerivAt (fun s : ℝ => A + s * α) α 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const α).const_add A
    have hB : HasDerivAt (fun s : ℝ => B + s * β) β 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const β).const_add B
    have h : HasDerivAt (fun s : ℝ => (A + s * α) * Real.cos (Ω * (T + s * τ)) +
        (B + s * β) * Real.sin (Ω * (T + s * τ)))
        (α * Real.cos (Ω * T) + β * Real.sin (Ω * T) +
          τ * (Ω * (B * Real.cos (Ω * T) - A * Real.sin (Ω * T)))) 0 := by
      refine ((hA.mul hl.cos).add (hB.mul hl.sin)).congr_deriv ?_
      simp
      ring
    exact h.deriv
  have h0 : deriv (fun s : ℝ => (A + s * α) * Real.cos (Ω * 0) +
      (B + s * β) * Real.sin (Ω * 0)) 0 = α := by
    have hA : HasDerivAt (fun s : ℝ => A + s * α) α 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const α).const_add A
    have hfun : (fun s : ℝ => (A + s * α) * Real.cos (Ω * 0) +
        (B + s * β) * Real.sin (Ω * 0)) = fun s => A + s * α := by
      funext s
      simp
    rw [hfun, hA.deriv]
  have h := hasDerivAt_action_natural_movingEndpoints_on (m := m) hV isOpen_univ
    hq.contDiffOn ha hb (fun _ _ => mem_univ _)
    (fun t _ => by
      rw [hd₀, hdd, hV']
      ring)
  refine h.congr_deriv ?_
  simp only [hd₀, he, h0]
  simp
  ring

/-- The action of the harmonic oscillator from the origin at time `0` to `x` at
time `T`, when `sin ΩT ≠ 0`, that is, when the end point is not conjugate to the
origin. Its derivative is `p dx − E dT` with `p = m Ω x cot ΩT` and
`E = m Ω² x² / (2 sin² ΩT)`. -/
theorem hasDerivAt_action_oscillator_endpoint (m Ω x ξ T τ : ℝ)
    (hT : Real.sin (Ω * T) ≠ 0) :
    HasDerivAt (fun s => action 0 (T + s * τ) (natural m fun y => m * Ω ^ 2 / 2 * y ^ 2)
        fun t => (x + s * ξ) * Real.sin (Ω * t) / Real.sin (Ω * (T + s * τ)))
      (m * Ω * x * Real.cos (Ω * T) / Real.sin (Ω * T) * ξ -
        m * Ω ^ 2 * x ^ 2 / (2 * Real.sin (Ω * T) ^ 2) * τ) 0 := by
  have hU : IsOpen {p : ℝ × ℝ | Real.sin (Ω * (T + p.1 * τ)) ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hq : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      (x + p.1 * ξ) * Real.sin (Ω * p.2) / Real.sin (Ω * (T + p.1 * τ)))
      {p : ℝ × ℝ | Real.sin (Ω * (T + p.1 * τ)) ≠ 0} :=
    ContDiffOn.div (by fun_prop) (by fun_prop) fun p hp => hp
  have hV : ContDiff ℝ ∞ (fun y : ℝ => m * Ω ^ 2 / 2 * y ^ 2) := by fun_prop
  have hV' : ∀ y : ℝ, deriv (fun x : ℝ => m * Ω ^ 2 / 2 * x ^ 2) y = m * Ω ^ 2 * y := by
    intro y
    have h : HasDerivAt (fun x : ℝ => m * Ω ^ 2 / 2 * x ^ 2) (m * Ω ^ 2 * y) y := by
      refine (((hasDerivAt_id y).pow 2).const_mul (m * Ω ^ 2 / 2)).congr_deriv ?_
      simp
      ring
    exact h.deriv
  have ha : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 := hasDerivAt_const 0 0
  have hb : HasDerivAt (fun s : ℝ => T + s * τ) τ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const τ).const_add T
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Ω * t) Ω t := fun t => by
    simpa using (hasDerivAt_id t).const_mul Ω
  have hd₀ : deriv (fun t : ℝ =>
      (x + 0 * ξ) * Real.sin (Ω * t) / Real.sin (Ω * (T + 0 * τ))) =
      fun t => x * Ω * Real.cos (Ω * t) / Real.sin (Ω * T) := by
    funext t
    have h : HasDerivAt (fun t : ℝ =>
        (x + 0 * ξ) * Real.sin (Ω * t) / Real.sin (Ω * (T + 0 * τ)))
        (x * Ω * Real.cos (Ω * t) / Real.sin (Ω * T)) t := by
      refine (((hlin t).sin.const_mul (x + 0 * ξ)).div_const
        (Real.sin (Ω * (T + 0 * τ)))).congr_deriv ?_
      simp only [zero_mul, add_zero]
      ring
    exact h.deriv
  have hdd : ∀ t : ℝ, deriv (fun t : ℝ => x * Ω * Real.cos (Ω * t) / Real.sin (Ω * T)) t =
      -(Ω ^ 2 * (x * Real.sin (Ω * t) / Real.sin (Ω * T))) := by
    intro t
    have h : HasDerivAt (fun t : ℝ => x * Ω * Real.cos (Ω * t) / Real.sin (Ω * T))
        (-(Ω ^ 2 * (x * Real.sin (Ω * t) / Real.sin (Ω * T)))) t := by
      refine (((hlin t).cos.const_mul (x * Ω)).div_const
        (Real.sin (Ω * T))).congr_deriv ?_
      ring
    exact h.deriv
  have he : deriv (fun s : ℝ =>
      (x + s * ξ) * Real.sin (Ω * (T + s * τ)) / Real.sin (Ω * (T + s * τ))) 0 = ξ := by
    have hev : (fun s : ℝ =>
        (x + s * ξ) * Real.sin (Ω * (T + s * τ)) / Real.sin (Ω * (T + s * τ))) =ᶠ[𝓝 0]
        fun s => x + s * ξ := by
      have hne : ∀ᶠ s : ℝ in 𝓝 0, Real.sin (Ω * (T + s * τ)) ≠ 0 := by
        have hc : ContinuousAt (fun s : ℝ => Real.sin (Ω * (T + s * τ))) 0 := by fun_prop
        exact hc.eventually_ne (by simpa using hT)
      filter_upwards [hne] with s hs
      field_simp
    rw [hev.deriv_eq]
    simp
  have h0 : deriv (fun s : ℝ =>
      (x + s * ξ) * Real.sin (Ω * 0) / Real.sin (Ω * (T + s * τ))) 0 = 0 := by
    simp
  have h := hasDerivAt_action_natural_movingEndpoints_on (m := m) hV hU hq ha hb
    (fun t _ => by simpa using hT)
    (fun t _ => by
      change m * deriv (deriv fun t : ℝ =>
        (x + 0 * ξ) * Real.sin (Ω * t) / Real.sin (Ω * (T + 0 * τ))) t = _
      rw [hd₀, hdd, hV']
      simp only [zero_mul, add_zero]
      ring)
  refine h.congr_deriv ?_
  simp only [hd₀, he, h0]
  simp only [zero_mul, add_zero, mul_zero, sub_zero]
  have hcs := Real.cos_sq_add_sin_sq (Ω * T)
  field_simp
  linear_combination (-(m * x ^ 2 * Ω ^ 2 * τ)) * hcs

end ProjectAinos.Mechanics
