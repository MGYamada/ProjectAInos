/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.OpenDomain

/-! # Local variation of a quadratic metric Lagrangian

The coefficients live on a normed coordinate model. All differential
identities are local; an open chart domain suffices for the first variation.
The connection and manifold interpretations are supplied separately.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open ContinuousLinearMap Set
open scoped ContDiff Topology

namespace ProjectAInos.GeneralRelativity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def quadraticLagrangian (B : E → E →L[ℝ] E →L[ℝ] ℝ) : Mechanics.Lagrangian E :=
  fun _ z => (1 / 2 : ℝ) * B z.1 z.2 z.2

/-- Differentiate both velocity slots and the position-dependent metric. -/
theorem quadraticLagrangian_fderiv (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (t : ℝ) (z w : E × E) (hB : DifferentiableAt ℝ B z.1) :
    fderiv ℝ (quadraticLagrangian B t) z w = (1 / 2 : ℝ) *
      ((fderiv ℝ B z.1 w.1) z.2 z.2 + B z.1 w.2 z.2 + B z.1 z.2 w.2) := by
  have hb : HasFDerivAt (fun q : E × E => B q.1)
      ((fderiv ℝ B z.1).comp (fst ℝ E E)) z :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := E × E) (F := E) (G := E →L[ℝ] E →L[ℝ] ℝ)
      (f := Prod.fst) (f' := fst ℝ E E) (g := B) (g' := fderiv ℝ B z.1)
      z hB.hasFDerivAt (hasFDerivAt_fst (𝕜 := ℝ))
  have hd := ((hb.clm_apply hasFDerivAt_snd).clm_apply hasFDerivAt_snd).const_mul (1 / 2 : ℝ)
  change fderiv ℝ (fun q : E × E => (1 / 2 : ℝ) * B q.1 q.2 q.2) z w = _
  rw [hd.fderiv]
  change (1 / 2 : ℝ) * (B z.1 z.2 w.2 +
    (B z.1 w.2 z.2 + (fderiv ℝ B z.1 w.1) z.2 z.2)) = _
  ring

theorem quadratic_force (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (q : ℝ → E) (t : ℝ) (hB : DifferentiableAt ℝ B (q t)) (w : E) :
    Mechanics.force (quadraticLagrangian B) q t w =
      (1 / 2 : ℝ) * (fderiv ℝ B (q t) w) (deriv q t) (deriv q t) := by
  change fderiv ℝ (quadraticLagrangian B t) (q t, deriv q t) (w, 0) = _
  rw [quadraticLagrangian_fderiv B t _ _ hB]
  simp

theorem quadratic_momentum (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (q : ℝ → E) (t : ℝ) (hB : DifferentiableAt ℝ B (q t))
    (hsym : ∀ v w, B (q t) v w = B (q t) w v) :
    Mechanics.momentum (quadraticLagrangian B) q t = B (q t) (deriv q t) := by
  ext w
  change fderiv ℝ (quadraticLagrangian B t) (q t, deriv q t) (0, w) = _
  rw [quadraticLagrangian_fderiv B t _ _ hB]
  simp only [map_zero, zero_apply, zero_add, hsym w (deriv q t)]
  ring

/-- The momentum derivative uses only a C² germ of the metric and curve. -/
theorem quadratic_momentum_hasDerivAt (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    {q : ℝ → E} {t : ℝ} (hB : ContDiffAt ℝ 2 B (q t)) (hq : ContDiffAt ℝ 2 q t)
    (hsym : ∀ x v w, B x v w = B x w v) :
    HasDerivAt (Mechanics.momentum (quadraticLagrangian B) q)
      ((fderiv ℝ B (q t) (deriv q t)) (deriv q t) + B (q t) (deriv (deriv q) t)) t := by
  have he : Mechanics.momentum (quadraticLagrangian B) q =ᶠ[𝓝 t]
      (fun s => B (q s) (deriv q s)) := by
    filter_upwards [hq.continuousAt (hB.eventually (by norm_num))] with s hs
    change ContDiffAt ℝ 2 B (q s) at hs
    exact quadratic_momentum B q s (hs.differentiableAt (by norm_num)) (hsym (q s))
  have hb : HasDerivAt (fun s => B (q s)) (fderiv ℝ B (q t) (deriv q t)) t :=
    (hB.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (hq.differentiableAt (by norm_num)).hasDerivAt
  have hv := ((hq.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  exact (hb.clm_apply hv).congr_of_eventuallyEq he

/-- The full Euler–Lagrange covector of a position-dependent quadratic metric. -/
theorem quadratic_eulerLagrange (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    {q : ℝ → E} {t : ℝ} (hB : ContDiffAt ℝ 2 B (q t)) (hq : ContDiffAt ℝ 2 q t)
    (hsym : ∀ x v w, B x v w = B x w v) (w : E) :
    Mechanics.eulerLagrange (quadraticLagrangian B) q t w =
      (1 / 2 : ℝ) * (fderiv ℝ B (q t) w) (deriv q t) (deriv q t) -
      (fderiv ℝ B (q t) (deriv q t)) (deriv q t) w -
      B (q t) (deriv (deriv q) t) w := by
  rw [Mechanics.eulerLagrange, sub_apply, quadratic_force B q t
    (hB.differentiableAt (by norm_num)), (quadratic_momentum_hasDerivAt B hB hq hsym).deriv]
  simp only [add_apply]
  ring

/-- Smoothness of the actual density on the open position domain. -/
theorem quadraticLagrangian_contDiffOn (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    {U : Set E} (hB : ContDiffOn ℝ 2 B U) :
    ContDiffOn ℝ 2 (Function.uncurry (quadraticLagrangian B))
      {z : ℝ × (E × E) | z.2.1 ∈ U} := by
  exact contDiffOn_const.mul
    (((hB.comp (contDiffOn_snd.fst) (fun _ h => h)).clm_apply
      contDiffOn_snd.snd).clm_apply contDiffOn_snd.snd)

variable [FiniteDimensional ℝ E]

/-- The first variation is proved on an open coordinate domain using compactness. -/
theorem quadratic_hasDerivAt_action (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U)
    {q η : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hq : ContDiff ℝ 2 q)
    (hη : ContDiff ℝ 2 η) (hstay : ∀ t ∈ Icc a b, q t ∈ U) :
    HasDerivAt (fun ε => Mechanics.action a b (quadraticLagrangian B)
      (Variational.perturb q η ε))
      (Mechanics.firstVariation a b (quadraticLagrangian B) q η) 0 :=
  Mechanics.hasDerivAt_action_firstVariation_on hab hq hη
    (hU.preimage (continuous_snd.fst)) (quadraticLagrangian_contDiffOn B hB) hstay

theorem quadratic_stationary_iff (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U)
    {q : ℝ → E} {a b : ℝ} (hab : a < b) (hq : ContDiff ℝ 2 q)
    (hstay : ∀ t ∈ Icc a b, q t ∈ U) :
    Mechanics.Stationary a b (quadraticLagrangian B) q ↔
      ∀ t ∈ Ioo a b, Mechanics.eulerLagrange (quadraticLagrangian B) q t = 0 :=
  Mechanics.stationary_iff_eulerLagrange_on hab hq (hU.preimage (continuous_snd.fst))
    (quadraticLagrangian_contDiffOn B hB) hstay

end ProjectAInos.GeneralRelativity
