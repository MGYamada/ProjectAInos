/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.QuadraticLagrangian
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The square-root particle Lagrangian on an open timelike domain

The coefficients may depend on all spacetime coordinates. Smoothness is used
only where the reference jet is timelike. The comparison with the quadratic
Lagrangian retains the derivative of the proper-speed factor.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open ContinuousLinearMap Set
open scoped ContDiff Topology

namespace ProjectAInos.GeneralRelativity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Coordinate proper speed, with timelikeness required by its differential laws. -/
def coordinateProperSpeed (B : E → E →L[ℝ] E →L[ℝ] ℝ) (z : E × E) : ℝ :=
  Real.sqrt (-B z.1 z.2 z.2)

def freeLagrangian (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℝ) : Mechanics.Lagrangian E :=
  fun _ z => -m * coordinateProperSpeed B z

/-- The jet domain restricts positions to `U` and velocities to the timelike cone. -/
def timelikeJets (B : E → E →L[ℝ] E →L[ℝ] ℝ) (U : Set E) : Set (ℝ × (E × E)) :=
  {z | z.2.1 ∈ U ∧ B z.2.1 z.2.2 z.2.2 < 0}

theorem freeLagrangian_fderiv (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (m t : ℝ) (z w : E × E) (hB : DifferentiableAt ℝ B z.1)
    (hv : B z.1 z.2 z.2 < 0) :
    fderiv ℝ (freeLagrangian B m t) z w =
      (m / coordinateProperSpeed B z) * fderiv ℝ (quadraticLagrangian B t) z w := by
  have hb : HasFDerivAt (fun q : E × E => B q.1)
      ((fderiv ℝ B z.1).comp (fst ℝ E E)) z :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := E × E) (F := E) (G := E →L[ℝ] E →L[ℝ] ℝ)
      (f := Prod.fst) (f' := fst ℝ E E) (g := B) (g' := fderiv ℝ B z.1)
      z hB.hasFDerivAt (hasFDerivAt_fst (𝕜 := ℝ))
  have hd := ((((hb.clm_apply hasFDerivAt_snd).clm_apply hasFDerivAt_snd).neg).sqrt
    (ne_of_gt (neg_pos.mpr hv))).const_mul (-m)
  simp only [Pi.neg_apply] at hd
  change fderiv ℝ (fun q : E × E => -m * Real.sqrt (-B q.1 q.2 q.2)) z w = _
  rw [hd.fderiv, quadraticLagrangian_fderiv B t z w hB]
  change -m * ((1 / (2 * Real.sqrt (-B z.1 z.2 z.2))) *
    -(B z.1 z.2 w.2 + (B z.1 w.2 z.2 + (fderiv ℝ B z.1 w.1) z.2 z.2))) = _
  dsimp only [coordinateProperSpeed]
  ring

theorem free_force (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℝ)
    (q : ℝ → E) (t : ℝ) (hB : DifferentiableAt ℝ B (q t))
    (hv : B (q t) (deriv q t) (deriv q t) < 0) :
    Mechanics.force (freeLagrangian B m) q t =
      (m / coordinateProperSpeed B (q t, deriv q t)) •
        Mechanics.force (quadraticLagrangian B) q t := by
  ext w
  exact freeLagrangian_fderiv B m t _ (w, 0) hB hv

theorem free_momentum (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℝ)
    (q : ℝ → E) (t : ℝ) (hB : DifferentiableAt ℝ B (q t))
    (hv : B (q t) (deriv q t) (deriv q t) < 0) :
    Mechanics.momentum (freeLagrangian B m) q t =
      (m / coordinateProperSpeed B (q t, deriv q t)) •
        Mechanics.momentum (quadraticLagrangian B) q t := by
  ext w
  exact freeLagrangian_fderiv B m t _ (0, w) hB hv

/-- Differentiating the proper-speed factor is essential for a non-affine parameter. -/
theorem free_momentum_hasDerivAt (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℝ)
    {q : ℝ → E} {t s' : ℝ} (hB : ContDiffAt ℝ 2 B (q t)) (hq : ContDiffAt ℝ 2 q t)
    (hsym : ∀ x v w, B x v w = B x w v)
    (hv : B (q t) (deriv q t) (deriv q t) < 0)
    (hs : HasDerivAt (fun r => coordinateProperSpeed B (q r, deriv q r)) s' t) :
    HasDerivAt (Mechanics.momentum (freeLagrangian B m) q)
      ((-(m * s') / coordinateProperSpeed B (q t, deriv q t) ^ 2) •
          Mechanics.momentum (quadraticLagrangian B) q t +
        (m / coordinateProperSpeed B (q t, deriv q t)) •
          deriv (Mechanics.momentum (quadraticLagrangian B) q) t) t := by
  have hp : 0 < coordinateProperSpeed B (q t, deriv q t) :=
    Real.sqrt_pos.mpr (neg_pos.mpr hv)
  have he : Mechanics.momentum (freeLagrangian B m) q =ᶠ[𝓝 t]
      (fun r => (m / coordinateProperSpeed B (q r, deriv q r)) •
        Mechanics.momentum (quadraticLagrangian B) q r) := by
    filter_upwards [hq.continuousAt (hB.eventually (by norm_num)),
      hs.continuousAt.eventually (lt_mem_nhds hp)] with r hr hrp
    change ContDiffAt ℝ 2 B (q r) at hr
    have hrv : B (q r) (deriv q r) (deriv q r) < 0 := by
      exact neg_pos.mp (Real.sqrt_pos.mp hrp)
    exact free_momentum B m q r (hr.differentiableAt (by norm_num)) hrv
  have hp' := (quadratic_momentum_hasDerivAt B hB hq hsym).differentiableAt.hasDerivAt
  have hm := (hasDerivAt_const t m).div hs (ne_of_gt hp)
  have hd := (hm.smul hp').congr_of_eventuallyEq he
  simpa only [zero_mul, zero_sub, Pi.div_apply, add_comm] using hd

theorem free_eulerLagrange (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℝ)
    {q : ℝ → E} {t s' : ℝ} (hB : ContDiffAt ℝ 2 B (q t)) (hq : ContDiffAt ℝ 2 q t)
    (hsym : ∀ x v w, B x v w = B x w v)
    (hv : B (q t) (deriv q t) (deriv q t) < 0)
    (hs : HasDerivAt (fun r => coordinateProperSpeed B (q r, deriv q r)) s' t) (w : E) :
    Mechanics.eulerLagrange (freeLagrangian B m) q t w =
      (m / coordinateProperSpeed B (q t, deriv q t)) *
        Mechanics.eulerLagrange (quadraticLagrangian B) q t w +
      (m * s' / coordinateProperSpeed B (q t, deriv q t) ^ 2) *
        Mechanics.momentum (quadraticLagrangian B) q t w := by
  rw [Mechanics.eulerLagrange, sub_apply, free_force B m q t
    (hB.differentiableAt (by norm_num)) hv,
    (free_momentum_hasDerivAt B m hB hq hsym hv hs).deriv]
  simp only [Mechanics.eulerLagrange, sub_apply, add_apply, smul_apply, smul_eq_mul]
  ring

theorem isOpen_timelikeJets (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U) : IsOpen (timelikeJets B U) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hb : ContDiffAt ℝ 2 (fun y : ℝ × (E × E) => B y.2.1 y.2.2 y.2.2) z :=
    (((hB.contDiffAt (hU.mem_nhds hz.1)).comp z contDiffAt_snd.fst).clm_apply
      contDiffAt_snd.snd).clm_apply contDiffAt_snd.snd
  exact Filter.inter_mem ((hU.preimage (continuous_snd.fst)).mem_nhds hz.1)
    (hb.continuousAt.eventually (gt_mem_nhds hz.2))

theorem freeLagrangian_contDiffOn (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℝ)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U) :
    ContDiffOn ℝ 2 (Function.uncurry (freeLagrangian B m)) (timelikeJets B U) := by
  intro z hz
  have hb : ContDiffAt ℝ 2 (fun y : ℝ × (E × E) => B y.2.1 y.2.2 y.2.2) z :=
    (((hB.contDiffAt (hU.mem_nhds hz.1)).comp z contDiffAt_snd.fst).clm_apply
      contDiffAt_snd.snd).clm_apply contDiffAt_snd.snd
  exact (contDiffAt_const.mul (hb.neg.sqrt (ne_of_gt (neg_pos.mpr hz.2)))).contDiffWithinAt

variable [FiniteDimensional ℝ E]

/-- The actual action is differentiated on its open timelike domain. -/
theorem free_hasDerivAt_action (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℝ)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U)
    {q η : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hq : ContDiff ℝ 2 q)
    (hη : ContDiff ℝ 2 η) (hstay : ∀ t ∈ Icc a b, q t ∈ U)
    (hv : ∀ t ∈ Icc a b, B (q t) (deriv q t) (deriv q t) < 0) :
    HasDerivAt (fun ε => Mechanics.action a b (freeLagrangian B m)
      (Variational.perturb q η ε))
      (Mechanics.firstVariation a b (freeLagrangian B m) q η) 0 :=
  Mechanics.hasDerivAt_action_firstVariation_on hab hq hη
    (isOpen_timelikeJets B hU hB) (freeLagrangian_contDiffOn B m hU hB)
    (fun t ht => ⟨hstay t ht, hv t ht⟩)

theorem free_stationary_iff (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℝ)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U)
    {q : ℝ → E} {a b : ℝ} (hab : a < b) (hq : ContDiff ℝ 2 q)
    (hstay : ∀ t ∈ Icc a b, q t ∈ U)
    (hv : ∀ t ∈ Icc a b, B (q t) (deriv q t) (deriv q t) < 0) :
    Mechanics.Stationary a b (freeLagrangian B m) q ↔
      ∀ t ∈ Ioo a b, Mechanics.eulerLagrange (freeLagrangian B m) q t = 0 :=
  Mechanics.stationary_iff_eulerLagrange_on hab hq
    (isOpen_timelikeJets B hU hB) (freeLagrangian_contDiffOn B m hU hB)
    (fun t ht => ⟨hstay t ht, hv t ht⟩)

end ProjectAInos.GeneralRelativity
