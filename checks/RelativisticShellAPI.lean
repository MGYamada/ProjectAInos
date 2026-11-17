/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SpecialRelativity.FutureShell
import ProjectAinos.SpecialRelativity.Einbein

/-! Public consumers of the mass shell and of the massless particle: the future mass shell as a
graph over the space momenta with the action of the Lorentz group, its comparison with the
ideal of the future sheet, and the action with an auxiliary field for every mass.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Set
open scoped ContDiff
namespace ProjectAinos.SpecialRelativity.FutureShell

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {m : ℝ}

example : IsOpen (domain d m) :=
  isOpen_domain

example (hm : m ≠ 0) : domain d m = univ :=
  domain_eq_univ hm

example (π : Fin d → ℝ) : π ∈ domain d 0 ↔ π ≠ 0 :=
  mem_domain_zero π

example (m : ℝ) (π : Fin d → ℝ) : spaceMomentum (point m π) = π :=
  spaceMomentum_point m π

example (m : ℝ) (π : Fin d → ℝ) : time (point m π) = energy m π :=
  time_point m π

example (p : MinkowskiModel d) :
    (Fin.cons (time p) (spaceMomentum p) : MinkowskiModel d) = p :=
  cons_time_spaceMomentum p

example (p : MinkowskiModel d) :
    intervalQuadratic p = time p ^ 2 - ∑ i, spaceMomentum p i ^ 2 :=
  intervalQuadratic_eq p

example {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    energy m π ^ 2 = m ^ 2 + ∑ i, π i ^ 2 :=
  energy_sq hπ

example {π : Fin d → ℝ} (hπ : π ∈ domain d m) : 0 < energy m π :=
  energy_pos hπ

example {π : Fin d → ℝ} (hπ : π ∈ domain d m) : point m π ∈ shell d m :=
  point_mem hπ

example {p : MinkowskiModel d} (hp : p ∈ shell d m) :
    spaceMomentum p ∈ domain d m :=
  spaceMomentum_mem hp

example {p : MinkowskiModel d} (hp : p ∈ shell d m) :
    point m (spaceMomentum p) = p :=
  point_spaceMomentum hp

example : ContDiffOn ℝ ∞ (energy (d := d) m) (domain d m) :=
  contDiffOn_energy

example : ContDiffOn ℝ ∞ (point (d := d) m) (domain d m) :=
  contDiffOn_point

example : ContDiff ℝ ∞ (spaceMomentum (d := d)) :=
  contDiff_spaceMomentum

example {p : MinkowskiModel d} (hp : p ∈ shell d m) : FutureCausal p :=
  futureCausal_of_mem hp

example : (0 : MinkowskiModel d) ∉ shell d m :=
  zero_notMem_shell

example (p : MinkowskiModel d) :
    p ∈ shell d 0 ↔ Lightlike p ∧ FutureCausal p :=
  mem_shell_zero_iff p

example (L : orthochronousLorentzGroup d) {p : MinkowskiModel d}
    (hp : p ∈ shell d m) : L.val.val p ∈ shell d m :=
  lorentz_mem_shell L hp

example (L : orthochronousLorentzGroup d) {π : Fin d → ℝ}
    (hπ : π ∈ domain d m) : point m (action m L π) = L.val.val (point m π) :=
  point_action L hπ

example (L : orthochronousLorentzGroup d) {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    action m L π ∈ domain d m :=
  action_mem L hπ

example (m : ℝ) (π : Fin d → ℝ) : action m (1 : orthochronousLorentzGroup d) π = π :=
  action_one m π

example (L K : orthochronousLorentzGroup d) {π : Fin d → ℝ}
    (hπ : π ∈ domain d m) : action m (L * K) π = action m L (action m K π) :=
  action_mul L K hπ

example (L : orthochronousLorentzGroup d) :
    ContDiffOn ℝ ∞ (action m L) (domain d m) :=
  contDiffOn_action L

example (z : Fin (d + 1) ⊕ Fin (d + 1) → ℝ) :
    time (momentumVector z) = -z (Sum.inr 0) :=
  time_momentumVector z

example (z : Fin (d + 1) ⊕ Fin (d + 1) → ℝ) :
    spaceMomentum (momentumVector z) = fun i : Fin d => z (Sum.inr i.succ) :=
  spaceMomentum_momentumVector z

example (m : ℝ) (z : Fin (d + 1) ⊕ Fin (d + 1) → ℝ) :
    FreeSmoothRing.lift z (MassShell.futureShellFunction d m) =
      z (Sum.inr 0) + relEnergy m fun i : Fin d => z (Sum.inr i.succ) :=
  lift_futureShellFunction m z

example (hm : 0 < m)
    (z : Fin (d + 1) ⊕ Fin (d + 1) → ℝ) :
    FreeSmoothRing.lift z (MassShell.futureShellFunction d m) = 0 ↔
      momentumVector z ∈ shell d m :=
  lift_futureShellFunction_eq_zero_iff hm z

end ProjectAinos.SpecialRelativity.FutureShell

open Set MeasureTheory Topology
open scoped ContDiff
namespace ProjectAinos.SpecialRelativity.Einbein

open SmoothGeometry SmoothGeometry.Minkowski Mechanics

variable {d : ℕ} {m : ℝ}

example : IsOpen (positiveJets d) :=
  isOpen_positiveJets

example {n : ℕ∞ω} :
    ContDiff ℝ n (intervalQuadratic : MinkowskiModel d → ℝ) :=
  contDiff_intervalQuadratic

example (v : MinkowskiModel d) :
    HasFDerivAt (intervalQuadratic : MinkowskiModel d → ℝ) ((2 : ℝ) • pair v) v :=
  hasFDerivAt_intervalQuadratic v

example (m : ℝ) :
    ContDiffOn ℝ 2 (Function.uncurry (lagrangian d m)) (positiveJets d) :=
  lagrangian_contDiffOn m

example (m : ℝ)
    {z : (MinkowskiModel d × ℝ) × (MinkowskiModel d × ℝ)} (hz : z.1.2 ≠ 0) (t : ℝ) :
    HasFDerivAt (lagrangian d m t)
      ((1 / 2 * ((z.1.2 ^ 2)⁻¹ * intervalQuadratic z.2.1 - m ^ 2)) • eComponent d -
        (z.1.2)⁻¹ • (pair z.2.1).comp (vComponent d)) z :=
  hasFDerivAt_lagrangian m hz t

variable {x : ℝ → MinkowskiModel d} {e : ℝ → ℝ} {a b : ℝ}

example (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) (t : ℝ) :
    HasDerivAt (fun s => (x s, e s)) (deriv x t, deriv e t) t :=
  hasDerivAt_path hx he t

example (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) (t : ℝ) :
    deriv (fun s => (x s, e s)) t = (deriv x t, deriv e t) :=
  deriv_path hx he t

example (w δx : MinkowskiModel d) (δe : ℝ) :
    positionCovector d w (δx, δe) = pair w δx :=
  positionCovector_apply w δx δe

example (w : MinkowskiModel d) :
    positionCovector d w = 0 ↔ w = 0 :=
  positionCovector_eq_zero_iff w

example (m : ℝ) (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) {t : ℝ}
    (ht : e t ≠ 0) :
    force (lagrangian d m) (fun s => (x s, e s)) t =
      (1 / 2 * ((e t ^ 2)⁻¹ * intervalQuadratic (deriv x t) - m ^ 2)) •
        ContinuousLinearMap.snd ℝ (MinkowskiModel d) ℝ :=
  force_lagrangian m hx he ht

example (m : ℝ) (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) {t : ℝ}
    (ht : e t ≠ 0) :
    momentum (lagrangian d m) (fun s => (x s, e s)) t =
      -positionCovector d ((e t)⁻¹ • deriv x t) :=
  momentum_lagrangian m hx he ht

example (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) {t : ℝ}
    (ht : e t ≠ 0) : DifferentiableAt ℝ (fun s => (e s)⁻¹ • deriv x s) t :=
  differentiableAt_inv_smul_deriv hx he ht

example (m : ℝ) (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) {t : ℝ}
    (ht : e t ≠ 0) :
    eulerLagrange (lagrangian d m) (fun s => (x s, e s)) t =
      (1 / 2 * ((e t ^ 2)⁻¹ * intervalQuadratic (deriv x t) - m ^ 2)) •
          ContinuousLinearMap.snd ℝ (MinkowskiModel d) ℝ +
        positionCovector d (deriv (fun s => (e s)⁻¹ • deriv x s) t) :=
  eulerLagrange_lagrangian m hx he ht

example (m : ℝ) (hab : a < b) (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e)
    (hpos : ∀ t ∈ Icc a b, 0 < e t) :
    Stationary a b (lagrangian d m) (fun s => (x s, e s)) ↔
      ∀ t ∈ Ioo a b, intervalQuadratic (deriv x t) = e t ^ 2 * m ^ 2 ∧
        deriv (fun s => (e s)⁻¹ • deriv x s) t = 0 :=
  stationary_iff m hab hx he hpos

example (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d m) (fun s => (x s, e s))) {t : ℝ} (ht : t ∈ Icc a b) :
    intervalQuadratic (deriv x t) = e t ^ 2 * m ^ 2 :=
  intervalQuadratic_deriv_eq_of_stationary hab hx he hpos h ht

example (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d m) (fun s => (x s, e s))) {t : ℝ} (ht : t ∈ Icc a b) :
    (e t)⁻¹ • deriv x t = (e a)⁻¹ • deriv x a :=
  inv_smul_deriv_eq_of_stationary hab hx he hpos h ht

example (hm : 0 < m) {v : MinkowskiModel d} (hv : Timelike v) (t : ℝ)
    (y : MinkowskiModel d) (w : ℝ) :
    lagrangian d m t ((y, properSpeed v / m), (v, w)) = -m * properSpeed v :=
  lagrangian_eliminate hm hv t y w

example (hm : m ≠ 0) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d m) (fun s => (x s, e s))) {t : ℝ} (ht : t ∈ Icc a b) :
    Timelike (deriv x t) :=
  timelike_of_stationary hm hab hx he hpos h ht

example (hm : 0 < m) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d m) (fun s => (x s, e s))) {t : ℝ} (ht : t ∈ Icc a b) :
    properSpeed (deriv x t) = e t * m :=
  properSpeed_deriv_eq_of_stationary hm hab hx he hpos h ht

example (hm : 0 < m) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d m) (fun s => (x s, e s))) {t : ℝ} (ht : t ∈ Icc a b) :
    fourVelocity (deriv x t) = fourVelocity (deriv x a) :=
  fourVelocity_eq_of_stationary hm hab hx he hpos h ht

example (hm : 0 < m) (hab : a < b) {x : ℝ → Spacetime}
    (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian 3 m) (fun s => (x s, e s))) :
    Stationary a b (freeLagrangian m) x :=
  free_stationary_of_stationary hm hab hx he hpos h

example (hm : 0 < m) (hab : a < b) {x : ℝ → Spacetime}
    (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) (hv : ∀ t ∈ Icc a b, Timelike (deriv x t))
    (hrel : ∀ t ∈ Icc a b, e t = properSpeed (deriv x t) / m)
    (h : Stationary a b (freeLagrangian m) x) :
    Stationary a b (lagrangian 3 m) (fun s => (x s, e s)) :=
  stationary_of_free_stationary hm hab hx he hv hrel h

example (hab : a < b) (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e)
    (hpos : ∀ t ∈ Icc a b, 0 < e t) :
    Stationary a b (lagrangian d 0) (fun s => (x s, e s)) ↔
      ∀ t ∈ Ioo a b, intervalQuadratic (deriv x t) = 0 ∧
        deriv (fun s => (e s)⁻¹ • deriv x s) t = 0 :=
  stationary_massless_iff hab hx he hpos

example (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d 0) (fun s => (x s, e s))) :
    intervalQuadratic ((e a)⁻¹ • deriv x a) = 0 ∧
      ∀ t ∈ Icc a b, deriv x t = e t • ((e a)⁻¹ • deriv x a) :=
  deriv_eq_smul_of_stationary_massless hab hx he hpos h

example (m : ℝ) {c ε : ℝ} (hc : c ≠ 0) (hε : ε ≠ 0) (s t : ℝ)
    (y y' v : MinkowskiModel d) (w w' : ℝ) :
    lagrangian d m s ((y, ε * c), (c • v, w)) = c * lagrangian d m t ((y', ε), (v, w')) :=
  lagrangian_reparametrize m hc hε s t y y' v w w'

example (m : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hfne : ∀ s ∈ uIcc a b, deriv f s ≠ 0)
    (hene : ∀ s ∈ uIcc a b, e (f s) ≠ 0) :
    action a b (lagrangian d m) (fun s => (x (f s), e (f s) * deriv f s)) =
      action (f a) (f b) (lagrangian d m) (fun t => (x t, e t)) :=
  action_reparametrize m hf hx he hfne hene

end ProjectAinos.SpecialRelativity.Einbein
