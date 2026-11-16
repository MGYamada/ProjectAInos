/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.Mechanics.Poisson.LiouvilleFlow

/-! Typed contracts for Hamiltonian vector fields in the analytic model: the
elements of a free C∞-ring as differentiable functions, trajectories as
solutions of a differential equation, Liouville's theorem for the flow of a
Hamiltonian, and the flows that are defined for all times. These examples use
default elaborator options. -/

open ProjectAInos ProjectAInos.Mechanics
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.SmoothRing
open ProjectAInos.SmoothAlgebra.FreeSmoothRing ProjectAInos.SmoothAlgebra.PhaseSpace
open ProjectAInos.SmoothGeometry ProjectAInos.SmoothGeometry.LinearODE
open ProjectAInos.SmoothGeometry.NonlinearODE
open Set MeasureTheory
open scoped ContDiff

noncomputable section

section FreeCalculus

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

example (s : FreeSmoothRing κ) :
    ContDiff ℝ ∞ (s.val : (κ → ℝ) → ℝ) :=
  contDiff_val s

example (s : FreeSmoothRing κ) (z w : κ → ℝ) :
    fderiv ℝ (s.val : (κ → ℝ) → ℝ) z w = ∑ a, (partialDerivation a s).val z * w a :=
  fderiv_val_apply s z w

example (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)) (z : κ → ℝ) (a : κ) :
    realField D z a = (D (generator a)).val z := rfl

example (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ))
    (z : κ → ℝ) (a : κ) :
    realField D z a = (D (generator a)).val z :=
  realField_apply D z a

example (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)) :
    ContDiff ℝ ∞ (realField D) :=
  contDiff_realField D

example (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ))
    (z w : κ → ℝ) (a : κ) :
    fderiv ℝ (realField D) z w a =
      ∑ b, (partialDerivation b (D (generator a))).val z * w b :=
  fderiv_realField_apply D z w a


end FreeCalculus

section RealCurve

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

example (c : κ → TimeFunction) (t : ℝ) (a : κ) : realCurve c t a = c a fun _ => t := rfl

example (c : κ → TimeFunction) (t : ℝ) (a : κ) :
    realCurve c t a = c a fun _ => t :=
  realCurve_apply c t a

example (c : κ → TimeFunction) (s : FreeSmoothRing κ) (t : ℝ) :
    FreeSmoothRing.lift c s (fun _ => t) = s.val (realCurve c t) :=
  lift_apply_const c s t

example (c : κ → TimeFunction) (t : ℝ) :
    HasDerivAt (realCurve c) (fun a => timeDerivative (c a) fun _ => t) t :=
  hasDerivAt_realCurve c t

example (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)) (c : κ → TimeFunction) :
    IsIntegralCurve D c ↔ ∀ t, HasDerivAt (realCurve c) (realField D (realCurve c t)) t :=
  isIntegralCurve_iff_hasDerivAt D c

example (π : PoissonStructure (FreeSmoothRing κ))
    (H : FreeSmoothRing κ) (c : κ → TimeFunction) :
    IsTrajectory π H c ↔
      ∀ t, HasDerivAt (realCurve c) (realField (π.hamiltonian H) (realCurve c t)) t :=
  isTrajectory_iff_hasDerivAt π H c

example (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)) (z : κ → ℝ) :
    traceCLM (fderiv ℝ (realField D) z) = (divergence D).val z :=
  traceCLM_fderiv_realField D z

end RealCurve

section Canonical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

example (H : PhaseSpace ι) :
    hamiltonianField H = realField ((PhaseSpace.canonical ι).hamiltonian H) := rfl

example (H : PhaseSpace ι) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField H z (Sum.inl i) = (partialDerivation (Sum.inr i) H).val z :=
  hamiltonianField_inl H z i

example (H : PhaseSpace ι) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField H z (Sum.inr i) = -(partialDerivation (Sum.inl i) H).val z :=
  hamiltonianField_inr H z i

example (H : PhaseSpace ι) :
    ContDiff ℝ ∞ (hamiltonianField H) :=
  contDiff_hamiltonianField H

example (H : PhaseSpace ι)
    (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (PhaseSpace.canonical ι) H c ↔
      ∀ t, HasDerivAt (realCurve c) (hamiltonianField H (realCurve c t)) t :=
  isTrajectory_canonical_iff_hasDerivAt H c

example (H : PhaseSpace ι) (z : ι ⊕ ι → ℝ) :
    traceCLM (fderiv ℝ (hamiltonianField H) z) = 0 :=
  traceCLM_fderiv_hamiltonianField H z

example (H : PhaseSpace ι) {t : ℝ} {A : Set (ι ⊕ ι → ℝ)}
    (hA : MeasurableSet A) (hAD : ∀ z ∈ A, (t, z) ∈ flowDomain (hamiltonianField H)) :
    volume ((fun z => flow (hamiltonianField H) (t, z)) '' A) = volume A :=
  volume_image_hamiltonianFlow H hA hAD

example (H : PhaseSpace ι)
    (hc : flowDomain (hamiltonianField H) = univ) (t : ℝ) :
    MeasurePreserving (fun z => flow (hamiltonianField H) (t, z)) volume volume :=
  measurePreserving_hamiltonianFlow H hc t

example {H : PhaseSpace ι} {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (PhaseSpace.canonical ι) H c) (t : ℝ) :
    (t, realCurve c 0) ∈ flowDomain (hamiltonianField H) ∧
      flow (hamiltonianField H) (t, realCurve c 0) = realCurve c t :=
  IsTrajectory.flow_eq h t

example (H : PhaseSpace ι) (hc : flowDomain (hamiltonianField H) = univ)
    (z₀ : ι ⊕ ι → ℝ) :
    ∃ c : ι ⊕ ι → TimeFunction, IsTrajectory (PhaseSpace.canonical ι) H c ∧
      realCurve c 0 = z₀ :=
  exists_isTrajectory H hc z₀


end Canonical

section Examples

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

example (c : ι → ℝ) (z : ι ⊕ ι → ℝ) (i : ι) (a : ι ⊕ ι) :
    |c i * z a| ≤ (∑ j, |c j|) * ‖z‖ :=
  abs_mul_le_sum_mul_norm c z i a

section Oscillator

open Oscillator

example (m : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (hamiltonian m k) z (Sum.inl i) = (m i)⁻¹ * z (Sum.inr i) :=
  Oscillator.hamiltonianField_inl m k z i

example (m : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (hamiltonian m k) z (Sum.inr i) = -(k * z (Sum.inl i)) :=
  Oscillator.hamiltonianField_inr m k z i

example (m : ι → ℝ) (k : ℝ) :
    flowDomain (hamiltonianField (hamiltonian m k)) = univ :=
  Oscillator.flowDomain_hamiltonianField m k

example (m : ι → ℝ) (k : ℝ) (t : ℝ) :
    MeasurePreserving (fun z => flow (hamiltonianField (hamiltonian m k)) (t, z))
      volume volume :=
  Oscillator.measurePreserving_hamiltonianFlow m k t

example (m a : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    realField (dissipativeField (Matrix.diagonal a) (hamiltonian m k)) z (Sum.inl i) =
      (m i)⁻¹ * z (Sum.inr i) :=
  Oscillator.realField_dissipativeField_inl m a k z i

example (m a : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    realField (dissipativeField (Matrix.diagonal a) (hamiltonian m k)) z (Sum.inr i) =
      -(k * z (Sum.inl i)) - a i * ((m i)⁻¹ * z (Sum.inr i)) :=
  Oscillator.realField_dissipativeField_inr m a k z i

example (m a : ι → ℝ) (k : ℝ) :
    flowDomain (realField (dissipativeField (Matrix.diagonal a) (hamiltonian m k))) = univ :=
  Oscillator.flowDomain_dissipativeField m a k

example (m a : ι → ℝ) (k : ℝ) (t : ℝ) {A : Set (ι ⊕ ι → ℝ)}
    (hA : MeasurableSet A) :
    volume ((fun z => flow (realField (dissipativeField (Matrix.diagonal a) (hamiltonian m k)))
        (t, z)) '' A) =
      ENNReal.ofReal (Real.exp (-(∑ i, a i * (m i)⁻¹) * t)) * volume A :=
  Oscillator.volume_image_dissipativeFlow m a k t hA

end Oscillator

section Pendulum

open Pendulum

example (m : ι → ℝ) (k : ℝ) :
    Pendulum.hamiltonian m k =
      kineticEnergy m - algebraMap ℝ (PhaseSpace ι) k * ∑ i, ringCos (q i) := rfl

example (m : ι → ℝ) (k : ℝ) (j : ι) :
    partialDerivation (Sum.inr j) (hamiltonian m k) =
      algebraMap ℝ (PhaseSpace ι) (m j)⁻¹ * p j :=
  Pendulum.partialDerivation_inr_hamiltonian m k j

example (m : ι → ℝ) (k : ℝ) (j : ι) :
    partialDerivation (Sum.inl j) (hamiltonian m k) =
      algebraMap ℝ (PhaseSpace ι) k * ringSin (q j) :=
  Pendulum.partialDerivation_inl_hamiltonian m k j

example (m : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (hamiltonian m k) z (Sum.inl i) = (m i)⁻¹ * z (Sum.inr i) :=
  Pendulum.hamiltonianField_inl m k z i

example (m : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (hamiltonian m k) z (Sum.inr i) = -(k * Real.sin (z (Sum.inl i))) :=
  Pendulum.hamiltonianField_inr m k z i

example (m : ι → ℝ) (k : ℝ) :
    flowDomain (hamiltonianField (hamiltonian m k)) = univ :=
  Pendulum.flowDomain_hamiltonianField m k

example (m : ι → ℝ) (k : ℝ) (t : ℝ) :
    MeasurePreserving (fun z => flow (hamiltonianField (hamiltonian m k)) (t, z))
      volume volume :=
  Pendulum.measurePreserving_hamiltonianFlow m k t

example (m : ι → ℝ) (k : ℝ) (z₀ : ι ⊕ ι → ℝ) :
    ∃ c : ι ⊕ ι → TimeFunction, IsTrajectory (canonical ι) (hamiltonian m k) c ∧
      realCurve c 0 = z₀ :=
  Pendulum.exists_isTrajectory m k z₀

end Pendulum

end Examples
