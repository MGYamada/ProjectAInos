/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SpecialRelativity.MassShellReduction

/-! Public consumers of the algebraic layer of relativistic particle mechanics: the
coordinate-time Hamiltonian of a free particle with its trajectories and its flow, the Poincaré
algebra of the orbital charges and its family in `1/c`, and the mass shell as a coisotropic
ideal with the reduction of its future sheet.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Set MeasureTheory

namespace ProjectAinos.SpecialRelativity.FreeParticle

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {d : ℕ} {m : ℝ}

example (hm : m ≠ 0) (i : Fin d) :
    partialDerivation (Sum.inr i) (hamiltonian d m) = velocity d m i :=
  partialDerivation_inr_hamiltonian hm i

example (hm : m ≠ 0) (i : Fin d) :
    partialDerivation (Sum.inl i) (hamiltonian d m) = 0 :=
  partialDerivation_inl_hamiltonian hm i

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (q i) (hamiltonian d m) = velocity d m i :=
  canonical_q_hamiltonian hm i

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (p i) (hamiltonian d m) = 0 :=
  canonical_p_hamiltonian hm i

example (hm : m ≠ 0) :
    hamiltonian d m * hamiltonian d m =
      algebraMap ℝ (PhaseSpace (Fin d)) (m ^ 2) + ∑ i, p i * p i :=
  hamiltonian_mul_self hm

example (hm : m ≠ 0) :
    ∑ i, velocity d m i * velocity d m i =
      1 - algebraMap ℝ (PhaseSpace (Fin d)) (m ^ 2) * (relEnergyInv m p * relEnergyInv m p) :=
  sum_velocity_mul_self hm

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).IsIntegral (hamiltonian d m) (p i) :=
  isIntegral_p hm i

example (hm : m ≠ 0) (i j : Fin d) :
    (canonical (Fin d)).IsIntegral (hamiltonian d m) (q i * p j - q j * p i) :=
  isIntegral_angularMomentum hm i j

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (hamiltonian d m * q i) (hamiltonian d m) = p i :=
  canonical_centreOfEnergy_hamiltonian hm i

example (z : Fin d ⊕ Fin d → ℝ) :
    FreeSmoothRing.lift z (hamiltonian d m) = relEnergy m fun i => z (Sum.inr i) :=
  lift_hamiltonian z

example (hm : 0 < m) (z : Fin d ⊕ Fin d → ℝ) :
    FreeSmoothRing.lift z (hamiltonian d m) = Real.sqrt (m ^ 2 + ∑ i, z (Sum.inr i) ^ 2) :=
  lift_hamiltonian_eq_sqrt hm z

example (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) (i : Fin d) :
    hamiltonianField (hamiltonian d m) z (Sum.inl i) =
      relEnergyInv m (fun j => z (Sum.inr j)) * z (Sum.inr i) :=
  hamiltonianField_inl hm z i

example (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) (i : Fin d) :
    hamiltonianField (hamiltonian d m) z (Sum.inr i) = 0 :=
  hamiltonianField_inr hm z i

example (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) :
    ∑ i, hamiltonianField (hamiltonian d m) z (Sum.inl i) ^ 2 < 1 :=
  sum_sq_hamiltonianField_lt_one hm z

example (hm : m ≠ 0) :
    flowDomain (hamiltonianField (hamiltonian d m)) = univ :=
  flowDomain_hamiltonianField hm

example (hm : m ≠ 0) (t : ℝ) :
    MeasurePreserving (fun z => flow (hamiltonianField (hamiltonian d m)) (t, z))
      volume volume :=
  measurePreserving_hamiltonianFlow hm t

example (hm : m ≠ 0) (c : Fin d ⊕ Fin d → TimeFunction) :
    IsTrajectory (canonical (Fin d)) (hamiltonian d m) c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) =
        relEnergyInv m (fun j => c (Sum.inr j)) * c (Sum.inr i)) ∧
      ∀ i, timeDerivative (c (Sum.inr i)) = 0 :=
  isTrajectory_iff hm c

example (hm : m ≠ 0) {c : Fin d ⊕ Fin d → TimeFunction}
    (h : IsTrajectory (canonical (Fin d)) (hamiltonian d m) c) (i : Fin d) (s t : Fin 1 → ℝ) :
    c (Sum.inr i) s = c (Sum.inr i) t :=
  momentum_eq_of_isTrajectory hm h i s t

example (m : ℝ) (q₀ p₀ : Fin d → ℝ) (t : ℝ) :
    realCurve (motion m q₀ p₀) t =
      Sum.elim (fun i => q₀ i + t * (relEnergyInv m p₀ * p₀ i)) p₀ :=
  realCurve_motion m q₀ p₀ t

example (m : ℝ) (q₀ p₀ : Fin d → ℝ) :
    realCurve (motion m q₀ p₀) 0 = Sum.elim q₀ p₀ :=
  realCurve_motion_zero m q₀ p₀

example (hm : m ≠ 0) (q₀ p₀ : Fin d → ℝ) :
    IsTrajectory (canonical (Fin d)) (hamiltonian d m) (motion m q₀ p₀) :=
  isTrajectory_motion hm q₀ p₀

example (hm : m ≠ 0) {c : Fin d ⊕ Fin d → TimeFunction}
    (h : IsTrajectory (canonical (Fin d)) (hamiltonian d m) c) (t : ℝ) :
    realCurve c t = realCurve (motion m (fun i => realCurve c 0 (Sum.inl i))
      fun i => realCurve c 0 (Sum.inr i)) t :=
  realCurve_eq_motion hm h t

example (hm : m ≠ 0) (t : ℝ) (q₀ p₀ : Fin d → ℝ) :
    flow (hamiltonianField (hamiltonian d m)) (t, Sum.elim q₀ p₀) =
      Sum.elim (fun i => q₀ i + t * (relEnergyInv m p₀ * p₀ i)) p₀ :=
  flow_hamiltonianField hm t q₀ p₀

end ProjectAinos.SpecialRelativity.FreeParticle

namespace ProjectAinos.SpecialRelativity.Poincare

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace SmoothGeometry

variable {d : ℕ} {m : ℝ}

example (σ : LorentzConvention) : (Minkowski.metricMatrix σ d).IsSymm :=
  Minkowski.metricMatrix_isSymm σ

example (σ : LorentzConvention) :
    Minkowski.metricMatrix σ d * Minkowski.metricMatrix σ d = 1 :=
  Minkowski.metricMatrix_mul_self σ

example (σ : LorentzConvention) (μ ν : Fin (d + 1)) :
    lorentzCharge σ d μ ν =
      lorentzSign σ μ • q μ * p ν - lorentzSign σ ν • q ν * p μ :=
  lorentzCharge_eq σ μ ν

example (σ : LorentzConvention) (μ ν : Fin (d + 1)) :
    lorentzCharge σ d μ ν = -lorentzCharge σ d ν μ :=
  lorentzCharge_antisymm σ μ ν

example (σ : LorentzConvention) (μ ν ρ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (lorentzCharge σ d μ ν) (p ρ) =
      algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d μ ρ) * p ν -
        algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d ν ρ) * p μ :=
  canonical_lorentzCharge_p σ μ ν ρ

example (σ : LorentzConvention) (μ ν ρ τ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (lorentzCharge σ d μ ν) (lorentzCharge σ d ρ τ) =
      algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d μ ρ) *
          lorentzCharge σ d ν τ -
        algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d ν ρ) *
          lorentzCharge σ d μ τ +
        algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d ν τ) *
          lorentzCharge σ d μ ρ -
        algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d μ τ) *
          lorentzCharge σ d ν ρ :=
  canonical_lorentzCharge_lorentzCharge σ μ ν ρ τ

example (σ : LorentzConvention) (μ ν : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (lorentzCharge σ d μ ν)
      (momentumQuadratic (Minkowski.metricMatrix σ d)) = 0 :=
  canonical_lorentzCharge_momentumQuadratic σ μ ν

example (i : Fin d) :
    loweredCoordinate (1 : Matrix (Fin d) (Fin d) ℝ) i = q i :=
  loweredCoordinate_one i

example (i j : Fin d) :
    angularMomentum d i j = q i * p j - q j * p i :=
  angularMomentum_eq i j

example (i j k : Fin d) :
    (canonical (Fin d)).bracket (angularMomentum d i j) (q k) =
      (if k = i then q j else 0) - if k = j then q i else 0 :=
  canonical_angularMomentum_q i j k

example (i j k : Fin d) :
    (canonical (Fin d)).bracket (angularMomentum d i j) (p k) =
      (if i = k then p j else 0) - if j = k then p i else 0 :=
  canonical_angularMomentum_p i j k

example (i j k l : Fin d) :
    (canonical (Fin d)).bracket (angularMomentum d i j) (angularMomentum d k l) =
      (if i = k then angularMomentum d j l else 0) -
          (if j = k then angularMomentum d i l else 0) +
        (if j = l then angularMomentum d i k else 0) -
        if i = l then angularMomentum d j k else 0 :=
  canonical_angularMomentum_angularMomentum i j k l

example (d : ℕ) (m : ℝ) : inertia d m 0 = algebraMap ℝ (PhaseSpace (Fin d)) m :=
  inertia_zero d m

example (d : ℕ) (m : ℝ) (i : Fin d) :
    boostCharge d m 0 i = algebraMap ℝ (PhaseSpace (Fin d)) m * q i :=
  boostCharge_zero d m i

example (d : ℕ) (m : ℝ) : inertia d m 1 = relEnergy m p :=
  inertia_one d m

example (hm : m ≠ 0) (ε : ℝ) : inertia d m ε * inertiaInv d m ε = 1 :=
  inertia_mul_inertiaInv hm ε

example (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    partialDerivation (Sum.inr i) (inertia d m ε) =
      algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * (inertiaInv d m ε * p i) :=
  partialDerivation_inr_inertia hm ε i

example (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    partialDerivation (Sum.inl i) (inertia d m ε) = 0 :=
  partialDerivation_inl_inertia hm ε i

example (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    (canonical (Fin d)).bracket (q i) (inertia d m ε) =
      algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * (inertiaInv d m ε * p i) :=
  canonical_q_inertia hm ε i

example (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    (canonical (Fin d)).bracket (p i) (inertia d m ε) = 0 :=
  canonical_p_inertia hm ε i

example (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    (canonical (Fin d)).bracket (inertia d m ε) (p i) = 0 :=
  canonical_inertia_p hm ε i

example (hm : m ≠ 0) (ε : ℝ) (i j : Fin d) :
    (canonical (Fin d)).bracket (boostCharge d m ε i) (p j) =
      if i = j then inertia d m ε else 0 :=
  canonical_boostCharge_p hm ε i j

example (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    (canonical (Fin d)).bracket (boostCharge d m ε i) (inertia d m ε) =
      algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * p i :=
  canonical_boostCharge_inertia hm ε i

example (hm : m ≠ 0) (ε : ℝ) (i j : Fin d) :
    (canonical (Fin d)).bracket (boostCharge d m ε i) (boostCharge d m ε j) =
      -(algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * angularMomentum d i j) :=
  canonical_boostCharge_boostCharge hm ε i j

example (hm : m ≠ 0) (ε : ℝ) (i j : Fin d) :
    (canonical (Fin d)).bracket (angularMomentum d i j) (inertia d m ε) = 0 :=
  canonical_angularMomentum_inertia hm ε i j

example (hm : m ≠ 0) (ε : ℝ) (i j k : Fin d) :
    (canonical (Fin d)).bracket (angularMomentum d i j) (boostCharge d m ε k) =
      (if k = i then boostCharge d m ε j else 0) - if k = j then boostCharge d m ε i else 0 :=
  canonical_angularMomentum_boostCharge hm ε i j k

end ProjectAinos.SpecialRelativity.Poincare

namespace ProjectAinos.SpecialRelativity.MassShell

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics SmoothGeometry

variable {d : ℕ} {m : ℝ}

example (σ : LorentzConvention) (d : ℕ) (m : ℝ) :
    (canonical (Fin (d + 1))).IsCoisotropic (shellIdeal σ d m) :=
  isCoisotropic_shellIdeal σ d m

example (σ : LorentzConvention) (m : ℝ) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (p μ) (shellFunction σ d m) = 0 :=
  bracket_p_shellFunction σ m μ

example (σ : LorentzConvention) (m : ℝ)
    (μ ν : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (Poincare.lorentzCharge σ d μ ν) (shellFunction σ d m) =
      0 :=
  bracket_lorentzCharge_shellFunction σ m μ ν

example (σ : LorentzConvention) (m : ℝ) (μ : Fin (d + 1)) :
    p μ ∈ (canonical (Fin (d + 1))).normalizer (shellIdeal σ d m) :=
  p_mem_normalizer_shellIdeal σ m μ

example (σ : LorentzConvention) (m : ℝ)
    (μ ν : Fin (d + 1)) :
    Poincare.lorentzCharge σ d μ ν ∈ (canonical (Fin (d + 1))).normalizer (shellIdeal σ d m) :=
  lorentzCharge_mem_normalizer_shellIdeal σ m μ ν

example (hm : m ≠ 0) : energy d m * energyInv d m = 1 :=
  energy_mul_energyInv hm

example (hm : m ≠ 0) :
    energy d m * energy d m =
      algebraMap ℝ (EventSpace d) (m ^ 2) + ∑ i : Fin d, p i.succ * p i.succ :=
  energy_mul_self hm

example :
    lorentzSign .timeNegative (0 : Fin (d + 1)) = -1 :=
  lorentzSign_timeNegative_zero

example (i : Fin d) :
    lorentzSign .timeNegative i.succ = 1 :=
  lorentzSign_timeNegative_succ i

example (hm : m ≠ 0) :
    shellFunction .timeNegative d m = (energy d m - p 0) * futureShellFunction d m :=
  shellFunction_eq hm

example (hm : m ≠ 0) :
    shellIdeal .timeNegative d m ≤ futureShellIdeal d m :=
  shellIdeal_le_futureShellIdeal hm

example (d : ℕ) (m : ℝ) :
    (canonical (Fin (d + 1))).IsCoisotropic (futureShellIdeal d m) :=
  isCoisotropic_futureShellIdeal d m

example (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).normalizer (shellIdeal .timeNegative d m) ≤
      (canonical (Fin (d + 1))).normalizer (futureShellIdeal d m) :=
  normalizer_shellIdeal_le hm

example (hm : m ≠ 0) (μ : Fin (d + 1)) :
    p μ ∈ (canonical (Fin (d + 1))).normalizer (futureShellIdeal d m) :=
  p_mem_normalizer_futureShellIdeal hm μ

example (hm : m ≠ 0) (μ ν : Fin (d + 1)) :
    Poincare.lorentzCharge .timeNegative d μ ν ∈
      (canonical (Fin (d + 1))).normalizer (futureShellIdeal d m) :=
  lorentzCharge_mem_normalizer_futureShellIdeal hm μ ν

example (hm : m ≠ 0) (h : EventSpace d) :
    (canonical (Fin (d + 1))).bracket (energy d m) h =
      energyInv d m * ∑ j : Fin d, p j.succ * (canonical (Fin (d + 1))).bracket (p j.succ) h :=
  bracket_energy hm h

example (hm : m ≠ 0) (h : EventSpace d) :
    (canonical (Fin (d + 1))).bracket (energyInv d m) h =
      -(energyInv d m * energyInv d m * energyInv d m *
        ∑ j : Fin d, p j.succ * (canonical (Fin (d + 1))).bracket (p j.succ) h) :=
  bracket_energyInv hm h

example (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (energy d m) (q 0) = 0 :=
  bracket_energy_q_zero hm

example (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (energyInv d m) (q 0) = 0 :=
  bracket_energyInv_q_zero hm

example (hm : m ≠ 0) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (energy d m) (p μ) = 0 :=
  bracket_energy_p hm μ

example (hm : m ≠ 0) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (energyInv d m) (p μ) = 0 :=
  bracket_energyInv_p hm μ

example (hm : m ≠ 0) (k : Fin d) :
    (canonical (Fin (d + 1))).bracket (energy d m) (q k.succ) = -velocity d m k :=
  bracket_energy_q_succ hm k

example (hm : m ≠ 0) (k : Fin d) :
    (canonical (Fin (d + 1))).bracket (energyInv d m) (q k.succ) =
      energyInv d m * energyInv d m * energyInv d m * p k.succ :=
  bracket_energyInv_q_succ hm k

example (hm : m ≠ 0) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (p μ) (energy d m) = 0 :=
  bracket_p_energy hm μ

example (hm : m ≠ 0) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (p μ) (energyInv d m) = 0 :=
  bracket_p_energyInv hm μ

example (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (q 0) (energy d m) = 0 :=
  bracket_q_zero_energy hm

example (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (q 0) (energyInv d m) = 0 :=
  bracket_q_zero_energyInv hm

example (hm : m ≠ 0) (k : Fin d) :
    (canonical (Fin (d + 1))).bracket (q k.succ) (energy d m) = velocity d m k :=
  bracket_q_succ_energy hm k

example (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (energy d m) (energyInv d m) = 0 :=
  bracket_energy_energyInv hm

example (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (energyInv d m) (energy d m) = 0 :=
  bracket_energyInv_energy hm

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (q 0) = 0 :=
  bracket_velocity_q_zero hm i

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (q 0) (velocity d m i) = 0 :=
  bracket_q_zero_velocity hm i

example (hm : m ≠ 0) (i : Fin d) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (p μ) = 0 :=
  bracket_velocity_p hm i μ

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (energy d m) = 0 :=
  bracket_velocity_energy hm i

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (energyInv d m) = 0 :=
  bracket_velocity_energyInv hm i

example (hm : m ≠ 0) (i j : Fin d) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (velocity d m j) = 0 :=
  bracket_velocity_velocity hm i j

example (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (q k.succ) =
      energyInv d m * energyInv d m * energyInv d m * p i.succ * p k.succ -
        if i = k then energyInv d m else 0 :=
  bracket_velocity_q_succ hm i k

example (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (q i.succ) (velocity d m k) =
      (if k = i then energyInv d m else 0) -
        energyInv d m * energyInv d m * energyInv d m * p k.succ * p i.succ :=
  bracket_q_succ_velocity hm i k

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (q 0) = 0 :=
  bracket_initialPosition_q_zero hm i

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (p 0) = -velocity d m i :=
  bracket_initialPosition_p_zero hm i

example (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (p k.succ) =
      if i = k then 1 else 0 :=
  bracket_initialPosition_p_succ hm i k

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (energy d m) = velocity d m i :=
  bracket_initialPosition_energy hm i

example (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (velocity d m k) =
      (if k = i then energyInv d m else 0) -
        energyInv d m * energyInv d m * energyInv d m * p k.succ * p i.succ :=
  bracket_initialPosition_velocity hm i k

example (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (q k.succ) =
      q 0 * ((if i = k then energyInv d m else 0) -
        energyInv d m * energyInv d m * energyInv d m * p i.succ * p k.succ) :=
  bracket_initialPosition_q_succ hm i k

example (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (initialPosition d m k) = 0 :=
  bracket_initialPosition_initialPosition hm i k

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (futureShellFunction d m) = 0 :=
  bracket_initialPosition_futureShellFunction hm i

example (m : ℝ) (i : Fin d) :
    toShellCoordinates d m (q (Sum.inl i)) = initialPosition d m i :=
  toShellCoordinates_q_inl m i

example (d : ℕ) (m : ℝ) :
    toShellCoordinates d m (q (Sum.inr ())) = q 0 :=
  toShellCoordinates_q_inr d m

example (m : ℝ) (i : Fin d) :
    toShellCoordinates d m (p (Sum.inl i)) = p i.succ :=
  toShellCoordinates_p_inl m i

example (d : ℕ) (m : ℝ) :
    toShellCoordinates d m (p (Sum.inr ())) = futureShellFunction d m :=
  toShellCoordinates_p_inr d m

example (d : ℕ) (m : ℝ) :
    ofShellCoordinates d m (q 0) = q (Sum.inr ()) :=
  ofShellCoordinates_q_zero d m

example (m : ℝ) (i : Fin d) :
    ofShellCoordinates d m (q i.succ) = q (Sum.inl i) + q (Sum.inr ()) *
      (relEnergyInv m (fun j : Fin d => p (Sum.inl j)) * p (Sum.inl i)) :=
  ofShellCoordinates_q_succ m i

example (d : ℕ) (m : ℝ) :
    ofShellCoordinates d m (p 0) =
      p (Sum.inr ()) - relEnergy m fun j : Fin d => p (Sum.inl j) :=
  ofShellCoordinates_p_zero d m

example (m : ℝ) (i : Fin d) :
    ofShellCoordinates d m (p i.succ) = p (Sum.inl i) :=
  ofShellCoordinates_p_succ m i

example (m : ℝ) (f : EventSpace d) :
    toShellCoordinates d m (ofShellCoordinates d m f) = f :=
  toShellCoordinates_ofShellCoordinates m f

example (m : ℝ) (g : PhaseSpace (Fin d ⊕ Unit)) :
    ofShellCoordinates d m (toShellCoordinates d m g) = g :=
  ofShellCoordinates_toShellCoordinates m g

example (hm : m ≠ 0) :
    IsPoissonHom (canonical (Fin d ⊕ Unit)).toAlmostPoissonStructure
      (canonical (Fin (d + 1))).toAlmostPoissonStructure (toShellCoordinates d m) :=
  isPoissonHom_toShellCoordinates hm

example (d : ℕ) (m : ℝ) :
    futureShellIdeal d m = Ideal.span (Set.range fun k : Unit =>
      toShellCoordinates d m (CyclicReduction.momentumEquation (Fin d) (fun _ => 0) k)) :=
  futureShellIdeal_eq d m

example (hm : m ≠ 0) :
    Function.Bijective (reductionHom d hm) :=
  reductionHom_bijective hm

example (hm : m ≠ 0) :
    IsPoissonHom (canonical (Fin d)).toAlmostPoissonStructure
      ((canonical (Fin (d + 1))).reduction (futureShellIdeal d m)).toAlmostPoissonStructure
      (reductionHom d hm) :=
  isPoissonHom_reductionHom hm

example (hm : m ≠ 0) {f : EventSpace d}
    (hf : f ∈ (canonical (Fin (d + 1))).normalizer (futureShellIdeal d m)) :
    reductionHom d hm (initialData d m f) =
      (canonical (Fin (d + 1))).reductionMap (futureShellIdeal d m) ⟨f, hf⟩ :=
  reductionHom_initialData hm hf

example (d : ℕ) (m : ℝ) : initialData d m (q 0) = 0 :=
  initialData_q_zero d m

example (m : ℝ) (i : Fin d) : initialData d m (p i.succ) = p i :=
  initialData_p_succ m i

example (d : ℕ) (m : ℝ) :
    initialData d m (p 0) = -FreeParticle.hamiltonian d m :=
  initialData_p_zero d m

example (m : ℝ) (i : Fin d) : initialData d m (q i.succ) = q i :=
  initialData_q_succ m i

example (m : ℝ) (i : Fin d) :
    initialData d m (Poincare.lorentzCharge .timeNegative d 0 i.succ) =
      FreeParticle.hamiltonian d m * q i :=
  initialData_lorentzCharge_zero_succ m i

example (m : ℝ) (i j : Fin d) :
    initialData d m (Poincare.lorentzCharge .timeNegative d i.succ j.succ) =
      Poincare.angularMomentum d i j :=
  initialData_lorentzCharge_succ_succ m i j

end ProjectAinos.SpecialRelativity.MassShell
