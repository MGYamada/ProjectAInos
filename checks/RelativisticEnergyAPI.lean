/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothAlgebra.RelEnergy
import ProjectAinos.SmoothAlgebra.Poisson.LinearMomentum
import ProjectAinos.SmoothAlgebra.Poisson.OrbitalCharge

/-! Public consumers of the shared algebra of the relativistic energy and of the charges of
affine maps: the operations `√(1 + Σ wᵢ²)` and its inverse, the energy `relEnergy` in a
C-infinity ring with its two relations and its derivative, the momentum functions of
translations and of linear maps, and the orbital charges of a constant metric.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

namespace ProjectAinos.SmoothAlgebra

open SmoothRing
open scoped ContDiff

section Operations

variable {d : ℕ}

example (w : Fin d → ℝ) : 0 < 1 + ∑ i, w i ^ 2 := SmoothOperation.one_add_sum_sq_pos w

example : ContDiff ℝ ∞ (fun w : Fin d → ℝ => 1 + ∑ i, w i ^ 2) :=
  SmoothOperation.contDiff_one_add_sum_sq

example (w : Fin d → ℝ) :
    SmoothOperation.lorentzFactor d w = Real.sqrt (1 + ∑ i, w i ^ 2) :=
  SmoothOperation.lorentzFactor_apply w

example (w : Fin d → ℝ) :
    SmoothOperation.invLorentzFactor d w = (Real.sqrt (1 + ∑ i, w i ^ 2))⁻¹ :=
  SmoothOperation.invLorentzFactor_apply w

example (w : Fin d → ℝ) : 0 < SmoothOperation.lorentzFactor d w :=
  SmoothOperation.lorentzFactor_pos w

example : SmoothOperation.lorentzFactor d * SmoothOperation.lorentzFactor d =
    1 + ∑ i, SmoothOperation.proj i * SmoothOperation.proj i :=
  SmoothOperation.lorentzFactor_mul_self

example : SmoothOperation.lorentzFactor d * SmoothOperation.invLorentzFactor d = 1 :=
  SmoothOperation.lorentzFactor_mul_invLorentzFactor

example (i : Fin d) :
    SmoothOperation.partialDeriv i (SmoothOperation.lorentzFactor d) =
      SmoothOperation.invLorentzFactor d * SmoothOperation.proj i :=
  SmoothOperation.partialDeriv_lorentzFactor i

end Operations

section RelEnergy

variable {A B : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [CommRing B] [Algebra ℝ B] [SmoothRing B] {d : ℕ}

example {m : ℝ} (hm : m ≠ 0) : algebraMap ℝ A m * algebraMap ℝ A m⁻¹ = 1 :=
  algebraMap_mul_algebraMap_inv hm

example (w : Fin d → A) :
    lorentzFactor w * lorentzFactor w = 1 + ∑ i, w i * w i :=
  lorentzFactor_mul_self w

example (w : Fin d → A) :
    lorentzFactor w * invLorentzFactor w = 1 :=
  lorentzFactor_mul_invLorentzFactor w

example {n : ℕ} (f : SmoothOperation n) (a : Fin n → ℝ) :
    op f (fun i => algebraMap ℝ A (a i)) = algebraMap ℝ A (f a) :=
  SmoothRing.op_algebraMap f a

example : lorentzFactor (fun _ : Fin d => (0 : A)) = 1 :=
  lorentzFactor_zero

example (D : SmoothDerivation A A) (w : Fin d → A) :
    D (lorentzFactor w) = invLorentzFactor w * ∑ i, w i * D (w i) :=
  SmoothDerivation.apply_lorentzFactor D w

example (φ : SmoothRingHom A B) (w : Fin d → A) :
    φ (lorentzFactor w) = lorentzFactor fun i => φ (w i) :=
  SmoothRingHom.map_lorentzFactor φ w

example (φ : SmoothRingHom A B) (w : Fin d → A) :
    φ (invLorentzFactor w) = invLorentzFactor fun i => φ (w i) :=
  SmoothRingHom.map_invLorentzFactor φ w

example (m : ℝ) : relEnergy m (fun _ : Fin d => (0 : A)) = algebraMap ℝ A m :=
  relEnergy_zero m

example {m : ℝ} (hm : m ≠ 0) (π : Fin d → A) :
    relEnergy m π * relEnergy m π = algebraMap ℝ A (m ^ 2) + ∑ i, π i * π i :=
  relEnergy_mul_self hm π

example {m : ℝ} (hm : m ≠ 0) (π : Fin d → A) :
    relEnergy m π * relEnergyInv m π = 1 :=
  relEnergy_mul_relEnergyInv hm π

example {m : ℝ} (hm : m ≠ 0) (D : SmoothDerivation A A)
    (π : Fin d → A) : D (relEnergy m π) = relEnergyInv m π * ∑ i, π i * D (π i) :=
  SmoothDerivation.apply_relEnergy hm D π

example {m : ℝ} (hm : m ≠ 0) (D : SmoothDerivation A A)
    (π : Fin d → A) : D (relEnergyInv m π) =
      -(relEnergyInv m π * relEnergyInv m π * relEnergyInv m π * ∑ i, π i * D (π i)) :=
  SmoothDerivation.apply_relEnergyInv hm D π

example {m : ℝ} (hm : m ≠ 0) (π : Fin d → A) :
    ∑ i, relEnergyInv m π * π i * (relEnergyInv m π * π i) =
      1 - algebraMap ℝ A (m ^ 2) * (relEnergyInv m π * relEnergyInv m π) :=
  sum_relEnergyInv_mul_sq hm π

example {m : ℝ} (hm : 0 < m) (π : Fin d → ℝ) :
    relEnergy m π = Real.sqrt (m ^ 2 + ∑ i, π i ^ 2) :=
  relEnergy_real hm π

example {m : ℝ} (hm : 0 < m) (π : Fin d → ℝ) : 0 < relEnergy m π :=
  relEnergy_real_pos hm π

example {m : ℝ} (hm : m ≠ 0) (π : Fin d → ℝ) :
    relEnergyInv m π = (relEnergy m π)⁻¹ :=
  relEnergyInv_real hm π

example {m : ℝ} (hm : m ≠ 0) (π : Fin d → ℝ) :
    ∑ i, (relEnergyInv m π * π i) ^ 2 < 1 :=
  sum_sq_relEnergyInv_mul_lt_one hm π

example {m : ℝ} (hm : m ≠ 0) (π : Fin d → ℝ) (i : Fin d) :
    |relEnergyInv m π * π i| < 1 :=
  abs_relEnergyInv_mul_lt_one hm π i

example (φ : SmoothRingHom A B) (m : ℝ) (π : Fin d → A) :
    φ (relEnergy m π) = relEnergy m fun i => φ (π i) :=
  SmoothRingHom.map_relEnergy φ m π

example (φ : SmoothRingHom A B) (m : ℝ) (π : Fin d → A) :
    φ (relEnergyInv m π) = relEnergyInv m fun i => φ (π i) :=
  SmoothRingHom.map_relEnergyInv φ m π

end RelEnergy

namespace PhaseSpace

open FreeSmoothRing

section LinearMomentum

variable {ι : Type*} [Fintype ι]

example (a b : ι → ℝ) :
    translationMomentum (a + b) = translationMomentum a + translationMomentum b :=
  translationMomentum_add a b

example (r : ℝ) (a : ι → ℝ) :
    translationMomentum (r • a) = r • translationMomentum a :=
  translationMomentum_smul r a

example (a b : ι → ℝ) :
    translationMomentum (a - b) = translationMomentum a - translationMomentum b :=
  translationMomentum_sub a b

example (A B : Matrix ι ι ℝ) :
    linearMomentum (A + B) = linearMomentum A + linearMomentum B :=
  linearMomentum_add A B

example (r : ℝ) (A : Matrix ι ι ℝ) :
    linearMomentum (r • A) = r • linearMomentum A :=
  linearMomentum_smul r A

example (A B : Matrix ι ι ℝ) :
    linearMomentum (A - B) = linearMomentum A - linearMomentum B :=
  linearMomentum_sub A B

variable [DecidableEq ι]

example (a : ι → ℝ) (ρ : ι) :
    (canonical ι).bracket (translationMomentum a) (q ρ) = -algebraMap ℝ (PhaseSpace ι) (a ρ) :=
  canonical_translationMomentum_q a ρ

example (a : ι → ℝ) (σ : ι) :
    (canonical ι).bracket (translationMomentum a) (p σ) = 0 :=
  canonical_translationMomentum_p a σ

example (a b : ι → ℝ) :
    (canonical ι).bracket (translationMomentum a) (translationMomentum b) = 0 :=
  canonical_translationMomentum_translationMomentum a b

example (A : Matrix ι ι ℝ) (ρ : ι) :
    (canonical ι).bracket (linearMomentum A) (q ρ) = -∑ μ, A μ ρ • q μ :=
  canonical_linearMomentum_q A ρ

example (A : Matrix ι ι ℝ) (σ : ι) :
    (canonical ι).bracket (linearMomentum A) (p σ) = ∑ ν, A σ ν • p ν :=
  canonical_linearMomentum_p A σ

example (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    (canonical ι).bracket (linearMomentum A) (translationMomentum a) =
      translationMomentum (Matrix.vecMul a A) :=
  canonical_linearMomentum_translationMomentum A a

example (A B : Matrix ι ι ℝ) :
    (canonical ι).bracket (linearMomentum A) (linearMomentum B) =
      linearMomentum (B * A - A * B) :=
  canonical_linearMomentum_linearMomentum A B

end LinearMomentum

section OrbitalCharge

variable {ι : Type*} [Fintype ι]

example (η : Matrix ι ι ℝ) (μ ν : ι) :
    orbitalCharge η μ ν = -orbitalCharge η ν μ :=
  orbitalCharge_antisymm η μ ν

example (η : Matrix ι ι ℝ) (μ : ι) : orbitalCharge η μ μ = 0 :=
  orbitalCharge_self η μ

variable [DecidableEq ι]

example (s : ι → ℝ) (μ : ι) :
    loweredCoordinate (Matrix.diagonal s) μ = s μ • q μ :=
  loweredCoordinate_diagonal s μ

example (s : ι → ℝ) :
    momentumQuadratic (Matrix.diagonal s) = ∑ σ, s σ • (p σ * p σ : PhaseSpace ι) :=
  momentumQuadratic_diagonal s

example (η : Matrix ι ι ℝ) (μ ν : ι) :
    (canonical ι).bracket (loweredCoordinate η μ) (p ν) =
      algebraMap ℝ (PhaseSpace ι) (η μ ν) :=
  canonical_loweredCoordinate_p η μ ν

example (η : Matrix ι ι ℝ) (ν μ : ι) :
    (canonical ι).bracket (p ν) (loweredCoordinate η μ) =
      -algebraMap ℝ (PhaseSpace ι) (η μ ν) :=
  canonical_p_loweredCoordinate η ν μ

example (η : Matrix ι ι ℝ) (μ ρ : ι) :
    (canonical ι).bracket (loweredCoordinate η μ) (q ρ) = 0 :=
  canonical_loweredCoordinate_q η μ ρ

example (η : Matrix ι ι ℝ) (μ ν : ι) :
    (canonical ι).bracket (loweredCoordinate η μ) (loweredCoordinate η ν) = 0 :=
  canonical_loweredCoordinate_loweredCoordinate η μ ν

example (η : Matrix ι ι ℝ) (μ ν ρ : ι) :
    (canonical ι).bracket (orbitalCharge η μ ν) (p ρ) =
      algebraMap ℝ (PhaseSpace ι) (η μ ρ) * p ν - algebraMap ℝ (PhaseSpace ι) (η ν ρ) * p μ :=
  canonical_orbitalCharge_p η μ ν ρ

example (η : Matrix ι ι ℝ) (μ ν ρ : ι) :
    (canonical ι).bracket (orbitalCharge η μ ν) (loweredCoordinate η ρ) =
      algebraMap ℝ (PhaseSpace ι) (η ρ μ) * loweredCoordinate η ν -
        algebraMap ℝ (PhaseSpace ι) (η ρ ν) * loweredCoordinate η μ :=
  canonical_orbitalCharge_loweredCoordinate η μ ν ρ

example {η : Matrix ι ι ℝ} (hη : η.IsSymm)
    (μ ν ρ σ : ι) :
    (canonical ι).bracket (orbitalCharge η μ ν) (orbitalCharge η ρ σ) =
      algebraMap ℝ (PhaseSpace ι) (η μ ρ) * orbitalCharge η ν σ -
        algebraMap ℝ (PhaseSpace ι) (η ν ρ) * orbitalCharge η μ σ +
        algebraMap ℝ (PhaseSpace ι) (η ν σ) * orbitalCharge η μ ρ -
        algebraMap ℝ (PhaseSpace ι) (η μ σ) * orbitalCharge η ν ρ :=
  canonical_orbitalCharge_orbitalCharge hη μ ν ρ σ

example (G : Matrix ι ι ℝ) (ν : ι) :
    (canonical ι).bracket (p ν) (momentumQuadratic G) = 0 :=
  canonical_p_momentumQuadratic G ν

example {η G : Matrix ι ι ℝ} (hη : η.IsSymm)
    (hG : η * G = 1) (μ : ι) :
    (canonical ι).bracket (loweredCoordinate η μ) (momentumQuadratic G) = 2 * p μ :=
  canonical_loweredCoordinate_momentumQuadratic hη hG μ

example {η G : Matrix ι ι ℝ} (hη : η.IsSymm)
    (hG : η * G = 1) (μ ν : ι) :
    (canonical ι).bracket (orbitalCharge η μ ν) (momentumQuadratic G) = 0 :=
  canonical_orbitalCharge_momentumQuadratic hη hG μ ν

end OrbitalCharge

end PhaseSpace

end ProjectAinos.SmoothAlgebra
