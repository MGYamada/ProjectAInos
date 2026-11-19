/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Hamiltonian
public import ProjectAinos.Mechanics.Poisson.CentralField
public import ProjectAinos.Mechanics.Poisson.InvariantTorus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Motion in the Coulomb field

Landau–Lifshitz, *The Classical Theory of Fields*, §39: a charge of mass `m` in the static
field of a fixed charge, with the potential energy `eφ = α/r`; the field attracts for `α < 0`.
The units have `c = 1`. The motion is planar, in the polar co-ordinates of
`Mechanics.CentralField` with `s = log r`, so the centre is excluded, and the Hamiltonian
`coulombHamiltonian m α = √(m² + p_r² + p_φ²/r²) + α/r` is an element of the free C-infinity
ring of `(s, φ, p_s, p_φ)`.

* Hamilton's equations: `canonical_s`, `canonical_φ`, `canonical_r` (`ṙ = p_r/E`),
  `canonical_pS` (`ṗ_s = H − m²/E`) and `canonical_radialMomentum`. The angle is cyclic and
  `p_φ` is an integral (`isIntegral_pφ`).
* The orbit equation. With `X = (p_φ² − α²)/r + α H` and `Y = p_φ p_r`,
  `p_φ² dX = (α² − p_φ²) Y dφ` and `dY = X dφ` (`canonical_orbitX_eq`, `canonical_orbitY_eq`,
  from `canonical_orbitX` and `canonical_orbitY`); `orbitX_mul_self_add` is the integral
  `X² + (p_φ² − α²) p_r² = p_φ² H² − m² (p_φ² − α²)`. `orbit_eq` integrates the equation in the
  angle along a solution between two times.
* `ℓ² > α²`, the rosette. Along a trajectory, `X = X₀ cos κψ − κ Y₀ sin κψ` in the angle
  `ψ = φ − φ(0)` with `κ = √(1 − α²/ℓ²)` (`rosette`), so
  `(ℓ² − α²)/r = X₀ cos κψ − κ Y₀ sin κψ − α ℰ` (`rosette_rInv`), with
  `X₀² + κ² Y₀² = ℓ² ℰ² − m² (ℓ² − α²)` (`rosette_amplitude`). The perihelia are
  `2π/κ = 2π|ℓ|/√(ℓ² − α²)` apart in the angle (`perihelion_iff`, `two_pi_div_rosetteRate`),
  more than `2π` for `α ≠ 0` (`two_pi_lt_two_pi_div_rosetteRate`). `isTrajectory_circular`:
  in an attracting field the circular orbit of the radius `r⁻² = α² m²/(ℓ² (ℓ² − α²))` is a
  trajectory, so the hypotheses of `rosette` are satisfied (`exists_isTrajectory_circular`).
* `ℓ² ≤ α²`, the spirals, for a solution between two times, such as the flow on its domain
  (`hasDerivAt_hamiltonianFlow`): `orbit_hyperbolic` (`0 < ℓ² < α²`),
  `X = X₀ cosh λψ + λ Y₀ sinh λψ` with `λ = √(α²/ℓ² − 1)`; `orbit_linear` (`ℓ² = α²`), `Y` is
  linear and `1/r` is quadratic in the angle.
* Fall to the centre. In an attracting field and for `ℓ² ≤ α²` the radial momentum decreases
  strictly, and the radius reaches `0` in a finite time in one of the two directions of time:
  `fall_to_centre`, the flow leaves its maximal domain at a finite time, and
  `not_isTrajectory_of_sq_le`, no trajectory exists for all times. Collision:
  `exists_r_lt_of_not_mem_flowDomain`, for all `α` and `ℓ` a solution that leaves the domain
  comes arbitrarily close to the centre before it does; `fall_to_centre_collision` combines the
  two. The motion after the collision is not part of the model.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics.CoulombMotion

open Set
open SmoothAlgebra SmoothRing FreeSmoothRing Mechanics Mechanics.CentralField
open SmoothGeometry SmoothGeometry.NonlinearODE

/-! ### The Hamiltonian -/

/-- The planar momentum in polar co-ordinates, `(p_r, p_φ/r) = (p_s/r, p_φ/r)`. -/
def polarMomentum : Fin 2 → Polar := ![rInv * pS, rInv * pφ]

/-- The energy `√(m² + p_r² + p_φ²/r²)` of the particle without the potential energy. -/
def kineticEnergy (m : ℝ) : Polar := relEnergy m polarMomentum

/-- The inverse of the kinetic energy. -/
def kineticEnergyInv (m : ℝ) : Polar := relEnergyInv m polarMomentum

/-- The Hamiltonian `√(m² + p_r² + p_φ²/r²) + α/r` of a charge in the Coulomb field, in the
polar co-ordinates `s = log r`, `φ`; for `m > 0` its values are `val_coulombHamiltonian`. The
potential energy is `eφ = α/r`; the field attracts for `α < 0`. The co-ordinate `s` exists only
away from the centre, and there the Hamiltonian is an element of the free C-infinity ring, a
smooth function on all of `ℝ⁴` (`contDiff_val`). -/
def coulombHamiltonian (m α : ℝ) : Polar := kineticEnergy m + algebraMap ℝ Polar α * rInv

/-- Evaluate the co-ordinate vector fields on polynomials in the co-ordinates and `1/r`. -/
local macro "polar_derivatives" : tactic =>
  `(tactic| simp only [SmoothDerivation.map_mul, map_add, map_sub, smul_eq_mul,
    dS_s, dS_φ, dS_pS, dS_pφ, dφ_s, dφ_φ, dφ_pS, dφ_pφ, dPS_s, dPS_φ, dPS_pS, dPS_pφ,
    dPφ_s, dPφ_φ, dPφ_pS, dPφ_pφ, dS_rInv, dφ_rInv, dPS_rInv, dPφ_rInv])

variable {m α : ℝ}

/-- `E² = m² + p_r² + p_φ²/r²`. -/
theorem kineticEnergy_mul_self (hm : m ≠ 0) :
    kineticEnergy m * kineticEnergy m =
      algebraMap ℝ Polar (m ^ 2) + rInv * rInv * (pS * pS + pφ * pφ) := by
  rw [kineticEnergy, relEnergy_mul_self hm, Fin.sum_univ_two, polarMomentum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The kinetic energy is invertible. -/
theorem kineticEnergy_mul_kineticEnergyInv (hm : m ≠ 0) :
    kineticEnergy m * kineticEnergyInv m = 1 :=
  relEnergy_mul_relEnergyInv hm _

/-- A vector field differentiates the kinetic energy by the chain rule. -/
theorem apply_kineticEnergy (hm : m ≠ 0) (D : SmoothDerivation Polar Polar) :
    D (kineticEnergy m) =
      kineticEnergyInv m * (rInv * pS * D (rInv * pS) + rInv * pφ * D (rInv * pφ)) := by
  rw [kineticEnergy, SmoothDerivation.apply_relEnergy hm, Fin.sum_univ_two, polarMomentum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- `∂H/∂s = −(p_s² + p_φ²)/(r² E) − α/r`. -/
theorem dS_coulombHamiltonian (hm : m ≠ 0) :
    dS (coulombHamiltonian m α) =
      -(kineticEnergyInv m * (rInv * rInv * (pS * pS + pφ * pφ))) -
        algebraMap ℝ Polar α * rInv := by
  rw [coulombHamiltonian, map_add, SmoothDerivation.map_algebraMap_mul, apply_kineticEnergy hm]
  polar_derivatives
  ring

/-- The angle is cyclic: `∂H/∂φ = 0`. -/
theorem dφ_coulombHamiltonian (hm : m ≠ 0) : dφ (coulombHamiltonian m α) = 0 := by
  rw [coulombHamiltonian, map_add, SmoothDerivation.map_algebraMap_mul, apply_kineticEnergy hm]
  polar_derivatives
  ring

/-- `∂H/∂p_s = p_s/(r² E)`. -/
theorem dPS_coulombHamiltonian (hm : m ≠ 0) :
    dPS (coulombHamiltonian m α) = kineticEnergyInv m * (rInv * rInv * pS) := by
  rw [coulombHamiltonian, map_add, SmoothDerivation.map_algebraMap_mul, apply_kineticEnergy hm]
  polar_derivatives
  ring

/-- `∂H/∂p_φ = p_φ/(r² E)`. -/
theorem dPφ_coulombHamiltonian (hm : m ≠ 0) :
    dPφ (coulombHamiltonian m α) = kineticEnergyInv m * (rInv * rInv * pφ) := by
  rw [coulombHamiltonian, map_add, SmoothDerivation.map_algebraMap_mul, apply_kineticEnergy hm]
  polar_derivatives
  ring

/-! ### Hamilton's equations and the integrals -/

/-- The canonical bracket of the polar phase space. -/
local notation "𝒫" => PhaseSpace.canonical (Fin 1 ⊕ Fin 1)

/-- The bracket with the Hamiltonian, by its partial derivatives. -/
theorem bracket_coulombHamiltonian (hm : m ≠ 0) (f : Polar) :
    (𝒫).bracket f (coulombHamiltonian m α) =
      dS f * (kineticEnergyInv m * (rInv * rInv * pS)) +
        dPS f * (kineticEnergyInv m * (rInv * rInv * (pS * pS + pφ * pφ)) +
          algebraMap ℝ Polar α * rInv) +
        dφ f * (kineticEnergyInv m * (rInv * rInv * pφ)) := by
  rw [bracket_eq, dS_coulombHamiltonian hm, dφ_coulombHamiltonian hm,
    dPS_coulombHamiltonian hm, dPφ_coulombHamiltonian hm]
  ring

/-- `ṡ = p_s/(r² E)`. -/
theorem canonical_s (hm : m ≠ 0) :
    (𝒫).bracket s (coulombHamiltonian m α) = kineticEnergyInv m * (rInv * rInv * pS) := by
  rw [bracket_coulombHamiltonian hm, dS_s, dPS_s, dφ_s]
  ring

/-- `φ̇ = p_φ/(r² E)`. -/
theorem canonical_φ (hm : m ≠ 0) :
    (𝒫).bracket φ (coulombHamiltonian m α) = kineticEnergyInv m * (rInv * rInv * pφ) := by
  rw [bracket_coulombHamiltonian hm, dS_φ, dPS_φ, dφ_φ]
  ring

/-- `ṗ_s = H − m²/E`. -/
theorem canonical_pS (hm : m ≠ 0) :
    (𝒫).bracket pS (coulombHamiltonian m α) =
      coulombHamiltonian m α - algebraMap ℝ Polar (m ^ 2) * kineticEnergyInv m := by
  rw [bracket_coulombHamiltonian hm, dS_pS, dPS_pS, dφ_pS, coulombHamiltonian]
  linear_combination (-kineticEnergyInv m) * kineticEnergy_mul_self hm +
    kineticEnergy m * kineticEnergy_mul_kineticEnergyInv hm

/-- The angle is cyclic: `ṗ_φ = 0`. -/
theorem canonical_pφ (hm : m ≠ 0) : (𝒫).bracket pφ (coulombHamiltonian m α) = 0 := by
  rw [bracket_coulombHamiltonian hm, dS_pφ, dPS_pφ, dφ_pφ]
  ring

/-- The angular momentum `p_φ` is an integral of the motion. -/
theorem isIntegral_pφ (hm : m ≠ 0) : (𝒫).IsIntegral (coulombHamiltonian m α) pφ :=
  canonical_pφ hm

/-- `d(1/r)/dt = −p_s/(r³ E)`. -/
theorem canonical_rInv (hm : m ≠ 0) :
    (𝒫).bracket rInv (coulombHamiltonian m α) =
      -(kineticEnergyInv m * (rInv * rInv * rInv * pS)) := by
  rw [bracket_coulombHamiltonian hm, dS_rInv, dPS_rInv, dφ_rInv]
  ring

/-- `ṙ = p_r/E`. -/
theorem canonical_r (hm : m ≠ 0) :
    (𝒫).bracket r (coulombHamiltonian m α) = kineticEnergyInv m * (rInv * pS) := by
  rw [bracket_coulombHamiltonian hm, dS_r, dPS_r, dφ_r]
  linear_combination (kineticEnergyInv m * rInv * pS) * r_mul_rInv

/-- The radial momentum `p_r = p_s/r` has `ṗ_r = (α + p_φ²/(r E))/r²`. -/
theorem canonical_radialMomentum (hm : m ≠ 0) :
    (𝒫).bracket (rInv * pS) (coulombHamiltonian m α) =
      rInv * rInv * (algebraMap ℝ Polar α + kineticEnergyInv m * (rInv * (pφ * pφ))) := by
  rw [AlmostPoissonStructure.bracket_mul_left, canonical_rInv hm, bracket_coulombHamiltonian hm,
    dS_pS, dPS_pS, dφ_pS]
  ring

/-- The function `X = (p_φ² − α²)/r + α H` of the orbit equation. -/
def orbitX (m α : ℝ) : Polar :=
  (pφ * pφ - algebraMap ℝ Polar (α ^ 2)) * rInv + algebraMap ℝ Polar α * coulombHamiltonian m α

/-- The function `Y = p_φ p_s/r = p_φ p_r` of the orbit equation. -/
def orbitY : Polar := pφ * pS * rInv

/-- `Ẋ = −(p_φ² − α²) p_s/(r³ E)`. -/
theorem canonical_orbitX (hm : m ≠ 0) :
    (𝒫).bracket (orbitX m α) (coulombHamiltonian m α) =
      -((pφ * pφ - algebraMap ℝ Polar (α ^ 2)) * pS * rInv * rInv * rInv *
        kineticEnergyInv m) := by
  rw [orbitX, AlmostPoissonStructure.bracket_add_left, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_self,
    AlmostPoissonStructure.bracket_algebraMap_left, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_algebraMap_left,
    canonical_pφ hm, canonical_rInv hm]
  ring

/-- `Ẏ = X p_φ/(r² E)`. -/
theorem canonical_orbitY (hm : m ≠ 0) :
    (𝒫).bracket orbitY (coulombHamiltonian m α) =
      orbitX m α * pφ * rInv * rInv * kineticEnergyInv m := by
  rw [orbitY, AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_mul_left,
    canonical_rInv hm, canonical_pS hm, canonical_pφ hm, orbitX, coulombHamiltonian]
  have h := kineticEnergy_mul_self hm
  simp only [map_pow] at h ⊢
  linear_combination (-(pφ * rInv * kineticEnergy m + algebraMap ℝ Polar α * pφ * rInv * rInv)) *
      kineticEnergy_mul_kineticEnergyInv hm +
    pφ * rInv * kineticEnergyInv m * h

/-- The orbit equation in the angle: `p_φ² dX = (α² − p_φ²) Y dφ`. -/
theorem canonical_orbitX_eq (hm : m ≠ 0) :
    pφ * pφ * (𝒫).bracket (orbitX m α) (coulombHamiltonian m α) =
      (algebraMap ℝ Polar (α ^ 2) - pφ * pφ) * orbitY *
        (𝒫).bracket φ (coulombHamiltonian m α) := by
  rw [canonical_orbitX hm, canonical_φ hm, orbitY]
  ring

/-- The orbit equation in the angle: `dY = X dφ`. -/
theorem canonical_orbitY_eq (hm : m ≠ 0) :
    (𝒫).bracket orbitY (coulombHamiltonian m α) =
      orbitX m α * (𝒫).bracket φ (coulombHamiltonian m α) := by
  rw [canonical_orbitY hm, canonical_φ hm]
  ring

/-- The energy relation `(H − α/r)² = m² + p_r² + p_φ²/r²`. -/
theorem coulombHamiltonian_sub_mul_self (hm : m ≠ 0) :
    (coulombHamiltonian m α - algebraMap ℝ Polar α * rInv) *
        (coulombHamiltonian m α - algebraMap ℝ Polar α * rInv) =
      algebraMap ℝ Polar (m ^ 2) + rInv * rInv * (pS * pS + pφ * pφ) := by
  rw [coulombHamiltonian, add_sub_cancel_right, kineticEnergy_mul_self hm]

/-- The amplitude of the orbit: `X² + (p_φ² − α²) p_r² = p_φ² H² − m² (p_φ² − α²)`. -/
theorem orbitX_mul_self_add (hm : m ≠ 0) :
    orbitX m α * orbitX m α +
        (pφ * pφ - algebraMap ℝ Polar (α ^ 2)) * (rInv * pS) * (rInv * pS) =
      pφ * pφ * (coulombHamiltonian m α * coulombHamiltonian m α) -
        algebraMap ℝ Polar (m ^ 2) * (pφ * pφ - algebraMap ℝ Polar (α ^ 2)) := by
  have h := coulombHamiltonian_sub_mul_self (α := α) hm
  rw [orbitX]
  simp only [map_pow] at h ⊢
  linear_combination (algebraMap ℝ Polar α ^ 2 - pφ * pφ) * h

/-- The energy relation for `Y`: `Y² = p_φ² (H² − m²) − 2α p_φ² H/r + p_φ² (α² − p_φ²)/r²`.
At `p_φ² = α²` the last term vanishes. -/
theorem orbitY_mul_self (hm : m ≠ 0) :
    orbitY * orbitY =
      pφ * pφ * (coulombHamiltonian m α * coulombHamiltonian m α - algebraMap ℝ Polar (m ^ 2)) -
        algebraMap ℝ Polar (2 * α) * pφ * pφ * coulombHamiltonian m α * rInv +
        pφ * pφ * (algebraMap ℝ Polar (α ^ 2) - pφ * pφ) * (rInv * rInv) := by
  have h := coulombHamiltonian_sub_mul_self (α := α) hm
  rw [orbitY]
  simp only [map_pow, map_mul, map_ofNat] at h ⊢
  linear_combination (-(pφ * pφ)) * h

/-! ### Solutions of Hamilton's equations -/

/-- A point `(s, φ, p_s, p_φ)` of the polar phase space. -/
abbrev PolarPoint : Type := (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → ℝ

/-- Along a solution of Hamilton's equations an observable changes by its bracket with the
Hamiltonian. -/
theorem hasDerivAt_lift {H : Polar} {y : ℝ → PolarPoint} {t : ℝ}
    (hy : HasDerivAt y (hamiltonianField H (y t)) t) (G : Polar) :
    HasDerivAt (fun r => FreeSmoothRing.lift (y r) G)
      (FreeSmoothRing.lift (y t) ((𝒫).bracket G H)) t := by
  have h := ((contDiff_val G).differentiable (by simp) (y t)).hasFDerivAt.comp_hasDerivAt t hy
  rw [fderiv_val_hamiltonianField] at h
  simp only [lift_real]
  exact h

/-- An integral of the motion takes the same value at two times of a solution between them. -/
theorem lift_eq_of_isIntegral {H G : Polar} {y : ℝ → PolarPoint} {a b : ℝ}
    (hy : ∀ t ∈ uIcc a b, HasDerivAt y (hamiltonianField H (y t)) t)
    (hG : (𝒫).IsIntegral H G) :
    FreeSmoothRing.lift (y b) G = FreeSmoothRing.lift (y a) G := by
  refine eq_of_hasDerivAt_zero (g := fun r => FreeSmoothRing.lift (y r) G) fun t ht => ?_
  have h := hasDerivAt_lift (hy t ht) G
  rwa [show (𝒫).bracket G H = 0 from hG, SmoothRingHom.map_zero] at h

/-- A pair `X, Y` with `dX = k Y dψ` and `dY = X dψ` between two times is a combination of
two solutions `C, S` of `C′ = k S`, `S′ = C` with `C(0) = 1`, `S(0) = 0`. -/
theorem eq_of_hasDerivAt_angle {X Y ψ ψ' C S : ℝ → ℝ} {k a b : ℝ}
    (hX : ∀ t ∈ uIcc a b, HasDerivAt X (k * Y t * ψ' t) t)
    (hY : ∀ t ∈ uIcc a b, HasDerivAt Y (X t * ψ' t) t)
    (hψ : ∀ t ∈ uIcc a b, HasDerivAt ψ (ψ' t) t)
    (hC : ∀ x, HasDerivAt C (k * S x) x) (hS : ∀ x, HasDerivAt S (C x) x)
    (hCS : ∀ x, C x * C x - k * (S x * S x) = 1) (hψa : ψ a = 0) (hC0 : C 0 = 1)
    (hS0 : S 0 = 0) :
    X b = X a * C (ψ b) + k * Y a * S (ψ b) ∧ Y b = Y a * C (ψ b) + X a * S (ψ b) := by
  have hP := eq_of_hasDerivAt_zero (g := fun t => X t * C (ψ t) - k * Y t * S (ψ t))
    fun t ht => by
      have h := ((hX t ht).mul ((hC (ψ t)).comp t (hψ t ht))).sub
        (((hY t ht).mul ((hS (ψ t)).comp t (hψ t ht))).const_mul k)
      convert h using 1
      · funext r
        simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, mul_assoc]
      · simp only [Function.comp_apply]
        ring
  have hQ := eq_of_hasDerivAt_zero (g := fun t => Y t * C (ψ t) - X t * S (ψ t))
    fun t ht => by
      have h := ((hY t ht).mul ((hC (ψ t)).comp t (hψ t ht))).sub
        ((hX t ht).mul ((hS (ψ t)).comp t (hψ t ht)))
      convert h using 1
      · funext r
        simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
      · simp only [Function.comp_apply]
        ring
  simp only [hψa, hC0, hS0, mul_one, mul_zero, sub_zero] at hP hQ
  constructor
  · linear_combination (-X b) * hCS (ψ b) + C (ψ b) * hP + k * S (ψ b) * hQ
  · linear_combination (-Y b) * hCS (ψ b) + C (ψ b) * hQ + S (ψ b) * hP

/-- The orbit equation along a solution with the angular momentum `ℓ ≠ 0`, between the times
`a` and `b`. In the angle `ψ = φ − φ(a)` the functions `X`, `Y` satisfy `dX/dψ = k Y` and
`dY/dψ = X` with `k = (α² − ℓ²)/ℓ²`, so they are combinations of the solutions `C`, `S` of
`C′ = k S`, `S′ = C`. -/
theorem orbit_eq (hm : m ≠ 0) {y : ℝ → PolarPoint} {a b ℓ : ℝ}
    (hy : ∀ t ∈ uIcc a b, HasDerivAt y (hamiltonianField (coulombHamiltonian m α) (y t)) t)
    (hℓ : pφ.val (y a) = ℓ) (hℓ0 : ℓ ≠ 0) {C S : ℝ → ℝ}
    (hC : ∀ x, HasDerivAt C ((α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * S x) x)
    (hS : ∀ x, HasDerivAt S (C x) x)
    (hCS : ∀ x, C x * C x - (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * (S x * S x) = 1) (hC0 : C 0 = 1)
    (hS0 : S 0 = 0) :
    (orbitX m α).val (y b) = (orbitX m α).val (y a) * C (φ.val (y b) - φ.val (y a)) +
        (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * orbitY.val (y a) * S (φ.val (y b) - φ.val (y a)) ∧
      orbitY.val (y b) = orbitY.val (y a) * C (φ.val (y b) - φ.val (y a)) +
        (orbitX m α).val (y a) * S (φ.val (y b) - φ.val (y a)) := by
  simp only [← lift_real] at hℓ ⊢
  have hℓt : ∀ t ∈ uIcc a b, FreeSmoothRing.lift (y t) pφ = ℓ := fun t ht =>
    (lift_eq_of_isIntegral (fun r hr => hy r (uIcc_subset_uIcc_left ht hr))
      (isIntegral_pφ hm)).trans hℓ
  refine eq_of_hasDerivAt_angle (X := fun t => FreeSmoothRing.lift (y t) (orbitX m α))
    (Y := fun t => FreeSmoothRing.lift (y t) orbitY)
    (ψ := fun t => FreeSmoothRing.lift (y t) φ - FreeSmoothRing.lift (y a) φ)
    (ψ' := fun t => FreeSmoothRing.lift (y t) ((𝒫).bracket φ (coulombHamiltonian m α)))
    (fun t ht => ?_) (fun t ht => ?_) (fun t ht => (hasDerivAt_lift (hy t ht) φ).sub_const _)
    hC hS hCS (sub_self _) hC0 hS0
  · have e := congrArg (FreeSmoothRing.lift (y t)) (canonical_orbitX_eq (α := α) hm)
    simp only [SmoothRingHom.map_mul, SmoothRingHom.map_sub, SmoothRingHom.map_algebraMap,
      Algebra.algebraMap_self_apply, hℓt t ht] at e
    refine (hasDerivAt_lift (hy t ht) _).congr_deriv ?_
    have hℓ2 : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ0
    field_simp
    linear_combination e
  · have e := congrArg (FreeSmoothRing.lift (y t)) (canonical_orbitY_eq (α := α) hm)
    simp only [SmoothRingHom.map_mul] at e
    exact (hasDerivAt_lift (hy t ht) _).congr_deriv e

/-- The flow of a Hamiltonian field through a point solves Hamilton's equations between the
times `0` and `t` of its domain, so the theorems for a solution between two times apply to it. -/
theorem hasDerivAt_hamiltonianFlow {H : Polar} {z : PolarPoint} {t : ℝ}
    (h : (t, z) ∈ flowDomain (hamiltonianField H)) :
    ∀ r ∈ uIcc 0 t, HasDerivAt (fun τ => flow (hamiltonianField H) (τ, z))
      (hamiltonianField H (flow (hamiltonianField H) (r, z))) r := fun _ hr =>
  hasDerivAt_flow (contDiff_hamiltonianField H) (mem_flowDomain_of_mem_uIcc h hr)

/-! ### The rosette: `ℓ² > α²` -/

/-- The rate `κ = √(1 − α²/ℓ²)` of the angle in the orbit of the angular momentum `ℓ`, for
`ℓ² > α²`. -/
def rosetteRate (α ℓ : ℝ) : ℝ := Real.sqrt (1 - α ^ 2 / ℓ ^ 2)

/-- `κ > 0`. -/
theorem rosetteRate_pos {ℓ : ℝ} (h : α ^ 2 < ℓ ^ 2) : 0 < rosetteRate α ℓ := by
  have hℓ : 0 < ℓ ^ 2 := lt_of_le_of_lt (sq_nonneg α) h
  refine Real.sqrt_pos.mpr ?_
  rw [sub_pos, div_lt_one hℓ]
  exact h

/-- `κ² = (ℓ² − α²)/ℓ²`. -/
theorem rosetteRate_sq {ℓ : ℝ} (h : α ^ 2 < ℓ ^ 2) :
    rosetteRate α ℓ ^ 2 = (ℓ ^ 2 - α ^ 2) / ℓ ^ 2 := by
  have hℓ : 0 < ℓ ^ 2 := lt_of_le_of_lt (sq_nonneg α) h
  rw [rosetteRate, Real.sq_sqrt (sub_nonneg.mpr ((div_le_one hℓ).mpr h.le)), sub_div,
    div_self hℓ.ne']

/-- The angle between successive perihelia, `2π/κ = 2π|ℓ|/√(ℓ² − α²)`. -/
theorem two_pi_div_rosetteRate {ℓ : ℝ} (h : α ^ 2 < ℓ ^ 2) :
    2 * Real.pi / rosetteRate α ℓ = 2 * Real.pi * |ℓ| / Real.sqrt (ℓ ^ 2 - α ^ 2) := by
  have hℓ : 0 < ℓ ^ 2 := lt_of_le_of_lt (sq_nonneg α) h
  have hs : 0 < Real.sqrt (ℓ ^ 2 - α ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr h)
  have ha : 0 < |ℓ| := abs_pos.mpr (by rintro rfl; simp at hℓ)
  have e : rosetteRate α ℓ = Real.sqrt (ℓ ^ 2 - α ^ 2) / |ℓ| := by
    rw [rosetteRate,
      show 1 - α ^ 2 / ℓ ^ 2 = (ℓ ^ 2 - α ^ 2) / ℓ ^ 2 by rw [sub_div, div_self hℓ.ne'],
      Real.sqrt_div' _ hℓ.le, Real.sqrt_sq_eq_abs]
  rw [e]
  field_simp

/-- The perihelion advances: for `α ≠ 0` the angle `2π/κ` between successive perihelia
exceeds `2π`. -/
theorem two_pi_lt_two_pi_div_rosetteRate {ℓ : ℝ} (h : α ^ 2 < ℓ ^ 2) (hα : α ≠ 0) :
    2 * Real.pi < 2 * Real.pi / rosetteRate α ℓ := by
  have hκ := rosetteRate_pos h
  have hℓ : 0 < ℓ ^ 2 := lt_of_le_of_lt (sq_nonneg α) h
  have hlt : rosetteRate α ℓ < 1 := by
    have h1 : rosetteRate α ℓ ^ 2 < 1 := by
      rw [rosetteRate_sq h, div_lt_one hℓ]
      linarith [pow_pos (abs_pos.mpr hα) 2, sq_abs α]
    nlinarith
  rw [lt_div_iff₀ hκ]
  nlinarith [Real.pi_pos]

/-- The rosette (Landau–Lifshitz §39): along a trajectory of the angular momentum `ℓ` with
`ℓ² > α²`, in the angle `ψ = φ(t) − φ(0)`,
`X(t) = X(0) cos κψ − κ Y(0) sin κψ` and `Y(t) = Y(0) cos κψ + κ⁻¹ X(0) sin κψ`
with `κ = √(1 − α²/ℓ²)`. -/
theorem rosette (hm : m ≠ 0) {c : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}
    (hc : IsTrajectory (𝒫) (coulombHamiltonian m α) c) {ℓ : ℝ}
    (hℓ : pφ.val (realCurve c 0) = ℓ) (hℓα : α ^ 2 < ℓ ^ 2) (t : ℝ) :
    (orbitX m α).val (realCurve c t) =
        (orbitX m α).val (realCurve c 0) *
            Real.cos (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) -
          rosetteRate α ℓ * orbitY.val (realCurve c 0) *
            Real.sin (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) ∧
      orbitY.val (realCurve c t) =
        orbitY.val (realCurve c 0) *
            Real.cos (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) +
          (rosetteRate α ℓ)⁻¹ * (orbitX m α).val (realCurve c 0) *
            Real.sin (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) := by
  have hy := (isTrajectory_canonical_iff_hasDerivAt _ c).mp hc
  have hκ := rosetteRate_pos hℓα
  have hκ0 : rosetteRate α ℓ ≠ 0 := hκ.ne'
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg α]
  have hk : (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 = -rosetteRate α ℓ ^ 2 := by
    rw [rosetteRate_sq hℓα]
    ring
  have hC : ∀ x, HasDerivAt (fun x => Real.cos (rosetteRate α ℓ * x))
      ((α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * (Real.sin (rosetteRate α ℓ * x) / rosetteRate α ℓ)) x := by
    intro x
    have h := (Real.hasDerivAt_cos (rosetteRate α ℓ * x)).comp x
      ((hasDerivAt_id' x).const_mul (rosetteRate α ℓ))
    refine h.congr_deriv ?_
    rw [hk]
    field_simp
  have hS : ∀ x, HasDerivAt (fun x => Real.sin (rosetteRate α ℓ * x) / rosetteRate α ℓ)
      (Real.cos (rosetteRate α ℓ * x)) x := by
    intro x
    have h := ((Real.hasDerivAt_sin (rosetteRate α ℓ * x)).comp x
      ((hasDerivAt_id' x).const_mul (rosetteRate α ℓ))).div_const (rosetteRate α ℓ)
    refine h.congr_deriv ?_
    field_simp
  have hCS : ∀ x, Real.cos (rosetteRate α ℓ * x) * Real.cos (rosetteRate α ℓ * x) -
      (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * (Real.sin (rosetteRate α ℓ * x) / rosetteRate α ℓ *
        (Real.sin (rosetteRate α ℓ * x) / rosetteRate α ℓ)) = 1 := by
    intro x
    rw [hk]
    field_simp
    linear_combination Real.cos_sq_add_sin_sq (rosetteRate α ℓ * x)
  obtain ⟨h1, h2⟩ := orbit_eq hm (a := 0) (b := t) (fun r _ => hy r) hℓ hℓ0 hC hS hCS
    (by simp) (by simp)
  constructor
  · rw [h1, hk]
    field_simp
    ring
  · rw [h2]
    ring

/-- The orbit equation of the rosette (Landau–Lifshitz §39):
`(ℓ² − α²)/r = X(0) cos κψ − κ Y(0) sin κψ − α ℰ`, with the energy `ℰ`. -/
theorem rosette_rInv (hm : m ≠ 0) {c : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}
    (hc : IsTrajectory (𝒫) (coulombHamiltonian m α) c) {ℓ : ℝ}
    (hℓ : pφ.val (realCurve c 0) = ℓ) (hℓα : α ^ 2 < ℓ ^ 2) (t : ℝ) :
    (ℓ ^ 2 - α ^ 2) * rInv.val (realCurve c t) =
      (orbitX m α).val (realCurve c 0) *
          Real.cos (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) -
        rosetteRate α ℓ * orbitY.val (realCurve c 0) *
          Real.sin (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) -
        α * (coulombHamiltonian m α).val (realCurve c 0) := by
  have hy := (isTrajectory_canonical_iff_hasDerivAt _ c).mp hc
  rw [← (rosette hm hc hℓ hℓα t).1]
  simp only [← lift_real] at hℓ ⊢
  have hpφ := (lift_eq_of_isIntegral (a := 0) (b := t) (fun r _ => hy r)
    (isIntegral_pφ (α := α) hm)).trans hℓ
  have hH := lift_eq_of_isIntegral (a := 0) (b := t) (fun r _ => hy r)
    (PoissonStructure.isIntegral_self (π := 𝒫) (coulombHamiltonian m α))
  rw [← hH, orbitX]
  simp only [SmoothRingHom.map_add, SmoothRingHom.map_mul, SmoothRingHom.map_sub,
    SmoothRingHom.map_algebraMap, Algebra.algebraMap_self_apply, hpφ]
  ring

/-- The amplitude of the rosette (Landau–Lifshitz §39): at a point with `p_φ = ℓ`,
`X² + κ² Y² = ℓ² H² − m² (ℓ² − α²)`. -/
theorem rosette_amplitude (hm : m ≠ 0) (z : PolarPoint) {ℓ : ℝ} (hℓ : pφ.val z = ℓ)
    (hℓα : α ^ 2 < ℓ ^ 2) :
    (orbitX m α).val z ^ 2 + rosetteRate α ℓ ^ 2 * orbitY.val z ^ 2 =
      ℓ ^ 2 * (coulombHamiltonian m α).val z ^ 2 - m ^ 2 * (ℓ ^ 2 - α ^ 2) := by
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg α]
  simp only [← lift_real] at hℓ ⊢
  have e := congrArg (FreeSmoothRing.lift z) (orbitX_mul_self_add (α := α) hm)
  simp only [SmoothRingHom.map_add, SmoothRingHom.map_mul, SmoothRingHom.map_sub,
    SmoothRingHom.map_algebraMap, Algebra.algebraMap_self_apply, hℓ] at e
  rw [rosetteRate_sq hℓα, orbitY, SmoothRingHom.map_mul, SmoothRingHom.map_mul, hℓ]
  have hk : (ℓ ^ 2 - α ^ 2) / ℓ ^ 2 *
      (ℓ * FreeSmoothRing.lift z pS * FreeSmoothRing.lift z rInv) ^ 2 =
        (ℓ ^ 2 - α ^ 2) * (FreeSmoothRing.lift z rInv * FreeSmoothRing.lift z pS) *
          (FreeSmoothRing.lift z rInv * FreeSmoothRing.lift z pS) := by
    field_simp
  rw [hk]
  linear_combination e

/-- The values of `f(ψ) = X₀ cos κψ − κ Y₀ sin κψ` are at most `√(X₀² + κ² Y₀²)`. -/
theorem orbit_le_sqrt (X₀ Y₀ κ ψ : ℝ) :
    X₀ * Real.cos (κ * ψ) - κ * Y₀ * Real.sin (κ * ψ) ≤ Real.sqrt (X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2) := by
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  nlinarith [Real.cos_sq_add_sin_sq (κ * ψ),
    sq_nonneg (X₀ * Real.sin (κ * ψ) + κ * Y₀ * Real.cos (κ * ψ))]

/-- The perihelia of the rosette (Landau–Lifshitz §39). The inverse radius is largest where
`f(ψ) = X₀ cos κψ − κ Y₀ sin κψ` takes its largest value `A = √(X₀² + κ² Y₀²)` (`rosette_rInv`).
If `f(ψ₁) = A > 0`, then `f(ψ₂) = A` exactly when `ψ₂ − ψ₁` is a multiple of `2π/κ`, the angle
`2π|ℓ|/√(ℓ² − α²)` of `two_pi_div_rosetteRate`. -/
theorem perihelion_iff {X₀ Y₀ κ ψ₁ ψ₂ : ℝ} (hκ : 0 < κ) (hA : 0 < X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2)
    (h₁ : X₀ * Real.cos (κ * ψ₁) - κ * Y₀ * Real.sin (κ * ψ₁) =
      Real.sqrt (X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2)) :
    X₀ * Real.cos (κ * ψ₂) - κ * Y₀ * Real.sin (κ * ψ₂) =
        Real.sqrt (X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2) ↔
      ∃ n : ℤ, ψ₂ = ψ₁ + n * (2 * Real.pi / κ) := by
  set A := Real.sqrt (X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2) with hAdef
  have hApos : 0 < A := Real.sqrt_pos.mpr hA
  have hA2 : A ^ 2 = X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2 := Real.sq_sqrt hA.le
  have hg : X₀ * Real.sin (κ * ψ₁) + κ * Y₀ * Real.cos (κ * ψ₁) = 0 := by
    have h := Real.cos_sq_add_sin_sq (κ * ψ₁)
    have h0 : (X₀ * Real.sin (κ * ψ₁) + κ * Y₀ * Real.cos (κ * ψ₁)) ^ 2 = 0 := by
      have h₁' := congrArg (· ^ 2) h₁
      linear_combination (X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2) * h - h₁' - hA2
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h0
  have hadd : X₀ * Real.cos (κ * ψ₂) - κ * Y₀ * Real.sin (κ * ψ₂) =
      A * Real.cos (κ * (ψ₂ - ψ₁)) := by
    have e : κ * ψ₂ = κ * ψ₁ + κ * (ψ₂ - ψ₁) := by ring
    rw [e, Real.cos_add, Real.sin_add]
    linear_combination Real.cos (κ * (ψ₂ - ψ₁)) * h₁ - Real.sin (κ * (ψ₂ - ψ₁)) * hg
  rw [hadd]
  constructor
  · intro h
    have hc : Real.cos (κ * (ψ₂ - ψ₁)) = 1 := by
      have := mul_left_cancel₀ hApos.ne' (h.trans (mul_one A).symm)
      exact this
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hc
    refine ⟨n, ?_⟩
    field_simp
    linarith
  · rintro ⟨n, rfl⟩
    have e : κ * (ψ₁ + n * (2 * Real.pi / κ) - ψ₁) = n * (2 * Real.pi) := by
      field_simp
      ring
    rw [e, Real.cos_int_mul_two_pi, mul_one]

/-! ### Spirals: `ℓ² ≤ α²`

For `ℓ² ≤ α²` and an attracting field there is no trajectory for all times
(`not_isTrajectory_of_sq_le`), so the orbit equation is stated for a solution between two
times, such as the flow on its domain (`hasDerivAt_hamiltonianFlow`). -/

/-- The rate `λ = √(α²/ℓ² − 1)` of the angle in a spiral orbit with `0 < ℓ² < α²`. -/
def spiralRate (α ℓ : ℝ) : ℝ := Real.sqrt (α ^ 2 / ℓ ^ 2 - 1)

/-- `λ > 0`. -/
theorem spiralRate_pos {ℓ : ℝ} (hℓ0 : ℓ ≠ 0) (h : ℓ ^ 2 < α ^ 2) : 0 < spiralRate α ℓ := by
  have hℓ : 0 < ℓ ^ 2 := by positivity
  refine Real.sqrt_pos.mpr ?_
  rw [sub_pos, one_lt_div hℓ]
  exact h

/-- `λ² = (α² − ℓ²)/ℓ²`. -/
theorem spiralRate_sq {ℓ : ℝ} (hℓ0 : ℓ ≠ 0) (h : ℓ ^ 2 < α ^ 2) :
    spiralRate α ℓ ^ 2 = (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 := by
  have hℓ : 0 < ℓ ^ 2 := by positivity
  rw [spiralRate, Real.sq_sqrt (sub_nonneg.mpr ((one_le_div hℓ).mpr h.le)), sub_div,
    div_self hℓ.ne']

/-- The spiral orbit (Landau–Lifshitz §39), for `0 < ℓ² < α²`: along a solution between the
times `a` and `b` with the angular momentum `ℓ`, in the angle `ψ = φ(b) − φ(a)`,
`X(b) = X(a) cosh λψ + λ Y(a) sinh λψ` and `Y(b) = Y(a) cosh λψ + λ⁻¹ X(a) sinh λψ`
with `λ = √(α²/ℓ² − 1)`. -/
theorem orbit_hyperbolic (hm : m ≠ 0) {y : ℝ → PolarPoint} {a b ℓ : ℝ}
    (hy : ∀ t ∈ uIcc a b, HasDerivAt y (hamiltonianField (coulombHamiltonian m α) (y t)) t)
    (hℓ : pφ.val (y a) = ℓ) (hℓ0 : ℓ ≠ 0) (hℓα : ℓ ^ 2 < α ^ 2) :
    (orbitX m α).val (y b) =
        (orbitX m α).val (y a) * Real.cosh (spiralRate α ℓ * (φ.val (y b) - φ.val (y a))) +
          spiralRate α ℓ * orbitY.val (y a) *
            Real.sinh (spiralRate α ℓ * (φ.val (y b) - φ.val (y a))) ∧
      orbitY.val (y b) =
        orbitY.val (y a) * Real.cosh (spiralRate α ℓ * (φ.val (y b) - φ.val (y a))) +
          (spiralRate α ℓ)⁻¹ * (orbitX m α).val (y a) *
            Real.sinh (spiralRate α ℓ * (φ.val (y b) - φ.val (y a))) := by
  have hlam := spiralRate_pos hℓ0 hℓα
  have hlam0 : spiralRate α ℓ ≠ 0 := hlam.ne'
  have hk : (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 = spiralRate α ℓ ^ 2 := (spiralRate_sq hℓ0 hℓα).symm
  have hC : ∀ x, HasDerivAt (fun x => Real.cosh (spiralRate α ℓ * x))
      ((α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * (Real.sinh (spiralRate α ℓ * x) / spiralRate α ℓ)) x := by
    intro x
    have h := (Real.hasDerivAt_cosh (spiralRate α ℓ * x)).comp x
      ((hasDerivAt_id' x).const_mul (spiralRate α ℓ))
    refine h.congr_deriv ?_
    rw [hk]
    field_simp
  have hS : ∀ x, HasDerivAt (fun x => Real.sinh (spiralRate α ℓ * x) / spiralRate α ℓ)
      (Real.cosh (spiralRate α ℓ * x)) x := by
    intro x
    have h := ((Real.hasDerivAt_sinh (spiralRate α ℓ * x)).comp x
      ((hasDerivAt_id' x).const_mul (spiralRate α ℓ))).div_const (spiralRate α ℓ)
    refine h.congr_deriv ?_
    field_simp
  have hCS : ∀ x, Real.cosh (spiralRate α ℓ * x) * Real.cosh (spiralRate α ℓ * x) -
      (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * (Real.sinh (spiralRate α ℓ * x) / spiralRate α ℓ *
        (Real.sinh (spiralRate α ℓ * x) / spiralRate α ℓ)) = 1 := by
    intro x
    rw [hk]
    field_simp
    linear_combination Real.cosh_sq (spiralRate α ℓ * x)
  obtain ⟨h1, h2⟩ := orbit_eq hm hy hℓ hℓ0 hC hS hCS (by simp) (by simp)
  constructor
  · rw [h1, hk]
    field_simp
  · rw [h2]
    ring

/-- The critical orbit (Landau–Lifshitz §39), for `ℓ² = α² ≠ 0`: along a solution between the
times `a` and `b` with the angular momentum `ℓ` and the energy `ℰ`, in the angle
`ψ = φ(b) − φ(a)`, `Y` is linear, `Y(b) = Y(a) + α ℰ ψ`, and the inverse radius is a quadratic
function of the angle, `2α ℓ² ℰ/r = ℓ² (ℰ² − m²) − (Y(a) + α ℰ ψ)²`. -/
theorem orbit_linear (hm : m ≠ 0) {y : ℝ → PolarPoint} {a b ℓ : ℝ}
    (hy : ∀ t ∈ uIcc a b, HasDerivAt y (hamiltonianField (coulombHamiltonian m α) (y t)) t)
    (hℓ : pφ.val (y a) = ℓ) (hℓ0 : ℓ ≠ 0) (hℓα : ℓ ^ 2 = α ^ 2) :
    orbitY.val (y b) = orbitY.val (y a) +
        α * (coulombHamiltonian m α).val (y a) * (φ.val (y b) - φ.val (y a)) ∧
      2 * α * ℓ ^ 2 * (coulombHamiltonian m α).val (y a) * rInv.val (y b) =
        ℓ ^ 2 * ((coulombHamiltonian m α).val (y a) ^ 2 - m ^ 2) -
          (orbitY.val (y a) +
            α * (coulombHamiltonian m α).val (y a) * (φ.val (y b) - φ.val (y a))) ^ 2 := by
  have hk : (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 = 0 := by rw [hℓα, sub_self, zero_div]
  have hC : ∀ x : ℝ, HasDerivAt (fun _ : ℝ => (1 : ℝ)) ((α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * x) x := by
    intro x
    rw [hk, zero_mul]
    exact hasDerivAt_const x 1
  have hCS : ∀ x : ℝ, (1 : ℝ) * 1 - (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * (x * x) = 1 := by
    intro x
    rw [hk]
    ring
  obtain ⟨-, h2⟩ := orbit_eq hm hy hℓ hℓ0 hC (fun x => hasDerivAt_id' x) hCS rfl rfl
  simp only [← lift_real] at hℓ h2 ⊢
  have hpφ := (lift_eq_of_isIntegral hy (isIntegral_pφ (α := α) hm)).trans hℓ
  have hH := lift_eq_of_isIntegral hy
    (PoissonStructure.isIntegral_self (π := 𝒫) (coulombHamiltonian m α))
  have hXa : FreeSmoothRing.lift (y a) (orbitX m α) =
      α * FreeSmoothRing.lift (y a) (coulombHamiltonian m α) := by
    rw [orbitX]
    simp only [SmoothRingHom.map_add, SmoothRingHom.map_mul, SmoothRingHom.map_sub,
      SmoothRingHom.map_algebraMap, Algebra.algebraMap_self_apply, hℓ]
    rw [← hℓα]
    ring
  rw [hXa, mul_one] at h2
  refine ⟨h2, ?_⟩
  rw [← h2]
  have e := congrArg (FreeSmoothRing.lift (y b)) (orbitY_mul_self (α := α) hm)
  simp only [SmoothRingHom.map_add, SmoothRingHom.map_mul, SmoothRingHom.map_sub,
    SmoothRingHom.map_algebraMap, Algebra.algebraMap_self_apply, hpφ, hH] at e
  rw [← hℓα] at e
  linear_combination e

/-! ### Values at a point -/

section Values

variable (z : PolarPoint)

/-- The co-ordinate `s` at a point. -/
theorem lift_s : FreeSmoothRing.lift z s = z (Sum.inl (Sum.inl 0)) := lift_generator z _

/-- The angle at a point. -/
theorem lift_φ : FreeSmoothRing.lift z φ = z (Sum.inl (Sum.inr 0)) := lift_generator z _

/-- The momentum `p_s` at a point. -/
theorem lift_pS : FreeSmoothRing.lift z pS = z (Sum.inr (Sum.inl 0)) := lift_generator z _

/-- The momentum `p_φ` at a point. -/
theorem lift_pφ : FreeSmoothRing.lift z pφ = z (Sum.inr (Sum.inr 0)) := lift_generator z _

/-- The radius at a point. -/
theorem lift_r : FreeSmoothRing.lift z r = Real.exp (z (Sum.inl (Sum.inl 0))) := by
  rw [r, SmoothRingHom.map_exp, lift_s]
  rfl

/-- The inverse radius at a point. -/
theorem lift_rInv : FreeSmoothRing.lift z rInv = Real.exp (-z (Sum.inl (Sum.inl 0))) := by
  rw [rInv, SmoothRingHom.map_exp, SmoothRingHom.map_neg, lift_s]
  rfl

/-- The inverse radius is positive. -/
theorem lift_rInv_pos : 0 < FreeSmoothRing.lift z rInv := by
  rw [lift_rInv]
  exact Real.exp_pos _

/-- `r · (1/r) = 1` at a point. -/
theorem lift_r_mul_rInv : FreeSmoothRing.lift z r * FreeSmoothRing.lift z rInv = 1 := by
  rw [← SmoothRingHom.map_mul, r_mul_rInv, SmoothRingHom.map_one]

/-- For a positive mass the kinetic energy is positive. -/
theorem lift_kineticEnergy_pos (hm : 0 < m) : 0 < FreeSmoothRing.lift z (kineticEnergy m) := by
  rw [kineticEnergy, SmoothRingHom.map_relEnergy]
  exact relEnergy_real_pos hm _

/-- The kinetic energy and its inverse at a point. -/
theorem lift_kineticEnergy_mul_inv (hm : m ≠ 0) :
    FreeSmoothRing.lift z (kineticEnergy m) * FreeSmoothRing.lift z (kineticEnergyInv m) = 1 := by
  rw [← SmoothRingHom.map_mul, kineticEnergy_mul_kineticEnergyInv hm, SmoothRingHom.map_one]

/-- `E² = m² + p_r² + p_φ²/r²` at a point. -/
theorem lift_kineticEnergy_mul_self (hm : m ≠ 0) :
    FreeSmoothRing.lift z (kineticEnergy m) * FreeSmoothRing.lift z (kineticEnergy m) =
      m ^ 2 + FreeSmoothRing.lift z rInv * FreeSmoothRing.lift z rInv *
        (FreeSmoothRing.lift z pS * FreeSmoothRing.lift z pS +
          FreeSmoothRing.lift z pφ * FreeSmoothRing.lift z pφ) := by
  have h := congrArg (FreeSmoothRing.lift z) (kineticEnergy_mul_self hm)
  simp only [SmoothRingHom.map_mul, SmoothRingHom.map_add, SmoothRingHom.map_algebraMap,
    Algebra.algebraMap_self_apply] at h
  exact h

/-- `H = E + α/r` at a point. -/
theorem lift_coulombHamiltonian :
    FreeSmoothRing.lift z (coulombHamiltonian m α) =
      FreeSmoothRing.lift z (kineticEnergy m) + α * FreeSmoothRing.lift z rInv := by
  rw [coulombHamiltonian, SmoothRingHom.map_add, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, Algebra.algebraMap_self_apply]

/-- For `m > 0` the Hamiltonian is `√(m² + e^{−2s} (p_s² + p_φ²)) + α e^{−s}`. -/
theorem val_coulombHamiltonian (hm : 0 < m) :
    (coulombHamiltonian m α).val z =
      Real.sqrt (m ^ 2 + Real.exp (-z (Sum.inl (Sum.inl 0))) ^ 2 *
          (z (Sum.inr (Sum.inl 0)) ^ 2 + z (Sum.inr (Sum.inr 0)) ^ 2)) +
        α * Real.exp (-z (Sum.inl (Sum.inl 0))) := by
  rw [← lift_real, lift_coulombHamiltonian, kineticEnergy, SmoothRingHom.map_relEnergy,
    relEnergy_real hm, Fin.sum_univ_two, lift_rInv]
  simp only [polarMomentum, Matrix.cons_val_zero, Matrix.cons_val_one, SmoothRingHom.map_mul,
    lift_rInv, lift_pS, lift_pφ]
  ring_nf

end Values

/-! ### The circular orbit -/

/-- The affine function `a + b t` of time. -/
def affineTime (a b : ℝ) : TimeFunction :=
  SmoothOperation.ofContDiff (fun x => a + b * x 0)
    (contDiff_const.add (contDiff_const.mul (contDiff_apply ℝ (fun _ => ℝ) 0)))

/-- The value of `a + b t` at the time `x 0`. -/
theorem affineTime_apply (a b : ℝ) (x : Fin 1 → ℝ) : affineTime a b x = a + b * x 0 := rfl

/-- The derivative of `a + b t` is `b`. -/
theorem hasDerivAt_affineTime (a b t : ℝ) :
    HasDerivAt (fun r : ℝ => affineTime a b fun _ => r) b t := by
  have h := ((hasDerivAt_id' t).const_mul b).const_add a
  rw [mul_one] at h
  exact h

/-- The uniform circular motion `s = s₀`, `φ = ϖ t`, `p_s = 0`, `p_φ = ℓ`. -/
def circularOrbit (s₀ ϖ ℓ : ℝ) : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction :=
  Sum.elim (Sum.elim (fun _ => affineTime s₀ 0) fun _ => affineTime 0 ϖ)
    (Sum.elim (fun _ => affineTime 0 0) fun _ => affineTime ℓ 0)

/-- The circular orbit (Landau–Lifshitz §39): in an attracting field, for `ℓ² > α²` and the
radius with `r⁻² = e^{−2s₀} = α² m²/(ℓ² (ℓ² − α²))`, the uniform circular motion with the
angular velocity `ϖ = −α e^{−s₀}/ℓ` and the angular momentum `ℓ` is a trajectory. -/
theorem isTrajectory_circular (hm : 0 < m) (hα : α < 0) {ℓ s₀ : ℝ} (hℓ : α ^ 2 < ℓ ^ 2)
    (hs₀ : Real.exp (-(2 * s₀)) = α ^ 2 * m ^ 2 / (ℓ ^ 2 * (ℓ ^ 2 - α ^ 2))) :
    IsTrajectory (𝒫) (coulombHamiltonian m α)
      (circularOrbit s₀ (-α * Real.exp (-s₀) / ℓ) ℓ) := by
  have hm0 : m ≠ 0 := hm.ne'
  have hℓ2 : 0 < ℓ ^ 2 := lt_of_le_of_lt (sq_nonneg α) hℓ
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    simp at hℓ2
  rw [isTrajectory_canonical_iff_hasDerivAt]
  intro t
  set c := circularOrbit s₀ (-α * Real.exp (-s₀) / ℓ) ℓ with hc
  set z := realCurve c t with hz
  have hs : z (Sum.inl (Sum.inl 0)) = s₀ := by
    rw [hz, realCurve_apply, hc, circularOrbit, Sum.elim_inl, Sum.elim_inl, affineTime_apply]
    ring
  have hpS : FreeSmoothRing.lift z pS = 0 := by
    rw [lift_pS, hz, realCurve_apply, hc, circularOrbit, Sum.elim_inr, Sum.elim_inl,
      affineTime_apply]
    ring
  have hpφ : FreeSmoothRing.lift z pφ = ℓ := by
    rw [lift_pφ, hz, realCurve_apply, hc, circularOrbit, Sum.elim_inr, Sum.elim_inr,
      affineTime_apply]
    ring
  set u := FreeSmoothRing.lift z rInv with hu
  set E := FreeSmoothRing.lift z (kineticEnergy m) with hE
  set Ei := FreeSmoothRing.lift z (kineticEnergyInv m) with hEi
  have hupos : 0 < u := lift_rInv_pos z
  have hu0 : u = Real.exp (-s₀) := by rw [hu, lift_rInv, hs]
  have hEpos : 0 < E := lift_kineticEnergy_pos z hm
  have hEEi : E * Ei = 1 := lift_kineticEnergy_mul_inv z hm0
  have hEE : E * E = m ^ 2 + u * u * (ℓ * ℓ) := by
    have h := lift_kineticEnergy_mul_self z hm0
    rw [hpS, hpφ] at h
    rw [h]
    ring
  have hu2 : u * u * (ℓ ^ 2 * (ℓ ^ 2 - α ^ 2)) = α ^ 2 * m ^ 2 := by
    have h1 : u * u = Real.exp (-(2 * s₀)) := by
      rw [hu, lift_rInv, hs, ← Real.exp_add]
      ring_nf
    have : ℓ ^ 2 - α ^ 2 ≠ 0 := (sub_pos.mpr hℓ).ne'
    rw [h1, hs₀]
    field_simp
  -- the balance of the centrifugal and the Coulomb force: `ℓ² u = −α E`
  have hbal : ℓ ^ 2 * u = -α * E := by
    have hsq : (ℓ ^ 2 * u) ^ 2 = (-α * E) ^ 2 := by
      linear_combination (-α ^ 2) * hEE + hu2
    have hpos1 : 0 < ℓ ^ 2 * u := mul_pos hℓ2 hupos
    have hpos2 : 0 < -α * E := mul_pos (neg_pos.mpr hα) hEpos
    nlinarith [sq_nonneg (ℓ ^ 2 * u - -α * E)]
  have hkey : ℓ ^ 2 * u * Ei = -α := by
    rw [hbal]
    linear_combination -α * hEEi
  rw [hasDerivAt_pi]
  rintro ((i | i) | (i | i)) <;> obtain rfl := Subsingleton.elim i 0
  · rw [hamiltonianField_inl]
    change HasDerivAt _ ((dPS (coulombHamiltonian m α)).val z) t
    rw [dPS_coulombHamiltonian hm0, ← lift_real]
    simp only [SmoothRingHom.map_mul, hpS, mul_zero]
    exact hasDerivAt_affineTime s₀ 0 t
  · rw [hamiltonianField_inl]
    change HasDerivAt _ ((dPφ (coulombHamiltonian m α)).val z) t
    rw [dPφ_coulombHamiltonian hm0, ← lift_real]
    simp only [SmoothRingHom.map_mul, hpφ]
    refine (hasDerivAt_affineTime 0 _ t).congr_deriv ?_
    rw [← hu, ← hEi, ← hu0]
    field_simp
    linear_combination -hkey
  · rw [hamiltonianField_inr]
    change HasDerivAt _ (-(dS (coulombHamiltonian m α)).val z) t
    rw [dS_coulombHamiltonian hm0, ← lift_real]
    simp only [SmoothRingHom.map_mul, SmoothRingHom.map_sub, SmoothRingHom.map_neg,
      SmoothRingHom.map_add, SmoothRingHom.map_algebraMap, Algebra.algebraMap_self_apply, hpS,
      hpφ]
    refine (hasDerivAt_affineTime 0 0 t).congr_deriv ?_
    rw [← hu, ← hEi]
    linear_combination (-u) * hkey
  · rw [hamiltonianField_inr]
    change HasDerivAt _ (-(dφ (coulombHamiltonian m α)).val z) t
    rw [dφ_coulombHamiltonian hm0]
    refine (hasDerivAt_affineTime ℓ 0 t).congr_deriv ?_
    rw [← lift_real, SmoothRingHom.map_zero, neg_zero]

/-- Circular orbits exist: the hypotheses of `rosette` are satisfied. -/
theorem exists_isTrajectory_circular (hm : 0 < m) (hα : α < 0) {ℓ : ℝ} (hℓ : α ^ 2 < ℓ ^ 2) :
    ∃ c : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction,
      IsTrajectory (𝒫) (coulombHamiltonian m α) c ∧ pφ.val (realCurve c 0) = ℓ := by
  have hℓ2 : 0 < ℓ ^ 2 := lt_of_le_of_lt (sq_nonneg α) hℓ
  have hq : 0 < α ^ 2 * m ^ 2 / (ℓ ^ 2 * (ℓ ^ 2 - α ^ 2)) := by
    have : 0 < α ^ 2 := by nlinarith
    have : 0 < m ^ 2 := by positivity
    have : 0 < ℓ ^ 2 - α ^ 2 := sub_pos.mpr hℓ
    positivity
  refine ⟨_, isTrajectory_circular hm hα hℓ
    (s₀ := -(Real.log (α ^ 2 * m ^ 2 / (ℓ ^ 2 * (ℓ ^ 2 - α ^ 2))) / 2)) ?_, ?_⟩
  · rw [show -(2 * -(Real.log (α ^ 2 * m ^ 2 / (ℓ ^ 2 * (ℓ ^ 2 - α ^ 2))) / 2)) =
      Real.log (α ^ 2 * m ^ 2 / (ℓ ^ 2 * (ℓ ^ 2 - α ^ 2))) by ring, Real.exp_log hq]
  · rw [← lift_real, lift_pφ, realCurve_apply, circularOrbit, Sum.elim_inr, Sum.elim_inr,
      affineTime_apply]
    ring

/-! ### Fall to the centre: `ℓ² ≤ α²` -/

/-- A bound of the derivative on a half-line bounds the growth of the function. -/
theorem le_add_mul_of_hasDerivAt {f f' : ℝ → ℝ} {a C t : ℝ}
    (hf : ∀ r, a ≤ r → HasDerivAt f (f' r) r) (hC : ∀ r, a ≤ r → f' r ≤ C) (ht : a ≤ t) :
    f t ≤ f a + C * (t - a) := by
  have h := (convex_Ici a).image_sub_le_mul_sub_of_deriv_le (f := f)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [(hf x (interior_subset hx)).deriv]
      exact hC x (interior_subset hx))
    a self_mem_Ici t ht ht
  linarith

/-- A lower bound of the derivative on a half-line bounds the decrease of the function. -/
theorem add_mul_le_of_hasDerivAt {f f' : ℝ → ℝ} {a C t : ℝ}
    (hf : ∀ r, a ≤ r → HasDerivAt f (f' r) r) (hC : ∀ r, a ≤ r → C ≤ f' r) (ht : a ≤ t) :
    f a + C * (t - a) ≤ f t := by
  have h := (convex_Ici a).mul_sub_le_image_sub_of_le_deriv (f := f)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [(hf x (interior_subset hx)).deriv]
      exact hC x (interior_subset hx))
    a self_mem_Ici t ht ht
  linarith

/-- The radial equations reach the centre in a finite time. Let `R > 0` and `P` satisfy
`Ṙ = P/(R E)` and `Ṗ = ℰ − m²/E` for all times, with `R E = ℰ R − α`, `E > 0` and `α < 0`.
Then `P` is not negative at all times after a time `t₀`: otherwise `R` decreases, `E`
increases, `Ṗ` increases and stays negative since `P < 0`, so `P ≤ P(t₀)`, `Ṙ` is bounded
by a negative number, and `R` reaches `0`. -/
theorem not_forall_neg_of_radial {R P E : ℝ → ℝ} {ℰ m α t₀ : ℝ} (hα : α < 0)
    (hR : ∀ t, 0 < R t) (hE : ∀ t, 0 < E t) (hRE : ∀ t, R t * E t = ℰ * R t - α)
    (hR' : ∀ t, HasDerivAt R (P t / (R t * E t)) t)
    (hP' : ∀ t, HasDerivAt P (ℰ - m ^ 2 / E t) t) (hneg : ∀ t, t₀ ≤ t → P t < 0) : False := by
  have hREpos : ∀ t, 0 < R t * E t := fun t => mul_pos (hR t) (hE t)
  have hRanti : ∀ t₁ t₂, t₀ ≤ t₁ → t₁ ≤ t₂ → R t₂ ≤ R t₁ := by
    intro t₁ t₂ h1 h2
    have := le_add_mul_of_hasDerivAt (a := t₁) (C := 0) (fun r _ => hR' r)
      (fun r hr => (div_neg_of_neg_of_pos (hneg r (h1.trans hr)) (hREpos r)).le) h2
    linarith
  have hEmono : ∀ t₁ t₂, t₀ ≤ t₁ → t₁ ≤ t₂ → E t₁ ≤ E t₂ := by
    intro t₁ t₂ h1 h2
    have hR12 := hRanti t₁ t₂ h1 h2
    have e : R t₁ * R t₂ * (E t₂ - E t₁) = α * (R t₂ - R t₁) := by
      linear_combination R t₁ * hRE t₂ - R t₂ * hRE t₁
    by_contra hlt
    push Not at hlt
    have h3 : R t₁ * R t₂ * (E t₂ - E t₁) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (hR t₁) (hR t₂)) (by linarith)
    have h4 : 0 ≤ α * (R t₂ - R t₁) := mul_nonneg_of_nonpos_of_nonpos hα.le (by linarith)
    linarith
  have hP'mono : ∀ t₁ t₂, t₀ ≤ t₁ → t₁ ≤ t₂ → ℰ - m ^ 2 / E t₁ ≤ ℰ - m ^ 2 / E t₂ := by
    intro t₁ t₂ h1 h2
    have := div_le_div_of_nonneg_left (sq_nonneg m) (hE t₁) (hEmono t₁ t₂ h1 h2)
    linarith
  have hP'nonpos : ∀ t, t₀ ≤ t → ℰ - m ^ 2 / E t ≤ 0 := by
    intro t₁ h1
    by_contra hb
    push Not at hb
    have hP1 := hneg t₁ h1
    have hd : 0 < (1 - P t₁) / (ℰ - m ^ 2 / E t₁) := div_pos (by linarith) hb
    have hlow := add_mul_le_of_hasDerivAt (a := t₁) (C := ℰ - m ^ 2 / E t₁)
      (fun r _ => hP' r) (fun r hr => hP'mono t₁ r h1 hr)
      (t := t₁ + (1 - P t₁) / (ℰ - m ^ 2 / E t₁)) (by linarith)
    have e : P t₁ + (ℰ - m ^ 2 / E t₁) * (t₁ + (1 - P t₁) / (ℰ - m ^ 2 / E t₁) - t₁) = 1 := by
      field_simp
      ring
    have := hneg (t₁ + (1 - P t₁) / (ℰ - m ^ 2 / E t₁)) (by linarith)
    linarith
  have hPle : ∀ t, t₀ ≤ t → P t ≤ P t₀ := fun t ht => by
    have := le_add_mul_of_hasDerivAt (a := t₀) (C := 0) (fun r _ => hP' r) hP'nonpos ht
    linarith
  have hB : ∀ t, t₀ ≤ t → R t * E t ≤ |ℰ| * R t₀ - α := by
    intro t ht
    rw [hRE t]
    have h1 := hRanti t₀ t le_rfl ht
    have h2 : ℰ * R t ≤ |ℰ| * R t := mul_le_mul_of_nonneg_right (le_abs_self ℰ) (hR t).le
    have h3 : |ℰ| * R t ≤ |ℰ| * R t₀ := mul_le_mul_of_nonneg_left h1 (abs_nonneg ℰ)
    linarith
  have hBpos : 0 < |ℰ| * R t₀ - α := lt_of_lt_of_le (hREpos t₀) (hB t₀ le_rfl)
  have hP0 := hneg t₀ le_rfl
  have hR'le : ∀ t, t₀ ≤ t → P t / (R t * E t) ≤ P t₀ / (|ℰ| * R t₀ - α) := by
    intro t ht
    rw [div_le_div_iff₀ (hREpos t) hBpos]
    nlinarith [mul_nonneg (sub_nonneg.mpr (hPle t ht)) hBpos.le,
      mul_nonneg (neg_nonneg.mpr hP0.le) (sub_nonneg.mpr (hB t ht))]
  obtain ⟨c, hc, hcP⟩ : ∃ c : ℝ, 0 < c ∧ P t₀ / (|ℰ| * R t₀ - α) = -c :=
    ⟨_, neg_pos.mpr (div_neg_of_neg_of_pos hP0 hBpos), (neg_neg _).symm⟩
  rw [hcP] at hR'le
  have hT : t₀ ≤ t₀ + (R t₀ / c + 1) := by
    have := div_pos (hR t₀) hc
    linarith
  have hfin := le_add_mul_of_hasDerivAt (a := t₀) (fun r _ => hR' r) hR'le hT
  have e : R t₀ + -c * (t₀ + (R t₀ / c + 1) - t₀) = -c := by
    have := hc.ne'
    field_simp
    ring
  have := hR (t₀ + (R t₀ / c + 1))
  linarith

/-- The radial equations reach the centre in a finite time, backwards: with the hypotheses of
`not_forall_neg_of_radial`, `P` is not positive at all times before a time `t₀`. -/
theorem not_forall_pos_of_radial {R P E : ℝ → ℝ} {ℰ m α t₀ : ℝ} (hα : α < 0)
    (hR : ∀ t, 0 < R t) (hE : ∀ t, 0 < E t) (hRE : ∀ t, R t * E t = ℰ * R t - α)
    (hR' : ∀ t, HasDerivAt R (P t / (R t * E t)) t)
    (hP' : ∀ t, HasDerivAt P (ℰ - m ^ 2 / E t) t) (hpos : ∀ t, t ≤ t₀ → 0 < P t) : False :=
  not_forall_neg_of_radial (R := fun t => R (-t)) (P := fun t => -P (-t)) (E := fun t => E (-t))
    (t₀ := -t₀) (m := m) hα (fun t => hR _) (fun t => hE _) (fun t => hRE _)
    (fun t => ((hR' (-t)).comp t (hasDerivAt_neg t)).congr_deriv (by ring))
    (fun t => ((hP' (-t)).comp t (hasDerivAt_neg t)).neg.congr_deriv (by ring))
    fun t ht => by
      have := hpos (-t) (by linarith)
      linarith

/-- In an attracting field (`α < 0`, `m > 0`) no solution of Hamilton's equations with the
angular momentum `ℓ² ≤ α²` exists for all times. Along a solution the radial momentum
`p_r = p_s/r` decreases strictly, since `ṗ_r = (α + ℓ²/(r E))/r²` and `ℓ² < |α| r E`; so `p_s`
is negative after a time or positive at all times, and the radial equations reach the centre in
a finite time (`not_forall_neg_of_radial`, `not_forall_pos_of_radial`). -/
theorem not_forall_hasDerivAt (hm : 0 < m) (hα : α < 0) {y : ℝ → PolarPoint}
    (hy : ∀ t, HasDerivAt y (hamiltonianField (coulombHamiltonian m α) (y t)) t)
    (hℓ : pφ.val (y 0) ^ 2 ≤ α ^ 2) : False := by
  have hm0 : m ≠ 0 := hm.ne'
  rw [← lift_real] at hℓ
  have hHt : ∀ t, FreeSmoothRing.lift (y t) (coulombHamiltonian m α) =
      FreeSmoothRing.lift (y 0) (coulombHamiltonian m α) := fun t =>
    lift_eq_of_isIntegral (a := 0) (b := t) (fun r _ => hy r)
      (PoissonStructure.isIntegral_self (π := 𝒫) (coulombHamiltonian m α))
  have hpφt : ∀ t, FreeSmoothRing.lift (y t) pφ = FreeSmoothRing.lift (y 0) pφ := fun t =>
    lift_eq_of_isIntegral (a := 0) (b := t) (fun r _ => hy r) (isIntegral_pφ (α := α) hm0)
  set ℰ := FreeSmoothRing.lift (y 0) (coulombHamiltonian m α) with hℰ
  set ℓ := FreeSmoothRing.lift (y 0) pφ with hℓdef
  have hEEi : ∀ t, FreeSmoothRing.lift (y t) (kineticEnergy m) *
      FreeSmoothRing.lift (y t) (kineticEnergyInv m) = 1 := fun t =>
    lift_kineticEnergy_mul_inv (y t) hm0
  have hEpos : ∀ t, 0 < FreeSmoothRing.lift (y t) (kineticEnergy m) := fun t =>
    lift_kineticEnergy_pos (y t) hm
  have hEipos : ∀ t, 0 < FreeSmoothRing.lift (y t) (kineticEnergyInv m) := fun t =>
    pos_of_mul_pos_right ((hEEi t).symm ▸ one_pos) (hEpos t).le
  -- the radial momentum decreases strictly
  have hpr_neg : ∀ t, FreeSmoothRing.lift (y t)
      ((𝒫).bracket (rInv * pS) (coulombHamiltonian m α)) < 0 := by
    intro t
    rw [canonical_radialMomentum hm0]
    simp only [SmoothRingHom.map_mul, SmoothRingHom.map_add, SmoothRingHom.map_algebraMap,
      Algebra.algebraMap_self_apply, hpφt]
    have hu := lift_rInv_pos (y t)
    have hEE := lift_kineticEnergy_mul_self (y t) hm0
    rw [hpφt] at hEE
    have hE := hEpos t
    have hEi := hEipos t
    have h1 := hEEi t
    set u := FreeSmoothRing.lift (y t) rInv
    set E := FreeSmoothRing.lift (y t) (kineticEnergy m)
    set Ei := FreeSmoothRing.lift (y t) (kineticEnergyInv m)
    set P := FreeSmoothRing.lift (y t) pS
    -- `u ℓ² < −α E`, from `(u ℓ²)² ≤ α² u² ℓ² < α² E²`
    have key : u * (ℓ * ℓ) < -α * E := by
      by_contra hk
      push Not at hk
      have h2 : (-α * E) ^ 2 ≤ (u * (ℓ * ℓ)) ^ 2 :=
        pow_le_pow_left₀ (mul_pos (neg_pos.mpr hα) hE).le hk 2
      have hm2 : 0 < α ^ 2 * m ^ 2 := by
        have : 0 < α ^ 2 := by nlinarith
        positivity
      nlinarith [mul_le_mul_of_nonneg_left hℓ (sq_nonneg (u * ℓ)), sq_nonneg (u * P),
        sq_nonneg α]
    have h3 : α + Ei * (u * (ℓ * ℓ)) < 0 := by
      have : Ei * (α * E + u * (ℓ * ℓ)) < 0 := mul_neg_of_pos_of_neg hEi (by linarith)
      linear_combination this - α * h1
    exact mul_neg_of_pos_of_neg (mul_pos hu hu) h3
  have hanti : StrictAnti fun t => FreeSmoothRing.lift (y t) (rInv * pS) :=
    strictAnti_of_deriv_neg fun t => by
      rw [(hasDerivAt_lift (hy t) (rInv * pS)).deriv]
      exact hpr_neg t
  -- the radial equations
  have hRpos : ∀ t, 0 < FreeSmoothRing.lift (y t) r := fun t => by
    rw [lift_r]
    exact Real.exp_pos _
  have hRE : ∀ t, FreeSmoothRing.lift (y t) r * FreeSmoothRing.lift (y t) (kineticEnergy m) =
      ℰ * FreeSmoothRing.lift (y t) r - α := fun t => by
    have h := lift_coulombHamiltonian (m := m) (α := α) (y t)
    rw [hHt] at h
    rw [h]
    linear_combination (-α) * lift_r_mul_rInv (y t)
  have hR' : ∀ t, HasDerivAt (fun t => FreeSmoothRing.lift (y t) r)
      (FreeSmoothRing.lift (y t) pS / (FreeSmoothRing.lift (y t) r *
        FreeSmoothRing.lift (y t) (kineticEnergy m))) t := fun t => by
    refine (hasDerivAt_lift (hy t) r).congr_deriv ?_
    rw [canonical_r hm0, SmoothRingHom.map_mul, SmoothRingHom.map_mul,
      eq_div_iff (mul_pos (hRpos t) (hEpos t)).ne']
    linear_combination (FreeSmoothRing.lift (y t) pS * FreeSmoothRing.lift (y t) r *
        FreeSmoothRing.lift (y t) rInv) * hEEi t +
      FreeSmoothRing.lift (y t) pS * lift_r_mul_rInv (y t)
  have hP' : ∀ t, HasDerivAt (fun t => FreeSmoothRing.lift (y t) pS)
      (ℰ - m ^ 2 / FreeSmoothRing.lift (y t) (kineticEnergy m)) t := fun t => by
    refine (hasDerivAt_lift (hy t) pS).congr_deriv ?_
    rw [canonical_pS hm0, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
      SmoothRingHom.map_algebraMap, Algebra.algebraMap_self_apply, hHt, div_eq_mul_inv,
      ← eq_inv_of_mul_eq_one_right (hEEi t)]
  have hsign : ∀ t, FreeSmoothRing.lift (y t) (rInv * pS) =
      FreeSmoothRing.lift (y t) rInv * FreeSmoothRing.lift (y t) pS := fun t =>
    SmoothRingHom.map_mul _ _ _
  by_cases h : ∃ t₀, FreeSmoothRing.lift (y t₀) (rInv * pS) < 0
  · obtain ⟨t₀, ht₀⟩ := h
    refine not_forall_neg_of_radial hα hRpos hEpos hRE hR' hP' (t₀ := t₀) fun t ht => ?_
    have h1 : FreeSmoothRing.lift (y t) (rInv * pS) < 0 :=
      lt_of_le_of_lt (hanti.antitone ht) ht₀
    rw [hsign] at h1
    by_contra hP
    push Not at hP
    exact absurd h1 (not_lt.mpr (mul_nonneg (lift_rInv_pos (y t)).le hP))
  · push Not at h
    refine not_forall_pos_of_radial hα hRpos hEpos hRE hR' hP' (t₀ := 0) fun t _ => ?_
    have h1 : 0 < FreeSmoothRing.lift (y t) (rInv * pS) :=
      lt_of_le_of_lt (h (t + 1)) (hanti (lt_add_one t))
    rw [hsign] at h1
    exact pos_of_mul_pos_right h1 (lift_rInv_pos (y t)).le

/-- Fall to the centre (Landau–Lifshitz §39): in an attracting field (`α < 0`, `m > 0`), from
every point with the angular momentum `ℓ² ≤ α²` the flow of Hamilton's equations leaves its
maximal domain at a finite time `t`, in one of the two directions of time. Between the times
`0` and `t` there is no solution (`mem_flowDomain_iff`). -/
theorem fall_to_centre (hm : 0 < m) (hα : α < 0) (z : PolarPoint)
    (hℓ : pφ.val z ^ 2 ≤ α ^ 2) :
    ∃ t, (t, z) ∉ flowDomain (hamiltonianField (coulombHamiltonian m α)) := by
  by_contra h
  push Not at h
  exact not_forall_hasDerivAt hm hα
    (y := fun t => flow (hamiltonianField (coulombHamiltonian m α)) (t, z))
    (fun t => hasDerivAt_flow (contDiff_hamiltonianField _) (h t)) (by rwa [flow_zero])

/-- In an attracting field no trajectory with the angular momentum `ℓ² ≤ α²` exists for all
times. -/
theorem not_isTrajectory_of_sq_le (hm : 0 < m) (hα : α < 0)
    {c : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}
    (hℓ : pφ.val (realCurve c 0) ^ 2 ≤ α ^ 2) :
    ¬ IsTrajectory (𝒫) (coulombHamiltonian m α) c := fun hc =>
  not_forall_hasDerivAt hm hα ((isTrajectory_canonical_iff_hasDerivAt _ c).mp hc) hℓ

/-! ### Collision -/

/-- The speed is less than one: `|p_r/E| < 1` and `|p_φ/(r E)| < 1`. -/
theorem abs_kineticEnergyInv_mul_lt_one (hm : m ≠ 0) (z : PolarPoint) :
    |FreeSmoothRing.lift z (kineticEnergyInv m) * FreeSmoothRing.lift z (rInv * pS)| < 1 ∧
      |FreeSmoothRing.lift z (kineticEnergyInv m) * FreeSmoothRing.lift z (rInv * pφ)| < 1 := by
  have h0 := abs_relEnergyInv_mul_lt_one hm (fun i => FreeSmoothRing.lift z (polarMomentum i)) 0
  have h1 := abs_relEnergyInv_mul_lt_one hm (fun i => FreeSmoothRing.lift z (polarMomentum i)) 1
  rw [kineticEnergyInv, SmoothRingHom.map_relEnergyInv]
  exact ⟨h0, h1⟩

/-- A bound of the rate of an observable along a solution between the times `0` and `t` bounds
its change. -/
theorem abs_lift_sub_le {H G : Polar} {y : ℝ → PolarPoint} {t C : ℝ}
    (hy : ∀ τ ∈ uIcc 0 t, HasDerivAt y (hamiltonianField H (y τ)) τ)
    (hC : ∀ τ ∈ uIcc 0 t, |FreeSmoothRing.lift (y τ) ((𝒫).bracket G H)| ≤ C) :
    |FreeSmoothRing.lift (y t) G - FreeSmoothRing.lift (y 0) G| ≤ C * |t| := by
  have h := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun τ => FreeSmoothRing.lift (y τ) G)
    (fun τ hτ => (hasDerivAt_lift (hy τ hτ) G).hasDerivWithinAt)
    (fun τ hτ => by
      rw [Real.norm_eq_abs]
      exact hC τ hτ) left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs, sub_zero] using h

/-- Collision: if the flow of the Coulomb Hamiltonian through `z` leaves its domain at the time
`T`, then between the times `0` and `T` the radius becomes smaller than every `ε > 0`. The
speed is less than one, so while the radius is at least `ε` the solution stays in a compact
set, and it does not leave the domain (`mem_flowDomain_of_isCompact`). -/
theorem exists_r_lt_of_not_mem_flowDomain (hm : 0 < m) {z : PolarPoint} {T : ℝ}
    (hT : (T, z) ∉ flowDomain (hamiltonianField (coulombHamiltonian m α))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ t ∈ uIcc 0 T, (t, z) ∈ flowDomain (hamiltonianField (coulombHamiltonian m α)) ∧
      r.val (flow (hamiltonianField (coulombHamiltonian m α)) (t, z)) < ε := by
  have hm0 : m ≠ 0 := hm.ne'
  by_contra hcon
  push Not at hcon
  apply hT
  set X := hamiltonianField (coulombHamiltonian m α) with hX
  set ρ := FreeSmoothRing.lift z r + |T| with hρ
  set B := ρ * (|FreeSmoothRing.lift z (coulombHamiltonian m α)| + |α| / ε) with hB
  set lo : PolarPoint := Sum.elim
    (Sum.elim (fun _ => Real.log ε) fun _ => FreeSmoothRing.lift z φ - |T| / ε)
    (Sum.elim (fun _ => -B) fun _ => FreeSmoothRing.lift z pφ) with hlo
  set hi : PolarPoint := Sum.elim
    (Sum.elim (fun _ => Real.log ρ) fun _ => FreeSmoothRing.lift z φ + |T| / ε)
    (Sum.elim (fun _ => B) fun _ => FreeSmoothRing.lift z pφ) with hhi
  refine mem_flowDomain_of_isCompact (contDiff_hamiltonianField _)
    (K := Set.pi univ fun a => Icc (lo a) (hi a)) (isCompact_univ_pi fun a => isCompact_Icc)
    fun t ht hD => ?_
  have hy := hasDerivAt_hamiltonianFlow hD
  set y := fun τ => flow X (τ, z) with hydef
  have hy0 : y 0 = z := flow_zero X z
  have hrε : ∀ τ ∈ uIcc 0 t, ε ≤ FreeSmoothRing.lift (y τ) r := fun τ hτ => by
    rw [lift_real]
    exact hcon τ (uIcc_subset_uIcc_left ht hτ) (mem_flowDomain_of_mem_uIcc hD hτ)
  have hu : ∀ τ ∈ uIcc 0 t, FreeSmoothRing.lift (y τ) rInv ≤ 1 / ε := fun τ hτ => by
    have h1 := lift_r_mul_rInv (y τ)
    have h2 := hrε τ hτ
    have h3 := lift_rInv_pos (y τ)
    rw [le_div_iff₀ hε]
    nlinarith
  have htT : |t| ≤ |T| := by
    rcases mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
      exact h2
    · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
      linarith
  have hpφ : FreeSmoothRing.lift (y t) pφ = FreeSmoothRing.lift z pφ := by
    rw [lift_eq_of_isIntegral hy (isIntegral_pφ (α := α) hm0), hy0]
  have hH : FreeSmoothRing.lift (y t) (coulombHamiltonian m α) =
      FreeSmoothRing.lift z (coulombHamiltonian m α) := by
    rw [lift_eq_of_isIntegral hy
      (PoissonStructure.isIntegral_self (π := 𝒫) (coulombHamiltonian m α)), hy0]
  -- the radius changes at a speed less than one
  have hr : |FreeSmoothRing.lift (y t) r - FreeSmoothRing.lift z r| ≤ 1 * |t| := by
    rw [← hy0]
    refine abs_lift_sub_le hy fun τ _ => ?_
    rw [canonical_r hm0, SmoothRingHom.map_mul]
    exact (abs_kineticEnergyInv_mul_lt_one hm0 (y τ)).1.le
  -- the angle changes at a rate at most `1/ε`
  have hφ : |FreeSmoothRing.lift (y t) φ - FreeSmoothRing.lift z φ| ≤ 1 / ε * |t| := by
    rw [← hy0]
    refine abs_lift_sub_le hy fun τ hτ => ?_
    rw [canonical_φ hm0]
    have h1 := (abs_kineticEnergyInv_mul_lt_one hm0 (y τ)).2
    have h2 := hu τ hτ
    have h3 := lift_rInv_pos (y τ)
    have e : FreeSmoothRing.lift (y τ) (kineticEnergyInv m * (rInv * rInv * pφ)) =
        FreeSmoothRing.lift (y τ) rInv * (FreeSmoothRing.lift (y τ) (kineticEnergyInv m) *
          FreeSmoothRing.lift (y τ) (rInv * pφ)) := by
      simp only [SmoothRingHom.map_mul]
      ring
    rw [e, abs_mul, abs_of_pos h3]
    calc _ ≤ FreeSmoothRing.lift (y τ) rInv * 1 :=
          mul_le_mul_of_nonneg_left h1.le h3.le
      _ ≤ 1 / ε := by rw [mul_one]; exact h2
  have hrt : FreeSmoothRing.lift (y t) r ≤ ρ := by
    have := (abs_le.mp hr).2
    linarith
  -- the momentum `p_s = r p_r` is bounded
  have hpS : |FreeSmoothRing.lift (y t) pS| ≤ B := by
    have h1 := (abs_kineticEnergyInv_mul_lt_one hm0 (y t)).1
    have hE := lift_kineticEnergy_pos (y t) hm
    have hEEi := lift_kineticEnergy_mul_inv (y t) hm0
    have hHt := lift_coulombHamiltonian (m := m) (α := α) (y t)
    rw [hH] at hHt
    have hu1 := hu t right_mem_uIcc
    have hu0 := lift_rInv_pos (y t)
    have hrpos : 0 < FreeSmoothRing.lift (y t) r := by
      rw [lift_r]
      exact Real.exp_pos _
    have hrr := lift_r_mul_rInv (y t)
    rw [SmoothRingHom.map_mul] at h1
    set E := FreeSmoothRing.lift (y t) (kineticEnergy m)
    set Ei := FreeSmoothRing.lift (y t) (kineticEnergyInv m)
    set u := FreeSmoothRing.lift (y t) rInv
    set P := FreeSmoothRing.lift (y t) pS
    set R := FreeSmoothRing.lift (y t) r
    set ℰ := FreeSmoothRing.lift z (coulombHamiltonian m α)
    -- `|u P| ≤ E`
    have huP : |u * P| ≤ E := by
      have e : u * P = E * (Ei * (u * P)) := by linear_combination (-(u * P)) * hEEi
      rw [e, abs_mul, abs_of_pos hE]
      nlinarith [abs_nonneg (Ei * (u * P))]
    -- `E = ℰ − α u ≤ |ℰ| + |α|/ε`
    have hEb : E ≤ |ℰ| + |α| / ε := by
      have : -α * u ≤ |α| / ε := by
        calc -α * u ≤ |α| * u := mul_le_mul_of_nonneg_right (neg_le_abs α) hu0.le
          _ ≤ |α| * (1 / ε) := mul_le_mul_of_nonneg_left hu1 (abs_nonneg α)
          _ = |α| / ε := by ring
      linarith [le_abs_self ℰ]
    have eP : P = R * (u * P) := by linear_combination (-P) * hrr
    rw [eP, abs_mul, abs_of_pos hrpos, hB]
    exact mul_le_mul hrt (huP.trans hEb) (abs_nonneg _) (hrpos.le.trans hrt)
  -- the point lies in the box
  rw [Set.mem_pi]
  rintro ((i | i) | (i | i)) - <;> obtain rfl := Subsingleton.elim i 0
  · have hs : flow X (t, z) (Sum.inl (Sum.inl 0)) = FreeSmoothRing.lift (y t) s :=
      (lift_s (y t)).symm
    have hR : FreeSmoothRing.lift (y t) r = Real.exp (FreeSmoothRing.lift (y t) s) := by
      rw [lift_r, lift_s]
    have h1 := hrε t right_mem_uIcc
    rw [hR] at h1 hrt
    rw [hs]
    constructor
    · exact (Real.log_le_iff_le_exp hε).mpr h1
    · exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hrt)).mpr hrt
  · have hs : flow X (t, z) (Sum.inl (Sum.inr 0)) = FreeSmoothRing.lift (y t) φ :=
      (lift_φ (y t)).symm
    rw [hs]
    have h1 := abs_le.mp hφ
    have h2 : 1 / ε * |t| ≤ |T| / ε := by
      rw [div_eq_mul_one_div |T|, mul_comm (|T|)]
      exact mul_le_mul_of_nonneg_left htT (by positivity)
    constructor <;> simp only [hlo, hhi, Sum.elim_inl, Sum.elim_inr] <;> linarith [h1.1, h1.2]
  · have hs : flow X (t, z) (Sum.inr (Sum.inl 0)) = FreeSmoothRing.lift (y t) pS :=
      (lift_pS (y t)).symm
    rw [hs]
    exact abs_le.mp hpS
  · have hs : flow X (t, z) (Sum.inr (Sum.inr 0)) = FreeSmoothRing.lift (y t) pφ :=
      (lift_pφ (y t)).symm
    rw [hs, hpφ]
    exact ⟨le_rfl, le_rfl⟩

/-- Fall to the centre with collision (Landau–Lifshitz §39): in an attracting field, from every
point with the angular momentum `ℓ² ≤ α²` the flow leaves its domain at a finite time `T`, and
before `T` the radius becomes smaller than every `ε > 0`. The motion after the collision is not
part of this model. -/
theorem fall_to_centre_collision (hm : 0 < m) (hα : α < 0) (z : PolarPoint)
    (hℓ : pφ.val z ^ 2 ≤ α ^ 2) :
    ∃ T, (T, z) ∉ flowDomain (hamiltonianField (coulombHamiltonian m α)) ∧
      ∀ ε, 0 < ε → ∃ t ∈ uIcc 0 T,
        (t, z) ∈ flowDomain (hamiltonianField (coulombHamiltonian m α)) ∧
          r.val (flow (hamiltonianField (coulombHamiltonian m α)) (t, z)) < ε := by
  obtain ⟨T, hT⟩ := fall_to_centre hm hα z hℓ
  exact ⟨T, hT, fun ε hε => exists_r_lt_of_not_mem_flowDomain hm hT hε⟩

end ProjectAinos.Electrodynamics.CoulombMotion
