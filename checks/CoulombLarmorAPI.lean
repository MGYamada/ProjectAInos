/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.CoulombMotion
import ProjectAinos.Electrodynamics.Larmor

/-! Public consumers of motion in the Coulomb field and Larmor's theorem (Landau–Lifshitz §§39, 45):
the relativistic Coulomb Hamiltonian in polar co-ordinates, its brackets and integrals, the orbit
functions, the rosette with its perihelion spacing and the circular instance, the spiral orbits on
intervals, the fall to the centre and the collision; the symmetric gauge, the exact identity between
the Hamiltonian in a uniform field and the rotating-frame Hamiltonian, its N-particle form with a
common ratio of charge to mass, the error bound for given solutions and the oscillator example.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section CoulombMotion

namespace ProjectAinos.Electrodynamics.CoulombMotion

open Set

open SmoothAlgebra SmoothRing FreeSmoothRing Mechanics Mechanics.CentralField

open SmoothGeometry SmoothGeometry.NonlinearODE

example :
    Fin 2 → Polar :=
  polarMomentum

example (m : ℝ) :
    Polar :=
  kineticEnergy m

example (m : ℝ) :
    Polar :=
  kineticEnergyInv m

example (m α : ℝ) :
    Polar :=
  coulombHamiltonian m α

variable {m α : ℝ}

example (hm : m ≠ 0) :
    kineticEnergy m * kineticEnergy m =
      algebraMap ℝ Polar (m ^ 2) + rInv * rInv * (pS * pS + pφ * pφ) :=
  kineticEnergy_mul_self hm

example (hm : m ≠ 0) :
    kineticEnergy m * kineticEnergyInv m = 1 :=
  kineticEnergy_mul_kineticEnergyInv hm

example (hm : m ≠ 0) (D : SmoothDerivation Polar Polar) :
    D (kineticEnergy m) =
      kineticEnergyInv m * (rInv * pS * D (rInv * pS) + rInv * pφ * D (rInv * pφ)) :=
  apply_kineticEnergy hm D

example (hm : m ≠ 0) :
    dS (coulombHamiltonian m α) =
      -(kineticEnergyInv m * (rInv * rInv * (pS * pS + pφ * pφ))) -
        algebraMap ℝ Polar α * rInv :=
  dS_coulombHamiltonian hm

example (hm : m ≠ 0) :
    dφ (coulombHamiltonian m α) = 0 :=
  dφ_coulombHamiltonian hm

example (hm : m ≠ 0) :
    dPS (coulombHamiltonian m α) = kineticEnergyInv m * (rInv * rInv * pS) :=
  dPS_coulombHamiltonian hm

example (hm : m ≠ 0) :
    dPφ (coulombHamiltonian m α) = kineticEnergyInv m * (rInv * rInv * pφ) :=
  dPφ_coulombHamiltonian hm

local notation "𝒫" => PhaseSpace.canonical (Fin 1 ⊕ Fin 1)

example (hm : m ≠ 0) (f : Polar) :
    (𝒫).bracket f (coulombHamiltonian m α) =
      dS f * (kineticEnergyInv m * (rInv * rInv * pS)) +
        dPS f * (kineticEnergyInv m * (rInv * rInv * (pS * pS + pφ * pφ)) +
          algebraMap ℝ Polar α * rInv) +
        dφ f * (kineticEnergyInv m * (rInv * rInv * pφ)) :=
  bracket_coulombHamiltonian hm f

example (hm : m ≠ 0) :
    (𝒫).bracket s (coulombHamiltonian m α) = kineticEnergyInv m * (rInv * rInv * pS) :=
  canonical_s hm

example (hm : m ≠ 0) :
    (𝒫).bracket φ (coulombHamiltonian m α) = kineticEnergyInv m * (rInv * rInv * pφ) :=
  canonical_φ hm

example (hm : m ≠ 0) :
    (𝒫).bracket pS (coulombHamiltonian m α) =
      coulombHamiltonian m α - algebraMap ℝ Polar (m ^ 2) * kineticEnergyInv m :=
  canonical_pS hm

example (hm : m ≠ 0) :
    (𝒫).bracket pφ (coulombHamiltonian m α) = 0 :=
  canonical_pφ hm

example (hm : m ≠ 0) :
    (𝒫).IsIntegral (coulombHamiltonian m α) pφ :=
  isIntegral_pφ hm

example (hm : m ≠ 0) :
    (𝒫).bracket rInv (coulombHamiltonian m α) =
      -(kineticEnergyInv m * (rInv * rInv * rInv * pS)) :=
  canonical_rInv hm

example (hm : m ≠ 0) :
    (𝒫).bracket r (coulombHamiltonian m α) = kineticEnergyInv m * (rInv * pS) :=
  canonical_r hm

example (hm : m ≠ 0) :
    (𝒫).bracket (rInv * pS) (coulombHamiltonian m α) =
      rInv * rInv * (algebraMap ℝ Polar α + kineticEnergyInv m * (rInv * (pφ * pφ))) :=
  canonical_radialMomentum hm

example (m α : ℝ) :
    Polar :=
  orbitX m α

example :
    Polar :=
  orbitY

example (hm : m ≠ 0) :
    (𝒫).bracket (orbitX m α) (coulombHamiltonian m α) =
      -((pφ * pφ - algebraMap ℝ Polar (α ^ 2)) * pS * rInv * rInv * rInv *
        kineticEnergyInv m) :=
  canonical_orbitX hm

example (hm : m ≠ 0) :
    (𝒫).bracket orbitY (coulombHamiltonian m α) =
      orbitX m α * pφ * rInv * rInv * kineticEnergyInv m :=
  canonical_orbitY hm

example (hm : m ≠ 0) :
    pφ * pφ * (𝒫).bracket (orbitX m α) (coulombHamiltonian m α) =
      (algebraMap ℝ Polar (α ^ 2) - pφ * pφ) * orbitY *
        (𝒫).bracket φ (coulombHamiltonian m α) :=
  canonical_orbitX_eq hm

example (hm : m ≠ 0) :
    (𝒫).bracket orbitY (coulombHamiltonian m α) =
      orbitX m α * (𝒫).bracket φ (coulombHamiltonian m α) :=
  canonical_orbitY_eq hm

example (hm : m ≠ 0) :
    (coulombHamiltonian m α - algebraMap ℝ Polar α * rInv) *
        (coulombHamiltonian m α - algebraMap ℝ Polar α * rInv) =
      algebraMap ℝ Polar (m ^ 2) + rInv * rInv * (pS * pS + pφ * pφ) :=
  coulombHamiltonian_sub_mul_self hm

example (hm : m ≠ 0) :
    orbitX m α * orbitX m α +
        (pφ * pφ - algebraMap ℝ Polar (α ^ 2)) * (rInv * pS) * (rInv * pS) =
      pφ * pφ * (coulombHamiltonian m α * coulombHamiltonian m α) -
        algebraMap ℝ Polar (m ^ 2) * (pφ * pφ - algebraMap ℝ Polar (α ^ 2)) :=
  orbitX_mul_self_add hm

example (hm : m ≠ 0) :
    orbitY * orbitY =
      pφ * pφ * (coulombHamiltonian m α * coulombHamiltonian m α - algebraMap ℝ Polar (m ^ 2)) -
        algebraMap ℝ Polar (2 * α) * pφ * pφ * coulombHamiltonian m α * rInv +
        pφ * pφ * (algebraMap ℝ Polar (α ^ 2) - pφ * pφ) * (rInv * rInv) :=
  orbitY_mul_self hm

example :
    Type :=
  PolarPoint

example {H : Polar} {y : ℝ → PolarPoint} {t : ℝ} (hy : HasDerivAt y (hamiltonianField H (y t)) t)
    (G : Polar) :
    HasDerivAt (fun r => FreeSmoothRing.lift (y r) G)
      (FreeSmoothRing.lift (y t) ((𝒫).bracket G H)) t :=
  hasDerivAt_lift hy G

example {H G : Polar} {y : ℝ → PolarPoint} {a b : ℝ}
    (hy : ∀ t ∈ uIcc a b, HasDerivAt y (hamiltonianField H (y t)) t) (hG : (𝒫).IsIntegral H G) :
    FreeSmoothRing.lift (y b) G = FreeSmoothRing.lift (y a) G :=
  lift_eq_of_isIntegral hy hG

example {X Y ψ ψ' C S : ℝ → ℝ} {k a b : ℝ} (hX : ∀ t ∈ uIcc a b, HasDerivAt X (k * Y t * ψ' t) t)
    (hY : ∀ t ∈ uIcc a b, HasDerivAt Y (X t * ψ' t) t)
    (hψ : ∀ t ∈ uIcc a b, HasDerivAt ψ (ψ' t) t) (hC : ∀ x, HasDerivAt C (k * S x) x)
    (hS : ∀ x, HasDerivAt S (C x) x) (hCS : ∀ x, C x * C x - k * (S x * S x) = 1) (hψa : ψ a = 0)
    (hC0 : C 0 = 1) (hS0 : S 0 = 0) :
    X b = X a * C (ψ b) + k * Y a * S (ψ b) ∧ Y b = Y a * C (ψ b) + X a * S (ψ b) :=
  eq_of_hasDerivAt_angle hX hY hψ hC hS hCS hψa hC0 hS0

example (hm : m ≠ 0) {y : ℝ → PolarPoint} {a b ℓ : ℝ}
    (hy : ∀ t ∈ uIcc a b, HasDerivAt y (hamiltonianField (coulombHamiltonian m α) (y t)) t)
    (hℓ : pφ.val (y a) = ℓ) (hℓ0 : ℓ ≠ 0) {C S : ℝ → ℝ}
    (hC : ∀ x, HasDerivAt C ((α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * S x) x) (hS : ∀ x, HasDerivAt S (C x) x)
    (hCS : ∀ x, C x * C x - (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * (S x * S x) = 1) (hC0 : C 0 = 1)
    (hS0 : S 0 = 0) :
    (orbitX m α).val (y b) = (orbitX m α).val (y a) * C (φ.val (y b) - φ.val (y a)) +
        (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 * orbitY.val (y a) * S (φ.val (y b) - φ.val (y a)) ∧
      orbitY.val (y b) = orbitY.val (y a) * C (φ.val (y b) - φ.val (y a)) +
        (orbitX m α).val (y a) * S (φ.val (y b) - φ.val (y a)) :=
  orbit_eq hm hy hℓ hℓ0 hC hS hCS hC0 hS0

example {H : Polar} {z : PolarPoint} {t : ℝ} (h : (t, z) ∈ flowDomain (hamiltonianField H)) :
    ∀ r ∈ uIcc 0 t, HasDerivAt (fun τ => flow (hamiltonianField H) (τ, z))
      (hamiltonianField H (flow (hamiltonianField H) (r, z))) r :=
  hasDerivAt_hamiltonianFlow h

example (α ℓ : ℝ) :
    ℝ :=
  rosetteRate α ℓ

example {ℓ : ℝ} (h : α ^ 2 < ℓ ^ 2) :
    0 < rosetteRate α ℓ :=
  rosetteRate_pos h

example {ℓ : ℝ} (h : α ^ 2 < ℓ ^ 2) :
    rosetteRate α ℓ ^ 2 = (ℓ ^ 2 - α ^ 2) / ℓ ^ 2 :=
  rosetteRate_sq h

example {ℓ : ℝ} (h : α ^ 2 < ℓ ^ 2) :
    2 * Real.pi / rosetteRate α ℓ = 2 * Real.pi * |ℓ| / Real.sqrt (ℓ ^ 2 - α ^ 2) :=
  two_pi_div_rosetteRate h

example {ℓ : ℝ} (h : α ^ 2 < ℓ ^ 2) (hα : α ≠ 0) :
    2 * Real.pi < 2 * Real.pi / rosetteRate α ℓ :=
  two_pi_lt_two_pi_div_rosetteRate h hα

example (hm : m ≠ 0) {c : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}
    (hc : IsTrajectory (𝒫) (coulombHamiltonian m α) c) {ℓ : ℝ} (hℓ : pφ.val (realCurve c 0) = ℓ)
    (hℓα : α ^ 2 < ℓ ^ 2) (t : ℝ) :
    (orbitX m α).val (realCurve c t) =
        (orbitX m α).val (realCurve c 0) *
            Real.cos (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) -
          rosetteRate α ℓ * orbitY.val (realCurve c 0) *
            Real.sin (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) ∧
      orbitY.val (realCurve c t) =
        orbitY.val (realCurve c 0) *
            Real.cos (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) +
          (rosetteRate α ℓ)⁻¹ * (orbitX m α).val (realCurve c 0) *
            Real.sin (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) :=
  rosette hm hc hℓ hℓα t

example (hm : m ≠ 0) {c : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}
    (hc : IsTrajectory (𝒫) (coulombHamiltonian m α) c) {ℓ : ℝ} (hℓ : pφ.val (realCurve c 0) = ℓ)
    (hℓα : α ^ 2 < ℓ ^ 2) (t : ℝ) :
    (ℓ ^ 2 - α ^ 2) * rInv.val (realCurve c t) =
      (orbitX m α).val (realCurve c 0) *
          Real.cos (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) -
        rosetteRate α ℓ * orbitY.val (realCurve c 0) *
          Real.sin (rosetteRate α ℓ * (φ.val (realCurve c t) - φ.val (realCurve c 0))) -
        α * (coulombHamiltonian m α).val (realCurve c 0) :=
  rosette_rInv hm hc hℓ hℓα t

example (hm : m ≠ 0) (z : PolarPoint) {ℓ : ℝ} (hℓ : pφ.val z = ℓ) (hℓα : α ^ 2 < ℓ ^ 2) :
    (orbitX m α).val z ^ 2 + rosetteRate α ℓ ^ 2 * orbitY.val z ^ 2 =
      ℓ ^ 2 * (coulombHamiltonian m α).val z ^ 2 - m ^ 2 * (ℓ ^ 2 - α ^ 2) :=
  rosette_amplitude hm z hℓ hℓα

example (X₀ Y₀ κ ψ : ℝ) :
    X₀ * Real.cos (κ * ψ) - κ * Y₀ * Real.sin (κ * ψ) ≤ Real.sqrt (X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2) :=
  orbit_le_sqrt X₀ Y₀ κ ψ

example {X₀ Y₀ κ ψ₁ ψ₂ : ℝ} (hκ : 0 < κ) (hA : 0 < X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2)
    (h₁ : X₀ * Real.cos (κ * ψ₁) - κ * Y₀ * Real.sin (κ * ψ₁) =
      Real.sqrt (X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2)) :
    X₀ * Real.cos (κ * ψ₂) - κ * Y₀ * Real.sin (κ * ψ₂) =
        Real.sqrt (X₀ ^ 2 + κ ^ 2 * Y₀ ^ 2) ↔
      ∃ n : ℤ, ψ₂ = ψ₁ + n * (2 * Real.pi / κ) :=
  perihelion_iff hκ hA h₁

example (α ℓ : ℝ) :
    ℝ :=
  spiralRate α ℓ

example {ℓ : ℝ} (hℓ0 : ℓ ≠ 0) (h : ℓ ^ 2 < α ^ 2) :
    0 < spiralRate α ℓ :=
  spiralRate_pos hℓ0 h

example {ℓ : ℝ} (hℓ0 : ℓ ≠ 0) (h : ℓ ^ 2 < α ^ 2) :
    spiralRate α ℓ ^ 2 = (α ^ 2 - ℓ ^ 2) / ℓ ^ 2 :=
  spiralRate_sq hℓ0 h

example (hm : m ≠ 0) {y : ℝ → PolarPoint} {a b ℓ : ℝ}
    (hy : ∀ t ∈ uIcc a b, HasDerivAt y (hamiltonianField (coulombHamiltonian m α) (y t)) t)
    (hℓ : pφ.val (y a) = ℓ) (hℓ0 : ℓ ≠ 0) (hℓα : ℓ ^ 2 < α ^ 2) :
    (orbitX m α).val (y b) =
        (orbitX m α).val (y a) * Real.cosh (spiralRate α ℓ * (φ.val (y b) - φ.val (y a))) +
          spiralRate α ℓ * orbitY.val (y a) *
            Real.sinh (spiralRate α ℓ * (φ.val (y b) - φ.val (y a))) ∧
      orbitY.val (y b) =
        orbitY.val (y a) * Real.cosh (spiralRate α ℓ * (φ.val (y b) - φ.val (y a))) +
          (spiralRate α ℓ)⁻¹ * (orbitX m α).val (y a) *
            Real.sinh (spiralRate α ℓ * (φ.val (y b) - φ.val (y a))) :=
  orbit_hyperbolic hm hy hℓ hℓ0 hℓα

example (hm : m ≠ 0) {y : ℝ → PolarPoint} {a b ℓ : ℝ}
    (hy : ∀ t ∈ uIcc a b, HasDerivAt y (hamiltonianField (coulombHamiltonian m α) (y t)) t)
    (hℓ : pφ.val (y a) = ℓ) (hℓ0 : ℓ ≠ 0) (hℓα : ℓ ^ 2 = α ^ 2) :
    orbitY.val (y b) = orbitY.val (y a) +
        α * (coulombHamiltonian m α).val (y a) * (φ.val (y b) - φ.val (y a)) ∧
      2 * α * ℓ ^ 2 * (coulombHamiltonian m α).val (y a) * rInv.val (y b) =
        ℓ ^ 2 * ((coulombHamiltonian m α).val (y a) ^ 2 - m ^ 2) -
          (orbitY.val (y a) +
            α * (coulombHamiltonian m α).val (y a) * (φ.val (y b) - φ.val (y a))) ^ 2 :=
  orbit_linear hm hy hℓ hℓ0 hℓα

section Values

variable (z : PolarPoint)

example :
    FreeSmoothRing.lift z s = z (Sum.inl (Sum.inl 0)) :=
  lift_s z

example :
    FreeSmoothRing.lift z φ = z (Sum.inl (Sum.inr 0)) :=
  lift_φ z

example :
    FreeSmoothRing.lift z pS = z (Sum.inr (Sum.inl 0)) :=
  lift_pS z

example :
    FreeSmoothRing.lift z pφ = z (Sum.inr (Sum.inr 0)) :=
  lift_pφ z

example :
    FreeSmoothRing.lift z r = Real.exp (z (Sum.inl (Sum.inl 0))) :=
  lift_r z

example :
    FreeSmoothRing.lift z rInv = Real.exp (-z (Sum.inl (Sum.inl 0))) :=
  lift_rInv z

example :
    0 < FreeSmoothRing.lift z rInv :=
  lift_rInv_pos z

example :
    FreeSmoothRing.lift z r * FreeSmoothRing.lift z rInv = 1 :=
  lift_r_mul_rInv z

example (hm : 0 < m) :
    0 < FreeSmoothRing.lift z (kineticEnergy m) :=
  lift_kineticEnergy_pos z hm

example (hm : m ≠ 0) :
    FreeSmoothRing.lift z (kineticEnergy m) * FreeSmoothRing.lift z (kineticEnergyInv m) = 1 :=
  lift_kineticEnergy_mul_inv z hm

example (hm : m ≠ 0) :
    FreeSmoothRing.lift z (kineticEnergy m) * FreeSmoothRing.lift z (kineticEnergy m) =
      m ^ 2 + FreeSmoothRing.lift z rInv * FreeSmoothRing.lift z rInv *
        (FreeSmoothRing.lift z pS * FreeSmoothRing.lift z pS +
          FreeSmoothRing.lift z pφ * FreeSmoothRing.lift z pφ) :=
  lift_kineticEnergy_mul_self z hm

example :
    FreeSmoothRing.lift z (coulombHamiltonian m α) =
      FreeSmoothRing.lift z (kineticEnergy m) + α * FreeSmoothRing.lift z rInv :=
  lift_coulombHamiltonian z

example (hm : 0 < m) :
    (coulombHamiltonian m α).val z =
      Real.sqrt (m ^ 2 + Real.exp (-z (Sum.inl (Sum.inl 0))) ^ 2 *
          (z (Sum.inr (Sum.inl 0)) ^ 2 + z (Sum.inr (Sum.inr 0)) ^ 2)) +
        α * Real.exp (-z (Sum.inl (Sum.inl 0))) :=
  val_coulombHamiltonian z hm

end Values

example (a b : ℝ) :
    TimeFunction :=
  affineTime a b

example (a b : ℝ) (x : Fin 1 → ℝ) :
    affineTime a b x = a + b * x 0 :=
  affineTime_apply a b x

example (a b t : ℝ) :
    HasDerivAt (fun r : ℝ => affineTime a b fun _ => r) b t :=
  hasDerivAt_affineTime a b t

example (s₀ ϖ ℓ : ℝ) :
    (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction :=
  circularOrbit s₀ ϖ ℓ

example (hm : 0 < m) (hα : α < 0) {ℓ s₀ : ℝ} (hℓ : α ^ 2 < ℓ ^ 2)
    (hs₀ : Real.exp (-(2 * s₀)) = α ^ 2 * m ^ 2 / (ℓ ^ 2 * (ℓ ^ 2 - α ^ 2))) :
    IsTrajectory (𝒫) (coulombHamiltonian m α)
      (circularOrbit s₀ (-α * Real.exp (-s₀) / ℓ) ℓ) :=
  isTrajectory_circular hm hα hℓ hs₀

example (hm : 0 < m) (hα : α < 0) {ℓ : ℝ} (hℓ : α ^ 2 < ℓ ^ 2) :
    ∃ c : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction,
      IsTrajectory (𝒫) (coulombHamiltonian m α) c ∧ pφ.val (realCurve c 0) = ℓ :=
  exists_isTrajectory_circular hm hα hℓ

example {f f' : ℝ → ℝ} {a C t : ℝ} (hf : ∀ r, a ≤ r → HasDerivAt f (f' r) r)
    (hC : ∀ r, a ≤ r → f' r ≤ C) (ht : a ≤ t) :
    f t ≤ f a + C * (t - a) :=
  le_add_mul_of_hasDerivAt hf hC ht

example {f f' : ℝ → ℝ} {a C t : ℝ} (hf : ∀ r, a ≤ r → HasDerivAt f (f' r) r)
    (hC : ∀ r, a ≤ r → C ≤ f' r) (ht : a ≤ t) :
    f a + C * (t - a) ≤ f t :=
  add_mul_le_of_hasDerivAt hf hC ht

example {R P E : ℝ → ℝ} {ℰ m α t₀ : ℝ} (hα : α < 0) (hR : ∀ t, 0 < R t) (hE : ∀ t, 0 < E t)
    (hRE : ∀ t, R t * E t = ℰ * R t - α) (hR' : ∀ t, HasDerivAt R (P t / (R t * E t)) t)
    (hP' : ∀ t, HasDerivAt P (ℰ - m ^ 2 / E t) t) (hneg : ∀ t, t₀ ≤ t → P t < 0) :
    False :=
  not_forall_neg_of_radial hα hR hE hRE hR' hP' hneg

example {R P E : ℝ → ℝ} {ℰ m α t₀ : ℝ} (hα : α < 0) (hR : ∀ t, 0 < R t) (hE : ∀ t, 0 < E t)
    (hRE : ∀ t, R t * E t = ℰ * R t - α) (hR' : ∀ t, HasDerivAt R (P t / (R t * E t)) t)
    (hP' : ∀ t, HasDerivAt P (ℰ - m ^ 2 / E t) t) (hpos : ∀ t, t ≤ t₀ → 0 < P t) :
    False :=
  not_forall_pos_of_radial hα hR hE hRE hR' hP' hpos

example (hm : 0 < m) (hα : α < 0) {y : ℝ → PolarPoint}
    (hy : ∀ t, HasDerivAt y (hamiltonianField (coulombHamiltonian m α) (y t)) t)
    (hℓ : pφ.val (y 0) ^ 2 ≤ α ^ 2) :
    False :=
  not_forall_hasDerivAt hm hα hy hℓ

example (hm : 0 < m) (hα : α < 0) (z : PolarPoint) (hℓ : pφ.val z ^ 2 ≤ α ^ 2) :
    ∃ t, (t, z) ∉ flowDomain (hamiltonianField (coulombHamiltonian m α)) :=
  fall_to_centre hm hα z hℓ

example (hm : 0 < m) (hα : α < 0) {c : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}
    (hℓ : pφ.val (realCurve c 0) ^ 2 ≤ α ^ 2) :
    ¬ IsTrajectory (𝒫) (coulombHamiltonian m α) c :=
  not_isTrajectory_of_sq_le hm hα hℓ

example (hm : m ≠ 0) (z : PolarPoint) :
    |FreeSmoothRing.lift z (kineticEnergyInv m) * FreeSmoothRing.lift z (rInv * pS)| < 1 ∧
      |FreeSmoothRing.lift z (kineticEnergyInv m) * FreeSmoothRing.lift z (rInv * pφ)| < 1 :=
  abs_kineticEnergyInv_mul_lt_one hm z

example {H G : Polar} {y : ℝ → PolarPoint} {t C : ℝ}
    (hy : ∀ τ ∈ uIcc 0 t, HasDerivAt y (hamiltonianField H (y τ)) τ)
    (hC : ∀ τ ∈ uIcc 0 t, |FreeSmoothRing.lift (y τ) ((𝒫).bracket G H)| ≤ C) :
    |FreeSmoothRing.lift (y t) G - FreeSmoothRing.lift (y 0) G| ≤ C * |t| :=
  abs_lift_sub_le hy hC

example (hm : 0 < m) {z : PolarPoint} {T : ℝ}
    (hT : (T, z) ∉ flowDomain (hamiltonianField (coulombHamiltonian m α))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ uIcc 0 T, (t, z) ∈ flowDomain (hamiltonianField (coulombHamiltonian m α)) ∧
      r.val (flow (hamiltonianField (coulombHamiltonian m α)) (t, z)) < ε :=
  exists_r_lt_of_not_mem_flowDomain hm hT hε

example (hm : 0 < m) (hα : α < 0) (z : PolarPoint) (hℓ : pφ.val z ^ 2 ≤ α ^ 2) :
    ∃ T, (T, z) ∉ flowDomain (hamiltonianField (coulombHamiltonian m α)) ∧
      ∀ ε, 0 < ε → ∃ t ∈ uIcc 0 T,
        (t, z) ∈ flowDomain (hamiltonianField (coulombHamiltonian m α)) ∧
          r.val (flow (hamiltonianField (coulombHamiltonian m α)) (t, z)) < ε :=
  fall_to_centre_collision hm hα z hℓ

end ProjectAinos.Electrodynamics.CoulombMotion

end CoulombMotion

section Larmor

namespace ProjectAinos.Electrodynamics.Larmor

open Set

open scoped NNReal Interval

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix Mechanics

example (B : Fin 3 → ℝ) :
    Fin 3 → FreeSmoothRing (Fin 3) :=
  symmetricGauge B

example (B : Fin 3 → ℝ) (i j : Fin 3) :
    ChargedParticle.magneticTensor (symmetricGauge B) i j =
      epsilon (fun k => algebraMap ℝ (FreeSmoothRing (Fin 3)) (B k)) i j :=
  magneticTensor_symmetricGauge B i j

example (B : Fin 3 → ℝ) (i : Fin 3) :
    PhaseSpace.ofPosition (Fin 3) (symmetricGauge B i) =
      algebraMap ℝ AngularMomentum.Space (1 / 2) *
        (RotatingFrame.angularVelocity B ⨯₃ AngularMomentum.q) i :=
  ofPosition_symmetricGauge B i

example (e m : ℝ) (B : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  larmorFrequency e m B

example (m e : ℝ) (U : AngularMomentum.Space) (B : Fin 3 → ℝ) :
    AngularMomentum.Space :=
  hamiltonian m e U B

example (m e : ℝ) (U : AngularMomentum.Space) (B : Fin 3 → ℝ) :
    hamiltonian m e U B = RotatingFrame.hamiltonian m U (larmorFrequency e m B) +
      algebraMap ℝ AngularMomentum.Space (e ^ 2 / (8 * m)) *
        ∑ i, (RotatingFrame.angularVelocity B ⨯₃ AngularMomentum.q) i ^ 2 :=
  hamiltonian_eq_rotating m e U B

example (m e : ℝ) (B : Fin 3 → ℝ) (y : Fin 3 ⊕ Fin 3 → ℝ) (j : Fin 3) :
    hamiltonianField (hamiltonian m e 0 B) y (Sum.inl j) =
      m⁻¹ * (y (Sum.inr j) - e / 2 * (B ⨯₃ fun i => y (Sum.inl i)) j) :=
  hamiltonianField_hamiltonian_inl m e B y j

example (m e : ℝ) (B : Fin 3 → ℝ) (y : Fin 3 ⊕ Fin 3 → ℝ) (j : Fin 3) :
    hamiltonianField (hamiltonian m e 0 B) y (Sum.inr j) =
      e / (2 * m) *
        ((fun i => y (Sum.inr i) - e / 2 * (B ⨯₃ fun i => y (Sum.inl i)) i) ⨯₃ B) j :=
  hamiltonianField_hamiltonian_inr m e B y j

example (m : ℝ) (Ω : Fin 3 → ℝ) (y : Fin 3 ⊕ Fin 3 → ℝ) (j : Fin 3) :
    hamiltonianField (RotatingFrame.hamiltonian m 0 Ω) y (Sum.inl j) =
      m⁻¹ * y (Sum.inr j) - (Ω ⨯₃ fun i => y (Sum.inl i)) j :=
  hamiltonianField_rotatingFrame_inl m Ω y j

example (m : ℝ) (Ω : Fin 3 → ℝ) (y : Fin 3 ⊕ Fin 3 → ℝ) (j : Fin 3) :
    hamiltonianField (RotatingFrame.hamiltonian m 0 Ω) y (Sum.inr j) =
      -(Ω ⨯₃ fun i => y (Sum.inr i)) j :=
  hamiltonianField_rotatingFrame_inr m Ω y j

example (γ : ℝ) (B : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  ratioLarmorFrequency γ B

example (e m : ℝ) (B : Fin 3 → ℝ) :
    larmorFrequency e m B = ratioLarmorFrequency (e / m) B :=
  larmorFrequency_eq_ratio e m B

section System

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

example (a : ι) :
    Fin 3 → PhaseSpace (ι × Fin 3) :=
  particleQ a

example (a : ι) :
    Fin 3 → PhaseSpace (ι × Fin 3) :=
  particleP a

example (Ω : Fin 3 → ℝ) :
    Fin 3 → PhaseSpace (ι × Fin 3) :=
  constVector ι Ω

example :
    Fin 3 → PhaseSpace (ι × Fin 3) :=
  totalAngularMomentum ι

example (m : ι → ℝ) (U : PhaseSpace (ι × Fin 3)) (Ω : Fin 3 → ℝ) :
    PhaseSpace (ι × Fin 3) :=
  rotatingHamiltonian m U Ω

example (B : Fin 3 → ℝ) (a : ι) :
    Fin 3 → PhaseSpace (ι × Fin 3) :=
  particleGauge B a

example (B : Fin 3 → ℝ) (a : ι) (i : Fin 3) :
    particleGauge B a i =
      algebraMap ℝ (PhaseSpace (ι × Fin 3)) (1 / 2) * (constVector ι B ⨯₃ particleQ a) i :=
  particleGauge_eq B a i

example (e : ℝ) (B : Fin 3 → ℝ) (a : ι) :
    Fin 3 → PhaseSpace (ι × Fin 3) :=
  particleKineticMomentum e B a

example (m e : ι → ℝ) (U : PhaseSpace (ι × Fin 3)) (B : Fin 3 → ℝ) :
    PhaseSpace (ι × Fin 3) :=
  systemHamiltonian m e U B

example {m e : ι → ℝ} {γ : ℝ} (he : ∀ a, e a / m a = γ) (U : PhaseSpace (ι × Fin 3))
    (B : Fin 3 → ℝ) :
    systemHamiltonian m e U B = rotatingHamiltonian m U (ratioLarmorFrequency γ B) +
      ∑ a, algebraMap ℝ (PhaseSpace (ι × Fin 3)) (e a ^ 2 / (8 * m a)) *
        ∑ i, (constVector ι B ⨯₃ particleQ a) i ^ 2 :=
  systemHamiltonian_eq_rotating he U B

example (m e : ℝ) (U : PhaseSpace (ι × Fin 3)) (B : Fin 3 → ℝ) :
    systemHamiltonian (fun _ => m) (fun _ => e) U B =
      rotatingHamiltonian (fun _ => m) U (larmorFrequency e m B) +
        ∑ a, algebraMap ℝ (PhaseSpace (ι × Fin 3)) (e ^ 2 / (8 * m)) *
          ∑ i, (constVector ι B ⨯₃ particleQ a) i ^ 2 :=
  systemHamiltonian_eq_rotating_const m e U B

example (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (a : ι) :
    Fin 3 → ℝ :=
  realQ z a

example (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (a : ι) :
    Fin 3 → ℝ :=
  realP z a

example (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    ι × Fin 3 → ℝ :=
  realPositions z

example (m : ι → ℝ) (Ω : Fin 3 → ℝ) (f : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ)
    (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    ι × Fin 3 ⊕ ι × Fin 3 → ℝ :=
  rotatingField m Ω f z

example (e : ℝ) (B : Fin 3 → ℝ) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (a : ι) :
    Fin 3 → ℝ :=
  realKineticMomentum e B z a

example (m e : ι → ℝ) (B : Fin 3 → ℝ) (f : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ)
    (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    ι × Fin 3 ⊕ ι × Fin 3 → ℝ :=
  larmorField m e B f z

example (m e : ι → ℝ) (B : Fin 3 → ℝ) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    ι × Fin 3 ⊕ ι × Fin 3 → ℝ :=
  diamagneticField m e B z

example {m e : ι → ℝ} {γ : ℝ} (he : ∀ a, e a / m a = γ) (B : Fin 3 → ℝ)
    (f : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    larmorField m e B f z =
      rotatingField m (ratioLarmorFrequency γ B) f z + diamagneticField m e B z :=
  larmorField_eq he B f z

example {B q : Fin 3 → ℝ} {R : ℝ} (hR0 : 0 ≤ R) (hq : ∑ j, q j ^ 2 ≤ R ^ 2) (i : Fin 3) :
    |(∑ j, B j ^ 2) * q i - (B ⬝ᵥ q) * B i| ≤ (∑ j, B j ^ 2) * R :=
  abs_diamagnetic_le hR0 hq i

example {m e : ι → ℝ} (B : Fin 3 → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ a, |e a ^ 2 / (4 * m a)| ≤ c)
    {R : ℝ} (hR0 : 0 ≤ R) {z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ}
    (hz : ∀ a, ∑ i, z (Sum.inl (a, i)) ^ 2 ≤ R ^ 2) :
    ‖diamagneticField m e B z‖ ≤ c * (∑ i, B i ^ 2) * R :=
  norm_diamagneticField_le B hc0 hc hR0 hz

example (m e : ι → ℝ) (B : Fin 3 → ℝ) :
    Continuous (diamagneticField m e B) :=
  continuous_diamagneticField m e B

example {m e : ι → ℝ} {γ : ℝ} (he : ∀ a, e a / m a = γ) (B : Fin 3 → ℝ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ a, |e a ^ 2 / (4 * m a)| ≤ c) {f : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ} {K : ℝ≥0}
    {s : Set (ι × Fin 3 ⊕ ι × Fin 3 → ℝ)}
    (hF : LipschitzOnWith K (rotatingField m (ratioLarmorFrequency γ B) f) s) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ x ∈ s, ∀ a, ∑ i, x (Sum.inl (a, i)) ^ 2 ≤ R ^ 2)
    {z Z : ℝ → ι × Fin 3 ⊕ ι × Fin 3 → ℝ} {L : ℝ}
    (hz : ∀ t ∈ Icc 0 L, HasDerivAt z (larmorField m e B f (z t)) t)
    (hZ : ∀ t ∈ Icc 0 L, HasDerivAt Z (rotatingField m (ratioLarmorFrequency γ B) f (Z t)) t)
    (hzs : ∀ t ∈ Icc 0 L, z t ∈ s) (hZs : ∀ t ∈ Icc 0 L, Z t ∈ s) (h0 : z 0 = Z 0) :
    ∀ t ∈ Icc 0 L, ‖z t - Z t‖ ≤ c * (∑ i, B i ^ 2) * R * t * Real.exp (K * t) :=
  norm_sub_le_larmor he B hc0 hc hF hR0 hR hz hZ hzs hZs h0

example {m : ℝ} (hm : 0 < m) (e : ℝ) (B : Fin 3 → ℝ) {f : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ}
    {K : ℝ≥0} {s : Set (ι × Fin 3 ⊕ ι × Fin 3 → ℝ)}
    (hF : LipschitzOnWith K (rotatingField (fun _ => m) (larmorFrequency e m B) f) s) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ x ∈ s, ∀ a, ∑ i, x (Sum.inl (a, i)) ^ 2 ≤ R ^ 2)
    {z Z : ℝ → ι × Fin 3 ⊕ ι × Fin 3 → ℝ} {L : ℝ}
    (hz : ∀ t ∈ Icc 0 L, HasDerivAt z (larmorField (fun _ => m) (fun _ => e) B f (z t)) t)
    (hZ : ∀ t ∈ Icc 0 L,
      HasDerivAt Z (rotatingField (fun _ => m) (larmorFrequency e m B) f (Z t)) t)
    (hzs : ∀ t ∈ Icc 0 L, z t ∈ s) (hZs : ∀ t ∈ Icc 0 L, Z t ∈ s) (h0 : z 0 = Z 0) :
    ∀ t ∈ Icc 0 L,
      ‖z t - Z t‖ ≤ e ^ 2 * (∑ i, B i ^ 2) * R / (4 * m) * t * Real.exp (K * t) :=
  norm_sub_le_larmor_const hm e B hF hR0 hR hz hZ hzs hZs h0

example (a : ι) :
    Fin 3 ⊕ Fin 3 → PhaseSpace (ι × Fin 3) :=
  particleGenerator a

example (a : ι) :
    SmoothRingHom AngularMomentum.Space (PhaseSpace (ι × Fin 3)) :=
  particleMap a

example (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (a : ι) :
    Fin 3 ⊕ Fin 3 → ℝ :=
  particlePoint z a

example (a : ι) (s : AngularMomentum.Space) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    (particleMap a s).val z = s.val (particlePoint z a) :=
  val_particleMap a s z

example (a b : ι) (j : Fin 3) (s : AngularMomentum.Space) :
    partialDerivation (Sum.inr (b, j)) (particleMap a s) =
      if a = b then particleMap a (partialDerivation (Sum.inr j) s) else 0 :=
  partialDerivation_inr_particleMap a b j s

example (a b : ι) (j : Fin 3) (s : AngularMomentum.Space) :
    partialDerivation (Sum.inl (b, j)) (particleMap a s) =
      if a = b then particleMap a (partialDerivation (Sum.inl j) s) else 0 :=
  partialDerivation_inl_particleMap a b j s

example (m : ι → ℝ) (U : PhaseSpace (ι × Fin 3)) (Ω : Fin 3 → ℝ) :
    rotatingHamiltonian m U Ω =
      ∑ a, particleMap a (RotatingFrame.hamiltonian (m a) 0 Ω) + U :=
  rotatingHamiltonian_eq_sum m U Ω

example (m e : ι → ℝ) (U : PhaseSpace (ι × Fin 3)) (B : Fin 3 → ℝ) :
    systemHamiltonian m e U B = ∑ a, particleMap a (hamiltonian (m a) (e a) 0 B) + U :=
  systemHamiltonian_eq_sum m e U B

example (V : FreeSmoothRing (ι × Fin 3)) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    (PhaseSpace.ofPosition (ι × Fin 3) V).val z = V.val (realPositions z) :=
  val_ofPosition V z

example (h : ι → AngularMomentum.Space) (V : FreeSmoothRing (ι × Fin 3))
    (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (b : ι) (j : Fin 3) :
    hamiltonianField (∑ a, particleMap a (h a) + PhaseSpace.ofPosition (ι × Fin 3) V) z
        (Sum.inl (b, j)) =
      hamiltonianField (h b) (particlePoint z b) (Sum.inl j) :=
  hamiltonianField_sum_particleMap_inl h V z b j

example (h : ι → AngularMomentum.Space) (V : FreeSmoothRing (ι × Fin 3))
    (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (b : ι) (j : Fin 3) :
    hamiltonianField (∑ a, particleMap a (h a) + PhaseSpace.ofPosition (ι × Fin 3) V) z
        (Sum.inr (b, j)) =
      hamiltonianField (h b) (particlePoint z b) (Sum.inr j) -
        (partialDerivation (b, j) V).val (realPositions z) :=
  hamiltonianField_sum_particleMap_inr h V z b j

example (m : ι → ℝ) (V : FreeSmoothRing (ι × Fin 3)) (Ω : Fin 3 → ℝ) :
    hamiltonianField (rotatingHamiltonian m (PhaseSpace.ofPosition (ι × Fin 3) V) Ω) =
      rotatingField m Ω (fun x k => -(partialDerivation k V).val x) :=
  hamiltonianField_rotatingHamiltonian m V Ω

example (m e : ι → ℝ) (V : FreeSmoothRing (ι × Fin 3)) (B : Fin 3 → ℝ) :
    hamiltonianField (systemHamiltonian m e (PhaseSpace.ofPosition (ι × Fin 3) V) B) =
      larmorField m e B (fun x k => -(partialDerivation k V).val x) :=
  hamiltonianField_systemHamiltonian m e V B

example {m e : ι → ℝ} {γ : ℝ} (he : ∀ a, e a / m a = γ) (B : Fin 3 → ℝ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ a, |e a ^ 2 / (4 * m a)| ≤ c) (V : FreeSmoothRing (ι × Fin 3)) {K : ℝ≥0}
    {s : Set (ι × Fin 3 ⊕ ι × Fin 3 → ℝ)}
    (hF : LipschitzOnWith K (hamiltonianField (rotatingHamiltonian m
      (PhaseSpace.ofPosition (ι × Fin 3) V) (ratioLarmorFrequency γ B))) s)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ s, ∀ a, ∑ i, x (Sum.inl (a, i)) ^ 2 ≤ R ^ 2)
    {z Z : ℝ → ι × Fin 3 ⊕ ι × Fin 3 → ℝ} {L : ℝ}
    (hz : ∀ t ∈ Icc 0 L, HasDerivAt z (hamiltonianField
      (systemHamiltonian m e (PhaseSpace.ofPosition (ι × Fin 3) V) B) (z t)) t)
    (hZ : ∀ t ∈ Icc 0 L, HasDerivAt Z (hamiltonianField (rotatingHamiltonian m
      (PhaseSpace.ofPosition (ι × Fin 3) V) (ratioLarmorFrequency γ B)) (Z t)) t)
    (hzs : ∀ t ∈ Icc 0 L, z t ∈ s) (hZs : ∀ t ∈ Icc 0 L, Z t ∈ s) (h0 : z 0 = Z 0) :
    ∀ t ∈ Icc 0 L, ‖z t - Z t‖ ≤ c * (∑ i, B i ^ 2) * R * t * Real.exp (K * t) :=
  norm_sub_le_larmor_of_hamiltonianField he B hc0 hc V hF hR0 hR hz hZ hzs hZs h0

end System

example (ι : Type*) (k : ℝ) :
    (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ :=
  oscillatorForce ι k

example (w t : ℝ) :
    Unit × Fin 3 ⊕ Unit × Fin 3 → ℝ :=
  exampleOrbit w t

example (w t : ℝ) :
    Unit × Fin 3 ⊕ Unit × Fin 3 → ℝ :=
  exampleVelocity w t

example (w t : ℝ) :
    HasDerivAt (exampleOrbit w) (exampleVelocity w t) t :=
  hasDerivAt_exampleOrbit w t

example (t : ℝ) :
    HasDerivAt (exampleOrbit 3)
      (rotatingField (fun _ => 1) (ratioLarmorFrequency 2 ![0, 0, 4]) (oscillatorForce Unit 9)
        (exampleOrbit 3 t)) t :=
  hasDerivAt_exampleOrbit_rotating t

example (t : ℝ) :
    HasDerivAt (exampleOrbit 5)
      (larmorField (fun _ => 1) (fun _ => 2) ![0, 0, 4] (oscillatorForce Unit 9)
        (exampleOrbit 5 t)) t :=
  hasDerivAt_exampleOrbit_larmor t

example :
    LipschitzWith 13
      (rotatingField (fun _ => 1) (ratioLarmorFrequency 2 ![0, 0, 4])
        (oscillatorForce Unit 9)) :=
  lipschitzWith_rotatingField_example

example {t : ℝ} (ht : 0 ≤ t) :
    ‖exampleOrbit 5 t - exampleOrbit 3 t‖ ≤ 16 * t * Real.exp (13 * t) :=
  norm_exampleOrbit_sub_le ht

end ProjectAinos.Electrodynamics.Larmor

end Larmor
