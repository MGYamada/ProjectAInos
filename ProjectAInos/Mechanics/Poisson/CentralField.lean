/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Elementary
public import ProjectAInos.Mechanics.Poisson.CyclicReduction
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Motion in a central field: polar co-ordinates and the radial Hamiltonian

Landau–Lifshitz §14 for a particle in the plane. The polar co-ordinates are
taken with the logarithm `s` of the radius, `r = exp s`, so that every
function is defined on a free C-infinity ring: `x = r cos φ`, `y = r sin φ`,
with the momenta `p_s = r p_r` and `p_φ`. The morphism `polarCoordinates`
writes a function of `(x, y, p_x, p_y)` in these co-ordinates.

* `isPoissonHom_polarCoordinates`: the polar co-ordinates are canonical.
* `polarCoordinates_angularMomentum`: the angular momentum is `p_φ`.
* `polarCoordinates_hamiltonian`: `|p|²/2m + U(|q|²)` becomes
  `(p_s² + p_φ²)/2mr² + U(r²)`, and `φ` is a cyclic co-ordinate.
* `reductionHom_radialHamiltonian`: in the reduced ring at `p_φ = ℓ` the
  Hamiltonian is `p_r²/2m + ℓ²/2mr² + V`. The reduction produces the
  centrifugal term.

In polar co-ordinates the potential energy `V` is a smooth function of `s`,
that is, an arbitrary smooth function of the radius `r > 0`; Coulomb's
potential is included. The comparison with the plane is for a potential energy
that is a smooth function of `|q|²`.
* `isTrajectory_plane`, `isTrajectory_radial`, `timeDerivative_angle`: a
  trajectory in polar co-ordinates gives a trajectory in the plane; its radial
  part is a trajectory of the radial Hamiltonian, and `φ̇ = ℓ/mr²`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.CentralField

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix CyclicReduction

/-- The phase space of a particle in the plane. -/
abbrev Plane := SmoothAlgebra.PhaseSpace (Fin 2)

/-- The phase space of the polar co-ordinates `(s, φ)` with `r = exp s`. The
radial co-ordinate has the index `Sum.inl 0`, the angle `Sum.inr 0`. -/
abbrev Polar := SmoothAlgebra.PhaseSpace (Fin 1 ⊕ Fin 1)

/-- The phase space of the radial motion, with the co-ordinate `s = log r`. -/
abbrev Radial := SmoothAlgebra.PhaseSpace (Fin 1)

/-- The logarithm `s` of the radius. -/
def s : Polar := PhaseSpace.q (Sum.inl 0)

/-- The angle `φ`. -/
def φ : Polar := PhaseSpace.q (Sum.inr 0)

/-- The momentum `p_s = r p_r` of the logarithm of the radius. -/
def pS : Polar := PhaseSpace.p (Sum.inl 0)

/-- The momentum `p_φ` of the angle. -/
def pφ : Polar := PhaseSpace.p (Sum.inr 0)

/-- The radius `r = exp s`. -/
def r : Polar := exp s

/-- The inverse radius `1/r = exp (−s)`. -/
def rInv : Polar := exp (-s)

/-- `cos φ`. -/
def cosφ : Polar := ringCos φ

/-- `sin φ`. -/
def sinφ : Polar := ringSin φ

theorem r_mul_rInv : r * rInv = 1 := exp_mul_exp_neg s

theorem cosφ_mul_cosφ_add_sinφ_mul_sinφ : cosφ * cosφ + sinφ * sinφ = 1 :=
  ringCos_mul_ringCos_add_ringSin_mul_ringSin φ

/-! ### The co-ordinate vector fields -/

/-- `∂/∂s`. -/
def dS : SmoothDerivation Polar Polar := partialDerivation (Sum.inl (Sum.inl 0))

/-- `∂/∂φ`. -/
def dφ : SmoothDerivation Polar Polar := partialDerivation (Sum.inl (Sum.inr 0))

/-- `∂/∂p_s`. -/
def dPS : SmoothDerivation Polar Polar := partialDerivation (Sum.inr (Sum.inl 0))

/-- `∂/∂p_φ`. -/
def dPφ : SmoothDerivation Polar Polar := partialDerivation (Sum.inr (Sum.inr 0))

theorem dS_s : dS s = 1 := partialDerivation_generator_self _
theorem dS_φ : dS φ = 0 := partialDerivation_generator_of_ne (by simp)
theorem dS_pS : dS pS = 0 := partialDerivation_generator_of_ne (by simp)
theorem dS_pφ : dS pφ = 0 := partialDerivation_generator_of_ne (by simp)
theorem dφ_s : dφ s = 0 := partialDerivation_generator_of_ne (by simp)
theorem dφ_φ : dφ φ = 1 := partialDerivation_generator_self _
theorem dφ_pS : dφ pS = 0 := partialDerivation_generator_of_ne (by simp)
theorem dφ_pφ : dφ pφ = 0 := partialDerivation_generator_of_ne (by simp)
theorem dPS_s : dPS s = 0 := partialDerivation_generator_of_ne (by simp)
theorem dPS_φ : dPS φ = 0 := partialDerivation_generator_of_ne (by simp)
theorem dPS_pS : dPS pS = 1 := partialDerivation_generator_self _
theorem dPS_pφ : dPS pφ = 0 := partialDerivation_generator_of_ne (by simp)
theorem dPφ_s : dPφ s = 0 := partialDerivation_generator_of_ne (by simp)
theorem dPφ_φ : dPφ φ = 0 := partialDerivation_generator_of_ne (by simp)
theorem dPφ_pS : dPφ pS = 0 := partialDerivation_generator_of_ne (by simp)
theorem dPφ_pφ : dPφ pφ = 1 := partialDerivation_generator_self _

theorem dS_r : dS r = r := by rw [r, apply_exp, dS_s, mul_one]
theorem dS_rInv : dS rInv = -rInv := by
  rw [rInv, apply_exp, map_neg, dS_s]
  ring
theorem dS_cosφ : dS cosφ = 0 := by rw [cosφ, apply_ringCos, dS_φ, mul_zero, neg_zero]
theorem dS_sinφ : dS sinφ = 0 := by rw [sinφ, apply_ringSin, dS_φ, mul_zero]
theorem dφ_r : dφ r = 0 := by rw [r, apply_exp, dφ_s, mul_zero]
theorem dφ_rInv : dφ rInv = 0 := by rw [rInv, apply_exp, map_neg, dφ_s, neg_zero, mul_zero]
theorem dφ_cosφ : dφ cosφ = -sinφ := by rw [cosφ, apply_ringCos, dφ_φ, mul_one, sinφ]
theorem dφ_sinφ : dφ sinφ = cosφ := by rw [sinφ, apply_ringSin, dφ_φ, mul_one, cosφ]
theorem dPS_r : dPS r = 0 := by rw [r, apply_exp, dPS_s, mul_zero]
theorem dPS_rInv : dPS rInv = 0 := by rw [rInv, apply_exp, map_neg, dPS_s, neg_zero, mul_zero]
theorem dPS_cosφ : dPS cosφ = 0 := by rw [cosφ, apply_ringCos, dPS_φ, mul_zero, neg_zero]
theorem dPS_sinφ : dPS sinφ = 0 := by rw [sinφ, apply_ringSin, dPS_φ, mul_zero]
theorem dPφ_r : dPφ r = 0 := by rw [r, apply_exp, dPφ_s, mul_zero]
theorem dPφ_rInv : dPφ rInv = 0 := by rw [rInv, apply_exp, map_neg, dPφ_s, neg_zero, mul_zero]
theorem dPφ_cosφ : dPφ cosφ = 0 := by rw [cosφ, apply_ringCos, dPφ_φ, mul_zero, neg_zero]
theorem dPφ_sinφ : dPφ sinφ = 0 := by rw [sinφ, apply_ringSin, dPφ_φ, mul_zero]

/-- The canonical bracket in the polar co-ordinates. -/
theorem bracket_eq (f g : Polar) :
    (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).bracket f g =
      dS f * dPS g - dPS f * dS g + (dφ f * dPφ g - dPφ f * dφ g) := by
  rw [PhaseSpace.canonical_bracket, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_one]
  rfl

/-- Evaluate the co-ordinate vector fields on polynomials in the co-ordinates,
`r`, `1/r`, `cos φ` and `sin φ`. -/
local macro "polar_derivatives" : tactic =>
  `(tactic| simp only [SmoothDerivation.map_mul, map_add, map_sub, smul_eq_mul,
    dS_s, dS_φ, dS_pS, dS_pφ, dφ_s, dφ_φ, dφ_pS, dφ_pφ, dPS_s, dPS_φ, dPS_pS, dPS_pφ,
    dPφ_s, dPφ_φ, dPφ_pS, dPφ_pφ, dS_r, dS_rInv, dS_cosφ, dS_sinφ, dφ_r, dφ_rInv, dφ_cosφ,
    dφ_sinφ, dPS_r, dPS_rInv, dPS_cosφ, dPS_sinφ, dPφ_r, dPφ_rInv, dPφ_cosφ, dPφ_sinφ])

/-! ### Polar co-ordinates -/

/-- The polar co-ordinates: `x = r cos φ`, `y = r sin φ`,
`p_x = (p_s cos φ − p_φ sin φ)/r`, `p_y = (p_s sin φ + p_φ cos φ)/r`. -/
def polarCoordinates : SmoothRingHom Plane Polar :=
  FreeSmoothRing.lift (Sum.elim ![r * cosφ, r * sinφ]
    ![rInv * (pS * cosφ - pφ * sinφ), rInv * (pS * sinφ + pφ * cosφ)])

theorem polarCoordinates_q_zero : polarCoordinates (PhaseSpace.q 0) = r * cosφ :=
  lift_generator _ _

theorem polarCoordinates_q_one : polarCoordinates (PhaseSpace.q 1) = r * sinφ :=
  lift_generator _ _

theorem polarCoordinates_p_zero :
    polarCoordinates (PhaseSpace.p 0) = rInv * (pS * cosφ - pφ * sinφ) :=
  lift_generator _ _

theorem polarCoordinates_p_one :
    polarCoordinates (PhaseSpace.p 1) = rInv * (pS * sinφ + pφ * cosφ) :=
  lift_generator _ _

/-- The polar co-ordinates are canonical (Landau–Lifshitz §14). -/
theorem isPoissonHom_polarCoordinates :
    IsPoissonHom (PhaseSpace.canonical (Fin 2)).toAlmostPoissonStructure
      (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).toAlmostPoissonStructure polarCoordinates := by
  have hr := r_mul_rInv
  have hc := cosφ_mul_cosφ_add_sinφ_mul_sinφ
  refine PhaseSpace.isPoissonHom_of_canonical
    (Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩)
    (Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩)
    (Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩)
  · rw [polarCoordinates_q_zero, bracket_eq]
    polar_derivatives
    ring
  · rw [polarCoordinates_q_zero, polarCoordinates_q_one, bracket_eq]
    polar_derivatives
    ring
  · rw [polarCoordinates_q_zero, polarCoordinates_q_one, bracket_eq]
    polar_derivatives
    ring
  · rw [polarCoordinates_q_one, bracket_eq]
    polar_derivatives
    ring
  · rw [polarCoordinates_p_zero, bracket_eq]
    polar_derivatives
    ring
  · rw [polarCoordinates_p_zero, polarCoordinates_p_one, bracket_eq]
    polar_derivatives
    ring
  · rw [polarCoordinates_p_zero, polarCoordinates_p_one, bracket_eq]
    polar_derivatives
    ring
  · rw [polarCoordinates_p_one, bracket_eq]
    polar_derivatives
    ring
  · change (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).bracket _ _ = (1 : Polar)
    rw [polarCoordinates_q_zero, polarCoordinates_p_zero, bracket_eq]
    polar_derivatives
    linear_combination (cosφ * cosφ + sinφ * sinφ) * hr + hc
  · change (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).bracket _ _ = (0 : Polar)
    rw [polarCoordinates_q_zero, polarCoordinates_p_one, bracket_eq]
    polar_derivatives
    ring
  · change (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).bracket _ _ = (0 : Polar)
    rw [polarCoordinates_q_one, polarCoordinates_p_zero, bracket_eq]
    polar_derivatives
    ring
  · change (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).bracket _ _ = (1 : Polar)
    rw [polarCoordinates_q_one, polarCoordinates_p_one, bracket_eq]
    polar_derivatives
    linear_combination (cosφ * cosφ + sinφ * sinφ) * hr + hc

/-- `x² + y² = r²`. -/
theorem polarCoordinates_q_sq :
    polarCoordinates (PhaseSpace.q ⬝ᵥ PhaseSpace.q) = r * r := by
  simp only [dotProduct, Fin.sum_univ_two, SmoothRingHom.map_add, SmoothRingHom.map_mul,
    polarCoordinates_q_zero, polarCoordinates_q_one]
  linear_combination (r * r) * cosφ_mul_cosφ_add_sinφ_mul_sinφ

/-- `p_x² + p_y² = (p_s² + p_φ²)/r²`, which is `p_r² + p_φ²/r²`. -/
theorem polarCoordinates_p_sq :
    polarCoordinates (PhaseSpace.p ⬝ᵥ PhaseSpace.p) = rInv * rInv * (pS * pS + pφ * pφ) := by
  simp only [dotProduct, Fin.sum_univ_two, SmoothRingHom.map_add, SmoothRingHom.map_mul,
    polarCoordinates_p_zero, polarCoordinates_p_one]
  linear_combination (rInv * rInv * (pS * pS + pφ * pφ)) * cosφ_mul_cosφ_add_sinφ_mul_sinφ

/-- The angular momentum `x p_y − y p_x` of a particle in the plane. -/
def angularMomentum : Plane :=
  PhaseSpace.q 0 * PhaseSpace.p 1 - PhaseSpace.q 1 * PhaseSpace.p 0

/-- In polar co-ordinates the angular momentum is the momentum `p_φ`. -/
theorem polarCoordinates_angularMomentum : polarCoordinates angularMomentum = pφ := by
  rw [angularMomentum, SmoothRingHom.map_sub, SmoothRingHom.map_mul, SmoothRingHom.map_mul,
    polarCoordinates_q_zero, polarCoordinates_q_one, polarCoordinates_p_zero,
    polarCoordinates_p_one]
  linear_combination (pφ * (cosφ * cosφ + sinφ * sinφ)) * r_mul_rInv +
    pφ * cosφ_mul_cosφ_add_sinφ_mul_sinφ

/-! ### The Hamiltonian -/

/-- The Hamiltonian `|p|²/2m + U(|q|²)` of a particle in a central field. The
potential energy is a smooth function of the square of the distance. -/
def hamiltonian (m : ℝ) (U : SmoothOperation 1) : Plane :=
  algebraMap ℝ Plane (m⁻¹ / 2) * (PhaseSpace.p ⬝ᵥ PhaseSpace.p) +
    op U fun _ => PhaseSpace.q ⬝ᵥ PhaseSpace.q

/-- The Hamiltonian in polar co-ordinates, `(p_s² + p_φ²)/2mr² + V(s)`. The
potential energy `V` is a smooth function of `s = log r`, that is, an
arbitrary smooth function of the radius `r > 0`. -/
def polarHamiltonian (m : ℝ) (V : SmoothOperation 1) : Polar :=
  algebraMap ℝ Polar (m⁻¹ / 2) * (rInv * rInv * (pS * pS + pφ * pφ)) + op V fun _ => s

/-- The potential energy `U(r²)` as a function of `s = log r`. -/
def logPotential (U : SmoothOperation 1) : SmoothOperation 1 :=
  SmoothOperation.comp U fun _ => SmoothOperation.exponential * SmoothOperation.exponential

theorem op_logPotential (U : SmoothOperation 1) : (op (logPotential U) fun _ => s) =
    op U fun _ => r * r := by
  rw [logPotential, op_comp]
  simp only [op_mul]
  rw [r, exp, Matrix.vec_single_eq_const]

theorem polarCoordinates_hamiltonian (m : ℝ) (U : SmoothOperation 1) :
    polarCoordinates (hamiltonian m U) = polarHamiltonian m (logPotential U) := by
  rw [hamiltonian, SmoothRingHom.map_add, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
    SmoothRingHom.map_op, polarCoordinates_p_sq, polarCoordinates_q_sq, polarHamiltonian,
    op_logPotential]

/-- The angle is a cyclic co-ordinate of the Hamiltonian. -/
theorem partialDerivation_polarHamiltonian (m : ℝ) (V : SmoothOperation 1) (k : Fin 1) :
    partialDerivation (Sum.inl (Sum.inr k)) (polarHamiltonian m V) = 0 := by
  rw [Subsingleton.elim k 0]
  change dφ (polarHamiltonian m V) = 0
  rw [polarHamiltonian, map_add, SmoothDerivation.map_algebraMap_mul, SmoothDerivation.chain,
    Fin.sum_univ_one]
  polar_derivatives
  simp only [mul_zero, add_zero]

/-- The Hamiltonian `p_r²/2m + ℓ²/2mr² + V` of the radial motion with the
angular momentum `ℓ`, in the co-ordinate `s = log r` and its momentum
`p_s = r p_r`: `(p_s² + ℓ²)/2mr² + V(s)`. -/
def radialHamiltonian (m : ℝ) (V : SmoothOperation 1) (ℓ : ℝ) : Radial :=
  algebraMap ℝ Radial (m⁻¹ / 2) * (exp (-PhaseSpace.q 0) * exp (-PhaseSpace.q 0) *
      (PhaseSpace.p 0 * PhaseSpace.p 0 + algebraMap ℝ Radial ℓ * algebraMap ℝ Radial ℓ)) +
    op V fun _ => PhaseSpace.q 0

/-- At `p_φ = ℓ` the Hamiltonian is the radial Hamiltonian. -/
theorem restriction_polarHamiltonian (m : ℝ) (V : SmoothOperation 1) (ℓ : ℝ) :
    restriction (Fin 1) (fun _ : Fin 1 => ℓ) (polarHamiltonian m V) =
      radialHamiltonian m V ℓ := by
  have hs : restriction (Fin 1) (fun _ : Fin 1 => ℓ) s = PhaseSpace.q 0 := by
    rw [s, PhaseSpace.q, restriction, lift_generator]
    rfl
  have hpS : restriction (Fin 1) (fun _ : Fin 1 => ℓ) pS = PhaseSpace.p 0 := by
    rw [pS, PhaseSpace.p, restriction, lift_generator]
    rfl
  have hpφ : restriction (Fin 1) (fun _ : Fin 1 => ℓ) pφ = algebraMap ℝ Radial ℓ := by
    rw [pφ, PhaseSpace.p, restriction, lift_generator]
    rfl
  simp only [polarHamiltonian, radialHamiltonian, rInv, SmoothRingHom.map_add,
    SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_op,
    SmoothRingHom.map_exp, SmoothRingHom.map_neg, hs, hpS, hpφ]

/-- The radius `r = exp s` on the radial phase space. -/
def radius : Radial := exp (PhaseSpace.q 0)

/-- The inverse radius on the radial phase space. -/
def radiusInv : Radial := exp (-PhaseSpace.q 0)

/-- The radial momentum `p_r = p_s / r`. -/
def radialMomentum : Radial := radiusInv * PhaseSpace.p 0

theorem radius_mul_radiusInv : radius * radiusInv = 1 := exp_mul_exp_neg _

/-- The radial Hamiltonian is `p_r²/2m + ℓ²/2mr² + V`: the reduction
produces the centrifugal energy. -/
theorem radialHamiltonian_eq (m : ℝ) (V : SmoothOperation 1) (ℓ : ℝ) :
    radialHamiltonian m V ℓ =
      algebraMap ℝ Radial (m⁻¹ / 2) * (radialMomentum * radialMomentum) +
        algebraMap ℝ Radial (ℓ * ℓ * (m⁻¹ / 2)) * (radiusInv * radiusInv) +
        op V fun _ => PhaseSpace.q 0 := by
  rw [radialHamiltonian, radialMomentum, radiusInv, map_mul, map_mul]
  ring

/-- The radius and the radial momentum are canonical: `{r, p_r} = 1`. -/
theorem canonical_radius_radialMomentum :
    (PhaseSpace.canonical (Fin 1)).bracket radius radialMomentum = 1 := by
  have h1 : partialDerivation (Sum.inl 0 : Fin 1 ⊕ Fin 1) radius = radius := by
    rw [radius, apply_exp, PhaseSpace.q, partialDerivation_generator_self, mul_one]
  have h2 : partialDerivation (Sum.inr 0 : Fin 1 ⊕ Fin 1) radius = 0 := by
    rw [radius, apply_exp, PhaseSpace.q, partialDerivation_generator_of_ne (by simp), mul_zero]
  have h3 : partialDerivation (Sum.inr 0 : Fin 1 ⊕ Fin 1) radialMomentum = radiusInv := by
    rw [radialMomentum, SmoothDerivation.map_mul, radiusInv, apply_exp, map_neg, PhaseSpace.q,
      PhaseSpace.p, partialDerivation_generator_self,
      partialDerivation_generator_of_ne (by simp), neg_zero, mul_zero, smul_zero, add_zero,
      smul_eq_mul, mul_one]
  rw [PhaseSpace.canonical_bracket, Fin.sum_univ_one, h1, h2, h3, zero_mul, sub_zero]
  exact radius_mul_radiusInv

/-! ### Reduction and trajectories -/

/-- The Hamiltonian in polar co-ordinates is in the normalizer of the ideal
`(p_φ − ℓ)`. -/
theorem polarHamiltonian_mem_normalizer (m : ℝ) (V : SmoothOperation 1) (ℓ : ℝ) :
    polarHamiltonian m V ∈ (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).normalizer
      (momentumIdeal (Fin 1) fun _ : Fin 1 => ℓ) :=
  mem_normalizer_of_cyclic (partialDerivation_polarHamiltonian m V) _

/-- The reduced Hamiltonian of a central field (Landau–Lifshitz §14): in the
reduced ring at the angular momentum `p_φ = ℓ`, the class of the Hamiltonian
is the radial Hamiltonian `p_r²/2m + ℓ²/2mr² + V`. -/
theorem reductionHom_radialHamiltonian (m : ℝ) (V : SmoothOperation 1) (ℓ : ℝ) :
    reductionHom (Fin 1) (fun _ : Fin 1 => ℓ) (radialHamiltonian m V ℓ) =
      (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).reductionMap
        (momentumIdeal (Fin 1) fun _ : Fin 1 => ℓ)
        ⟨polarHamiltonian m V, polarHamiltonian_mem_normalizer m V ℓ⟩ := by
  rw [← restriction_polarHamiltonian]
  exact reductionHom_restriction _

variable {m : ℝ} {U V : SmoothOperation 1}
  {x : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}

/-- A trajectory in polar co-ordinates gives a trajectory in the plane, for a
potential energy `U(|q|²)` that is smooth on the plane. -/
theorem isTrajectory_plane
    (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1))
      (polarHamiltonian m (logPotential U)) x) :
    IsTrajectory (PhaseSpace.canonical (Fin 2)) (hamiltonian m U)
      fun a => FreeSmoothRing.lift x (polarCoordinates (generator a)) :=
  IsTrajectory.of_isPoissonHom isPoissonHom_polarCoordinates
    (by rwa [polarCoordinates_hamiltonian])

/-- Along a trajectory in polar co-ordinates the angular momentum of the
motion in the plane is `p_φ`. -/
theorem lift_angularMomentum :
    FreeSmoothRing.lift (fun a => FreeSmoothRing.lift x (polarCoordinates (generator a)))
      angularMomentum = x (Sum.inr (Sum.inr 0)) := by
  have h : FreeSmoothRing.lift (fun a => polarCoordinates (generator a)) angularMomentum =
      polarCoordinates angularMomentum :=
    congrArg (fun χ : SmoothRingHom Plane Polar => χ angularMomentum)
      (FreeSmoothRing.hom_ext (f := FreeSmoothRing.lift fun a => polarCoordinates (generator a))
        (g := polarCoordinates) fun a => lift_generator _ _)
  rw [← map_lift, h, polarCoordinates_angularMomentum, pφ, PhaseSpace.p, lift_generator]

/-- The momentum `p_φ` is constant along a trajectory. -/
theorem pφ_eq_algebraMap
    (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)) (polarHamiltonian m V) x) :
    x (Sum.inr (Sum.inr 0)) =
      algebraMap ℝ TimeFunction (x (Sum.inr (Sum.inr 0)) fun _ => 0) :=
  p_eq_algebraMap_of_cyclic (partialDerivation_polarHamiltonian m V 0) hx

/-- The radial motion (Landau–Lifshitz §14): the radial part of a trajectory
with the angular momentum `ℓ` is a trajectory of the radial Hamiltonian. -/
theorem isTrajectory_radial
    (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)) (polarHamiltonian m V) x) {ℓ : ℝ}
    (hℓ : x (Sum.inr (Sum.inr 0)) = algebraMap ℝ TimeFunction ℓ) :
    IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ)
      fun a => x (Sum.map Sum.inl Sum.inl a) := by
  have h := isTrajectory_restriction (c := fun _ : Fin 1 => ℓ)
    (partialDerivation_polarHamiltonian m V) hx fun k => by
      rw [Subsingleton.elim k 0]
      exact hℓ
  rwa [restriction_polarHamiltonian] at h

/-- The angle along a trajectory: `φ̇ = p_φ / m r²` (Landau–Lifshitz (14.3)). -/
theorem timeDerivative_angle
    (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)) (polarHamiltonian m V) x) :
    timeDerivative (x (Sum.inl (Sum.inr 0))) =
      FreeSmoothRing.lift x (algebraMap ℝ Polar m⁻¹ * (rInv * rInv * pφ)) := by
  have h2 : algebraMap ℝ Polar m⁻¹ =
      algebraMap ℝ Polar (m⁻¹ / 2) + algebraMap ℝ Polar (m⁻¹ / 2) := by
    rw [← map_add]
    congr 1
    ring
  have hb : (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).bracket (generator (Sum.inl (Sum.inr 0)))
      (polarHamiltonian m V) = algebraMap ℝ Polar m⁻¹ * (rInv * rInv * pφ) := by
    change (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).bracket φ (polarHamiltonian m V) = _
    rw [bracket_eq, polarHamiltonian]
    simp only [map_add, SmoothDerivation.map_algebraMap_mul, SmoothDerivation.chain,
      Fin.sum_univ_one]
    polar_derivatives
    rw [h2]
    simp only [mul_zero, zero_mul, add_zero, sub_zero, mul_one, zero_add]
    ring
  rw [hx, hb]

/-! ### The plane of the motion -/

/-- The position is orthogonal to the angular momentum `M = q × p`. -/
theorem q_dotProduct_M : AngularMomentum.q ⬝ᵥ AngularMomentum.M = 0 :=
  dot_self_cross AngularMomentum.q AngularMomentum.p

/-- The momentum is orthogonal to the angular momentum. -/
theorem p_dotProduct_M : AngularMomentum.p ⬝ᵥ AngularMomentum.M = 0 :=
  dot_cross_self AngularMomentum.q AngularMomentum.p

/-- The orbit lies in a plane (Landau–Lifshitz §14): along a trajectory of a
central Hamiltonian in space, the position at every time is orthogonal to the
angular momentum at the time `0`. -/
theorem sum_q_mul_M_eq_zero (f : SmoothOperation 3) {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory AngularMomentum.canonical (op f AngularMomentum.scalars) c) (t : ℝ) :
    ∑ a, (c (Sum.inl a) fun _ => t) *
      (FreeSmoothRing.lift c (AngularMomentum.M a) fun _ => 0) = 0 := by
  have h0 : FreeSmoothRing.lift c (AngularMomentum.q ⬝ᵥ AngularMomentum.M) = 0 := by
    rw [q_dotProduct_M, SmoothRingHom.map_zero]
  have ht := congrArg (fun g : TimeFunction => g fun _ => t) h0
  simp only [dotProduct, SmoothRingHom.map_sum, SmoothRingHom.map_mul, AngularMomentum.q,
    PhaseSpace.q, lift_generator, SmoothOperation.sum_apply, TimeFunction.mul_apply] at ht
  have hz : (0 : TimeFunction) (fun _ => t) = 0 := rfl
  refine (Finset.sum_congr rfl fun a _ => ?_).trans (ht.trans hz)
  rw [AngularMomentum.lift_M_eq f h a (fun _ => 0) fun _ => t]

end ProjectAInos.Mechanics.CentralField
