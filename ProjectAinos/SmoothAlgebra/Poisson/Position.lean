/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.Poisson.Canonical
public import ProjectAinos.SmoothAlgebra.FreeChainRule
import Mathlib.Tactic.Ring

/-!
# Functions of the positions on a canonical phase space

A smooth function `f` of the positions is the element `ofPosition f` of the canonical phase
space: the substitution `xᵢ ↦ qᵢ`.

* `partialDerivation_inl_ofPosition`, `partialDerivation_inr_ofPosition`: its derivative in a
  position is the derivative of `f`, and its derivative in a momentum is zero.
* `canonical_ofPosition_bracket`: `{f, H} = Σᵢ ∂ᵢf ∂H/∂pᵢ`, and
  `canonical_p_ofPosition`: `{pᵢ, f} = −∂ᵢf`. Two functions of the positions commute.
* `momentumShift c χ` is the substitution `q ↦ q`, `pᵢ ↦ pᵢ + c ∂ᵢχ`. It is a Poisson
  automorphism (`isPoissonHom_momentumShift`, `momentumShift_neg_momentumShift`) and it fixes
  the functions of the positions.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SmoothAlgebra

open SmoothRing FreeSmoothRing

namespace PhaseSpace

variable {ι : Type*}

/-- A function of the positions as a function on the phase space. -/
def ofPosition : SmoothRingHom (FreeSmoothRing ι) (PhaseSpace ι) := lift q

@[simp] theorem ofPosition_generator (i : ι) : ofPosition (generator i) = q i :=
  lift_generator _ i

/-- The value at a point of the phase space is the value at its position. -/
theorem lift_ofPosition (z : ι ⊕ ι → ℝ) (f : FreeSmoothRing ι) :
    lift z (ofPosition f) = lift (fun i => z (Sum.inl i)) f := by
  rw [ofPosition, map_lift]
  simp only [q, lift_generator]

variable [Fintype ι] [DecidableEq ι]

/-- The derivative of a function of the positions in a position. -/
theorem partialDerivation_inl_ofPosition (i : ι) (f : FreeSmoothRing ι) :
    partialDerivation (Sum.inl i) (ofPosition f) = ofPosition (partialDerivation i f) := by
  rw [ofPosition, derivation_lift_mul, Finset.sum_eq_single i]
  · rw [q, partialDerivation_generator_self, mul_one]
  · intro j _ hj
    rw [q, partialDerivation_generator_of_ne (c := Sum.inl i) (i := Sum.inl j)
      (fun h => hj (Sum.inl.inj h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- A function of the positions does not depend on the momenta. -/
theorem partialDerivation_inr_ofPosition (i : ι) (f : FreeSmoothRing ι) :
    partialDerivation (Sum.inr i) (ofPosition f) = 0 := by
  rw [ofPosition, derivation_lift_mul]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [q, partialDerivation_generator_of_ne (c := Sum.inr i) (i := Sum.inl j) (by simp), mul_zero]

/-- `{f, H} = Σᵢ ∂ᵢf ∂H/∂pᵢ` for a function `f` of the positions. -/
theorem canonical_ofPosition_bracket (f : FreeSmoothRing ι) (H : PhaseSpace ι) :
    (canonical ι).bracket (ofPosition f) H =
      ∑ i, ofPosition (partialDerivation i f) * partialDerivation (Sum.inr i) H := by
  rw [canonical_bracket]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialDerivation_inl_ofPosition, partialDerivation_inr_ofPosition, zero_mul, sub_zero]

/-- `{pᵢ, f} = −∂ᵢf` for a function `f` of the positions. -/
theorem canonical_p_ofPosition (i : ι) (f : FreeSmoothRing ι) :
    (canonical ι).bracket (p i) (ofPosition f) = -ofPosition (partialDerivation i f) := by
  rw [canonical_p_bracket, partialDerivation_inl_ofPosition]

/-- `{f, pᵢ} = ∂ᵢf` for a function `f` of the positions. -/
theorem canonical_ofPosition_p (i : ι) (f : FreeSmoothRing ι) :
    (canonical ι).bracket (ofPosition f) (p i) = ofPosition (partialDerivation i f) := by
  rw [(canonical ι).antisymm, canonical_p_ofPosition, neg_neg]

/-- `{qᵢ, f} = 0` for a function `f` of the positions. -/
theorem canonical_q_ofPosition (i : ι) (f : FreeSmoothRing ι) :
    (canonical ι).bracket (q i) (ofPosition f) = 0 := by
  rw [canonical_q_bracket, partialDerivation_inr_ofPosition]

/-- Two functions of the positions commute. -/
theorem canonical_ofPosition_ofPosition (f g : FreeSmoothRing ι) :
    (canonical ι).bracket (ofPosition f) (ofPosition g) = 0 := by
  rw [canonical_ofPosition_bracket]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [partialDerivation_inr_ofPosition, mul_zero]

/-! ### The shift of the momenta by a gradient -/

/-- The substitution `q ↦ q`, `pᵢ ↦ pᵢ + c ∂ᵢχ` for a function `χ` of the positions. -/
def momentumShift (c : ℝ) (χ : FreeSmoothRing ι) : SmoothRingHom (PhaseSpace ι) (PhaseSpace ι) :=
  lift (Sum.elim q fun i => p i + algebraMap ℝ (PhaseSpace ι) c *
    ofPosition (partialDerivation i χ))

omit [Fintype ι] in
@[simp] theorem momentumShift_q (c : ℝ) (χ : FreeSmoothRing ι) (i : ι) :
    momentumShift c χ (q i) = q i :=
  lift_generator _ _

omit [Fintype ι] in
@[simp] theorem momentumShift_p (c : ℝ) (χ : FreeSmoothRing ι) (i : ι) :
    momentumShift c χ (p i) =
      p i + algebraMap ℝ (PhaseSpace ι) c * ofPosition (partialDerivation i χ) :=
  lift_generator _ _

omit [Fintype ι] in
/-- The shift of the momenta fixes the functions of the positions. -/
theorem momentumShift_ofPosition (c : ℝ) (χ f : FreeSmoothRing ι) :
    momentumShift c χ (ofPosition f) = ofPosition f := by
  rw [ofPosition, map_lift]
  simp only [momentumShift_q]

/-- The shift of the momenta by a gradient preserves the canonical bracket. -/
theorem isPoissonHom_momentumShift (c : ℝ) (χ : FreeSmoothRing ι) :
    IsPoissonHom (canonical ι).toAlmostPoissonStructure (canonical ι).toAlmostPoissonStructure
      (momentumShift c χ) := by
  refine isPoissonHom_of_canonical (fun i j => ?_) (fun i j => ?_) (fun i j => ?_)
  · rw [momentumShift_q, momentumShift_q, canonical_q_q]
  · rw [momentumShift_p, momentumShift_p]
    simp only [AlmostPoissonStructure.bracket_add_left, AlmostPoissonStructure.bracket_add_right,
      AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_mul_right,
      AlmostPoissonStructure.bracket_algebraMap_left,
      AlmostPoissonStructure.bracket_algebraMap_right, canonical_p_p, canonical_p_ofPosition,
      canonical_ofPosition_p, canonical_ofPosition_ofPosition, mul_zero, add_zero, zero_add]
    rw [partialDerivation_comm i j χ]
    ring
  · rw [momentumShift_q, momentumShift_p]
    simp only [AlmostPoissonStructure.bracket_add_right,
      AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_right,
      canonical_q_p, canonical_q_ofPosition, mul_zero, add_zero]

omit [Fintype ι] in
/-- The shift by `−c` is the inverse of the shift by `c`. -/
theorem momentumShift_neg_momentumShift (c : ℝ) (χ : FreeSmoothRing ι) (s : PhaseSpace ι) :
    momentumShift (-c) χ (momentumShift c χ s) = s := by
  have h : (momentumShift (-c) χ).comp (momentumShift c χ) = SmoothRingHom.id (PhaseSpace ι) :=
    hom_ext fun a => by
      rcases a with i | i
      · change momentumShift (-c) χ (momentumShift c χ (q i)) = q i
        rw [momentumShift_q, momentumShift_q]
      · change momentumShift (-c) χ (momentumShift c χ (p i)) = p i
        rw [momentumShift_p, SmoothRingHom.map_add, SmoothRingHom.map_mul,
          SmoothRingHom.map_algebraMap, momentumShift_ofPosition, momentumShift_p, map_neg]
        ring
  exact DFunLike.congr_fun h s

end PhaseSpace

end ProjectAinos.SmoothAlgebra
