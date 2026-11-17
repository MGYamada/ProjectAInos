/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.ProperTime
public import ProjectAinos.SmoothGeometry.Minkowski.ReverseCauchySchwarz
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The energy and the momentum measured by an observer

Let `u` be an observer, a future unit timelike vector, and `p` the momentum vector of a
particle (Landau–Lifshitz, *The Classical Theory of Fields*, §9). With the normalized pairing
`pair`, which is `−g` for the convention `(−+++)`:

* `observerEnergy u p = pair u p` is the energy and `observerMomentum u p = p − E u`, a vector
  of the rest space of `u`, is the momentum (`observerEnergy_smul_add_observerMomentum`);
* `observerEnergy_pos`: the energy of a future timelike momentum is positive, and it is at least
  the mass (`properSpeed_le_observerEnergy`);
* `observerEnergy_sq`: `E² = Q(p) + |p⊥|²`, so `E² = m² + |p⊥|²` on the mass shell
  (`observerEnergy_sq_of_mass`). The length of `p⊥` is taken with the positive definite form of
  the rest space;
* `restForm_observerVelocity_lt_one`: the velocity `p⊥/E` has length less than one;
* `observerEnergy_transform`: transforming the observer and the particle together does not
  change the energy;
* `observerEnergy_change`: for a second observer `u'`,
  `E' = γ E − ⟨γ w, p⊥⟩`, where `γ = pair u' u` and `γ w` is the part of `u'` in the rest space
  of `u`.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} (u : Observer d)

/-- The energy of the momentum `p` measured by the observer `u`. -/
def observerEnergy (p : MinkowskiModel d) : ℝ := u.clock p

/-- The momentum measured by the observer `u`: the part of `p` in the rest space of `u`. -/
def observerMomentum (p : MinkowskiModel d) : u.restSpace := u.project p

/-- The velocity measured by the observer `u`: the momentum divided by the energy. -/
def observerVelocity (p : MinkowskiModel d) : u.restSpace :=
  (observerEnergy u p)⁻¹ • observerMomentum u p

/-- The energy is `−g(u, p)` for `(−+++)` and `g(u, p)` for `(+−−−)`. -/
theorem observerEnergy_convention (σ : LorentzConvention) (p : MinkowskiModel d) :
    observerEnergy u p = σ.timeSign * minkowskiForm σ d u.velocity p := by
  rw [metric_eq, ← mul_assoc, σ.timeSign_mul_self, one_mul]
  rfl

/-- The momentum is the energy along the observer plus the part in the rest space. -/
theorem observerEnergy_smul_add_observerMomentum (p : MinkowskiModel d) :
    observerEnergy u p • u.velocity + (observerMomentum u p : MinkowskiModel d) = p :=
  u.decomposition p

/-- The energy is at least the proper length of the momentum, which is the mass. -/
theorem properSpeed_le_observerEnergy {p : MinkowskiModel d} (hp : FutureCausal p) :
    properSpeed p ≤ observerEnergy u p :=
  u.sqrt_le_clock hp

/-- The energy of a future timelike momentum is positive. -/
theorem observerEnergy_pos {p : MinkowskiModel d} (hp : FutureTimelike p) :
    0 < observerEnergy u p :=
  (Real.sqrt_pos.mpr ((futureTimelike_iff p).mp hp).1).trans_le
    (properSpeed_le_observerEnergy u hp.futureCausal)

/-- `E² = Q(p) + |p⊥|²`. -/
theorem observerEnergy_sq (p : MinkowskiModel d) :
    observerEnergy u p ^ 2 =
      intervalQuadratic p + u.restForm (observerMomentum u p) (observerMomentum u p) := by
  have h := u.intervalQuadratic_eq p
  rw [observerEnergy, observerMomentum]
  linarith

/-- On the mass shell `Q(p) = m²` the energy is `E² = m² + |p⊥|²`. -/
theorem observerEnergy_sq_of_mass {p : MinkowskiModel d} {m : ℝ}
    (hp : intervalQuadratic p = m ^ 2) :
    observerEnergy u p ^ 2 =
      m ^ 2 + u.restForm (observerMomentum u p) (observerMomentum u p) := by
  rw [observerEnergy_sq, hp]

/-- The momentum `m U` of a timelike velocity is on the mass shell. -/
theorem intervalQuadratic_smul_fourVelocity (m : ℝ) {v : MinkowskiModel d} (hv : Timelike v) :
    intervalQuadratic (m • fourVelocity v) = m ^ 2 := by
  rw [QuadraticMap.map_smul, fourVelocity_unit hv, smul_eq_mul, mul_one, pow_two]

/-- The square of the length of the velocity is `1 − Q(p)/E²`. -/
theorem restForm_observerVelocity {p : MinkowskiModel d} (hE : observerEnergy u p ≠ 0) :
    u.restForm (observerVelocity u p) (observerVelocity u p) =
      1 - intervalQuadratic p / observerEnergy u p ^ 2 := by
  have h := observerEnergy_sq u p
  rw [observerVelocity, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  field_simp
  linarith

/-- The velocity of a particle with a future timelike momentum is less than the speed of
light. -/
theorem restForm_observerVelocity_lt_one {p : MinkowskiModel d} (hp : FutureTimelike p) :
    u.restForm (observerVelocity u p) (observerVelocity u p) < 1 := by
  have hE := observerEnergy_pos u hp
  rw [restForm_observerVelocity u hE.ne']
  have hQ : 0 < intervalQuadratic p := ((futureTimelike_iff p).mp hp).1
  have hpos : 0 < intervalQuadratic p / observerEnergy u p ^ 2 := div_pos hQ (pow_pos hE 2)
  linarith

/-- Transforming the observer and the particle together leaves the energy unchanged. -/
theorem observerEnergy_transform (L : orthochronousLorentzGroup d) (p : MinkowskiModel d) :
    observerEnergy (u.transform L) (L.val.val p) = observerEnergy u p :=
  u.clock_transform L p

/-- The momentum measured by the transformed observer is the transformed momentum. -/
theorem observerMomentum_transform (L : orthochronousLorentzGroup d) (p : MinkowskiModel d) :
    (observerMomentum (u.transform L) (L.val.val p) : MinkowskiModel d) =
      L.val.val (observerMomentum u p : MinkowskiModel d) :=
  u.project_transform L p

/-- The energy measured by a second observer `u'`: `E' = γ E − ⟨γ w, p⊥⟩`, with
`γ = pair u' u` and `γ w` the part of `u'` in the rest space of `u`. -/
theorem observerEnergy_change (u' : Observer d) (p : MinkowskiModel d) :
    observerEnergy u' p =
      observerEnergy u u'.velocity * observerEnergy u p -
        u.restForm (observerMomentum u u'.velocity) (observerMomentum u p) := by
  have hp := u.decomposition p
  have hu' := u.decomposition u'.velocity
  have hrest1 : pair u.velocity (u.project p : MinkowskiModel d) = 0 := u.clock_rest (u.project p)
  have hrest2 : pair (u.project u'.velocity : MinkowskiModel d) u.velocity = 0 := by
    rw [pair_comm]
    exact u.clock_rest (u.project u'.velocity)
  have hform : u.restForm (u.project u'.velocity) (u.project p) =
      -pair (u.project u'.velocity : MinkowskiModel d) (u.project p : MinkowskiModel d) := rfl
  have hE : observerEnergy u' p = pair
      (u.clock u'.velocity • u.velocity + (u.project u'.velocity : MinkowskiModel d))
      (u.clock p • u.velocity + (u.project p : MinkowskiModel d)) := by
    rw [hp, hu']
    rfl
  rw [hE, observerEnergy, observerEnergy, observerMomentum, observerMomentum, hform]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hrest1, hrest2]
  have hunit : pair u.velocity u.velocity = 1 := u.unit
  rw [hunit]
  ring

end ProjectAinos.SpecialRelativity
