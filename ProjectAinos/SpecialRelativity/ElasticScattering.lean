/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.Decay
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The kinematics of a collision of two particles

Two particles with the momenta `p₁`, `p₂` collide and leave with the momenta `p₃`, `p₄`
(Landau–Lifshitz, *The Classical Theory of Fields*, §13). With the quadratic form `Q`, which is
`−g(p, p)` for `(−+++)`, the invariants are

`s = Q(p₁ + p₂)`, `t = Q(p₁ − p₃)`, `u = Q(p₁ − p₄)`.

* `mandelstam_sum`: if `p₁ + p₂ = p₃ + p₄` then `s + t + u = Q(p₁) + Q(p₂) + Q(p₃) + Q(p₄)`,
  the sum of the squares of the four masses.
* **Centre of momentum.** For an elastic collision, in which the masses are unchanged, the
  energy and the length of the momentum of each particle are unchanged in the frame of the
  centre of momentum (`ElasticCollision.energy_eq`, `ElasticCollision.momentum_sq_eq`), and
  `t = −|𝐩₁ − 𝐩₃|² ≤ 0` (`ElasticCollision.mandelstamT_eq`). Every unit vector of the rest
  space of the centre of momentum is the direction of an outgoing momentum
  (`exists_elasticCollision`).
* **Target at rest.** If `p₂ = m₂ u` for an observer `u`, then `s = m₁² + m₂² + 2 m₂ E₁`
  (`mandelstamS_target_at_rest`) and `t = m₂² + Q(p₄) − 2 m₂ E₄`
  (`mandelstamT_target_at_rest`), so `t = −2 m₂ (E₄ − m₂)` for an elastic collision.

These are consequences of the conservation of the momentum and of the mass shells. They do not
determine the angle of the scattering.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {p₁ p₂ p₃ p₄ : MinkowskiModel d}

/-- The invariant `s = Q(p₁ + p₂)`: the square of the energy in the frame of the centre of
momentum. -/
def mandelstamS (p₁ p₂ : MinkowskiModel d) : ℝ := intervalQuadratic (p₁ + p₂)

/-- The invariant `t = Q(p₁ − p₃)`: the square of the transferred momentum. -/
def mandelstamT (p₁ p₃ : MinkowskiModel d) : ℝ := intervalQuadratic (p₁ - p₃)

/-- The invariant `u = Q(p₁ − p₄)`. -/
def mandelstamU (p₁ p₄ : MinkowskiModel d) : ℝ := intervalQuadratic (p₁ - p₄)

/-- The quadratic form of a difference. -/
theorem intervalQuadratic_sub (v w : MinkowskiModel d) :
    intervalQuadratic (v - w) = intervalQuadratic v - 2 * pair v w + intervalQuadratic w := by
  simp only [intervalQuadratic_apply, map_sub, sub_apply, pair_comm w v]
  ring

/-- `s + t + u` is the sum of the squares of the four masses. -/
theorem mandelstam_sum (hcons : p₁ + p₂ = p₃ + p₄) :
    mandelstamS p₁ p₂ + mandelstamT p₁ p₃ + mandelstamU p₁ p₄ =
      intervalQuadratic p₁ + intervalQuadratic p₂ + intervalQuadratic p₃ +
        intervalQuadratic p₄ := by
  have h4 : p₄ = p₁ + p₂ - p₃ := by rw [hcons]; abel
  subst h4
  simp only [mandelstamS, mandelstamT, mandelstamU, intervalQuadratic_apply, map_add, map_sub,
    add_apply, sub_apply, pair_comm p₂ p₁, pair_comm p₃ p₁, pair_comm p₃ p₂]
  ring

/-! ### The frame of the centre of momentum -/

/-- An elastic collision: the momentum is conserved, the masses of the two particles are
unchanged, and the total momentum is future timelike. -/
structure ElasticCollision (p₁ p₂ p₃ p₄ : MinkowskiModel d) (m₁ m₂ : ℝ) : Prop where
  conservation : p₁ + p₂ = p₃ + p₄
  first_in : intervalQuadratic p₁ = m₁ ^ 2
  second_in : intervalQuadratic p₂ = m₂ ^ 2
  first_out : intervalQuadratic p₃ = m₁ ^ 2
  second_out : intervalQuadratic p₄ = m₂ ^ 2
  future : FutureTimelike (p₁ + p₂)

namespace ElasticCollision

variable {m₁ m₂ : ℝ} (h : ElasticCollision p₁ p₂ p₃ p₄ m₁ m₂)

include h in
theorem mandelstamS_pos : 0 < mandelstamS p₁ p₂ :=
  ((futureTimelike_iff _).mp h.future).1

include h in
/-- The incoming pair, as a decay of the total momentum. -/
theorem decay_in :
    TwoBodyDecay (p₁ + p₂) p₁ p₂ (Real.sqrt (mandelstamS p₁ p₂)) m₁ m₂ where
  conservation := rfl
  parent := (Real.sq_sqrt h.mandelstamS_pos.le).symm
  first := h.first_in
  second := h.second_in
  mass_pos := Real.sqrt_pos.mpr h.mandelstamS_pos
  future := h.future

include h in
/-- The outgoing pair, as a decay of the total momentum. -/
theorem decay_out :
    TwoBodyDecay (p₁ + p₂) p₃ p₄ (Real.sqrt (mandelstamS p₁ p₂)) m₁ m₂ where
  conservation := h.conservation
  parent := (Real.sq_sqrt h.mandelstamS_pos.le).symm
  first := h.first_out
  second := h.second_out
  mass_pos := Real.sqrt_pos.mpr h.mandelstamS_pos
  future := h.future

/-- The frame of the centre of momentum. -/
def centre : Observer d := centreOfMomentum (p₁ + p₂) h.future

/-- In the frame of the centre of momentum the energy of the first particle is unchanged. -/
theorem energy_eq : observerEnergy h.centre p₃ = observerEnergy h.centre p₁ :=
  h.decay_out.energy_first.trans h.decay_in.energy_first.symm

/-- In the frame of the centre of momentum the energy of the second particle is unchanged. -/
theorem energy_eq_second : observerEnergy h.centre p₄ = observerEnergy h.centre p₂ :=
  h.decay_out.energy_second.trans h.decay_in.energy_second.symm

/-- In the frame of the centre of momentum the length of the momentum is unchanged. -/
theorem momentum_sq_eq :
    h.centre.restForm (observerMomentum h.centre p₃) (observerMomentum h.centre p₃) =
      h.centre.restForm (observerMomentum h.centre p₁) (observerMomentum h.centre p₁) :=
  h.decay_out.momentum_sq_first.trans h.decay_in.momentum_sq_first.symm

/-- `t = −|𝐩₁ − 𝐩₃|²` in the frame of the centre of momentum. -/
theorem mandelstamT_eq :
    mandelstamT p₁ p₃ = -h.centre.restForm
      (observerMomentum h.centre p₁ - observerMomentum h.centre p₃)
      (observerMomentum h.centre p₁ - observerMomentum h.centre p₃) := by
  have hsplit := h.centre.intervalQuadratic_eq (p₁ - p₃)
  have hE : h.centre.clock (p₁ - p₃) = 0 := by
    have h1 := h.energy_eq
    rw [observerEnergy, observerEnergy] at h1
    rw [map_sub, h1, sub_self]
  have hproj : h.centre.project (p₁ - p₃) =
      observerMomentum h.centre p₁ - observerMomentum h.centre p₃ :=
    map_sub h.centre.project p₁ p₃
  rw [mandelstamT, hsplit, hE, hproj]
  ring

include h in
/-- The square of the transferred momentum is not positive. -/
theorem mandelstamT_nonpos : mandelstamT p₁ p₃ ≤ 0 := by
  rw [h.mandelstamT_eq, neg_nonpos]
  by_cases hz : observerMomentum h.centre p₁ - observerMomentum h.centre p₃ = 0
  · rw [hz, map_zero]
  · exact (h.centre.restForm_posDef _ hz).le

end ElasticCollision

/-- The outgoing directions: for incoming momenta of the future cone with a timelike total, and
for every unit vector `n` of the rest space of the centre of momentum, there is an elastic
collision in which the first particle leaves with the momentum `(√λ/2√s) n`. -/
theorem exists_elasticCollision {m₁ m₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hp₁ : FutureCausal p₁) (hp₂ : FutureCausal p₂) (hQ₁ : intervalQuadratic p₁ = m₁ ^ 2)
    (hQ₂ : intervalQuadratic p₂ = m₂ ^ 2) (hP : FutureTimelike (p₁ + p₂))
    (n : (centreOfMomentum (p₁ + p₂) hP).restSpace)
    (hn : (centreOfMomentum (p₁ + p₂) hP).restForm n n = 1) :
    ∃ q₃ q₄ : MinkowskiModel d, ElasticCollision p₁ p₂ q₃ q₄ m₁ m₂ ∧
      FutureCausal q₃ ∧ FutureCausal q₄ ∧
      ((centreOfMomentum (p₁ + p₂) hP).project q₃ : MinkowskiModel d) =
        (Real.sqrt (kallen (mandelstamS p₁ p₂) (m₁ ^ 2) (m₂ ^ 2)) /
          (2 * Real.sqrt (mandelstamS p₁ p₂))) • (n : MinkowskiModel d) := by
  have hs : 0 < mandelstamS p₁ p₂ := ((futureTimelike_iff _).mp hP).1
  have hM : 0 < Real.sqrt (mandelstamS p₁ p₂) := Real.sqrt_pos.mpr hs
  have hle : m₁ + m₂ ≤ Real.sqrt (mandelstamS p₁ p₂) := by
    have h := invariantMass_add_le hp₁ hp₂
    have h1 : invariantMass p₁ = m₁ := by
      rw [invariantMass, properSpeed, hQ₁, Real.sqrt_sq hm₁]
    have h2 : invariantMass p₂ = m₂ := by
      rw [invariantMass, properSpeed, hQ₂, Real.sqrt_sq hm₂]
    rw [h1, h2] at h
    exact h
  have htotal : Real.sqrt (mandelstamS p₁ p₂) • (centreOfMomentum (p₁ + p₂) hP).velocity =
      p₁ + p₂ := properSpeed_smul_fourVelocity hP
  obtain ⟨q₃, q₄, hdec, h3, h4, hproj⟩ :=
    exists_twoBodyDecay (centreOfMomentum (p₁ + p₂) hP) hM hm₁ hm₂ hle n hn
  have hsq : Real.sqrt (mandelstamS p₁ p₂) ^ 2 = mandelstamS p₁ p₂ := Real.sq_sqrt hs.le
  rw [hsq] at hproj
  refine ⟨q₃, q₄, ⟨?_, hQ₁, hQ₂, hdec.first, hdec.second, hP⟩, h3, h4, hproj⟩
  rw [← htotal]
  exact hdec.conservation

/-! ### A target at rest -/

/-- For a target at rest, `s = m₁² + m₂² + 2 m₂ E₁`. -/
theorem mandelstamS_target_at_rest (u : Observer d) (p₁ : MinkowskiModel d) (m₂ : ℝ) :
    mandelstamS p₁ (m₂ • u.velocity) =
      intervalQuadratic p₁ + m₂ ^ 2 + 2 * m₂ * observerEnergy u p₁ := by
  have hpair : pair p₁ u.velocity = observerEnergy u p₁ := pair_comm _ _
  rw [mandelstamS, intervalQuadratic_add, QuadraticMap.map_smul, u.unit, map_smul, hpair]
  simp only [smul_eq_mul]
  ring

/-- For a target at rest, `t = m₂² + Q(p₄) − 2 m₂ E₄`. -/
theorem mandelstamT_target_at_rest (u : Observer d) (m₂ : ℝ)
    (hcons : p₁ + m₂ • u.velocity = p₃ + p₄) :
    mandelstamT p₁ p₃ = m₂ ^ 2 + intervalQuadratic p₄ - 2 * m₂ * observerEnergy u p₄ := by
  have hdiff : p₁ - p₃ = p₄ - m₂ • u.velocity := by
    rw [sub_eq_sub_iff_add_eq_add, hcons, add_comm]
  have hpair : pair p₄ u.velocity = observerEnergy u p₄ := pair_comm _ _
  rw [mandelstamT, hdiff, intervalQuadratic_sub, QuadraticMap.map_smul, u.unit, map_smul, hpair]
  simp only [smul_eq_mul]
  ring

/-- For an elastic collision with a target at rest, `t = −2 m₂ (E₄ − m₂)`: the square of the
transferred momentum is given by the kinetic energy of the recoil. -/
theorem mandelstamT_elastic_target_at_rest (u : Observer d) (m₂ : ℝ)
    (hcons : p₁ + m₂ • u.velocity = p₃ + p₄) (hshell : intervalQuadratic p₄ = m₂ ^ 2) :
    mandelstamT p₁ p₃ = -(2 * m₂ * (observerEnergy u p₄ - m₂)) := by
  rw [mandelstamT_target_at_rest u m₂ hcons, hshell]
  ring

end ProjectAinos.SpecialRelativity
