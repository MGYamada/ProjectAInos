/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SpecialRelativity.ElasticScattering
import ProjectAinos.SpecialRelativity.Causality
import ProjectAinos.SpecialRelativity.Factorization

/-! Public consumers of the kinematics of collisions and of the Lorentz group: the invariant
mass and the frame of the centre of momentum, the decay into two particles, the invariants of a
collision of two particles, signals with a finite speed, and the factorization of a Lorentz
transformation into a boost and a rotation.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

namespace ProjectAinos.SmoothGeometry.Minkowski

variable {d : ℕ}

example {u p : MinkowskiModel d} (hu : FutureTimelike u) (hp : FutureCausal p) (hp0 : p ≠ 0) :
    0 < pair u p :=
  pair_pos_of_futureTimelike hu hp hp0

example {u p : MinkowskiModel d} (hu : FutureTimelike u) (hp : Causal p) (h : 0 ≤ pair u p) :
    FutureCausal p :=
  futureCausal_of_pair_nonneg hu hp h

example (u : Observer d) : FutureTimelike u.velocity := u.futureTimelike

end ProjectAinos.SmoothGeometry.Minkowski

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {p q : MinkowskiModel d}

example (p : MinkowskiModel d) : 0 ≤ invariantMass p :=
  invariantMass_nonneg p

example (hp : FutureCausal p) : invariantMass p ^ 2 = intervalQuadratic p :=
  invariantMass_sq hp

example (L : LorentzGroup d) (p : MinkowskiModel d) :
    invariantMass (L.val p) = invariantMass p :=
  invariantMass_lorentz L p

example (hp : FutureCausal p) (hq : FutureCausal q) :
    invariantMass p + invariantMass q ≤ invariantMass (p + q) :=
  invariantMass_add_le hp hq

example (hp : FutureCausal p) (hq : FutureCausal q) (hp0 : p ≠ 0)
    (hQp : intervalQuadratic p = 0) (hQq : intervalQuadratic q = 0) (hpq : pair p q = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ q = c • p :=
  exists_smul_of_pair_eq_zero hp hq hp0 hQp hQq hpq

example (hp : FutureCausal p) (hq : FutureCausal q)
    (hp0 : p ≠ 0) :
    intervalQuadratic (p + q) = 0 ↔ intervalQuadratic p = 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ q = c • p :=
  intervalQuadratic_add_eq_zero_iff hp hq hp0

example {P : MinkowskiModel d} (hP : FutureTimelike P) :
    observerEnergy (centreOfMomentum P hP) P = invariantMass P :=
  observerEnergy_centreOfMomentum hP

example {P : MinkowskiModel d} (hP : FutureTimelike P) :
    observerMomentum (centreOfMomentum P hP) P = 0 :=
  observerMomentum_centreOfMomentum hP

example {P : MinkowskiModel d} (hP : FutureTimelike P) (u : Observer d)
    (h : observerMomentum u P = 0) : u = centreOfMomentum P hP :=
  eq_centreOfMomentum hP u h

example {P : MinkowskiModel d} (hP0 : P ≠ 0)
    (hQ : intervalQuadratic P = 0) : ¬∃ u : Observer d, observerMomentum u P = 0 :=
  not_exists_observer_of_null hP0 hQ

end ProjectAinos.SpecialRelativity

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ}

example (M m₁ m₂ : ℝ) :
    kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2) = (M ^ 2 - (m₁ + m₂) ^ 2) * (M ^ 2 - (m₁ - m₂) ^ 2) :=
  kallen_sq M m₁ m₂

example {M m₁ m₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (h : m₁ + m₂ ≤ M) :
    0 ≤ kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2) :=
  kallen_sq_nonneg hm₁ hm₂ h

namespace TwoBodyDecay

variable {P p₁ p₂ : MinkowskiModel d} {M m₁ m₂ : ℝ} (h : TwoBodyDecay P p₁ p₂ M m₁ m₂)

include h in
example : pair p₁ p₂ = (M ^ 2 - m₁ ^ 2 - m₂ ^ 2) / 2 :=
  pair_eq h

include h in
example : properSpeed P = M :=
  properSpeed_eq h

example (w : MinkowskiModel d) :
    observerEnergy h.restFrame w = M⁻¹ * pair P w :=
  observerEnergy_restFrame h w

example :
    observerEnergy h.restFrame p₁ = (M ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * M) :=
  energy_first h

example :
    observerEnergy h.restFrame p₂ = (M ^ 2 + m₂ ^ 2 - m₁ ^ 2) / (2 * M) :=
  energy_second h

example : observerEnergy h.restFrame p₁ + observerEnergy h.restFrame p₂ = M :=
  energy_add h

example :
    observerMomentum h.restFrame p₁ + observerMomentum h.restFrame p₂ = 0 :=
  momentum_add h

example :
    h.restFrame.restForm (observerMomentum h.restFrame p₁) (observerMomentum h.restFrame p₁) =
      kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2) / (4 * M ^ 2) :=
  momentum_sq_first h

example :
    h.restFrame.restForm (observerMomentum h.restFrame p₂) (observerMomentum h.restFrame p₂) =
      kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2) / (4 * M ^ 2) :=
  momentum_sq_second h

include h in
example (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hp₁ : FutureCausal p₁)
    (hp₂ : FutureCausal p₂) : m₁ + m₂ ≤ M :=
  mass_add_le h hm₁ hm₂ hp₁ hp₂

example (hM : M = m₁ + m₂) :
    p₁ = m₁ • h.restFrame.velocity ∧ p₂ = m₂ • h.restFrame.velocity :=
  eq_smul_of_threshold h hM

end TwoBodyDecay

example (u : Observer d) {M m₁ m₂ : ℝ} (hM : 0 < M) (hm₁ : 0 ≤ m₁)
    (hm₂ : 0 ≤ m₂) (hle : m₁ + m₂ ≤ M) (n : u.restSpace) (hn : u.restForm n n = 1) :
    ∃ p₁ p₂ : MinkowskiModel d, TwoBodyDecay (M • u.velocity) p₁ p₂ M m₁ m₂ ∧
      FutureCausal p₁ ∧ FutureCausal p₂ ∧
      (u.project p₁ : MinkowskiModel d) =
        (Real.sqrt (kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2)) / (2 * M)) • (n : MinkowskiModel d) :=
  exists_twoBodyDecay u hM hm₁ hm₂ hle n hn

end ProjectAinos.SpecialRelativity

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {p₁ p₂ p₃ p₄ : MinkowskiModel d}

example (v w : MinkowskiModel d) :
    intervalQuadratic (v - w) = intervalQuadratic v - 2 * pair v w + intervalQuadratic w :=
  intervalQuadratic_sub v w

example (hcons : p₁ + p₂ = p₃ + p₄) :
    mandelstamS p₁ p₂ + mandelstamT p₁ p₃ + mandelstamU p₁ p₄ =
      intervalQuadratic p₁ + intervalQuadratic p₂ + intervalQuadratic p₃ +
        intervalQuadratic p₄ :=
  mandelstam_sum hcons

namespace ElasticCollision

variable {m₁ m₂ : ℝ} (h : ElasticCollision p₁ p₂ p₃ p₄ m₁ m₂)

include h in
example : 0 < mandelstamS p₁ p₂ :=
  mandelstamS_pos h

include h in
example :
    TwoBodyDecay (p₁ + p₂) p₁ p₂ (Real.sqrt (mandelstamS p₁ p₂)) m₁ m₂ :=
  decay_in h

include h in
example :
    TwoBodyDecay (p₁ + p₂) p₃ p₄ (Real.sqrt (mandelstamS p₁ p₂)) m₁ m₂ :=
  decay_out h

example : observerEnergy h.centre p₃ = observerEnergy h.centre p₁ :=
  energy_eq h

example : observerEnergy h.centre p₄ = observerEnergy h.centre p₂ :=
  energy_eq_second h

example :
    h.centre.restForm (observerMomentum h.centre p₃) (observerMomentum h.centre p₃) =
      h.centre.restForm (observerMomentum h.centre p₁) (observerMomentum h.centre p₁) :=
  momentum_sq_eq h

example :
    mandelstamT p₁ p₃ = -h.centre.restForm
      (observerMomentum h.centre p₁ - observerMomentum h.centre p₃)
      (observerMomentum h.centre p₁ - observerMomentum h.centre p₃) :=
  mandelstamT_eq h

include h in
example : mandelstamT p₁ p₃ ≤ 0 :=
  mandelstamT_nonpos h

end ElasticCollision

example {m₁ m₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hp₁ : FutureCausal p₁) (hp₂ : FutureCausal p₂) (hQ₁ : intervalQuadratic p₁ = m₁ ^ 2)
    (hQ₂ : intervalQuadratic p₂ = m₂ ^ 2) (hP : FutureTimelike (p₁ + p₂))
    (n : (centreOfMomentum (p₁ + p₂) hP).restSpace)
    (hn : (centreOfMomentum (p₁ + p₂) hP).restForm n n = 1) :
    ∃ q₃ q₄ : MinkowskiModel d, ElasticCollision p₁ p₂ q₃ q₄ m₁ m₂ ∧
      FutureCausal q₃ ∧ FutureCausal q₄ ∧
      ((centreOfMomentum (p₁ + p₂) hP).project q₃ : MinkowskiModel d) =
        (Real.sqrt (kallen (mandelstamS p₁ p₂) (m₁ ^ 2) (m₂ ^ 2)) /
          (2 * Real.sqrt (mandelstamS p₁ p₂))) • (n : MinkowskiModel d) :=
  exists_elasticCollision hm₁ hm₂ hp₁ hp₂ hQ₁ hQ₂ hP n hn

example (u : Observer d) (p₁ : MinkowskiModel d) (m₂ : ℝ) :
    mandelstamS p₁ (m₂ • u.velocity) =
      intervalQuadratic p₁ + m₂ ^ 2 + 2 * m₂ * observerEnergy u p₁ :=
  mandelstamS_target_at_rest u p₁ m₂

example (u : Observer d) (m₂ : ℝ)
    (hcons : p₁ + m₂ • u.velocity = p₃ + p₄) :
    mandelstamT p₁ p₃ = m₂ ^ 2 + intervalQuadratic p₄ - 2 * m₂ * observerEnergy u p₄ :=
  mandelstamT_target_at_rest u m₂ hcons

example (u : Observer d) (m₂ : ℝ)
    (hcons : p₁ + m₂ • u.velocity = p₃ + p₄) (hshell : intervalQuadratic p₄ = m₂ ^ 2) :
    mandelstamT p₁ p₃ = -(2 * m₂ * (observerEnergy u p₄ - m₂)) :=
  mandelstamT_elastic_target_at_rest u m₂ hcons hshell

end ProjectAinos.SpecialRelativity

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ}

example (f : PoincareGroup d)
    (hf : PoincareGroup.linear f ∈ orthochronousLorentzGroup d) (p q : MinkowskiModel d) :
    CausallyPrecedes (f.val p) (f.val q) ↔ CausallyPrecedes p q :=
  causallyPrecedes_poincare f hf p q

namespace IsCausalRelation

variable {R : MinkowskiModel d → MinkowskiModel d → Prop}

example (hR : IsCausalRelation R) (f : PoincareGroup d)
    (hf : PoincareGroup.linear f ∈ orthochronousLorentzGroup d) :
    IsCausalRelation fun p q => R (f.val.symm p) (f.val.symm q) :=
  transform hR f hf

example (hR : IsCausalRelation R) {p q : MinkowskiModel d}
    (h : Spacelike (q - p)) : ¬R p q :=
  not_of_spacelike hR h

example (hR : IsCausalRelation R) (u : Observer d) {p q : MinkowskiModel d}
    (h : R p q) (hne : p ≠ q) : 0 < u.clock (q - p) :=
  clock_pos hR u h hne

example (hR : IsCausalRelation R) (u : Observer d)
    {p q : MinkowskiModel d} (h : R p q) :
    u.restForm (u.project (q - p)) (u.project (q - p)) ≤ u.clock (q - p) ^ 2 :=
  restForm_le_clock_sq hR u h

end IsCausalRelation

example :
    IsCausalRelation (fun p q : MinkowskiModel d => CausallyPrecedes p q) :=
  isCausalRelation_causallyPrecedes

end ProjectAinos.SpecialRelativity

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ}

example (v : MinkowskiModel d) : pair (timeAxis d) v = time v :=
  pair_timeAxis v

example (R : LorentzGroup d) :
    R ∈ rotationGroup d ↔ R.val (timeAxis d) = timeAxis d :=
  mem_rotationGroup_iff R

example {R : LorentzGroup d} (hR : R ∈ rotationGroup d) (v : MinkowskiModel d) :
    time (R.val v) = time v :=
  time_rotation hR v

example {R : LorentzGroup d} (hR : R ∈ rotationGroup d)
    (v : MinkowskiModel d) : ‖space (R.val v)‖ = ‖space v‖ :=
  norm_space_rotation hR v

example : rotationGroup d ≤ orthochronousLorentzGroup d :=
  rotationGroup_le_orthochronous

example (β : Velocity d) :
    (boost β).val β.observer.velocity = timeAxis d :=
  boost_observer β

example (β : Velocity d) :
    (boost β).val.symm (timeAxis d) = β.observer.velocity :=
  boost_symm_timeAxis β

example (L : orthochronousLorentzGroup d) :
    (boostPart L).observer.velocity = L.val.val.symm (timeAxis d) :=
  observer_boostPart L

example (L : orthochronousLorentzGroup d) :
    L.val.val (boostPart L).observer.velocity = timeAxis d :=
  apply_observer_boostPart L

example (L : orthochronousLorentzGroup d) : rotationPart L ∈ rotationGroup d :=
  rotationPart_mem L

example (L : orthochronousLorentzGroup d) :
    rotationPart L * boost (boostPart L) = L.val :=
  rotationPart_mul_boost L

example (L : orthochronousLorentzGroup d) {R : LorentzGroup d}
    (hR : R ∈ rotationGroup d) {β : Velocity d} (h : R * boost β = L.val) :
    β = boostPart L ∧ R = rotationPart L :=
  eq_of_mul_boost_eq L hR h

example (β : Velocity d) : boostPart (boostOrthochronous β) = β :=
  boostPart_boost β

example (β : Velocity d) : rotationPart (boostOrthochronous β) = 1 :=
  rotationPart_boost β

example (L : orthochronousLorentzGroup d) :
    boostPart L = Velocity.zero d ↔ L.val ∈ rotationGroup d :=
  boostPart_eq_zero_iff L

example (β₁ β₂ : Velocity d) :
    boostPart (boostOrthochronous β₁ * boostOrthochronous β₂) =
      Velocity.transform (boostOrthochronous β₂)⁻¹ β₁ :=
  boostPart_boost_mul_boost β₁ β₂

example (β₁ β₂ : Velocity d) : wignerRotation β₁ β₂ ∈ rotationGroup d :=
  wignerRotation_mem β₁ β₂

example (β₁ β₂ : Velocity d) :
    wignerRotation β₁ β₂ * boost (Velocity.transform (boostOrthochronous β₂)⁻¹ β₁) =
      boost β₁ * boost β₂ :=
  wignerRotation_mul_boost β₁ β₂

example {β₁ β₂ β₃ : Velocity d}
    (h : boost β₁ * boost β₂ = boost β₃) : wignerRotation β₁ β₂ = 1 :=
  wignerRotation_eq_one_of_boost h

example (β : Velocity d) :
    wignerRotation β (Velocity.zero d) = 1 :=
  wignerRotation_zero_right β

example (β : Velocity d) :
    wignerRotation (Velocity.zero d) β = 1 :=
  wignerRotation_zero_left β

section Collinear

variable (e : Space d) (he : ‖e‖ = 1)

include he in
example : inner ℝ e e = 1 :=
  inner_self_of_norm_one e he

example (b : ℝ) (hb : |b| < 1) :
    (collinearVelocity e he b hb).gamma ^ 2 * (1 - b ^ 2) = 1 :=
  gamma_collinear_identity e he b hb

example (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    (collinearVelocity e he ((a + b) / (1 + a * b)) (composed_speed_lt_one a b ha hb)).gamma =
      (collinearVelocity e he a ha).gamma * (collinearVelocity e he b hb).gamma *
        (1 + a * b) :=
  gamma_collinear_composed e he a b ha hb

example (b : ℝ) (hb : |b| < 1) :
    (collinearVelocity e he b hb).gamma ^ 2 / (1 + (collinearVelocity e he b hb).gamma) *
      b ^ 2 = (collinearVelocity e he b hb).gamma - 1 :=
  gamma_collinear_ratio e he b hb

example (b : ℝ) (hb : |b| < 1) (v : MinkowskiModel d) :
    time ((boost (collinearVelocity e he b hb)).val v) =
      (collinearVelocity e he b hb).gamma * (time v - b * inner ℝ e (space v)) :=
  boost_collinear_time e he b hb v

example (b : ℝ) (hb : |b| < 1) (v : MinkowskiModel d) :
    space ((boost (collinearVelocity e he b hb)).val v) = space v +
      (((collinearVelocity e he b hb).gamma - 1) * inner ℝ e (space v) -
        (collinearVelocity e he b hb).gamma * b * time v) • e :=
  boost_collinear_space e he b hb v

example (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    boost (collinearVelocity e he a ha) * boost (collinearVelocity e he b hb) =
      boost (collinearVelocity e he ((a + b) / (1 + a * b))
        (composed_speed_lt_one a b ha hb)) :=
  boost_collinear_mul e he a b ha hb

example (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    wignerRotation (collinearVelocity e he a ha) (collinearVelocity e he b hb) = 1 :=
  wignerRotation_collinear e he a b ha hb

end Collinear

end ProjectAinos.SpecialRelativity
