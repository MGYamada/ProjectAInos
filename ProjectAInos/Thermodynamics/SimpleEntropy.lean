module

public import ProjectAInos.Thermodynamics.ThermalStrips
public import Mathlib.Analysis.Convex.Continuous

/-!
# Entropy and concavity on one simple system

Local comparable reference intervals determine the entropy coordinate on a
simple-system domain. The convex-combination premise proves concavity, which
gives continuity in finite-dimensional equilibrium coordinates.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical.SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- The normalized affine coordinate, extended by zero outside the equilibrium
domain only to provide an ordinary function on its coordinate space. -/
noncomputable def referenceEntropy (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀)) (x : SimpleCoordinates n) : ℝ := by
  classical
  exact if hx : x ∈ S.domain then
    (S.exists_coordinate_of_local_intervals hlocal x₀ x₁ hstrict ⟨x, hx⟩).choose
  else 0

theorem referenceEntropy_repr (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀))
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) :
    P.completedState (S.represent x) - P.completedState (S.represent x₀) =
      S.referenceEntropy hlocal x₀ x₁ hstrict x •
        (P.completedState (S.represent x₁) - P.completedState (S.represent x₀)) := by
  rw [referenceEntropy, dite_eq_left hx]
  exact (S.exists_coordinate_of_local_intervals hlocal x₀ x₁ hstrict ⟨x, hx⟩).choose_spec

/-- The reference entropy orders all states of this single system. -/
theorem referenceEntropy_relation_iff (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀))
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain) :
    P.relation (S.represent x) (S.represent y) ↔
      S.referenceEntropy hlocal x₀ x₁ hstrict x ≤ S.referenceEntropy hlocal x₀ x₁ hstrict y := by
  obtain ⟨he, hne⟩ := P.strict_reference_direction hstrict
  have hdiff : P.completedState (S.represent y) - P.completedState (S.represent x) =
      (S.referenceEntropy hlocal x₀ x₁ hstrict y -
        S.referenceEntropy hlocal x₀ x₁ hstrict x) •
        (P.completedState (S.represent x₁) - P.completedState (S.represent x₀)) := by
    rw [sub_smul, ← S.referenceEntropy_repr hlocal x₀ x₁ hstrict hy,
      ← S.referenceEntropy_repr hlocal x₀ x₁ hstrict hx]
    abel
  rw [P.relation_iff_nonneg_of_completed_difference he hne _ _ _ hdiff]
  exact sub_nonneg

/-- A7 makes the affine entropy coordinate concave in equilibrium coordinates. -/
theorem referenceEntropy_concave (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀)) :
    ConcaveOn ℝ S.domain (S.referenceEntropy hlocal x₀ x₁ hstrict) := by
  refine ⟨S.convex_domain, ?_⟩
  intro x hx y hy a b ha hb hab
  let s := S.referenceEntropy hlocal x₀ x₁ hstrict
  let e := P.completedState (S.represent x₁) - P.completedState (S.represent x₀)
  let a' : ℝ≥0 := ⟨a, ha⟩
  let b' : ℝ≥0 := ⟨b, hb⟩
  have hab' : a' + b' = 1 := NNReal.eq hab
  have hmix := S.mixing x hx y hy a' b' hab'
  have hz := S.convex_domain hx hy ha hb hab
  have hmixvalue : P.completedState (a' • S.represent x + b' • S.represent y) =
      (a * s x + b * s y) • e + P.completedState (S.represent x₀) := by
    rw [map_add, P.completedState_smul, P.completedState_smul,
      eq_add_of_sub_eq (S.referenceEntropy_repr hlocal x₀ x₁ hstrict hx),
      eq_add_of_sub_eq (S.referenceEntropy_repr hlocal x₀ x₁ hstrict hy)]
    change a • (s x • e + P.completedState (S.represent x₀)) +
      b • (s y • e + P.completedState (S.represent x₀)) = _
    calc
      _ = (a * s x + b * s y) • e + (a + b) • P.completedState (S.represent x₀) := by module
      _ = _ := by rw [hab, one_smul]
  have hdiff : P.completedState (S.represent (a • x + b • y)) -
      P.completedState (a' • S.represent x + b' • S.represent y) =
      (s (a • x + b • y) - (a * s x + b * s y)) • e := by
    rw [hmixvalue, eq_add_of_sub_eq (S.referenceEntropy_repr hlocal x₀ x₁ hstrict hz)]
    change (s (a • x + b • y) • e + _) - ((a * s x + b * s y) • e + _) = _
    module
  obtain ⟨he, hne⟩ := P.strict_reference_direction hstrict
  have h := (P.relation_iff_nonneg_of_completed_difference he hne _ _ _ hdiff).mp hmix
  exact sub_nonneg.mp h

theorem referenceEntropy_continuousOn (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀)) :
    ContinuousOn (S.referenceEntropy hlocal x₀ x₁ hstrict) S.domain :=
  (S.referenceEntropy_concave hlocal x₀ x₁ hstrict).continuousOn S.isOpen_domain

theorem referenceEntropy_normalized (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀)) :
    S.referenceEntropy hlocal x₀ x₁ hstrict x₀ = 0 ∧
      S.referenceEntropy hlocal x₀ x₁ hstrict x₁ = 1 := by
  have hne := (P.strict_reference_direction hstrict).2
  constructor
  · apply smul_left_injective ℝ hne
    dsimp only
    rw [← S.referenceEntropy_repr hlocal x₀ x₁ hstrict x₀.property,
      sub_self, zero_smul]
  · apply smul_left_injective ℝ hne
    dsimp only
    rw [← S.referenceEntropy_repr hlocal x₀ x₁ hstrict x₁.property, one_smul]

/-- Two copies of a single simple system are ordered by their total reference
entropy, as a consequence of the common affine direction. -/
theorem referenceEntropy_pair_relation_iff (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀))
    (a b c d : S.domain) :
    P.relation (S.represent a + S.represent b) (S.represent c + S.represent d) ↔
      S.referenceEntropy hlocal x₀ x₁ hstrict a + S.referenceEntropy hlocal x₀ x₁ hstrict b ≤
        S.referenceEntropy hlocal x₀ x₁ hstrict c + S.referenceEntropy hlocal x₀ x₁ hstrict d := by
  obtain ⟨he, hne⟩ := P.strict_reference_direction hstrict
  have hdiff : P.completedState (S.represent c + S.represent d) -
      P.completedState (S.represent a + S.represent b) =
      (S.referenceEntropy hlocal x₀ x₁ hstrict c + S.referenceEntropy hlocal x₀ x₁ hstrict d -
        (S.referenceEntropy hlocal x₀ x₁ hstrict a + S.referenceEntropy hlocal x₀ x₁ hstrict b)) •
        (P.completedState (S.represent x₁) - P.completedState (S.represent x₀)) := by
    simp only [map_add]
    rw [eq_add_of_sub_eq (S.referenceEntropy_repr hlocal x₀ x₁ hstrict a.property),
      eq_add_of_sub_eq (S.referenceEntropy_repr hlocal x₀ x₁ hstrict b.property),
      eq_add_of_sub_eq (S.referenceEntropy_repr hlocal x₀ x₁ hstrict c.property),
      eq_add_of_sub_eq (S.referenceEntropy_repr hlocal x₀ x₁ hstrict d.property)]
    module
  rw [P.relation_iff_nonneg_of_completed_difference he hne _ _ _ hdiff]
  exact sub_nonneg

/-- Thermal equilibrium of two copies is equivalent to maximizing their total
entropy over all admissible splits of the same joined coordinate state. -/
theorem equilibrium_iff_referenceEntropy_maximum (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀))
    (J : ThermalJoin P S.domain S.domain (fun x => S.represent x) (fun y => S.represent y))
    (x y : S.domain) :
    J.Equilibrium x y ↔ ∀ u v : S.domain, joinedState u v = joinedState x y →
      S.referenceEntropy hlocal x₀ x₁ hstrict u + S.referenceEntropy hlocal x₀ x₁ hstrict v ≤
        S.referenceEntropy hlocal x₀ x₁ hstrict x + S.referenceEntropy hlocal x₀ x₁ hstrict y := by
  constructor
  · intro heq u v huv
    apply (S.referenceEntropy_pair_relation_iff hlocal x₀ x₁ hstrict u v x y).mp
    apply P.trans (J.contact u v)
    rw [huv]
    exact heq
  · intro hmax
    obtain ⟨u, v, huv, hsplit⟩ := J.splitting (joinedState x y)
    exact P.trans hsplit
      ((S.referenceEntropy_pair_relation_iff hlocal x₀ x₁ hstrict u v x y).mpr (hmax u v huv))

end ProjectAInos.Thermodynamics.Physical.SimpleSystem
