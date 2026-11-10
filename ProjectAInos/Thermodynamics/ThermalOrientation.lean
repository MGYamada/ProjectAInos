module

public import ProjectAInos.Thermodynamics.ThermalFamily
public import ProjectAInos.Thermodynamics.EnergyOrientation

/-!
# Common energy orientation under thermal contact

LY Theorem 4.2 uses T1 and T2 only. At an equilibrium split, a vertical interior
accessibility step in either component gives an accessibility step in the joined
system at fixed work coordinates. Opposite component orientations would let the
joined state reach both higher and lower total energies, contradicting its
simple-system orientation. T2 supplies an equilibrium split for every joined
state, so any two nonempty systems admitting a thermal join have the same sign.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X}

namespace SimpleSystem

/-- The supporting-plane sign orders any accessible point on the same energy
fiber; unlike strict interior movement, this permits equality. -/
theorem HasSign.energy_le_of_relation_same_work {n : ℕ} (S : SimpleSystem P n)
    {s : ℝ} {x y : SimpleCoordinates n} (h : S.HasSign s x)
    (hy : y ∈ S.domain) (hxy : P.relation (S.represent x) (S.represent y))
    (hv : y.2 = x.2) : s * x.1 ≤ s * y.1 := by
  have hp := h y ⟨hy, hxy⟩
  have heq : pressureForm (S.pressure x) (y - x) = y.1 - x.1 := by
    simp [pressureForm, hv]
  rw [heq] at hp
  nlinarith

end SimpleSystem

namespace SimpleThermalJoin

variable {n m : ℕ} {S : SimpleSystem P n} {T : SimpleSystem P m}

/-- T1 forces the two components of an equilibrium split to have the same
energy orientation. Neither the zeroth law nor transversality is used. -/
theorem same_orientation_of_equilibrium (J : SimpleThermalJoin S T)
    (x : S.domain) (y : T.domain) (hxy : J.thermalJoin.Equilibrium x y) :
    (S.Positive x ∧ T.Positive y) ∨ (S.Negative x ∧ T.Negative y) := by
  obtain ⟨a, ha, hav⟩ := S.exists_interior_same_work x.property
  obtain ⟨b, hb, hbv⟩ := T.exists_interior_same_work y.property
  let a' : S.domain := ⟨a, (interior_subset ha).1⟩
  let b' : T.domain := ⟨b, (interior_subset hb).1⟩
  let z := J.point (joinedState x y)
  let za := J.point (joinedState a' y)
  let zb := J.point (joinedState x b')
  have hza : P.relation (J.system.represent z) (J.system.represent za) := by
    simp only [z, za, J.represent_point]
    exact P.trans hxy (P.trans (P.add_mono (interior_subset ha).2 (P.refl _))
      (J.thermalJoin.contact a' y))
  have hzb : P.relation (J.system.represent z) (J.system.represent zb) := by
    simp only [z, zb, J.represent_point]
    exact P.trans hxy (P.trans (P.add_mono (P.refl _) (interior_subset hb).2)
      (J.thermalJoin.contact x b'))
  have hvza : za.val.2 = z.val.2 := by
    change Fin.append a.2 y.val.2 = Fin.append x.val.2 y.val.2
    rw [hav]
  have hvzb : zb.val.2 = z.val.2 := by
    change Fin.append x.val.2 b.2 = Fin.append x.val.2 y.val.2
    rw [hbv]
  rcases J.system.positive_or_negative z.property with hp | hn
  · have hEa := SimpleSystem.HasSign.energy_le_of_relation_same_work
      J.system hp za.property hza hvza
    have hEb := SimpleSystem.HasSign.energy_le_of_relation_same_work
      J.system hp zb.property hzb hvzb
    change 1 * (x.val.1 + y.val.1) ≤ 1 * (a.1 + y.val.1) at hEa
    change 1 * (x.val.1 + y.val.1) ≤ 1 * (x.val.1 + b.1) at hEb
    left
    constructor
    · rcases S.positive_or_negative x.property with hx | hx
      · exact hx
      · have hlt := SimpleSystem.HasSign.energy_lt_of_interior_same_work S
          (by norm_num : (-1 : ℝ) ≠ 0) hx ha hav
        linarith
    · rcases T.positive_or_negative y.property with hy | hy
      · exact hy
      · have hlt := SimpleSystem.HasSign.energy_lt_of_interior_same_work T
          (by norm_num : (-1 : ℝ) ≠ 0) hy hb hbv
        linarith
  · have hEa := SimpleSystem.HasSign.energy_le_of_relation_same_work
      J.system hn za.property hza hvza
    have hEb := SimpleSystem.HasSign.energy_le_of_relation_same_work
      J.system hn zb.property hzb hvzb
    change (-1) * (x.val.1 + y.val.1) ≤ (-1) * (a.1 + y.val.1) at hEa
    change (-1) * (x.val.1 + y.val.1) ≤ (-1) * (x.val.1 + b.1) at hEb
    right
    constructor
    · rcases S.positive_or_negative x.property with hx | hx
      · have hlt := SimpleSystem.HasSign.energy_lt_of_interior_same_work S
          one_ne_zero hx ha hav
        linarith
      · exact hx
    · rcases T.positive_or_negative y.property with hy | hy
      · have hlt := SimpleSystem.HasSign.energy_lt_of_interior_same_work T
          one_ne_zero hy hb hbv
        linarith
      · exact hy

/-- T2 supplies a common-sign equilibrium split; sign constancy within each
simple system transfers the result to arbitrary component states. -/
theorem same_orientation (J : SimpleThermalJoin S T) (x : S.domain) (y : T.domain) :
    (S.Positive x ∧ T.Positive y) ∨ (S.Negative x ∧ T.Negative y) := by
  obtain ⟨a, b, hab, hsplit⟩ := J.thermalJoin.splitting (joinedState x y)
  have heq : J.thermalJoin.Equilibrium a b := by
    change P.relation (J.thermalJoin.represent (joinedState a b)) (S.represent a + T.represent b)
    rw [hab]
    exact hsplit
  rcases J.same_orientation_of_equilibrium a b heq with hp | hn
  · exact Or.inl ⟨S.positive_everywhere a.property hp.1 x x.property,
      T.positive_everywhere b.property hp.2 y y.property⟩
  · exact Or.inr ⟨S.negative_everywhere a.property hn.1 x x.property,
      T.negative_everywhere b.property hn.2 y y.property⟩

theorem positive_iff (J : SimpleThermalJoin S T) (x : S.domain) (y : T.domain) :
    S.Positive x ↔ T.Positive y := by
  rcases J.same_orientation x y with hp | hn
  · exact ⟨fun _ => hp.2, fun _ => hp.1⟩
  · constructor
    · intro hx
      exact False.elim (S.not_hasSign_neg one_ne_zero x.property hx hn.1)
    · intro hy
      exact False.elim (T.not_hasSign_neg one_ne_zero y.property hy hn.2)

end SimpleThermalJoin

namespace ThermalFamily

variable (F : ThermalFamily P)

/-- LY 4.2 for two represented member states. The proof only inspects the
thermal join's T1 geometry and T2 splitting. -/
theorem positive_iff {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T) (x : S.domain) (y : T.domain) :
    S.Positive x ↔ T.Positive y := (F.join S T hS hT).positive_iff x y

/-- One positive member state fixes the orientation throughout the family. -/
theorem positive_everywhere {n : ℕ} (S : SimpleSystem P n) (hS : F.admitted S)
    (x : S.domain) (hx : S.Positive x) :
    ∀ {m : ℕ} (T : SimpleSystem P m), F.admitted T → ∀ y : T.domain, T.Positive y := by
  intro m T hT y
  exact (F.positive_iff S T hS hT x y).mp hx

/-- The common-orientation dichotomy includes families with no represented
states: in that case both universally quantified alternatives are vacuous. -/
theorem common_energy_orientation :
    (∀ {n : ℕ} (S : SimpleSystem P n), F.admitted S → ∀ x : S.domain, S.Positive x) ∨
    (∀ {n : ℕ} (S : SimpleSystem P n), F.admitted S → ∀ x : S.domain, S.Negative x) := by
  classical
  by_cases hp : ∃ n, ∃ S : SimpleSystem P n, ∃ hS : F.admitted S, ∃ x : S.domain, S.Positive x
  · obtain ⟨n, S, hS, x, hx⟩ := hp
    exact Or.inl (F.positive_everywhere S hS x hx)
  · right
    intro n S hS x
    rcases S.positive_or_negative x.property with hx | hx
    · exact False.elim (hp ⟨n, S, hS, x, hx⟩)
    · exact hx

end ThermalFamily

end ProjectAInos.Thermodynamics.Physical
