module

public import ProjectAInos.Thermodynamics.SimpleSystem
public import ProjectAInos.Thermodynamics.ThermalEquilibrium
public import ProjectAInos.Thermodynamics.ThermalStrips
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Typed thermal families

Thermal contact joins two represented simple systems, with one energy coordinate
and the concatenated work coordinates. Positive scaling acts on both the physical
state and its extensive coordinates. Thermal premises concern represented simple
states only; they do not impose thermal equilibrium on arbitrary composites or
on the empty system. Intermediate lemmas take simple-system comparison and
open strict strips as explicit inputs.
`ProjectAInos.Thermodynamics.Physical.ThermalFamily.simpleComparison` and
`ProjectAInos.Thermodynamics.Physical.ThermalFamily.localMixtureIntervals_of_axioms` in
`ProjectAInos.Thermodynamics.SimpleComparison` discharge those inputs from the
geometric premises of the admitted systems, including thermal joins.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
variable {P : Accessibility X}

/-- The extensive coordinate domain of a positive scaled copy. -/
def SimpleSystem.scaledDomain {n : ℕ} (S : SimpleSystem P n) (r : ℝ≥0) :
    Set (SimpleCoordinates n) := {z | (r : ℝ)⁻¹ • z ∈ S.domain}

/-- Geometric data for a scaled member of a family, with its domain and physical
representation fixed by extensive scaling. Only positive scales are used below. -/
structure ScaledSimpleSystem {n : ℕ} (S : SimpleSystem P n) (r : ℝ≥0) where
  system : SimpleSystem P n
  domain_eq : system.domain = S.scaledDomain r
  represent_eq : ∀ z, system.represent z = r • S.represent ((r : ℝ)⁻¹ • z)

namespace ScaledSimpleSystem

variable {n : ℕ} {S : SimpleSystem P n} {r : ℝ≥0}

/-- The scaled coordinate point belongs to the scaled equilibrium domain. -/
def point (D : ScaledSimpleSystem S r) (hr : 0 < r) (x : S.domain) : D.system.domain :=
  ⟨(r : ℝ) • x.val, by
    rw [D.domain_eq]
    change (r : ℝ)⁻¹ • ((r : ℝ) • x.val) ∈ S.domain
    simpa only [inv_smul_smul₀ (NNReal.coe_ne_zero.mpr hr.ne')] using x.property⟩

@[simp] theorem represent_point (D : ScaledSimpleSystem S r) (hr : 0 < r) (x : S.domain) :
    D.system.represent (D.point hr x) = r • S.represent x := by
  rw [D.represent_eq]
  simp only [point, inv_smul_smul₀ (NNReal.coe_ne_zero.mpr hr.ne')]

end ScaledSimpleSystem

/-- The exact coordinate chart for a thermal join: retain total energy and
concatenate the two work-coordinate vectors. -/
def thermalJoinCoordinates (n m : ℕ) :
    (ℝ × WorkCoordinates n × WorkCoordinates m) ≃ SimpleCoordinates (n + m) where
  toFun z := (z.1, Fin.append z.2.1 z.2.2)
  invFun z := (z.1, (fun i => z.2 (Fin.castAdd m i)), fun j => z.2 (Fin.natAdd n j))
  left_inv z := by rcases z with ⟨U, V, W⟩; simp
  right_inv z := by rcases z with ⟨U, V⟩; simp only [Fin.append_castAdd_natAdd]

/-- T1 and the ordinary splitting clause of T2, with a geometrically regular
joined simple system. The `system` field includes all A7/S1--S3 premises;
contact and splitting alone do not provide unique support, locally Lipschitz
pressure, or path-connected relative boundaries. The weaker `ThermalJoin`
layer retains contact/splitting without this geometric requirement. -/
structure SimpleThermalJoin {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m) where
  thermalJoin : ThermalJoin P S.domain T.domain (fun x => S.represent x) (fun y => T.represent y)
  system : SimpleSystem P (n + m)
  domain_eq : system.domain = thermalJoinCoordinates n m '' joinedDomain S.domain T.domain
  represent_eq : ∀ z : joinedDomain S.domain T.domain,
    system.represent (thermalJoinCoordinates n m z) = thermalJoin.represent z

namespace SimpleThermalJoin

variable {n m : ℕ} {S : SimpleSystem P n} {T : SimpleSystem P m}

/-- A point of the thermal join in its simple-system coordinates. -/
def point (J : SimpleThermalJoin S T) (z : joinedDomain S.domain T.domain) : J.system.domain :=
  ⟨thermalJoinCoordinates n m z, by rw [J.domain_eq]; exact ⟨z, z.property, rfl⟩⟩

@[simp] theorem represent_point (J : SimpleThermalJoin S T)
    (z : joinedDomain S.domain T.domain) :
    J.system.represent (J.point z) = J.thermalJoin.represent z := J.represent_eq z

/-- Comparison on the simple thermal join transfers to its equilibrium splits.
Comparison is an explicit intermediate input, not part of thermal contact. -/
theorem equilibrium_products_comparable (J : SimpleThermalJoin S T)
    (hCH : ∀ x y : J.system.domain,
      P.relation (J.system.represent x) (J.system.represent y) ∨
        P.relation (J.system.represent y) (J.system.represent x))
    (x u : S.domain) (y v : T.domain)
    (hxy : J.thermalJoin.Equilibrium x y) (huv : J.thermalJoin.Equilibrium u v) :
    P.relation (S.represent x + T.represent y) (S.represent u + T.represent v) ∨
      P.relation (S.represent u + T.represent v) (S.represent x + T.represent y) := by
  have h := hCH (J.point (joinedState x y)) (J.point (joinedState u v))
  simp only [represent_point] at h
  rcases h with h | h
  · exact Or.inl (P.trans (J.thermalJoin.contact x y) (P.trans h huv))
  · exact Or.inr (P.trans (J.thermalJoin.contact u v) (P.trans h hxy))

end SimpleThermalJoin

/-- A family of simple systems closed under positive scaling and thermal joins.
The fields record T1--T4 and symmetry of unordered thermal contact. The thermal
relation is constrained only on represented member states. No comparison
hypothesis is included. Zero endpoints retain their adiabatic meaning through
`Accessibility.split`, without declaring the empty system thermally equivalent
to every simple state. -/
structure ThermalFamily (P : Accessibility X) where
  admitted : ∀ {n : ℕ}, SimpleSystem P n → Prop
  scale : ∀ {n : ℕ} (S : SimpleSystem P n), admitted S →
    ∀ r : ℝ≥0, 0 < r → ScaledSimpleSystem S r
  scale_admitted : ∀ {n : ℕ} (S : SimpleSystem P n) (hS : admitted S)
    (r : ℝ≥0) (hr : 0 < r), admitted (scale S hS r hr).system
  join : ∀ {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m),
    admitted S → admitted T → SimpleThermalJoin S T
  join_admitted : ∀ {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : admitted S) (hT : admitted T), admitted (join S T hS hT).system
  thermal : X → X → Prop
  thermal_iff : ∀ {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : admitted S) (hT : admitted T) (x : S.domain) (y : T.domain),
    thermal (S.represent x) (T.represent y) ↔ (join S T hS hT).thermalJoin.Equilibrium x y
  thermal_symm : ∀ {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m),
    admitted S → admitted T → ∀ (x : S.domain) (y : T.domain),
      thermal (S.represent x) (T.represent y) → thermal (T.represent y) (S.represent x)
  zeroth_law : ∀ {n m k : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (U : SimpleSystem P k), admitted S → admitted T → admitted U →
      ∀ (x : S.domain) (y : T.domain) (z : U.domain),
        thermal (S.represent x) (T.represent y) → thermal (T.represent y) (U.represent z) →
          thermal (S.represent x) (U.represent z)
  scaled_copy : ∀ {n : ℕ} (S : SimpleSystem P n), admitted S →
    ∀ (x : S.domain) (t : ℝ≥0), 0 < t → t < 1 →
      thermal ((1 - t) • S.represent x) (t • S.represent x)
  transversality : ∀ {n : ℕ} (S : SimpleSystem P n), admitted S → ∀ x : S.domain,
    ∃ a b : S.domain, thermal (S.represent a) (S.represent b) ∧
      (P.relation (S.represent a) (S.represent x) ∧ ¬ P.relation (S.represent x) (S.represent a)) ∧
      (P.relation (S.represent x) (S.represent b) ∧ ¬ P.relation (S.represent b) (S.represent x))

namespace ThermalFamily

variable (F : ThermalFamily P)

/-- A nonvacuous thermal family has an admitted simple system with at least
one equilibrium state. Conditional theorems need not assume this predicate. -/
def Nontrivial : Prop :=
  ∃ n, ∃ S : SimpleSystem P n, F.admitted S ∧ S.domain.Nonempty

/-- A physical state represented in some simple member of the thermal family. -/
def IsState (x : X) : Prop :=
  ∃ n, ∃ S : SimpleSystem P n, F.admitted S ∧ ∃ z : S.domain, x = S.represent z

theorem nontrivial_iff_exists_isState : F.Nontrivial ↔ ∃ x, F.IsState x := by
  constructor
  · rintro ⟨n, S, hS, x, hx⟩
    exact ⟨S.represent x, n, S, hS, ⟨x, hx⟩, rfl⟩
  · rintro ⟨x, n, S, hS, z, _⟩
    exact ⟨n, S, hS, z.val, z.property⟩

theorem isState_represent {n : ℕ} (S : SimpleSystem P n) (hS : F.admitted S)
    (x : S.domain) : F.IsState (S.represent x) := ⟨n, S, hS, x, rfl⟩

/-- Positive scaling stays inside the family of represented simple states. -/
theorem isState_scale {x : X} (hx : F.IsState x) {r : ℝ≥0} (hr : 0 < r) :
    F.IsState (r • x) := by
  obtain ⟨n, S, hS, z, rfl⟩ := hx
  exact ⟨n, (F.scale S hS r hr).system, F.scale_admitted S hS r hr,
    (F.scale S hS r hr).point hr z, (ScaledSimpleSystem.represent_point _ hr z).symm⟩

theorem symm {x y : X} (hx : F.IsState x) (hy : F.IsState y)
    (h : F.thermal x y) : F.thermal y x := by
  obtain ⟨_, S, hS, u, rfl⟩ := hx
  obtain ⟨_, T, hT, v, rfl⟩ := hy
  exact F.thermal_symm S T hS hT u v h

theorem trans {x y z : X} (hx : F.IsState x) (hy : F.IsState y) (hz : F.IsState z)
    (hxy : F.thermal x y) (hyz : F.thermal y z) : F.thermal x z := by
  obtain ⟨_, S, hS, u, rfl⟩ := hx
  obtain ⟨_, T, hT, v, rfl⟩ := hy
  obtain ⟨_, U, hU, w, rfl⟩ := hz
  exact F.zeroth_law S T U hS hT hU u v w hxy hyz

theorem scaled_copy_of_isState {x : X} (hx : F.IsState x)
    {t : ℝ≥0} (ht : 0 < t) (ht1 : t < 1) :
    F.thermal ((1 - t) • x) (t • x) := by
  obtain ⟨_, S, hS, z, rfl⟩ := hx
  exact F.scaled_copy S hS z t ht ht1

/-- Typed T2 gives equilibrium with every positive scaled copy. The premise
is applied to a represented state of the scaled simple system, not a composite. -/
theorem self_scale {x : X} (hx : F.IsState x) {r : ℝ≥0} (hr : 0 < r) :
    F.thermal x (r • x) := by
  have hsum : 0 < 1 + r := by positivity
  have hlt : r / (1 + r) < 1 := (div_lt_one hsum).2 (by simp)
  have hleft : (1 - r / (1 + r)) * (1 + r) = 1 := by
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ hsum.ne', add_tsub_cancel_right]
  have hright : r / (1 + r) * (1 + r) = r := div_mul_cancel₀ _ hsum.ne'
  simpa only [smul_smul, hleft, hright, one_smul] using
    F.scaled_copy_of_isState (F.isState_scale hx hsum) (div_pos hr hsum) hlt

theorem refl {x : X} (hx : F.IsState x) : F.thermal x x := by
  simpa only [one_smul] using F.self_scale hx (r := 1) zero_lt_one

/-- LY Theorem 4.1 within a typed thermal family. -/
theorem scale_iff {x y : X} (hx : F.IsState x) (hy : F.IsState y)
    {r s : ℝ≥0} (hr : 0 < r) (hs : 0 < s) :
    F.thermal x y ↔ F.thermal (r • x) (s • y) := by
  have hx' := F.isState_scale hx hr
  have hy' := F.isState_scale hy hs
  have hxr := F.self_scale hx hr
  have hys := F.self_scale hy hs
  constructor
  · intro h
    exact F.trans hx' hx hy' (F.symm hx hx' hxr) (F.trans hx hy hy' h hys)
  · intro h
    exact F.trans hx hx' hy hxr (F.trans hx' hy' hy h (F.symm hy hy' hys))

/-- Simple-system comparison, kept separate from the thermal family axioms. -/
def SimpleComparison : Prop :=
  ∀ {n : ℕ} (S : SimpleSystem P n), F.admitted S → ∀ x y : S.domain,
    P.relation (S.represent x) (S.represent y) ∨ P.relation (S.represent y) (S.represent x)

/-- Thermal mixtures of two equilibrium reference states are comparable with
every state of the original simple system once comparison on simple thermal
joins is available. Strictness of the reference pair is not needed for this
comparison step. The endpoints use adiabatic splitting only. -/
theorem mixture_comparable (hsimpleCH : F.SimpleComparison)
    {n : ℕ} (S : SimpleSystem P n) (hS : F.admitted S)
    (x₀ x₁ y : S.domain) (hthermal : F.thermal (S.represent x₀) (S.represent x₁))
    (t : ℝ≥0) (ht1 : t ≤ 1) :
    P.relation ((1 - t) • S.represent x₀ + t • S.represent x₁) (S.represent y) ∨
      P.relation (S.represent y) ((1 - t) • S.represent x₀ + t • S.represent x₁) := by
  by_cases ht0 : t = 0
  · simpa only [ht0, tsub_zero, one_smul, P.zero_scale, add_zero] using hsimpleCH S hS x₀ y
  by_cases ht_eq : t = 1
  · simpa only [ht_eq, tsub_self, one_smul, P.zero_scale, zero_add] using hsimpleCH S hS x₁ y
  have ht : 0 < t := pos_iff_ne_zero.mpr ht0
  have htlt : t < 1 := lt_of_le_of_ne ht1 ht_eq
  have ha : 0 < 1 - t := tsub_pos_of_lt htlt
  have hab : 1 - t + t = 1 := tsub_add_cancel_of_le ht1
  let A := F.scale S hS (1 - t) ha
  let B := F.scale S hS t ht
  have hA : F.admitted A.system := F.scale_admitted S hS (1 - t) ha
  have hB : F.admitted B.system := F.scale_admitted S hS t ht
  let J := F.join A.system B.system hA hB
  have hxy : J.thermalJoin.Equilibrium (A.point ha x₀) (B.point ht x₁) := by
    apply (F.thermal_iff A.system B.system hA hB _ _).mp
    simpa only [ScaledSimpleSystem.represent_point] using
      (F.scale_iff (F.isState_represent S hS x₀) (F.isState_represent S hS x₁) ha ht).mp hthermal
  have hyy : J.thermalJoin.Equilibrium (A.point ha y) (B.point ht y) := by
    apply (F.thermal_iff A.system B.system hA hB _ _).mp
    simpa only [ScaledSimpleSystem.represent_point] using F.scaled_copy S hS y t ht htlt
  have hcomp := J.equilibrium_products_comparable
    (hsimpleCH J.system (F.join_admitted A.system B.system hA hB))
    (A.point ha x₀) (A.point ha y) (B.point ht x₁) (B.point ht y) hxy hyy
  simp only [ScaledSimpleSystem.represent_point] at hcomp
  have hsplit := P.split (1 - t) t (S.represent y)
  rw [hab, one_smul] at hsplit
  exact hcomp.elim (fun h => Or.inl (P.trans h hsplit.2))
    (fun h => Or.inr (P.trans hsplit.1 h))

/-- T4 supplies the reference pair, while typed thermal joining supplies all
mixture comparisons. This intermediate lemma takes comparison and strict-strip
openness explicitly;
`ProjectAInos.Thermodynamics.Physical.ThermalFamily.localMixtureIntervals_of_axioms` in
`ProjectAInos.Thermodynamics.SimpleComparison` supplies both from the admitted
simple systems' geometric axioms. -/
theorem localMixtureIntervals (hsimpleCH : F.SimpleComparison)
    {n : ℕ} (S : SimpleSystem P n) (hS : F.admitted S)
    (hopen : ∀ a b : S.domain, IsOpen {y : S.domain |
      (P.relation (S.represent a) (S.represent y) ∧
        ¬ P.relation (S.represent y) (S.represent a)) ∧
      (P.relation (S.represent y) (S.represent b) ∧
        ¬ P.relation (S.represent b) (S.represent y))}) :
    S.LocalMixtureIntervals := by
  intro x
  obtain ⟨a, b, hthermal, hax, hxb⟩ := F.transversality S hS x
  refine ⟨a, b, ⟨P.trans hax.1 hxb.1, ?_⟩, _, hopen a b, ⟨hax, hxb⟩, ?_⟩
  · intro hba
    exact hax.2 (P.trans hxb.1 hba)
  · intro y hy
    exact ⟨hy.1.1, hy.2.1, fun t ht =>
      F.mixture_comparable hsimpleCH S hS a b y hthermal t ht⟩

end ThermalFamily

end ProjectAInos.Thermodynamics.Physical
