module

public import ProjectAInos.Thermodynamics.ThermalFamily

/-!
# Thermal coherence between a joined state and its split components

Thermal equivalence is not invariant under arbitrary adiabatic equivalence.
The component result instead uses a concrete cycle: split an iterated join,
merge two copies of one component by convex mixing, then use equilibrium with
the twice-scaled component to recover the original state.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X}

namespace SimpleThermalJoin

variable {n m : ℕ} {S : SimpleSystem P n} {T : SimpleSystem P m}

/-- T2 for a joined state in the canonical simple-system chart. -/
theorem exists_split (J : SimpleThermalJoin S T) (z : J.system.domain) :
    ∃ x : S.domain, ∃ y : T.domain, J.point (joinedState x y) = z ∧
      P.relation (J.system.represent z) (S.represent x + T.represent y) := by
  have hz : z.val ∈ thermalJoinCoordinates n m '' joinedDomain S.domain T.domain := by
    simpa only [J.domain_eq] using z.property
  obtain ⟨q, hq, hqz⟩ := hz
  obtain ⟨x, y, hxy, hsplit⟩ := J.thermalJoin.splitting ⟨q, hq⟩
  have heq : J.point (joinedState x y) = z := by
    apply Subtype.ext
    change thermalJoinCoordinates n m (joinedState x y).val = z.val
    rw [hxy]
    exact hqz
  refine ⟨x, y, heq, ?_⟩
  rw [← heq, J.represent_point, hxy]
  exact hsplit

/-- Equilibrium identifies the joined state's adiabatic class with the sum of
its component classes, without identifying their thermal-equivalence classes. -/
theorem stateClass_eq_sum_of_equilibrium (J : SimpleThermalJoin S T)
    (x : S.domain) (y : T.domain) (h : J.thermalJoin.Equilibrium x y) :
    P.stateClass (J.system.represent (J.point (joinedState x y))) =
      P.stateClass (S.represent x) + P.stateClass (T.represent y) := by
  apply le_antisymm
  · rw [J.represent_point]
    change P.relation (J.thermalJoin.represent (joinedState x y)) (S.represent x + T.represent y)
    exact h
  · rw [J.represent_point]
    change P.relation (S.represent x + T.represent y) (J.thermalJoin.represent (joinedState x y))
    exact J.thermalJoin.contact x y

end SimpleThermalJoin

namespace SimpleSystem

/-- The average of two equilibrium coordinates in a convex simple domain. -/
noncomputable def midpointState {n : ℕ} (S : SimpleSystem P n) (x y : S.domain) : S.domain :=
  ⟨(1 / 2 : ℝ) • x.val + (1 / 2 : ℝ) • y.val,
    S.convex_domain x.property y.property (by norm_num) (by norm_num) (by norm_num)⟩

/-- Convex mixing recombines two copies into twice their average state. -/
theorem stateClass_midpoint_merge {n : ℕ} (S : SimpleSystem P n) (x y : S.domain) :
    P.stateClass (S.represent x) + P.stateClass (S.represent y) ≤
      (2 : ℝ≥0) • P.stateClass (S.represent (S.midpointState x y)) := by
  have h := P.scale_mono (2 : ℝ≥0)
    (S.mixing x x.property y y.property (1 / 2) (1 / 2) (by norm_num))
  change P.stateClass ((2 : ℝ≥0) • ((1 / 2 : ℝ≥0) • S.represent x +
      (1 / 2 : ℝ≥0) • S.represent y)) ≤
    P.stateClass ((2 : ℝ≥0) • S.represent _) at h
  simpa [midpointState, smul_add, smul_smul] using h

end SimpleSystem

namespace ThermalFamily

variable (F : ThermalFamily P)

/-- An equilibrium joined state is in thermal equilibrium with its first
component. This follows from two thermal splittings and the physical merging
of two copies of that component, not from thermal invariance under arbitrary
adiabatic equivalence. -/
theorem join_thermal_left {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T) (x : S.domain) (y : T.domain)
    (hthermal : F.thermal (S.represent x) (T.represent y)) :
    F.thermal ((F.join S T hS hT).system.represent
      ((F.join S T hS hT).point (joinedState x y))) (S.represent x) := by
  let J := F.join S T hS hT
  let z := J.point (joinedState x y)
  have hJ : F.admitted J.system := F.join_admitted S T hS hT
  let L := F.join J.system S hJ hS
  let A := F.scale S hS 2 (by norm_num)
  have hA : F.admitted A.system := F.scale_admitted S hS 2 (by norm_num)
  let K := F.join A.system T hA hT
  have hx2thermal : F.thermal (A.system.represent (A.point (by norm_num) x)) (T.represent y) := by
    have h := (F.scale_iff (F.isState_represent S hS x) (F.isState_represent T hT y)
      (r := 2) (s := 1) (by norm_num) (by norm_num)).mp hthermal
    simpa only [ScaledSimpleSystem.represent_point, one_smul] using h
  have hJeq := J.stateClass_eq_sum_of_equilibrium x y ((F.thermal_iff S T hS hT x y).mp hthermal)
  have hKeq := K.stateClass_eq_sum_of_equilibrium (A.point (by norm_num) x) y
    ((F.thermal_iff A.system T hA hT _ _).mp hx2thermal)
  obtain ⟨z₁, x₂, houter, hsplitL⟩ := L.thermalJoin.splitting (joinedState z x)
  obtain ⟨x₁, y₁, hinner, hsplitJ⟩ := J.exists_split z₁
  let avg := S.midpointState x₁ x₂
  have houterU : z₁.val.1 + x₂.val.1 = z.val.1 + x.val.1 :=
    congrArg (fun q : joinedDomain J.system.domain S.domain => q.val.1) houter
  have houterV : z₁.val.2 = z.val.2 :=
    congrArg (fun q : joinedDomain J.system.domain S.domain => q.val.2.1) houter
  have hx₂V : x₂.val.2 = x.val.2 :=
    congrArg (fun q : joinedDomain J.system.domain S.domain => q.val.2.2) houter
  have hinnerU : x₁.val.1 + y₁.val.1 = z₁.val.1 :=
    congrArg (fun q : J.system.domain => q.val.1) hinner
  have hwork : Fin.append x₁.val.2 y₁.val.2 = Fin.append x.val.2 y.val.2 := by
    calc
      _ = z₁.val.2 := congrArg (fun q : J.system.domain => q.val.2) hinner
      _ = z.val.2 := houterV
      _ = _ := rfl
  have hx₁V : x₁.val.2 = x.val.2 := by
    funext i
    simpa only [Fin.append_left] using congrFun hwork (Fin.castAdd m i)
  have hy₁V : y₁.val.2 = y.val.2 := by
    funext i
    simpa only [Fin.append_right] using congrFun hwork (Fin.natAdd n i)
  have htotal : x₁.val.1 + x₂.val.1 + y₁.val.1 = 2 * x.val.1 + y.val.1 := by
    change z₁.val.1 + x₂.val.1 = (x.val.1 + y.val.1) + x.val.1 at houterU
    linarith
  have hKcoords : joinedState (A.point (by norm_num) avg) y₁ =
      joinedState (A.point (by norm_num) x) y := by
    apply Subtype.ext
    apply Prod.ext
    · change (2 : ℝ) * ((1 / 2 : ℝ) * x₁.val.1 + (1 / 2 : ℝ) * x₂.val.1) + y₁.val.1 =
        2 * x.val.1 + y.val.1
      linarith
    · apply Prod.ext
      · change (2 : ℝ) • ((1 / 2 : ℝ) • x₁.val.2 + (1 / 2 : ℝ) • x₂.val.2) =
          (2 : ℝ) • x.val.2
        rw [hx₁V, hx₂V]
        module
      · exact hy₁V
  have hcontactK : P.stateClass (A.system.represent (A.point (by norm_num) avg)) +
      P.stateClass (T.represent y₁) ≤
      P.stateClass (K.system.represent (K.point (joinedState (A.point (by norm_num) x) y))) := by
    rw [K.represent_point]
    change P.relation (A.system.represent (A.point (by norm_num) avg) + T.represent y₁)
      (K.thermalJoin.represent (joinedState (A.point (by norm_num) x) y))
    simpa only [hKcoords] using K.thermalJoin.contact (A.point (by norm_num) avg) y₁
  apply (F.thermal_iff J.system S hJ hS z x).mpr
  change P.stateClass (L.thermalJoin.represent (joinedState z x)) ≤
    P.stateClass (J.system.represent z) + P.stateClass (S.represent x)
  calc
    _ ≤ P.stateClass (J.system.represent z₁) + P.stateClass (S.represent x₂) := hsplitL
    _ ≤ (P.stateClass (S.represent x₁) + P.stateClass (T.represent y₁)) +
        P.stateClass (S.represent x₂) := add_le_add (show
          P.stateClass (J.system.represent z₁) ≤
            P.stateClass (S.represent x₁) + P.stateClass (T.represent y₁) from hsplitJ) le_rfl
    _ = (P.stateClass (S.represent x₁) + P.stateClass (S.represent x₂)) +
        P.stateClass (T.represent y₁) := by ac_rfl
    _ ≤ (2 : ℝ≥0) • P.stateClass (S.represent avg) + P.stateClass (T.represent y₁) :=
      add_le_add (S.stateClass_midpoint_merge x₁ x₂) le_rfl
    _ = P.stateClass (A.system.represent (A.point (by norm_num) avg)) +
        P.stateClass (T.represent y₁) := by rw [ScaledSimpleSystem.represent_point]; rfl
    _ ≤ P.stateClass (K.system.represent (K.point (joinedState (A.point (by norm_num) x) y))) := hcontactK
    _ = (2 : ℝ≥0) • P.stateClass (S.represent x) + P.stateClass (T.represent y) := by
      rw [hKeq, ScaledSimpleSystem.represent_point]; rfl
    _ = P.stateClass (J.system.represent z) + P.stateClass (S.represent x) := by
      rw [hJeq, two_smul]
      ac_rfl

/-- The same joined state is also in equilibrium with its second component. -/
theorem join_thermal_right {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T) (x : S.domain) (y : T.domain)
    (hthermal : F.thermal (S.represent x) (T.represent y)) :
    F.thermal ((F.join S T hS hT).system.represent
      ((F.join S T hS hT).point (joinedState x y))) (T.represent y) :=
  F.trans (F.isState_represent _ (F.join_admitted S T hS hT) _)
    (F.isState_represent S hS x) (F.isState_represent T hT y)
    (F.join_thermal_left S T hS hT x y hthermal) hthermal

/-- Coordinate-preserving equilibrium splitting puts the joined state and
both components in the same thermal class. The exact coordinate equation is
essential; arbitrary adiabatic equivalence would not suffice. -/
theorem thermal_with_split_components {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (z : (F.join S T hS hT).system.domain) (x : S.domain) (y : T.domain)
    (hcoords : (F.join S T hS hT).point (joinedState x y) = z)
    (hsplit : P.relation ((F.join S T hS hT).system.represent z)
      (S.represent x + T.represent y)) :
    F.thermal ((F.join S T hS hT).system.represent z) (S.represent x) ∧
      F.thermal ((F.join S T hS hT).system.represent z) (T.represent y) := by
  have hthermal : F.thermal (S.represent x) (T.represent y) := by
    apply (F.thermal_iff S T hS hT x y).mpr
    change P.relation ((F.join S T hS hT).thermalJoin.represent (joinedState x y)) _
    rw [← SimpleThermalJoin.represent_point, hcoords]
    exact hsplit
  constructor
  · simpa only [hcoords] using F.join_thermal_left S T hS hT x y hthermal
  · simpa only [hcoords] using F.join_thermal_right S T hS hT x y hthermal

/-- Every joined state has a coordinate-preserving reversible split whose
components share the joined state's thermal class. -/
theorem exists_coherent_split {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T) (z : (F.join S T hS hT).system.domain) :
    ∃ x : S.domain, ∃ y : T.domain,
      (F.join S T hS hT).point (joinedState x y) = z ∧
      P.relation ((F.join S T hS hT).system.represent z) (S.represent x + T.represent y) ∧
      F.thermal ((F.join S T hS hT).system.represent z) (S.represent x) ∧
      F.thermal ((F.join S T hS hT).system.represent z) (T.represent y) := by
  obtain ⟨x, y, hcoords, hsplit⟩ := (F.join S T hS hT).exists_split z
  exact ⟨x, y, hcoords, hsplit,
    F.thermal_with_split_components S T hS hT z x y hcoords hsplit⟩

end ThermalFamily

end ProjectAInos.Thermodynamics.Physical
