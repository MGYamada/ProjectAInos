module

public import ProjectAInos.Thermodynamics.CalibratorExistence
public import ProjectAInos.Thermodynamics.SimpleComparison
public import ProjectAInos.Thermodynamics.ThermalJoinCoherence
public import ProjectAInos.Thermodynamics.ThermalClasses
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Component rigidity in the absence of entropy calibrators

If equivalent joined states have equilibrium splits whose first components
are not adiabatically equivalent, single-system comparison produces a crossed
calibrator. Consequently, absence of calibrators forces both components to
stay on fixed adiabats. Graph uniqueness then fixes each component whenever
its work coordinates are fixed.

A separate topological lemma propagates constancy along coordinate fibers
through an open connected product domain. These are ingredients of the
unique-splitting branch; no existence of a calibrator or product comparison is
assumed as a positive premise.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics

/-- A function constant along both kinds of coordinate fibers is constant on
an open preconnected subset of a product. No topology on its target is needed. -/
theorem eq_of_fiberwise_constant_on_open_preconnected
    {A B Q : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {D : Set (A × B)} (hopen : IsOpen D) (hconnected : IsPreconnected D)
    (f : D → Q)
    (hfst : ∀ x y : D, x.val.1 = y.val.1 → f x = f y)
    (hsnd : ∀ x y : D, x.val.2 = y.val.2 → f x = f y) (x y : D) : f x = f y := by
  let : PreconnectedSpace D := isPreconnected_iff_preconnectedSpace.mp hconnected
  have hlocal : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).mpr
    intro u
    obtain ⟨U, V, hU, huU, hV, huV, hsub⟩ :=
      mem_nhds_prod_iff'.mp (hopen.mem_nhds u.property)
    refine ⟨Subtype.val ⁻¹' (U ×ˢ V), (hU.prod hV).preimage continuous_subtype_val,
      ⟨huU, huV⟩, ?_⟩
    intro v hv
    let w : D := ⟨(u.val.1, v.val.2), hsub ⟨huU, hv.2⟩⟩
    exact (hsnd v w rfl).trans (hfst w u rfl)
  exact hlocal.apply_eq_of_preconnectedSpace x y

/-- An equivalence relation holding along coordinate fibers holds throughout
an open preconnected product domain. -/
theorem relation_of_fiberwise_on_open_preconnected
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {D : Set (A × B)} (hopen : IsOpen D) (hconnected : IsPreconnected D)
    (R : D → D → Prop) (hR : Equivalence R)
    (hfst : ∀ x y : D, x.val.1 = y.val.1 → R x y)
    (hsnd : ∀ x y : D, x.val.2 = y.val.2 → R x y) (x y : D) : R x y := by
  let r : Setoid D := ⟨R, hR⟩
  have heq : (Quotient.mk r x) = Quotient.mk r y :=
    eq_of_fiberwise_constant_on_open_preconnected hopen hconnected (Quotient.mk r)
      (fun u v h => Quotient.sound (hfst u v h))
      (fun u v h => Quotient.sound (hsnd u v h)) x y
  exact Quotient.exact heq

namespace Physical

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
variable {P : Accessibility X}

namespace Accessibility

/-- Without a crossed calibrator, comparable first components of equivalent
products must be equivalent separately, as must the second components. -/
theorem components_equivalent_of_no_calibrator {A B : Type*}
    (P : Accessibility X) (represent₁ : A → X) (represent₂ : B → X)
    (hcompare : ∀ a b : A, P.relation (represent₁ a) (represent₁ b) ∨
      P.relation (represent₁ b) (represent₁ a))
    (hno : ¬ ∃ a b : A, ∃ c d : B,
      IsEntropyCalibrator P (represent₁ a) (represent₁ b) (represent₂ c) (represent₂ d))
    (a b : A) (c d : B)
    (hsum : P.relation (represent₁ a + represent₂ c) (represent₁ b + represent₂ d) ∧
      P.relation (represent₁ b + represent₂ d) (represent₁ a + represent₂ c)) :
    (P.relation (represent₁ a) (represent₁ b) ∧ P.relation (represent₁ b) (represent₁ a)) ∧
      (P.relation (represent₂ c) (represent₂ d) ∧ P.relation (represent₂ d) (represent₂ c)) := by
  have hfirst : P.relation (represent₁ a) (represent₁ b) ∧
      P.relation (represent₁ b) (represent₁ a) := by
    rcases hcompare a b with hab | hba
    · by_contra h
      have hstrict : P.relation (represent₁ a) (represent₁ b) ∧
          ¬ P.relation (represent₁ b) (represent₁ a) := ⟨hab, fun hba => h ⟨hab, hba⟩⟩
      exact hno ⟨a, b, d, c, hstrict, P.strict_reference_of_crossed hstrict hsum, hsum⟩
    · by_contra h
      have hstrict : P.relation (represent₁ b) (represent₁ a) ∧
          ¬ P.relation (represent₁ a) (represent₁ b) := ⟨hba, fun hab => h ⟨hab, hba⟩⟩
      exact hno ⟨b, a, c, d, hstrict, P.strict_reference_of_crossed hstrict hsum.symm, hsum.symm⟩
  refine ⟨hfirst, ?_⟩
  apply (P.completedState_eq_iff _ _).mp
  have htotal := (P.completedState_eq_iff _ _).mpr hsum
  have hcomponent := (P.completedState_eq_iff _ _).mpr hfirst
  simp only [map_add, hcomponent] at htotal
  exact add_left_cancel htotal

end Accessibility

namespace ThermalJoin

variable {W₁ W₂ : Type*} {Γ₁ : Set (ℝ × W₁)} {Γ₂ : Set (ℝ × W₂)}
variable {represent₁ : Γ₁ → X} {represent₂ : Γ₂ → X}
variable (J : ThermalJoin P Γ₁ Γ₂ represent₁ represent₂)

/-- Equilibrium products remain equivalent when their joined states move
along one adiabat; equality of the joined coordinates is unnecessary. -/
theorem equivalent_splits_of_equivalent_joined (a b : Γ₁) (c d : Γ₂)
    (hjoined : P.relation (J.represent (joinedState a c)) (J.represent (joinedState b d)) ∧
      P.relation (J.represent (joinedState b d)) (J.represent (joinedState a c)))
    (hac : J.Equilibrium a c) (hbd : J.Equilibrium b d) :
    P.relation (represent₁ a + represent₂ c) (represent₁ b + represent₂ d) ∧
      P.relation (represent₁ b + represent₂ d) (represent₁ a + represent₂ c) :=
  ⟨P.trans (J.contact a c) (P.trans hjoined.1 hbd),
    P.trans (J.contact b d) (P.trans hjoined.2 hac)⟩

end ThermalJoin

namespace SimpleSystem

variable {n : ℕ}

/-- Adiabatically equivalent states with equal work coordinates coincide,
without choosing an orientation for the energy coordinate. -/
theorem eq_of_equivalent_of_same_work (S : SimpleSystem P n) (x y : S.domain)
    (heq : P.relation (S.represent x) (S.represent y) ∧
      P.relation (S.represent y) (S.represent x)) (hwork : x.val.2 = y.val.2) : x = y := by
  have hy := (S.mem_boundary_iff_equivalent x.property y.property).mpr heq
  apply Subtype.ext
  obtain hp | hp := S.positive_or_reflected_positive
  · exact S.boundary_eq_of_same_work hp x.property (S.mem_boundary_self x.property) hy hwork
  · apply (energyReflection n).injective
    have hx' : energyReflection n x.val ∈ S.reflected.domain := by simp
    have hy' : energyReflection n y.val ∈ S.reflected.boundary (energyReflection n x.val) := by
      rw [S.reflected_boundary]
      simpa only [mem_preimage, energyReflection_involutive] using hy
    exact S.reflected.boundary_eq_of_same_work hp hx' (S.reflected.mem_boundary_self hx') hy' hwork

/-- The boundary projection is open for either orientation of energy. -/
theorem boundaryDomain_isOpen_any_orientation (S : SimpleSystem P n)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) : IsOpen (S.boundaryDomain x) := by
  obtain hp | hp := S.positive_or_reflected_positive
  · exact S.boundaryDomain_isOpen hp hx
  · have hx' : energyReflection n x ∈ S.reflected.domain := by simpa using hx
    have hdomain : S.reflected.boundaryDomain (energyReflection n x) = S.boundaryDomain x := by
      ext v
      constructor
      · rintro ⟨y, hy, hyv⟩
        refine ⟨energyReflection n y, ?_, hyv⟩
        simpa only [S.reflected_boundary, mem_preimage, energyReflection_involutive] using hy
      · rintro ⟨y, hy, hyv⟩
        refine ⟨energyReflection n y, ?_, hyv⟩
        simpa only [S.reflected_boundary, mem_preimage, energyReflection_involutive] using hy
    rw [← hdomain]
    exact S.reflected.boundaryDomain_isOpen hp hx'

end SimpleSystem

namespace SimpleThermalJoin

variable {n m : ℕ} {S : SimpleSystem P n} {T : SimpleSystem P m}
variable (J : SimpleThermalJoin S T)

/-- In the absence of calibrators, both equilibrium split components are
adiabatically fixed along each joined adiabat. -/
theorem split_components_equivalent_of_no_calibrator
    (hno : ¬ ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d))
    (a b : S.domain) (c d : T.domain)
    (hjoined : P.relation (J.thermalJoin.represent (joinedState a c))
        (J.thermalJoin.represent (joinedState b d)) ∧
      P.relation (J.thermalJoin.represent (joinedState b d))
        (J.thermalJoin.represent (joinedState a c)))
    (hac : J.thermalJoin.Equilibrium a c) (hbd : J.thermalJoin.Equilibrium b d) :
    (P.relation (S.represent a) (S.represent b) ∧ P.relation (S.represent b) (S.represent a)) ∧
      (P.relation (T.represent c) (T.represent d) ∧ P.relation (T.represent d) (T.represent c)) :=
  P.components_equivalent_of_no_calibrator (fun x : S.domain => S.represent x)
    (fun y : T.domain => T.represent y)
    S.comparison hno a b c d
    (J.thermalJoin.equivalent_splits_of_equivalent_joined a b c d hjoined hac hbd)

/-- The first component is fixed along a joined adiabat whenever its work
coordinate is fixed. This follows from absence of calibrators, without a
continuity or uniqueness assumption on the chosen thermal splitting. -/
theorem split_left_eq_of_same_work_of_no_calibrator
    (hno : ¬ ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d))
    (a b : S.domain) (c d : T.domain)
    (hjoined : P.relation (J.thermalJoin.represent (joinedState a c))
        (J.thermalJoin.represent (joinedState b d)) ∧
      P.relation (J.thermalJoin.represent (joinedState b d))
        (J.thermalJoin.represent (joinedState a c)))
    (hac : J.thermalJoin.Equilibrium a c) (hbd : J.thermalJoin.Equilibrium b d)
    (hwork : a.val.2 = b.val.2) : a = b :=
  S.eq_of_equivalent_of_same_work a b
    (J.split_components_equivalent_of_no_calibrator hno a b c d hjoined hac hbd).1 hwork

theorem split_right_eq_of_same_work_of_no_calibrator
    (hno : ¬ ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d))
    (a b : S.domain) (c d : T.domain)
    (hjoined : P.relation (J.thermalJoin.represent (joinedState a c))
        (J.thermalJoin.represent (joinedState b d)) ∧
      P.relation (J.thermalJoin.represent (joinedState b d))
        (J.thermalJoin.represent (joinedState a c)))
    (hac : J.thermalJoin.Equilibrium a c) (hbd : J.thermalJoin.Equilibrium b d)
    (hwork : c.val.2 = d.val.2) : c = d :=
  T.eq_of_equivalent_of_same_work c d
    (J.split_components_equivalent_of_no_calibrator hno a b c d hjoined hac hbd).2 hwork

end SimpleThermalJoin

/-- Work-coordinate concatenation as a homeomorphism, used to express a joined
adiabat over a product of the two work spaces. -/
def workPairCoordinates (n m : ℕ) :
    (WorkCoordinates n × WorkCoordinates m) ≃ₜ WorkCoordinates (n + m) where
  toFun v := Fin.append v.1 v.2
  invFun v := (fun i => v (Fin.castAdd m i), fun j => v (Fin.natAdd n j))
  left_inv v := by rcases v with ⟨v, w⟩; simp
  right_inv v := Fin.append_castAdd_natAdd
  continuous_toFun := by
    apply continuous_pi
    intro i
    induction i using Fin.addCases with
    | left i => simpa only [Fin.append_left, Function.comp_def] using
        (continuous_apply i).comp continuous_fst
    | right i => simpa only [Fin.append_right, Function.comp_def] using
        (continuous_apply i).comp continuous_snd
  continuous_invFun :=
    (continuous_pi (fun i => continuous_apply (Fin.castAdd m i))).prodMk
      (continuous_pi (fun j => continuous_apply (Fin.natAdd n j)))

namespace ThermalFamily

variable (F : ThermalFamily P)

/-- Under absence of calibrators, any joined adiabat parameterized over an
open connected work domain is one thermal class. Component coherence is
derived from the thermal axioms, not assumed under adiabatic equivalence. -/
theorem thermal_on_joined_graph_of_no_calibrator
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (hno : ¬ ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d))
    {D : Set (WorkCoordinates n × WorkCoordinates m)}
    (hopen : IsOpen D) (hconnected : IsPreconnected D)
    (z : D → (F.join S T hS hT).system.domain)
    (hwork : ∀ u, (z u).val.2 = Fin.append u.val.1 u.val.2)
    (hadiabat : ∀ u v, P.relation ((F.join S T hS hT).system.represent (z u))
        ((F.join S T hS hT).system.represent (z v)) ∧
      P.relation ((F.join S T hS hT).system.represent (z v))
        ((F.join S T hS hT).system.represent (z u))) (u v : D) :
    F.thermal ((F.join S T hS hT).system.represent (z u))
      ((F.join S T hS hT).system.represent (z v)) := by
  classical
  let J := F.join S T hS hT
  choose a b hcoord hsplit hleft hright using fun w : D => F.exists_coherent_split S T hS hT (z w)
  have hstates w := F.isState_represent J.system (F.join_admitted S T hS hT) (z w)
  have hworksplit w : Fin.append (a w).val.2 (b w).val.2 = Fin.append w.val.1 w.val.2 :=
    (congrArg (fun q : J.system.domain => q.val.2) (hcoord w)).trans (hwork w)
  have ha w : (a w).val.2 = w.val.1 := by
    funext i
    simpa only [Fin.append_left] using congrFun (hworksplit w) (Fin.castAdd m i)
  have hb w : (b w).val.2 = w.val.2 := by
    funext i
    simpa only [Fin.append_right] using congrFun (hworksplit w) (Fin.natAdd n i)
  have heq w : J.thermalJoin.Equilibrium (a w) (b w) := by
    have h := hsplit w
    rw [← hcoord w, J.represent_point] at h
    exact h
  have hj w w' : P.relation (J.thermalJoin.represent (joinedState (a w) (b w)))
        (J.thermalJoin.represent (joinedState (a w') (b w'))) ∧
      P.relation (J.thermalJoin.represent (joinedState (a w') (b w')))
        (J.thermalJoin.represent (joinedState (a w) (b w))) := by
    rw [← J.represent_point, ← J.represent_point, hcoord w, hcoord w']
    exact hadiabat w w'
  apply relation_of_fiberwise_on_open_preconnected hopen hconnected
    (fun w w' => F.thermal (J.system.represent (z w)) (J.system.represent (z w')))
    ⟨fun w => F.refl (hstates w),
      fun {w w'} h => F.symm (hstates w) (hstates w') h,
      fun {w w' w''} h h' => F.trans (hstates w) (hstates w') (hstates w'') h h'⟩ ?_ ?_ u v
  · intro w w' hww'
    have hab : a w = a w' := J.split_left_eq_of_same_work_of_no_calibrator hno
      (a w) (a w') (b w) (b w') (hj w w') (heq w) (heq w')
      ((ha w).trans (hww'.trans (ha w').symm))
    apply F.trans (hstates w) (F.isState_represent S hS (a w)) (hstates w') (hleft w)
    simpa only [hab] using F.symm (hstates w') (F.isState_represent S hS (a w')) (hleft w')
  · intro w w' hww'
    have hab : b w = b w' := J.split_right_eq_of_same_work_of_no_calibrator hno
      (a w) (a w') (b w) (b w') (hj w w') (heq w) (heq w')
      ((hb w).trans (hww'.trans (hb w').symm))
    apply F.trans (hstates w) (F.isState_represent T hT (b w)) (hstates w') (hright w)
    simpa only [hab] using F.symm (hstates w') (F.isState_represent T hT (b w')) (hright w')

/-- If two simple systems had no entropy calibrator, every adiabat of their
thermal join would be a single thermal class. The graph domain is open and
connected by simple-system geometry; no continuity of a selected splitting is
required. This conclusion does not rule out a universal joined isotherm. -/
theorem joined_boundary_thermal_of_no_calibrator
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (hno : ¬ ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d))
    (anchor x y : (F.join S T hS hT).system.domain)
    (hx : x.val ∈ (F.join S T hS hT).system.boundary anchor.val)
    (hy : y.val ∈ (F.join S T hS hT).system.boundary anchor.val) :
    F.thermal ((F.join S T hS hT).system.represent x)
      ((F.join S T hS hT).system.represent y) := by
  classical
  let J := F.join S T hS hT
  let H := workPairCoordinates n m
  let D := H ⁻¹' J.system.boundaryDomain anchor.val
  have hopen : IsOpen D :=
    (J.system.boundaryDomain_isOpen_any_orientation anchor.property).preimage H.continuous
  have hconnected : IsPreconnected D := H.isPreconnected_preimage.mpr
    (J.system.boundaryDomain_isPathConnected anchor.property).isConnected.isPreconnected
  let z : D → J.system.domain := fun v =>
    ⟨(J.system.boundaryEnergy anchor.val (H v.val), H v.val),
      (J.system.boundaryEnergy_mem v.property).1⟩
  have hz (w : D) : (z w).val ∈ J.system.boundary anchor.val :=
    J.system.boundaryEnergy_mem w.property
  have heq (w : D) :=
    (J.system.mem_boundary_iff_equivalent anchor.property (z w).property).mp (hz w)
  have hadiabat (u v : D) : P.relation (J.system.represent (z u))
      (J.system.represent (z v)) ∧ P.relation (J.system.represent (z v))
        (J.system.represent (z u)) :=
    ⟨P.trans (heq u).2 (heq v).1, P.trans (heq v).2 (heq u).1⟩
  have hwork (w : D) : (z w).val.2 = Fin.append w.val.1 w.val.2 := rfl
  have hrep (p : J.system.domain) (hp : p.val ∈ J.system.boundary anchor.val) :
      ∃ w : D, z w = p := by
    have hmem : H.symm p.val.2 ∈ D := by
      change H (H.symm p.val.2) ∈ J.system.boundaryDomain anchor.val
      rw [H.apply_symm_apply]
      exact ⟨p.val, hp, rfl⟩
    let w : D := ⟨H.symm p.val.2, hmem⟩
    refine ⟨w, J.system.eq_of_equivalent_of_same_work (z w) p ?_ ?_⟩
    · have hp' := (J.system.mem_boundary_iff_equivalent anchor.property p.property).mp hp
      exact ⟨P.trans (heq w).2 hp'.1, P.trans hp'.2 (heq w).1⟩
    · exact H.apply_symm_apply p.val.2
  obtain ⟨u, hu⟩ := hrep x hx
  obtain ⟨v, hv⟩ := hrep y hy
  simpa only [hu, hv] using F.thermal_on_joined_graph_of_no_calibrator
    S T hS hT hno hopen hconnected z hwork hadiabat u v

/-- The exact conclusion of the unique-splitting branch: absence of a calibrator
forces the thermal join to be one thermal class. The universal-isotherm case
is retained explicitly instead of being excluded merely by split uniqueness. -/
theorem joined_all_thermal_of_no_calibrator
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (hno : ¬ ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d))
    (x y : (F.join S T hS hT).system.domain) :
    F.thermal ((F.join S T hS hT).system.represent x)
      ((F.join S T hS hT).system.represent y) := by
  apply F.all_thermal_of_equivalent_thermal (F.join S T hS hT).system
    (F.join_admitted S T hS hT) ?_ x y
  intro a b hab
  exact F.joined_boundary_thermal_of_no_calibrator S T hS hT hno a a b
    ((F.join S T hS hT).system.mem_boundary_self a.property)
    (((F.join S T hS hT).system.mem_boundary_iff_equivalent a.property b.property).mpr hab)

/-- A non-universal thermal join already supplies a calibrator, using only the
simple-system and thermal axioms. -/
theorem exists_calibrator_of_joined_not_thermal
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (x y : (F.join S T hS hT).system.domain)
    (hxy : ¬ F.thermal ((F.join S T hS hT).system.represent x)
      ((F.join S T hS hT).system.represent y)) :
    ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d) := by
  by_contra hno
  exact hxy (F.joined_all_thermal_of_no_calibrator S T hS hT hno x y)

end ThermalFamily

end Physical

end ProjectAInos.Thermodynamics
