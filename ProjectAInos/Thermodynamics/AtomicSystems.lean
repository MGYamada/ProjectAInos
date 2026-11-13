module

public import ProjectAInos.Thermodynamics.ReactionCalibration
public import ProjectAInos.Thermodynamics.HasCalibratorsOfAxioms

/-!
# Atomic simple systems from coordinate domains

The atomic state types are fixed coordinate-domain subtypes, chosen before the
raw composite type and its accessibility relation. This avoids a recursive
definition in which a simple system's domain would depend on its own atom type.

An admitted simple system is matched to these data by equality of its domain
and agreement of its representation on that domain. Its chart, physical-state
composition label, and nonemptiness obligations then follow. The geometric and thermal axioms remain
properties of the supplied simple systems and family; no comparison axiom is
introduced by this interface.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

/-- Coordinate domains specifying the atomic systems before constructing raw
composites or an accessibility relation. Openness and physical axioms belong
to the subsequently supplied `SimpleSystem`, not to this data container. -/
structure AtomicDomains (Γ : Type*) where
  dimension : Γ → ℕ
  domain : ∀ g, Set (SimpleCoordinates (dimension g))

namespace AtomicDomains

variable {Γ : Type*} (D : AtomicDomains Γ)

/-- An atomic state is an actual point in its fixed coordinate domain. -/
abbrev State (g : Γ) : Type := D.domain g

/-- Finite composition and nonnegative scaling of the coordinate atoms,
quotiented only by the structural composite laws. -/
abbrev Raw := CompositeState (Σ g, D.State g)

/-- The raw atom representing a point of one fixed simple-system domain. -/
def atom (g : Γ) (x : D.State g) : D.Raw := CompositeState.mk (.atom ⟨g, x⟩)

/-- Ambient representation of a coordinate-domain atom. Outside the physical
domain its value is fixed to zero solely to obtain an ordinary function. -/
noncomputable def represent (g : Γ) (x : SimpleCoordinates (D.dimension g)) : D.Raw := by
  classical
  exact if hx : x ∈ D.domain g then D.atom g ⟨x, hx⟩ else 0

@[simp] theorem represent_of_mem (g : Γ) {x : SimpleCoordinates (D.dimension g)}
    (hx : x ∈ D.domain g) : D.represent g x = D.atom g ⟨x, hx⟩ := by
  simp [represent, hx]

@[simp] theorem represent_state (g : Γ) (x : D.State g) :
    D.represent g x.val = D.atom g x := D.represent_of_mem g x.property

theorem represent_of_not_mem (g : Γ) {x : SimpleCoordinates (D.dimension g)}
    (hx : x ∉ D.domain g) : D.represent g x = 0 := by
  simp [represent, hx]

/-- Canonical extensive composition label, counting the amount of each simple
system independently of its thermodynamic coordinates. -/
noncomputable def label : D.Raw →+ (Γ →₀ ℝ≥0) := Nonreactive.compositionLabel D.State

@[simp] theorem label_atom (g : Γ) (x : D.State g) :
    D.label (D.atom g x) = Finsupp.single g 1 := rfl

@[simp] theorem label_represent (g : Γ) {x : SimpleCoordinates (D.dimension g)}
    (hx : x ∈ D.domain g) : D.label (D.represent g x) = Finsupp.single g 1 := by
  rw [D.represent_of_mem g hx, D.label_atom]

@[simp] theorem label_scale (r : ℝ≥0) (x : D.Raw) :
    D.label (r • x) = r • D.label x := Nonreactive.compositionLabel_scale D.State r x

theorem state_nonempty {g : Γ} (h : (D.domain g).Nonempty) : Nonempty (D.State g) :=
  h.to_subtype

theorem label_surjective (hnonempty : ∀ g, (D.domain g).Nonempty) :
    Function.Surjective D.label :=
  Nonreactive.compositionLabel_surjective D.State (fun g => D.state_nonempty (hnonempty g))

variable {P : Accessibility D.Raw}

/-- Domain equality determines the entire atomic chart; users do not supply a
separate map or surjectivity premise. -/
def chart (g : Γ) (S : SimpleSystem P (D.dimension g))
    (hdomain : S.domain = D.domain g) : D.State g ≃ S.domain :=
  Set.equivOfEq hdomain.symm

@[simp] theorem chart_val (g : Γ) (S : SimpleSystem P (D.dimension g))
    (hdomain : S.domain = D.domain g) (x : D.State g) :
    (D.chart g S hdomain x).val = x.val := rfl

theorem chart_represent (g : Γ) (S : SimpleSystem P (D.dimension g))
    (hdomain : S.domain = D.domain g) (hrepresent : Set.EqOn S.represent (D.represent g) (D.domain g))
    (x : D.State g) :
    S.represent (D.chart g S hdomain x) = CompositeState.mk (.atom ⟨g, x⟩) := by
  rw [D.chart_val, hrepresent x.property, D.represent_state]
  rfl

/-- Every coordinate state of the simple system, not only a selected chart
image, has precisely one unit of its specified composition label. -/
theorem simpleSystem_label (g : Γ) (S : SimpleSystem P (D.dimension g))
    (hdomain : S.domain = D.domain g) (hrepresent : Set.EqOn S.represent (D.represent g) (D.domain g))
    (x : S.domain) : D.label (S.represent x) = Finsupp.single g 1 := by
  have hx : x.val ∈ D.domain g := hdomain ▸ x.property
  rw [hrepresent hx]
  exact D.label_represent g hx

theorem simpleSystem_nonempty (g : Γ) (S : SimpleSystem P (D.dimension g))
    (hdomain : S.domain = D.domain g) (hnonempty : (D.domain g).Nonempty) :
    S.domain.Nonempty := hdomain.symm ▸ hnonempty

/-- A concrete coordinate-domain presentation supplies all charts and
nonemptiness bookkeeping for the calibrated equal-composition entropy theorem. -/
theorem exists_calibrated_entropy (F : ThermalFamily P)
    (S : ∀ g, SimpleSystem P (D.dimension g)) (hS : ∀ g, F.admitted (S g))
    (hdomain : ∀ g, (S g).domain = D.domain g)
    (hrepresent : ∀ g, Set.EqOn (S g).represent (D.represent g) (D.domain g))
    (hnonempty : ∀ g, (D.domain g).Nonempty) :
    ∃ entropy : D.Raw →+ ℝ,
      CalibratedEntropyPrinciple D.label P.relation entropy :=
  F.exists_calibrated_entropy F.hasCalibrators_of_axioms D.dimension S hS
    (fun g => D.simpleSystem_nonempty g (S g) (hdomain g) (hnonempty g))
    (fun g => D.chart g (S g) (hdomain g))
    (fun g => D.chart_represent g (S g) (hdomain g) (hrepresent g))

/-- The reacting entropy theorem for canonical coordinate atoms. The only
additional physical reaction premise is absence of sinks for actual label
transitions; no manual chart or label law is required. -/
theorem exists_weak_entropy (F : ThermalFamily P)
    (S : ∀ g, SimpleSystem P (D.dimension g)) (hS : ∀ g, F.admitted (S g))
    (hdomain : ∀ g, (S g).domain = D.domain g)
    (hrepresent : ∀ g, Set.EqOn (S g).represent (D.represent g) (D.domain g))
    (hnonempty : ∀ g, (D.domain g).Nonempty)
    (hM : Reactions.RawNoSinks D.label P.relation) :
    ∃ (entropy totalEntropy : D.Raw →+ ℝ) (B : (Γ →₀ ℝ≥0) →ₗ[ℝ≥0] ℝ),
      WeakEntropyPrinciple D.label P.relation entropy totalEntropy B :=
  F.exists_weak_entropy_of_calibrators F.hasCalibrators_of_axioms D.dimension S hS
    (fun g => D.simpleSystem_nonempty g (S g) (hdomain g) (hnonempty g))
    (fun g => D.state_nonempty (hnonempty g))
    (fun g => D.chart g (S g) (hdomain g))
    (fun g => D.chart_represent g (S g) (hdomain g) (hrepresent g)) hM

/-- The canonical presentation satisfies ECH when accessibility preserves
labels. Physical comparison and common realization are already proved;
`exchangeComparison_nonreactive` discharges conservation for the generated
nonreactive relation. -/
theorem exchangeComparison (F : ThermalFamily P)
    (S : ∀ g, SimpleSystem P (D.dimension g)) (hS : ∀ g, F.admitted (S g))
    (hdomain : ∀ g, (S g).domain = D.domain g)
    (hrepresent : ∀ g, Set.EqOn (S g).represent (D.represent g) (D.domain g))
    (hpreserved : ∀ {x y}, P.relation x y → D.label x = D.label y) :
    ExchangeComparison P.StateSpace :=
  F.exchangeComparison_of_calibrators F.hasCalibrators_of_axioms D.dimension S hS
    (fun g => D.chart g (S g) (hdomain g))
    (fun g => D.chart_represent g (S g) (hdomain g) (hrepresent g)) hpreserved

/-- Composite generators may include mixing and thermal contact. Conservation
is required only for generators; it is proved for their A1–A6 closure. Physical
comparison follows from the thermal family, without assuming CH or ECH. -/
theorem exchangeComparison_nonreactive
    (elementary : D.Raw → D.Raw → Prop)
    (hbasic : ∀ {x y}, elementary x y → D.label x = D.label y)
    (F : ThermalFamily (Nonreactive.generatedAccessibility elementary CompositeState.zero_scale))
    (S : ∀ g, SimpleSystem
      (Nonreactive.generatedAccessibility elementary CompositeState.zero_scale) (D.dimension g))
    (hS : ∀ g, F.admitted (S g))
    (hdomain : ∀ g, (S g).domain = D.domain g)
    (hrepresent : ∀ g, Set.EqOn (S g).represent (D.represent g) (D.domain g)) :
    ExchangeComparison (Nonreactive.generatedAccessibility elementary CompositeState.zero_scale).StateSpace :=
  D.exchangeComparison F S hS hdomain hrepresent
    (Nonreactive.Generated.label_eq D.label D.label_scale hbasic)

/-- The restricted atomic-only specialization. Its premises do not provide an
inhabited physical model: atomic-only generators obstruct convex mixing on a
nonempty open primitive domain (issue #27). Use composite generators above. -/
theorem exchangeComparison_atomicOnly
    (elementary : ∀ g, D.State g → D.State g → Prop)
    (F : ThermalFamily (Nonreactive.accessibility D.State elementary))
    (S : ∀ g, SimpleSystem (Nonreactive.accessibility D.State elementary) (D.dimension g))
    (hS : ∀ g, F.admitted (S g))
    (hdomain : ∀ g, (S g).domain = D.domain g)
    (hrepresent : ∀ g, Set.EqOn (S g).represent (D.represent g) (D.domain g)) :
    ExchangeComparison (Nonreactive.accessibility D.State elementary).StateSpace :=
  D.exchangeComparison F S hS hdomain hrepresent
    (Nonreactive.accessibility_label_eq D.State elementary)

end AtomicDomains

end ProjectAInos.Thermodynamics.Physical
