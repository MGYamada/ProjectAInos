module

public import ProjectAInos.Thermodynamics.ThermalSlopes
public import ProjectAInos.Thermodynamics.SimpleComparison
public import ProjectAInos.Thermodynamics.ThermalClassOrder

/-!
# Location of isotherms

LY Theorem 4.6 follows from the supporting-slope characterization of thermal
equilibrium, the zeroth law, and transversality. If every adiabat is contained
in a thermal class, the interval classes of supporting slopes factor through
entropy. Their ordering along vertical lines globalizes on the entropy range;
T4 makes the class label locally constant. Connectedness then leaves one class.

Both energy orientations are covered. The negative convention uses the scalar
coordinate `-S`; it does not require the thermal family to contain a reflected
simple system. Empty equilibrium domains are included in the first alternative.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

namespace SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- Reference entropy is strictly increasing on each energy fiber in the
positive convention. -/
theorem referenceEntropy_energy_strictMono (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀))
    (hpositive : ∀ z ∈ S.domain, S.Positive z) (v : WorkCoordinates n) :
    StrictMonoOn (fun u => S.referenceEntropy hlocal x₀ x₁ hstrict (u, v))
      (S.energyDomain v) := by
  intro a ha b hb hab
  apply lt_of_not_ge
  intro hba
  have hr := (S.referenceEntropy_relation_iff hlocal x₀ x₁ hstrict hb ha).mpr hba
  have henergy := (S.accessible_iff_signed_energy_le one_ne_zero hpositive hb ha rfl).mp hr
  simp only [one_mul, not_le.mpr hab] at henergy

/-- In the negative convention the negative reference entropy is strictly
increasing along the original energy coordinate. -/
theorem neg_referenceEntropy_energy_strictMono (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀))
    (hnegative : ∀ z ∈ S.domain, S.Negative z) (v : WorkCoordinates n) :
    StrictMonoOn (fun u => -S.referenceEntropy hlocal x₀ x₁ hstrict (u, v))
      (S.energyDomain v) := by
  intro a ha b hb hab
  apply neg_lt_neg
  apply lt_of_not_ge
  intro hab'
  have hr := (S.referenceEntropy_relation_iff hlocal x₀ x₁ hstrict ha hb).mpr hab'
  have henergy := (S.accessible_iff_signed_energy_le (by norm_num : (-1 : ℝ) ≠ 0)
    hnegative ha hb rfl).mp hr
  simp only [neg_one_mul] at henergy
  linarith

end SimpleSystem

namespace ThermalFamily

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} (F : ThermalFamily P) {n : ℕ}

/-- If each adiabat is contained in a thermal class, T3 and T4 force the entire
simple system to be one thermal class. No energy-sign premise is needed. -/
theorem all_thermal_of_equivalent_thermal (S : SimpleSystem P n) (hS : F.admitted S)
    (hadiabat : ∀ x y : S.domain,
      P.relation (S.represent x) (S.represent y) ∧
        P.relation (S.represent y) (S.represent x) →
      F.thermal (S.represent x) (S.represent y)) (x y : S.domain) :
    F.thermal (S.represent x) (S.represent y) := by
  classical
  obtain ⟨z, hz, hxz⟩ := S.irreversible x x.property
  let z' : S.domain := ⟨z, hz⟩
  let hlocal := F.localMixtureIntervals_of_axioms S hS
  let s := S.referenceEntropy hlocal x z' hxz
  have hs := S.referenceEntropy_concave hlocal x z' hxz
  have hcont := S.referenceEntropy_continuousOn hlocal x z' hxz
  let R : S.domain → S.domain → Prop := fun a b => F.thermal (S.represent a) (S.represent b)
  let lower : S.domain → ℝ := fun a => rightSlope (SimpleSystem.energyEntropy s a.val.2) a.val.1
  let upper : S.domain → ℝ := fun a => leftSlope (SimpleSystem.energyEntropy s a.val.2) a.val.1
  have hrefl : ∀ a, R a a := fun a => F.refl (F.isState_represent S hS a)
  have hsymm : ∀ {a b}, R a b → R b a := fun {a b} h =>
    F.symm (F.isState_represent S hS a) (F.isState_represent S hS b) h
  have htrans : ∀ {a b c}, R a b → R b c → R a c := fun {a b c} hab hbc =>
    F.trans (F.isState_represent S hS a) (F.isState_represent S hS b)
      (F.isState_represent S hS c) hab hbc
  have hinter : ∀ a b, R a b ↔ (Icc (lower a) (upper a) ∩
      Icc (lower b) (upper b)).Nonempty := by
    intro a b
    rw [← S.entropySlopes_eq_Icc hs a, ← S.entropySlopes_eq_Icc hs b]
    exact F.thermal_iff_entropySlopes_inter S hS hlocal x z' hxz a b
  let q := intervalClassLabel R lower
  have hqmem (a : S.domain) : q a ∈ S.entropySlopes s a := by
    rw [S.entropySlopes_eq_Icc hs a]
    exact intervalClassLabel_mem hrefl hinter a
  have hqiff (a b : S.domain) : q a = q b ↔ R a b :=
    intervalClassLabel_eq_iff hrefl (fun {a b} => hsymm (a := a) (b := b))
      (fun {a b c} => htrans (a := a) (b := b) (c := c)) hinter a b
  have hqmono : ∀ a b : S.domain, a.val.2 = b.val.2 → a.val.1 ≤ b.val.1 →
      -q a ≤ -q b := by
    intro a b hv he
    rcases he.lt_or_eq with he | he
    · exact neg_le_neg (S.entropySlopes_antitone s hv he (hqmem a) (hqmem b))
    · have hab : a = b := Subtype.ext (Prod.ext he hv)
      simp only [hab, le_refl]
  have hqfiber : ∀ a b : S.domain, s a = s b → -q a = -q b := by
    intro a b hab
    apply congrArg Neg.neg
    apply (hqiff a b).mpr
    apply hadiabat a b
    exact ⟨(S.referenceEntropy_relation_iff hlocal x z' hxz a.property b.property).mpr hab.le,
      (S.referenceEntropy_relation_iff hlocal x z' hxz b.property a.property).mpr hab.ge⟩
  have hqtransverse : ∀ a : S.domain, ∃ b c : S.domain,
      s b < s a ∧ s a < s c ∧ -q b = -q c := by
    intro a
    obtain ⟨b, c, hbc, hba, hac⟩ := F.transversality S hS a
    refine ⟨b, c, ?_, ?_, congrArg Neg.neg ((hqiff b c).mpr hbc)⟩
    · apply lt_of_not_ge
      intro hab
      exact hba.2 ((S.referenceEntropy_relation_iff hlocal x z' hxz a.property b.property).mpr hab)
    · apply lt_of_not_ge
      intro hca
      exact hac.2 ((S.referenceEntropy_relation_iff hlocal x z' hxz c.property a.property).mpr hca)
  have heq : -q x = -q y := by
    rcases S.positive_or_negative x.property with hp | hn
    · exact constant_of_vertical_order_transverse S.isOpen_domain S.convex_domain hcont
        (S.referenceEntropy_energy_strictMono hlocal x z' hxz
          (S.positive_everywhere x.property hp)) (fun a => -q a) hqmono hqfiber hqtransverse x y
    · apply constant_of_vertical_order_transverse S.isOpen_domain S.convex_domain hcont.neg
        (S.neg_referenceEntropy_energy_strictMono hlocal x z' hxz
          (S.negative_everywhere x.property hn)) (fun a => -q a) hqmono
      · intro a b hab
        exact hqfiber a b (neg_injective hab)
      · intro a
        obtain ⟨b, c, hba, hac, hbc⟩ := hqtransverse a
        exact ⟨c, b, neg_lt_neg hac, neg_lt_neg hba, hbc.symm⟩
  exact (hqiff x y).mp (neg_injective heq)

/-- LY 4.6, in adiabatic-order form: either all states are thermally equivalent,
or two adiabatically equivalent states belong to different thermal classes. -/
theorem isotherm_dichotomy (S : SimpleSystem P n) (hS : F.admitted S) :
    (∀ x y : S.domain, F.thermal (S.represent x) (S.represent y)) ∨
      ∃ x y : S.domain,
        (P.relation (S.represent x) (S.represent y) ∧
          P.relation (S.represent y) (S.represent x)) ∧
        ¬ F.thermal (S.represent x) (S.represent y) := by
  classical
  by_cases h : ∀ x y : S.domain,
      P.relation (S.represent x) (S.represent y) ∧
        P.relation (S.represent y) (S.represent x) →
      F.thermal (S.represent x) (S.represent y)
  · exact Or.inl (F.all_thermal_of_equivalent_thermal S hS h)
  · push Not at h
    exact Or.inr h

/-- The boundary formulation of LY 4.6: the second alternative consists of two
non-equilibrium states on one relative forward-sector boundary. -/
theorem isotherm_boundary_dichotomy (S : SimpleSystem P n) (hS : F.admitted S) :
    (∀ x y : S.domain, F.thermal (S.represent x) (S.represent y)) ∨
      ∃ x y : S.domain, y.val ∈ S.boundary x.val ∧
        ¬ F.thermal (S.represent x) (S.represent y) := by
  rcases F.isotherm_dichotomy S hS with hall | ⟨x, y, hxy, hnot⟩
  · exact Or.inl hall
  · exact Or.inr ⟨x, y, (S.mem_boundary_iff_equivalent x.property y.property).mpr hxy, hnot⟩

end ThermalFamily

end ProjectAInos.Thermodynamics.Physical
