module

public import ProjectAInos.Thermodynamics.AtomicSystems
public import Mathlib.Tactic

/-!
# Canonical atoms with heating and reversible mixing

This model repairs the atomic-only obstruction in issue #27. Raw states remain
formal composites; energy and amount are observables, not raw identifications.
-/
@[expose] public section
noncomputable section
open scoped NNReal
namespace ProjectAInos.Thermodynamics.Physical.AtomicReservoir
open Nonreactive

def domains : AtomicDomains Unit where
  dimension _ := 0
  domain _ := {z | 0 < z.1}

abbrev Raw := domains.Raw
abbrev Energy := {u : ℝ // 0 < u}
def atom (u : Energy) : Raw := domains.atom () ⟨(u.val, 0), u.property⟩
def amount : Raw →+ ℝ≥0 := CompositeState.label (fun _ => 1)
def energy : Raw →+ ℝ := CompositeState.label (fun a => a.2.val.1)

@[simp] theorem amount_atom (u : Energy) : amount (atom u) = 1 := rfl
@[simp] theorem energy_atom (u : Energy) : energy (atom u) = u.val := rfl
@[simp] theorem amount_scale (r : ℝ≥0) (x : Raw) : amount (r • x) = r * amount x :=
  CompositeState.label_scale _ r x
@[simp] theorem energy_scale (r : ℝ≥0) (x : Raw) : energy (r • x) = (r : ℝ) * energy x :=
  CompositeState.label_scale _ r x

theorem label_apply (x : Raw) (g : Unit) : domains.label x g = amount x := by
  induction x using Quotient.inductionOn with
  | h x =>
    induction x with
    | atom a =>
      cases g
      obtain ⟨g, a⟩ := a
      cases g
      change (Finsupp.single () (1 : ℝ≥0)) () = 1
      simp
    | empty => rfl
    | compose x y ihx ihy => exact congrArg₂ (· + ·) ihx ihy
    | scale r x ih => exact congrArg (r * ·) ih

def mean (r s : ℝ≥0) (hrs : 0 < r + s) (u v : Energy) : Energy :=
  ⟨((r : ℝ) * u.val + (s : ℝ) * v.val) / (r + s), by
    apply div_pos _ (NNReal.coe_pos.mpr hrs)
    by_cases hr : r = 0
    · simp only [hr, zero_add] at hrs
      simpa [hr] using mul_pos (NNReal.coe_pos.mpr hrs) v.property
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)) u.property)
        (mul_nonneg s.coe_nonneg v.property.le)⟩

/-- Heating, mixing, and reversible separation are actual generators. -/
inductive Step : Raw → Raw → Prop
  | heat (u v : Energy) (h : u.val ≤ v.val) : Step (atom u) (atom v)
  | mix (r s : ℝ≥0) (hrs : 0 < r + s) (u v : Energy) :
      Step (r • atom u + s • atom v) ((r + s) • atom (mean r s hrs u v))
  | separate (r s : ℝ≥0) (hrs : 0 < r + s) (u v : Energy) :
      Step ((r + s) • atom (mean r s hrs u v)) (r • atom u + s • atom v)

def accessibility : Accessibility Raw := generatedAccessibility Step CompositeState.zero_scale

theorem Step.amount_eq {x y : Raw} (h : Step x y) : amount x = amount y := by
  cases h <;> simp

theorem Step.label_eq {x y : Raw} (h : Step x y) : domains.label x = domains.label y := by
  apply Finsupp.ext
  intro g
  simpa only [label_apply] using h.amount_eq

theorem mean_energy (r s : ℝ≥0) (hrs : 0 < r + s) (u v : Energy) :
    energy ((r+s) • atom (mean r s hrs u v)) = energy (r • atom u + s • atom v) := by
  simp only [energy_scale, energy_atom, map_add, mean, NNReal.coe_add]
  exact mul_div_cancel₀ _ (ne_of_gt (NNReal.coe_pos.mpr hrs))

theorem Step.energy_le {x y : Raw} (h : Step x y) : energy x ≤ energy y := by
  cases h with
  | heat u v h => exact h
  | mix r s hrs u v => exact (mean_energy r s hrs u v).symm.le
  | separate r s hrs u v => exact (mean_energy r s hrs u v).le

theorem amount_eq {x y : Raw} (h : accessibility.relation x y) : amount x = amount y := by
  have hh := Generated.label_eq domains.label domains.label_scale Step.label_eq h
  simpa only [label_apply] using congrArg (fun f => f ()) hh

theorem energy_le {x y : Raw} (h : accessibility.relation x y) : energy x ≤ energy y :=
  Generated.eval_le energy (fun r x => energy_scale r x) Step.energy_le h

private def unitEnergy : Energy := ⟨1, by norm_num⟩

/-- Every finite composite equilibrates reversibly to a single weighted atom.
Zero amount is represented by zero times an arbitrary positive atom. -/
theorem normal_form (x : Raw) : ∃ u : Energy,
    accessibility.relation x (amount x • atom u) ∧
    accessibility.relation (amount x • atom u) x := by
  induction x using Quotient.inductionOn with
  | h x =>
    change ∃ u : Energy,
      accessibility.relation (CompositeState.mk x) (amount (CompositeState.mk x) • atom u) ∧
      accessibility.relation (amount (CompositeState.mk x) • atom u) (CompositeState.mk x)
    induction x with
    | atom a =>
      obtain ⟨g, z⟩ := a
      cases g
      let u : Energy := ⟨z.val.1, z.property⟩
      have hz : (⟨(), z⟩ : Σ g, domains.State g) = ⟨(), ⟨(u.val, 0), u.property⟩⟩ := by
        congr 1
        apply Subtype.ext
        change (z.val.1, z.val.2) = (z.val.1, 0)
        congr 1
        ext i
        exact Fin.elim0 i
      rw [hz]
      change ∃ v, accessibility.relation (atom u) ((1 : ℝ≥0) • atom v) ∧
        accessibility.relation ((1 : ℝ≥0) • atom v) (atom u)
      exact ⟨u, by simpa using accessibility.refl (atom u),
        by simpa using accessibility.refl (atom u)⟩
    | empty =>
      change ∃ u, accessibility.relation 0 ((0 : ℝ≥0) • atom u) ∧
        accessibility.relation ((0 : ℝ≥0) • atom u) 0
      refine ⟨unitEnergy, ?_, ?_⟩ <;> simpa using accessibility.refl (0 : Raw)
    | compose x y ihx ihy =>
      obtain ⟨u, hxu, hux⟩ := ihx
      obtain ⟨v, hyv, hvy⟩ := ihy
      let r := amount (CompositeState.mk x)
      let s := amount (CompositeState.mk y)
      change accessibility.relation _ (r • atom u) at hxu
      change accessibility.relation (r • atom u) _ at hux
      change accessibility.relation _ (s • atom v) at hyv
      change accessibility.relation (s • atom v) _ at hvy
      change ∃ u, accessibility.relation (CompositeState.mk x + CompositeState.mk y)
        ((r+s) • atom u) ∧ accessibility.relation ((r+s) • atom u)
        (CompositeState.mk x + CompositeState.mk y)
      by_cases hrs : 0 < r + s
      · exact ⟨mean r s hrs u v,
          accessibility.trans (accessibility.add_mono hxu hyv) (.basic (.mix r s hrs u v)),
          accessibility.trans (.basic (.separate r s hrs u v)) (accessibility.add_mono hux hvy)⟩
      · have hr : r = 0 := by
          exact le_antisymm ((le_add_right le_rfl : r ≤ r+s).trans (le_of_not_gt hrs)) zero_le
        have hs : s = 0 := by
          exact le_antisymm ((le_add_left le_rfl : s ≤ r+s).trans (le_of_not_gt hrs)) zero_le
        refine ⟨unitEnergy, ?_, ?_⟩
        · simpa only [hr, hs, zero_add, CompositeState.zero_scale] using accessibility.add_mono hxu hyv
        · simpa only [hr, hs, zero_add, CompositeState.zero_scale] using accessibility.add_mono hux hvy
    | scale r x ih =>
      obtain ⟨u, hxu, hux⟩ := ih
      refine ⟨u, ?_, ?_⟩
      · simpa only [show CompositeState.mk (.scale r x) = r • CompositeState.mk x from rfl,
          amount_scale, mul_smul] using accessibility.scale_mono r hxu
      · simpa only [show CompositeState.mk (.scale r x) = r • CompositeState.mk x from rfl,
          amount_scale, mul_smul] using accessibility.scale_mono r hux

/-- A derived characterization, not a comparison premise on generators. -/
theorem relation_iff (x y : Raw) : accessibility.relation x y ↔
    amount x = amount y ∧ energy x ≤ energy y := by
  refine ⟨fun h => ⟨amount_eq h, energy_le h⟩, ?_⟩
  rintro ⟨hm, he⟩
  obtain ⟨u, hxu, hux⟩ := normal_form x
  obtain ⟨v, hyv, hvy⟩ := normal_form y
  have hu : energy x = (amount x : ℝ) * u.val := by
    simpa using le_antisymm (energy_le hxu) (energy_le hux)
  have hv : energy y = (amount y : ℝ) * v.val := by
    simpa using le_antisymm (energy_le hyv) (energy_le hvy)
  apply accessibility.trans hxu
  apply accessibility.trans _ hvy
  rw [← hm]
  by_cases hr : amount x = 0
  · simp only [hr, CompositeState.zero_scale]
    exact accessibility.refl 0
  · have huv : u.val ≤ v.val := by
      rw [hu, hv, ← hm] at he
      exact (mul_le_mul_iff_right₀ (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr))).mp he
    exact accessibility.scale_mono _ (.basic (.heat u v huv))

end ProjectAInos.Thermodynamics.Physical.AtomicReservoir
