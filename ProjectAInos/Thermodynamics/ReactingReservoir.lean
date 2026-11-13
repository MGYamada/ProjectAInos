module

public import ProjectAInos.Thermodynamics.AtomicSystems
public import ProjectAInos.Thermodynamics.ReservoirModel

/-!
# Two interconvertible species of canonical reservoirs

The accessibility model conserves total amount and permits energy increases.
The composition labels remain distinct raw observables. Conversions at fixed
energy are reversible, and heating gives a strict process.
-/

@[expose] public section
noncomputable section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical.ReactingReservoir

def domains : AtomicDomains Bool where
  dimension _ := 0
  domain _ := Reservoir.domain 0

abbrev Raw := domains.Raw
abbrev Composition := Bool →₀ ℝ≥0
abbrev Energy := {u : ℝ // 0 < u}

def atom (g : Bool) (u : Energy) : Raw :=
  domains.atom g ⟨(u.val, 0), u.property⟩

def labelAmount (a : Composition) : ℝ≥0 := a false + a true

def amount (x : Raw) : ℝ≥0 := labelAmount (domains.label x)

def energy : Raw →+ ℝ := CompositeState.label (fun a => a.2.val.1)

@[simp] theorem label_atom (g : Bool) (u : Energy) :
    domains.label (atom g u) = Finsupp.single g 1 := rfl

@[simp] theorem amount_atom (g : Bool) (u : Energy) : amount (atom g u) = 1 := by
  cases g <;> simp [amount, labelAmount]

@[simp] theorem energy_atom (g : Bool) (u : Energy) : energy (atom g u) = u.val := rfl

@[simp] theorem amount_add (x y : Raw) : amount (x + y) = amount x + amount y := by
  simp only [amount, labelAmount, map_add, Finsupp.add_apply]
  ac_rfl

@[simp] theorem amount_scale (r : ℝ≥0) (x : Raw) : amount (r • x) = r * amount x := by
  simp [amount, labelAmount, mul_add, smul_eq_mul]

@[simp] theorem energy_scale (r : ℝ≥0) (x : Raw) :
    energy (r • x) = (r : ℝ) * energy x := CompositeState.label_scale _ r x

/-- Evaluate the raw state in the ordered energy/amount model. -/
def sector (x : Raw) : SectorState := (energy x, amount x)

@[simp] theorem sector_add (x y : Raw) : sector (x + y) = sector x + sector y := by
  change (energy (x + y), (amount (x + y) : ℝ)) =
    (energy x + energy y, (amount x : ℝ) + amount y)
  simp

@[simp] theorem sector_scale (r : ℝ≥0) (x : Raw) : sector (r • x) = r • sector x := by
  change (energy (r • x), (amount (r • x) : ℝ)) =
    ((r : ℝ) * energy x, (r : ℝ) * amount x)
  simp

def accessibility : Accessibility Raw where
  relation x y := Reservoir.accessibility.relation (sector x) (sector y)
  refl x := Reservoir.accessibility.refl (sector x)
  trans := Reservoir.accessibility.trans
  add_mono h k := by simpa only [sector_add] using Reservoir.accessibility.add_mono h k
  scale_mono r {_ _} h := by simpa only [sector_scale] using Reservoir.accessibility.scale_mono r h
  zero_scale := CompositeState.zero_scale
  split r s x := by
    simpa only [sector_add, sector_scale] using Reservoir.accessibility.split r s (sector x)
  stable x y z w ε hpos hlim h := Reservoir.accessibility.stable
    (sector x) (sector y) (sector z) (sector w) ε hpos hlim (by simpa only [sector_add, sector_scale] using h)

theorem relation_iff (x y : Raw) : accessibility.relation x y ↔
    amount x = amount y ∧ energy x ≤ energy y := by
  change ((amount x : ℝ) = amount y ∧ energy x ≤ energy y) ↔ _
  rw [NNReal.coe_inj]

def unitEnergy : Energy := ⟨1, by norm_num⟩

/-- A composition can be realized with unit energy per amount of each species. -/
def reference (a : Composition) : Raw :=
  a false • atom false unitEnergy + a true • atom true unitEnergy

@[simp] theorem label_reference (a : Composition) : domains.label (reference a) = a := by
  ext g
  cases g <;> simp [reference]

@[simp] theorem amount_reference (a : Composition) : amount (reference a) = labelAmount a := by
  change labelAmount (domains.label (reference a)) = _
  rw [label_reference]

@[simp] theorem energy_reference (a : Composition) :
    energy (reference a) = (labelAmount a : ℝ) := by
  simp [reference, labelAmount, unitEnergy]

theorem labelTransition_iff (a b : Composition) :
    Reactions.LabelTransition domains.label accessibility.relation a b ↔
      labelAmount a = labelAmount b := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have h := ((relation_iff x y).mp hxy).1
    simpa only [amount, hx, hy] using h
  · intro h
    refine ⟨reference a, reference b, label_reference a, label_reference b, ?_⟩
    exact (relation_iff _ _).mpr ⟨by simpa only [amount_reference] using h,
      by simp only [energy_reference, h, le_refl]⟩

theorem noSinks : Reactions.RawNoSinks domains.label accessibility.relation := by
  rintro a b ⟨z, h⟩
  have : Std.Symm (Reactions.LabelTransition domains.label accessibility.relation) :=
    ⟨fun p q hpq => (labelTransition_iff q p).mpr ((labelTransition_iff p q).mp hpq).symm⟩
  exact ⟨z, symm h⟩

theorem directCost_eq_zero {a b : Composition} (h : labelAmount a = labelAmount b) :
    Reactions.calibratedDirectCost domains.label energy accessibility.relation a b = 0 := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨⟨reference a, label_reference a⟩, ⟨reference b, label_reference b⟩, ?_, ?_⟩
    · apply (relation_iff _ _).mpr
      simp [h]
    · simp [h]
  · apply le_sInf
    rintro _ ⟨x, y, hxy, rfl⟩
    exact EReal.coe_nonneg.mpr (sub_nonneg.mpr ((relation_iff _ _).mp hxy).2)

/-- Unit amounts of the two species have unequal labels and zero conversion cost. -/
theorem unitConversion :
    accessibility.relation (atom false unitEnergy) (atom true unitEnergy) ∧
    domains.label (atom false unitEnergy) ≠ domains.label (atom true unitEnergy) ∧
    Reactions.calibratedDirectCost domains.label energy accessibility.relation
      (domains.label (atom false unitEnergy)) (domains.label (atom true unitEnergy)) = 0 := by
  refine ⟨(relation_iff _ _).mpr (by simp), ?_, directCost_eq_zero (by
    change amount (atom false unitEnergy) = amount (atom true unitEnergy)
    simp)⟩
  intro h
  have he := congrArg (fun a : Composition => a false) h
  simp at he

def represent {n : ℕ} (g : Bool) (r : ℝ≥0) (z : SimpleCoordinates n) : Raw :=
  if 0 < z.1 then r • domains.represent g ((r : ℝ)⁻¹ * z.1, 0)
  else r • atom g unitEnergy

theorem represent_pos {n : ℕ} (g : Bool) (r : ℝ≥0) (hr : 0 < r)
    (z : SimpleCoordinates n) (hz : 0 < z.1) :
    represent g r z = r • atom g ⟨(r : ℝ)⁻¹ * z.1,
      mul_pos (inv_pos.mpr (NNReal.coe_pos.mpr hr)) hz⟩ := by
  rw [represent, ite_eq_left hz,
    domains.represent_of_mem g (mul_pos (inv_pos.mpr (NNReal.coe_pos.mpr hr)) hz)]
  rfl

theorem sector_represent {n : ℕ} (g : Bool) (r : ℝ≥0) (hr : 0 < r)
    (z : SimpleCoordinates n) (hz : 0 < z.1) :
    sector (represent g r z) = Reservoir.represent r z := by
  rw [represent_pos g r hr z hz]
  change (energy (_ • _), (amount (_ • _) : ℝ)) = (z.1, (r : ℝ))
  simp [mul_inv_cancel_left₀ (NNReal.coe_ne_zero.mpr hr.ne')]

theorem forwardSector_eq {n : ℕ} (g : Bool) (r : ℝ≥0) (hr : 0 < r)
    {x : SimpleCoordinates n} (hx : x ∈ Reservoir.domain n) :
    accessibility.forwardSector (Reservoir.domain n) (represent g r) x =
      Reservoir.accessibility.forwardSector (Reservoir.domain n) (Reservoir.represent r) x := by
  ext y
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    change Reservoir.accessibility.relation (sector (represent g r x)) (sector (represent g r y)) at h
    rwa [sector_represent g r hr x hx, sector_represent g r hr y hy] at h
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    change Reservoir.accessibility.relation (sector (represent g r x)) (sector (represent g r y))
    rwa [sector_represent g r hr x hx, sector_represent g r hr y hy]

/-- The representation preserves the reservoir sector geometry for either species. -/
def system (n : ℕ) (g : Bool) (r : ℝ≥0) (hr : 0 < r) : SimpleSystem accessibility n where
  domain := Reservoir.domain n
  isOpen_domain := (Reservoir.system n r).isOpen_domain
  convex_domain := (Reservoir.system n r).convex_domain
  represent := represent g r
  mixing x hx y hy a b hab := by
    have hz := (Reservoir.system n r).convex_domain hx hy a.coe_nonneg b.coe_nonneg
      (congrArg (fun t : ℝ≥0 => (t : ℝ)) hab)
    change Reservoir.accessibility.relation (sector (a • represent g r x + b • represent g r y))
      (sector (represent g r _))
    rw [sector_add, sector_scale, sector_scale, sector_represent g r hr x hx,
      sector_represent g r hr y hy, sector_represent g r hr _ hz]
    exact (Reservoir.system n r).mixing x hx y hy a b hab
  irreversible x hx := by
    obtain ⟨y, hy, hxy, hyx⟩ := (Reservoir.system n r).irreversible x hx
    refine ⟨y, hy, ?_, ?_⟩
    · change Reservoir.accessibility.relation (sector (represent g r x)) (sector (represent g r y))
      rwa [sector_represent g r hr x hx, sector_represent g r hr y hy]
    · change ¬ Reservoir.accessibility.relation (sector (represent g r y)) (sector (represent g r x))
      rwa [sector_represent g r hr x hx, sector_represent g r hr y hy]
  pressure := fun _ => 0
  pressure_support x hx := by
    rw [forwardSector_eq g r hr hx]
    exact (Reservoir.system n r).pressure_support x hx
  unique_support x hx f hf := by
    rw [forwardSector_eq g r hr hx] at hf
    exact (Reservoir.system n r).unique_support x hx f hf
  pressure_locallyLipschitz := (Reservoir.system n r).pressure_locallyLipschitz
  boundary_pathConnected x hx := by
    rw [forwardSector_eq g r hr hx]
    exact (Reservoir.system n r).boundary_pathConnected x hx

def scaled (n : ℕ) (g : Bool) (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) :
    ScaledSimpleSystem (system n g r hr) s where
  system := system n g (s * r) (mul_pos hs hr)
  domain_eq := (Reservoir.scaled n r s hs).domain_eq
  represent_eq z := by
    have hspos := NNReal.coe_pos.mpr hs
    have hz : 0 < (s : ℝ)⁻¹ * z.1 ↔ 0 < z.1 :=
      mul_pos_iff_of_pos_left (inv_pos.mpr hspos)
    change represent g (s * r) z = s • represent g r ((s : ℝ)⁻¹ • z)
    by_cases h : 0 < z.1
    · simp only [represent, Prod.smul_fst, smul_eq_mul, ite_eq_left h, ite_eq_left (hz.mpr h),
        mul_smul, NNReal.coe_mul, mul_inv_rev]
      congr 2
      simp only [mul_assoc]
    · simp only [represent, Prod.smul_fst, smul_eq_mul, ite_eq_right h,
        ite_eq_right (mt hz.mp h), mul_smul]

/-- Contact can choose the reference species for the joined representation,
since equal-energy conversions between species are reversible. -/
def contact (n m : ℕ) (g h : Bool) (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) :
    ThermalJoin accessibility (system n g r hr).domain (system m h s hs).domain
      (fun x => (system n g r hr).represent x) (fun y => (system m h s hs).represent y) where
  represent z := represent false (r + s) (thermalJoinCoordinates n m z)
  contact x y := by
    change Reservoir.accessibility.relation (sector (represent g r x.val + represent h s y.val))
      (sector (represent false (r+s) _))
    have hz : 0 < x.val.1 + y.val.1 := add_pos x.property y.property
    rw [sector_add, sector_represent g r hr _ x.property, sector_represent h s hs _ y.property,
      sector_represent false (r+s) (add_pos hr hs) _ hz]
    exact (Reservoir.contact n m r s).contact x y
  splitting z := by
    obtain ⟨u, v, hu, hv, huv⟩ := z.property
    refine ⟨⟨(u, z.val.2.1), hu⟩, ⟨(v, z.val.2.2), hv⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact Prod.ext huv.symm rfl
    · have hz : 0 < z.val.1 := huv ▸ add_pos hu hv
      change Reservoir.accessibility.relation (sector (represent false (r+s) _))
        (sector (represent g r _ + represent h s _))
      rw [sector_add, sector_represent g r hr _ hu, sector_represent h s hs _ hv,
        sector_represent false (r+s) (add_pos hr hs) _ hz]
      change ((r : ℝ) + (s : ℝ) = (r : ℝ) + (s : ℝ)) ∧ z.val.1 ≤ u + v
      exact ⟨rfl, huv.le⟩

theorem contact_equilibrium (n m : ℕ) (g h : Bool) (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s)
    (x : (system n g r hr).domain) (y : (system m h s hs).domain) :
    (contact n m g h r s hr hs).Equilibrium x y := by
  change Reservoir.accessibility.relation (sector (represent false (r+s) _))
    (sector (represent g r x.val + represent h s y.val))
  have hz : 0 < x.val.1 + y.val.1 := add_pos x.property y.property
  rw [sector_add, sector_represent g r hr _ x.property, sector_represent h s hs _ y.property,
    sector_represent false (r+s) (add_pos hr hs) _ hz]
  exact Reservoir.contact_equilibrium n m r s x y

def join (n m : ℕ) (g h : Bool) (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) :
    SimpleThermalJoin (system n g r hr) (system m h s hs) where
  thermalJoin := contact n m g h r s hr hs
  system := system (n + m) false (r + s) (add_pos hr hs)
  domain_eq := Reservoir.join_domain n m r s
  represent_eq _ := rfl

/-- Admitted systems are exactly the positive-amount members of either species. -/
def Admitted {n : ℕ} (S : SimpleSystem accessibility n) : Prop :=
  ∃ g r, ∃ hr : 0 < r, S = system n g r hr

def memberScale {n : ℕ} (S : SimpleSystem accessibility n) (hS : Admitted S)
    (s : ℝ≥0) (hs : 0 < s) :
    {D : ScaledSimpleSystem S s // Admitted D.system} := by
  let g := hS.choose
  let r := hS.choose_spec.choose
  have hr : 0 < r := hS.choose_spec.choose_spec.choose
  have hSr : S = system n g r hr := hS.choose_spec.choose_spec.choose_spec
  rw [hSr]
  exact ⟨scaled n g r s hr hs, ⟨g, s * r, mul_pos hs hr, rfl⟩⟩

def memberJoin {n m : ℕ} (S : SimpleSystem accessibility n) (T : SimpleSystem accessibility m)
    (hS : Admitted S) (hT : Admitted T) :
    {J : SimpleThermalJoin S T // Admitted J.system ∧
      ∀ x : S.domain, ∀ y : T.domain, J.thermalJoin.Equilibrium x y} := by
  let g := hS.choose
  let r := hS.choose_spec.choose
  have hr : 0 < r := hS.choose_spec.choose_spec.choose
  have hSr : S = system n g r hr := hS.choose_spec.choose_spec.choose_spec
  let h := hT.choose
  let s := hT.choose_spec.choose
  have hs : 0 < s := hT.choose_spec.choose_spec.choose
  have hTs : T = system m h s hs := hT.choose_spec.choose_spec.choose_spec
  rw [hSr, hTs]
  exact ⟨join n m g h r s hr hs, ⟨false, r+s, add_pos hr hs, rfl⟩,
    contact_equilibrium n m g h r s hr hs⟩

/-- The canonical reacting model satisfies the full thermal-family interface. -/
def family : ThermalFamily accessibility where
  admitted := Admitted
  scale S hS r hr := (memberScale S hS r hr).val
  scale_admitted S hS r hr := (memberScale S hS r hr).property
  join S T hS hT := (memberJoin S T hS hT).val
  join_admitted S T hS hT := (memberJoin S T hS hT).property.1
  thermal := fun _ _ => True
  thermal_iff S T hS hT x y := ⟨fun _ => (memberJoin S T hS hT).property.2 x y, fun _ => trivial⟩
  thermal_symm := by intros; trivial
  zeroth_law := by intros; trivial
  scaled_copy := by intros; trivial
  transversality {n} S hS x := by
    obtain ⟨g, r, hr, rfl⟩ := hS
    obtain ⟨a, b, _, hax, hxb⟩ := Reservoir.family.transversality (Reservoir.system n r)
      (Reservoir.system_admitted n (NNReal.coe_pos.mpr hr)) x
    refine ⟨a, b, trivial, ?_, ?_⟩
    · change Reservoir.accessibility.relation (sector (represent g r a.val))
        (sector (represent g r x.val)) ∧
        ¬ Reservoir.accessibility.relation (sector (represent g r x.val))
          (sector (represent g r a.val))
      rwa [sector_represent g r hr _ a.property, sector_represent g r hr _ x.property]
    · change Reservoir.accessibility.relation (sector (represent g r x.val))
        (sector (represent g r b.val)) ∧
        ¬ Reservoir.accessibility.relation (sector (represent g r b.val))
          (sector (represent g r x.val))
      rwa [sector_represent g r hr _ b.property, sector_represent g r hr _ x.property]

def primitive (g : Bool) : SimpleSystem accessibility 0 := system 0 g 1 (by norm_num)

theorem primitive_represent (g : Bool) :
    Set.EqOn (primitive g).represent (domains.represent g) (domains.domain g) := by
  intro z hz
  have hz' : 0 < z.1 := hz
  change represent g 1 z = domains.represent g z
  simp only [represent, ite_eq_left hz', NNReal.coe_one, inv_one, one_mul, one_smul]
  congr 1
  change (z.1, 0) = (z.1, z.2)
  congr 1
  ext i
  exact Fin.elim0 i

/-- Weak entropy on the actual two-species canonical atoms. -/
theorem exists_weak_entropy :
    ∃ (entropy totalEntropy : Raw →+ ℝ) (B : Composition →ₗ[ℝ≥0] ℝ),
      WeakEntropyPrinciple domains.label accessibility.relation entropy totalEntropy B :=
  domains.exists_weak_entropy family primitive
    (fun g => ⟨g, 1, by norm_num, rfl⟩)
    (fun _ => rfl) primitive_represent
    (fun _ => Reservoir.system_nonempty 0 1) noSinks

/-- The same entropy is monotone across an actual conversion and characterizes
accessibility within every fixed composition. -/
theorem exists_monotone_conversion :
    ∃ totalEntropy : Raw →+ ℝ,
      totalEntropy (atom false unitEnergy) ≤ totalEntropy (atom true unitEnergy) ∧
      CalibratedEntropyPrinciple domains.label accessibility.relation totalEntropy := by
  obtain ⟨_, totalEntropy, _, h⟩ := exists_weak_entropy
  exact ⟨totalEntropy, h.monotone _ _ unitConversion.1, h.total⟩

end ProjectAInos.Thermodynamics.Physical.ReactingReservoir
