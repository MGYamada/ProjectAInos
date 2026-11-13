module

public import ProjectAInos.Thermodynamics.AtomicProcesses
public import ProjectAInos.Thermodynamics.ReservoirModel

/-!
# A populated thermal family on canonical atomic composites

An amount-r reservoir of energy U is represented by r copies of the atom U/r.
The family has constant temperature, zero pressure, genuine mixing, and
irreversible heating. Its raw states are the atoms required by AtomicDomains.
-/
@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace ProjectAInos.Thermodynamics.Physical.AtomicReservoir

/-- Outside the positive-energy halfspace, use a reference atom as the
ambient extension. This choice is compatible with positive scaling. -/
def represent {n : ℕ} (r : ℝ≥0) (z : SimpleCoordinates n) : Raw :=
  if 0 < z.1 then r • domains.represent () ((r : ℝ)⁻¹ * z.1, 0)
  else r • atom ⟨1, by norm_num⟩

theorem represent_pos {n : ℕ} (r : ℝ≥0) (hr : 0 < r)
    (z : SimpleCoordinates n) (hz : 0 < z.1) :
    represent r z = r • atom ⟨(r : ℝ)⁻¹ * z.1,
      mul_pos (inv_pos.mpr (NNReal.coe_pos.mpr hr)) hz⟩ := by
  rw [represent, ite_eq_left hz, domains.represent_of_mem () (mul_pos (inv_pos.mpr (NNReal.coe_pos.mpr hr)) hz)]
  rfl

theorem amount_represent {n : ℕ} (r : ℝ≥0) (hr : 0 < r)
    (z : SimpleCoordinates n) (hz : 0 < z.1) : amount (represent r z) = r := by
  rw [represent_pos r hr z hz]
  simp

theorem energy_represent {n : ℕ} (r : ℝ≥0) (hr : 0 < r)
    (z : SimpleCoordinates n) (hz : 0 < z.1) : energy (represent r z) = z.1 := by
  rw [represent_pos r hr z hz]
  simp [mul_inv_cancel_left₀ (NNReal.coe_ne_zero.mpr hr.ne')]

theorem represent_relation_iff {n m : ℕ} (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s)
    (x : SimpleCoordinates n) (y : SimpleCoordinates m) (hx : 0 < x.1) (hy : 0 < y.1) :
    accessibility.relation (represent r x) (represent s y) ↔ r = s ∧ x.1 ≤ y.1 := by
  rw [relation_iff, amount_represent r hr x hx, amount_represent s hs y hy,
    energy_represent r hr x hx, energy_represent s hs y hy]

theorem forwardSector_eq {n : ℕ} (r : ℝ≥0) (hr : 0 < r)
    {x : SimpleCoordinates n} (hx : x ∈ Reservoir.domain n) :
    accessibility.forwardSector (Reservoir.domain n) (represent r) x = {y | x.1 ≤ y.1} := by
  ext y
  constructor
  · rintro ⟨hy, h⟩
    exact ((represent_relation_iff r r hr hr x y hx hy).mp h).2
  · intro hy
    have hyp : 0 < y.1 := lt_of_lt_of_le hx hy
    exact ⟨hyp, (represent_relation_iff r r hr hr x y hx hyp).mpr ⟨rfl, hy⟩⟩

/-- All geometric simple-system premises are inherited from the proved
halfspace geometry, after identifying the actual generated forward sectors. -/
def system (n : ℕ) (r : ℝ≥0) (hr : 0 < r) : SimpleSystem accessibility n where
  domain := Reservoir.domain n
  isOpen_domain := (Reservoir.system n r).isOpen_domain
  convex_domain := (Reservoir.system n r).convex_domain
  represent := represent r
  mixing x hx y hy a b hab := by
    have hz := (Reservoir.system n r).convex_domain hx hy a.coe_nonneg b.coe_nonneg
      (congrArg (fun t : ℝ≥0 => (t : ℝ)) hab)
    rw [relation_iff]
    simp only [map_add, amount_scale, energy_scale, amount_represent r hr x hx,
      amount_represent r hr y hy, amount_represent r hr _ hz,
      energy_represent r hr x hx, energy_represent r hr y hy, energy_represent r hr _ hz]
    constructor
    · rw [← add_mul, hab, one_mul]
    · exact le_rfl
  irreversible x hx := by
    refine ⟨(x.1 + 1, x.2), by change 0 < x.1 + 1; linarith [show 0 < x.1 from hx], ?_⟩
    have hy : 0 < (x.1 + 1) := by linarith [show 0 < x.1 from hx]
    rw [represent_relation_iff r r hr hr x _ hx hy,
      represent_relation_iff r r hr hr _ x hy hx]
    exact ⟨⟨rfl, by simp⟩, by rintro ⟨_, h⟩; linarith⟩
  pressure := fun _ => 0
  pressure_support x hx := by
    rw [forwardSector_eq r hr hx, ← Reservoir.forwardSector_eq (r : ℝ) hx]
    exact (Reservoir.system n r).pressure_support x hx
  unique_support x hx f hf := by
    rw [forwardSector_eq r hr hx] at hf
    exact Reservoir.unique_support x f hf
  pressure_locallyLipschitz := (Reservoir.system n r).pressure_locallyLipschitz
  boundary_pathConnected x hx := by
    rw [forwardSector_eq r hr hx, ← Reservoir.forwardSector_eq (r : ℝ) hx]
    exact (Reservoir.system n r).boundary_pathConnected x hx

theorem system_nonempty (n : ℕ) (r : ℝ≥0) (hr : 0 < r) : (system n r hr).domain.Nonempty :=
  ⟨(1, 0), by norm_num [system, Reservoir.domain]⟩

theorem represent_scale {n : ℕ} (r s : ℝ≥0) (z : SimpleCoordinates n) :
    represent (s*r) z = s • represent r ((s : ℝ)⁻¹ • z) := by
  by_cases hs : s = 0
  · subst s
    simp [represent]
  have hspos : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hz : 0 < (s : ℝ)⁻¹ * z.1 ↔ 0 < z.1 :=
    mul_pos_iff_of_pos_left (inv_pos.mpr hspos)
  by_cases h : 0 < z.1
  · simp only [represent, Prod.smul_fst, smul_eq_mul, ite_eq_left h, ite_eq_left (hz.mpr h),
      mul_smul, NNReal.coe_mul, mul_inv_rev]
    congr 2
    simp only [mul_assoc]
  · simp only [represent, Prod.smul_fst, smul_eq_mul, ite_eq_right h,
      ite_eq_right (mt hz.mp h), mul_smul]

def scaled (n : ℕ) (r : ℝ≥0) (hr : 0 < r) (s : ℝ≥0) (hs : 0 < s) :
    ScaledSimpleSystem (system n r hr) s where
  system := system n (s*r) (mul_pos hs hr)
  domain_eq := by
    ext z
    change 0 < z.1 ↔ 0 < (s : ℝ)⁻¹ * z.1
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr (NNReal.coe_pos.mpr hs))).symm
  represent_eq := represent_scale r s

def contact (n m : ℕ) (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) :
    ThermalJoin accessibility (system n r hr).domain (system m s hs).domain
      (fun x => (system n r hr).represent x) (fun y => (system m s hs).represent y) where
  represent z := represent (n := n+m) (r+s) (thermalJoinCoordinates n m z)
  contact x y := by
    rw [relation_iff]
    have hz : 0 < x.val.1 + y.val.1 := add_pos x.property y.property
    simp only [system, map_add, amount_represent r hr x.val x.property,
      amount_represent s hs y.val y.property, energy_represent r hr x.val x.property,
      energy_represent s hs y.val y.property]
    rw [amount_represent (r+s) (add_pos hr hs) _ hz,
      energy_represent (r+s) (add_pos hr hs) _ hz]
    exact ⟨rfl, le_rfl⟩
  splitting z := by
    obtain ⟨u, v, hu, hv, huv⟩ := z.property
    refine ⟨⟨(u, z.val.2.1), hu⟩, ⟨(v, z.val.2.2), hv⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact Prod.ext huv.symm rfl
    · rw [relation_iff]
      have hz : 0 < z.val.1 := huv ▸ add_pos hu hv
      simp only [system, map_add, amount_represent r hr _ hu, amount_represent s hs _ hv,
        energy_represent r hr _ hu, energy_represent s hs _ hv]
      rw [amount_represent (r+s) (add_pos hr hs) _ hz,
        energy_represent (r+s) (add_pos hr hs) _ hz]
      exact ⟨rfl, huv.le⟩

def join (n m : ℕ) (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) :
    SimpleThermalJoin (system n r hr) (system m s hs) where
  thermalJoin := contact n m r s hr hs
  system := system (n+m) (r+s) (add_pos hr hs)
  domain_eq := Reservoir.join_domain n m r s
  represent_eq _ := rfl

theorem contact_equilibrium (n m : ℕ) (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s)
    (x : (system n r hr).domain) (y : (system m s hs).domain) :
    (contact n m r s hr hs).Equilibrium x y := by
  rw [ThermalJoin.Equilibrium, relation_iff]
  dsimp only [contact, system]
  have hz : 0 < x.val.1 + y.val.1 := add_pos x.property y.property
  rw [amount_represent (r+s) (add_pos hr hs) _ hz,
    energy_represent (r+s) (add_pos hr hs) _ hz]
  simp only [system, map_add, amount_represent r hr _ x.property,
    amount_represent s hs _ y.property, energy_represent r hr _ x.property,
    energy_represent s hs _ y.property]
  exact ⟨trivial, le_rfl⟩

/-- Membership records a specific positive amount; it is populated below. -/
def Admitted {n : ℕ} (S : SimpleSystem accessibility n) : Prop :=
  ∃ r : ℝ≥0, ∃ hr : 0 < r, S = system n r hr

def memberAmount {n : ℕ} (S : SimpleSystem accessibility n) : ℝ≥0 :=
  amount (S.represent (1, 0))

@[simp] theorem memberAmount_system (n : ℕ) (r : ℝ≥0) (hr : 0 < r) :
    memberAmount (system n r hr) = r := amount_represent r hr (1, 0) (by norm_num)

theorem memberAmount_pos {n : ℕ} (S : SimpleSystem accessibility n) (hS : Admitted S) :
    0 < memberAmount S := by
  obtain ⟨r, hr, rfl⟩ := hS
  simpa using hr

theorem member_eq {n : ℕ} (S : SimpleSystem accessibility n) (hS : Admitted S) :
    S = system n (memberAmount S) (memberAmount_pos S hS) := by
  obtain ⟨r, hr, rfl⟩ := hS
  simp

def memberScale {n : ℕ} (S : SimpleSystem accessibility n) (hS : Admitted S)
    (s : ℝ≥0) (hs : 0 < s) : ScaledSimpleSystem S s where
  system := system n (s * memberAmount S) (mul_pos hs (memberAmount_pos S hS))
  domain_eq := by
    obtain ⟨r, hr, rfl⟩ := hS
    exact (scaled n r hr s hs).domain_eq
  represent_eq z := by
    obtain ⟨r, hr, rfl⟩ := hS
    change represent (s * memberAmount (system n r hr)) z = s • represent r ((s : ℝ)⁻¹ • z)
    rw [memberAmount_system]
    exact represent_scale r s z

theorem memberScale_admitted {n : ℕ} (S : SimpleSystem accessibility n) (hS : Admitted S)
    (s : ℝ≥0) (hs : 0 < s) : Admitted (memberScale S hS s hs).system := by
  obtain ⟨r, hr, rfl⟩ := hS
  exact ⟨s*r, mul_pos hs hr, by simp [memberScale]⟩

def memberJoin {n m : ℕ} (S : SimpleSystem accessibility n) (T : SimpleSystem accessibility m)
    (hS : Admitted S) (hT : Admitted T) : SimpleThermalJoin S T where
  thermalJoin :=
    { represent z := represent (memberAmount S + memberAmount T) (thermalJoinCoordinates n m z)
      contact x y := by
        obtain ⟨r, hr, rfl⟩ := hS
        obtain ⟨s, hs, rfl⟩ := hT
        simpa only [memberAmount_system, contact] using (contact n m r s hr hs).contact x y
      splitting z := by
        obtain ⟨r, hr, rfl⟩ := hS
        obtain ⟨s, hs, rfl⟩ := hT
        simpa only [memberAmount_system, contact] using (contact n m r s hr hs).splitting z }
  system := system (n+m) (memberAmount S + memberAmount T)
    (add_pos (memberAmount_pos S hS) (memberAmount_pos T hT))
  domain_eq := by
    obtain ⟨r, hr, rfl⟩ := hS
    obtain ⟨s, hs, rfl⟩ := hT
    exact Reservoir.join_domain n m r s
  represent_eq _ := rfl

theorem memberJoin_admitted {n m : ℕ} (S : SimpleSystem accessibility n)
    (T : SimpleSystem accessibility m) (hS : Admitted S) (hT : Admitted T) :
    Admitted (memberJoin S T hS hT).system := by
  obtain ⟨r, hr, rfl⟩ := hS
  obtain ⟨s, hs, rfl⟩ := hT
  exact ⟨r+s, add_pos hr hs, by simp [memberJoin]⟩

/-- The thermal relation is universal on this constant-temperature family;
adiabatic accessibility still has strict, irreversible energy increases. -/
def family : ThermalFamily accessibility where
  admitted := Admitted
  scale := memberScale
  scale_admitted := memberScale_admitted
  join := memberJoin
  join_admitted := memberJoin_admitted
  thermal := fun _ _ => True
  thermal_iff S T hS hT x y := by
    obtain ⟨r, hr, rfl⟩ := hS
    obtain ⟨s, hs, rfl⟩ := hT
    constructor
    · intro _
      simpa only [memberJoin, memberAmount_system, ThermalJoin.Equilibrium, contact] using
        contact_equilibrium _ _ r s hr hs x y
    · intro _; trivial
  thermal_symm := by intros; trivial
  zeroth_law := by intros; trivial
  scaled_copy := by intros; trivial
  transversality {n} S hS x := by
    obtain ⟨r, hr, rfl⟩ := hS
    have hx : 0 < x.val.1 := x.property
    let a : (system n r hr).domain := ⟨(x.val.1 / 2, x.val.2), by change 0 < x.val.1 / 2; positivity⟩
    let b : (system n r hr).domain := ⟨(2*x.val.1, x.val.2), by change 0 < 2*x.val.1; positivity⟩
    refine ⟨a, b, trivial, ?_, ?_⟩
    · change accessibility.relation (represent r a.val) (represent r x.val) ∧
        ¬ accessibility.relation (represent r x.val) (represent r a.val)
      rw [represent_relation_iff r r hr hr _ _ a.property hx,
        represent_relation_iff r r hr hr _ _ hx a.property]
      dsimp only [a]
      exact ⟨⟨rfl, by linarith⟩, by rintro ⟨_, h⟩; linarith⟩
    · change accessibility.relation (represent r x.val) (represent r b.val) ∧
        ¬ accessibility.relation (represent r b.val) (represent r x.val)
      rw [represent_relation_iff r r hr hr _ _ hx b.property,
        represent_relation_iff r r hr hr _ _ b.property hx]
      dsimp only [b]
      exact ⟨⟨rfl, by linarith⟩, by rintro ⟨_, h⟩; linarith⟩

theorem family_nontrivial : family.Nontrivial :=
  ⟨0, system 0 1 (by norm_num), ⟨1, by norm_num, rfl⟩, system_nonempty 0 1 (by norm_num)⟩

theorem canonical_represent :
    Set.EqOn (system 0 1 (by norm_num)).represent (domains.represent ()) (domains.domain ()) := by
  intro z hz
  have hz' : 0 < z.1 := hz
  change represent 1 z = domains.represent () z
  simp only [represent, ite_eq_left hz', NNReal.coe_one, inv_one, one_mul, one_smul]
  congr 1
  change (z.1, 0) = (z.1, z.2)
  congr 1
  ext i
  exact Fin.elim0 i

/-- The admitted reservoir agrees with the canonical atom on its proper
physical domain and takes a different value at the ambient origin. -/
theorem canonical_represent_ne :
    (system 0 1 (by norm_num)).represent ≠ domains.represent () := by
  intro h
  have hz : (0 : SimpleCoordinates 0) ∉ domains.domain () := by
    change ¬ (0 : ℝ) < 0
    simp
  have he := congrFun h (0 : SimpleCoordinates 0)
  rw [domains.represent_of_not_mem () hz] at he
  change represent 1 (0 : SimpleCoordinates 0) = 0 at he
  have ha := congrArg amount he
  simp [represent] at ha

/-- The repaired endpoint is instantiated on the actual canonical atoms,
including all thermal-family premises. Neither CH nor ECH is an input. -/
theorem exchangeComparison : ExchangeComparison accessibility.StateSpace :=
  domains.exchangeComparison_nonreactive Step Step.label_eq family
    (fun _ => system 0 1 (by norm_num)) (fun _ => ⟨1, by norm_num, rfl⟩)
    (fun _ => rfl) (fun _ => canonical_represent)

end ProjectAInos.Thermodynamics.Physical.AtomicReservoir
