module

public import ProjectAInos.Thermodynamics.SectorModel
public import ProjectAInos.Thermodynamics.ThermalFamily
public import ProjectAInos.Thermodynamics.HasCalibratorsOfAxioms
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# A populated smooth thermal family of reservoirs

Energy is entropy, amount is conserved, and work coordinates have zero pressure.
Positive-energy reservoirs of every finite work dimension are closed under
positive scaling and thermal joining. The thermal relation is universal on
this family, while adiabatic accessibility orders energy at equal amount and
admits irreversible energy increases. This witnesses the full geometric and thermal interfaces;
it is not a nonconstant-temperature or canonical-atomic-composite model.
-/

@[expose] public section

open Set
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical.Reservoir

/-- Accessibility compares energy/entropy at equal amount. -/
def accessibility : Accessibility SectorState where
  relation := (· ≤ ·)
  refl := le_refl
  trans := le_trans
  add_mono := fun h k => add_le_add h k
  scale_mono := fun a {_ _} h => smul_le_smul_of_nonneg_left h (show 0 ≤ a from bot_le)
  zero_scale := zero_smul _
  split a b x := by rw [add_smul]; exact ⟨le_rfl, le_rfl⟩
  stable := SectorState.stability

/-- The energy is positive; the work coordinates are unrestricted. -/
def domain (n : ℕ) : Set (SimpleCoordinates n) := {z | 0 < z.1}

/-- A reservoir of amount `r` represents energy as its entropy coordinate. -/
def represent {n : ℕ} (r : ℝ) (z : SimpleCoordinates n) : SectorState := (z.1, r)

theorem relation_iff {n m : ℕ} (r q : ℝ) (x : SimpleCoordinates n)
    (y : SimpleCoordinates m) :
    accessibility.relation (represent r x) (represent q y) ↔ r = q ∧ x.1 ≤ y.1 := Iff.rfl

theorem forwardSector_eq {n : ℕ} (r : ℝ) {x : SimpleCoordinates n}
    (hx : x ∈ domain n) :
    accessibility.forwardSector (domain n) (represent r) x = {y | x.1 ≤ y.1} := by
  ext y
  change (0 < y.1 ∧ r = r ∧ x.1 ≤ y.1) ↔ x.1 ≤ y.1
  exact ⟨fun h => h.2.2, fun h => ⟨lt_of_lt_of_le hx h, rfl, h⟩⟩

theorem relative_boundary_eq {n : ℕ} (r : ℝ) {x : SimpleCoordinates n}
    (hx : x ∈ domain n) :
    domain n ∩ frontier (accessibility.forwardSector (domain n) (represent r) x) =
      {y | y.1 = x.1} := by
  rw [forwardSector_eq r hx]
  have hfront : frontier {y : SimpleCoordinates n | x.1 ≤ y.1} = {y | y.1 = x.1} := by
    change frontier (Prod.fst ⁻¹' Ici x.1) = _
    rw [← isOpenMap_fst.preimage_frontier_eq_frontier_preimage continuous_fst, frontier_Ici]
    rfl
  rw [hfront]
  ext y
  change (0 < y.1 ∧ y.1 = x.1) ↔ y.1 = x.1
  exact ⟨And.right, fun h => ⟨h ▸ hx, h⟩⟩

theorem unique_support {n : ℕ} (x : SimpleCoordinates n)
    (f : SimpleCoordinates n →ₗ[ℝ] ℝ)
    (hf : SupportsAt {y | x.1 ≤ y.1} x f) :
    LinearMap.ker f = LinearMap.ker (pressureForm (0 : WorkCoordinates n)) := by
  have hwork (v : WorkCoordinates n) : f (0, v) = 0 := by
    have hp := hf.2 (x + (0, v)) (by simp)
    have hm := hf.2 (x - (0, v)) (by simp)
    simp only [map_add, map_sub] at hp hm
    linarith
  have heval (z : SimpleCoordinates n) : f z = z.1 * f (1, 0) := by
    have hz : z = z.1 • (1, 0) + (0, z.2) := by ext <;> simp
    calc
      f z = f (z.1 • (1, 0) + (0, z.2)) := congrArg f hz
      _ = z.1 * f (1, 0) := by rw [map_add, map_smul, hwork, add_zero]; rfl
  have henergy : f (1, 0) ≠ 0 := by
    intro hzero
    apply hf.1
    apply LinearMap.ext
    intro z
    change f z = 0
    rw [heval, hzero, mul_zero]
  ext z
  change f z = 0 ↔ pressureForm (0 : WorkCoordinates n) z = 0
  rw [heval]
  simp [pressureForm, henergy]

/-- A smooth reservoir satisfies A7 and S1--S3 for every amount parameter. -/
noncomputable def system (n : ℕ) (r : ℝ) : SimpleSystem accessibility n where
  domain := domain n
  isOpen_domain := isOpen_lt continuous_const continuous_fst
  convex_domain := by
    intro x hx y hy a b ha hb hab
    change 0 < a * x.1 + b * y.1
    change 0 < x.1 at hx
    change 0 < y.1 at hy
    by_cases ha0 : a = 0
    · subst a
      simpa [show b = 1 by linarith] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx)
        (mul_nonneg hb hy.le)
  represent := represent r
  mixing := by
    intro x hx y hy a b hab
    constructor
    · change (a : ℝ) * r + (b : ℝ) * r = r
      have h : (a : ℝ) + b = 1 := congrArg (fun t : ℝ≥0 => (t : ℝ)) hab
      rw [← add_mul, h, one_mul]
    · change (a : ℝ) * x.1 + (b : ℝ) * y.1 ≤ (a : ℝ) * x.1 + (b : ℝ) * y.1
      exact le_rfl
  irreversible := by
    intro x hx
    have hxpos : 0 < x.1 := hx
    refine ⟨(x.1 + 1, x.2), by change 0 < x.1 + 1; linarith, ?_⟩
    change (r = r ∧ x.1 ≤ x.1 + 1) ∧ ¬ (r = r ∧ x.1 + 1 ≤ x.1)
    constructor
    · exact ⟨rfl, by linarith⟩
    · rintro ⟨_, h⟩
      linarith
  pressure := fun _ => 0
  pressure_support := by
    intro x hx
    right
    refine ⟨neg_ne_zero.mpr (pressureForm_ne_zero 0), ?_⟩
    intro y hy
    rw [forwardSector_eq r hx] at hy
    have hy' : x.1 ≤ y.1 := hy
    change -(y.1 + ∑ i : Fin n, (0 : ℝ) * y.2 i) ≤
      -(x.1 + ∑ i : Fin n, (0 : ℝ) * x.2 i)
    simpa using neg_le_neg hy'
  unique_support := by
    intro x hx f hf
    rw [forwardSector_eq r hx] at hf
    exact unique_support x f hf
  pressure_locallyLipschitz := (LocallyLipschitz.const 0).locallyLipschitzOn
  boundary_pathConnected := by
    intro x hx
    rw [relative_boundary_eq r hx]
    have hconv : Convex ℝ {y : SimpleCoordinates n | y.1 = x.1} := by
      intro u hu v hv a b _ _ hab
      change a * u.1 + b * v.1 = x.1
      rw [hu, hv, ← add_mul, hab, one_mul]
    exact hconv.isPathConnected ⟨x, rfl⟩

theorem system_nonempty (n : ℕ) (r : ℝ) : (system n r).domain.Nonempty :=
  ⟨(1, 0), by norm_num [system, domain]⟩

/-- Positive extensive scaling preserves the reservoir coordinate model. -/
noncomputable def scaled (n : ℕ) (r : ℝ) (s : ℝ≥0) (hs : 0 < s) :
    ScaledSimpleSystem (system n r) s where
  system := system n ((s : ℝ) * r)
  domain_eq := by
    ext z
    change 0 < z.1 ↔ 0 < (s : ℝ)⁻¹ * z.1
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr (NNReal.coe_pos.mpr hs))).symm
  represent_eq := by
    intro z
    change (z.1, (s : ℝ) * r) = ((s : ℝ) * ((s : ℝ)⁻¹ * z.1), (s : ℝ) * r)
    rw [mul_inv_cancel_left₀ (NNReal.coe_ne_zero.mpr hs.ne')]

/-- Contact is reversible for every pair of reservoir states. -/
noncomputable def contact (n m : ℕ) (r q : ℝ) :
    ThermalJoin accessibility (system n r).domain (system m q).domain
      (fun x => (system n r).represent x) (fun y => (system m q).represent y) where
  represent z := (z.val.1, r + q)
  contact _ _ := le_rfl
  splitting z := by
    obtain ⟨u, v, hu, hv, huv⟩ := z.property
    refine ⟨⟨(u, z.val.2.1), hu⟩, ⟨(v, z.val.2.2), hv⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact Prod.ext huv.symm rfl
    · change r + q = r + q ∧ z.val.1 ≤ u + v
      exact ⟨rfl, huv.le⟩

/-- The canonical join domain is again the positive-energy halfspace. -/
theorem join_domain (n m : ℕ) (r q : ℝ) :
    (system (n + m) (r + q)).domain =
      thermalJoinCoordinates n m '' joinedDomain (system n r).domain (system m q).domain := by
  ext z
  constructor
  · intro hz
    refine ⟨(thermalJoinCoordinates n m).symm z, ?_, (thermalJoinCoordinates n m).apply_symm_apply z⟩
    refine ⟨z.1 / 2, z.1 / 2, ?_, ?_, ?_⟩
    · change 0 < z.1 / 2
      exact div_pos hz (by norm_num)
    · change 0 < z.1 / 2
      exact div_pos hz (by norm_num)
    · change z.1 = z.1 / 2 + z.1 / 2
      ring
  · rintro ⟨w, ⟨u, v, hu, hv, huv⟩, rfl⟩
    change 0 < w.1
    rw [huv]
    exact add_pos hu hv

/-- A concrete thermal join with every simple-system field proved. -/
noncomputable def join (n m : ℕ) (r q : ℝ) :
    SimpleThermalJoin (system n r) (system m q) where
  thermalJoin := contact n m r q
  system := system (n + m) (r + q)
  domain_eq := join_domain n m r q
  represent_eq _ := rfl

@[simp] theorem contact_equilibrium (n m : ℕ) (r q : ℝ)
    (x : (system n r).domain) (y : (system m q).domain) :
    (contact n m r q).Equilibrium x y := le_rfl

/-- Members of the reservoir family have positive physical amount. -/
def Admitted {n : ℕ} (S : SimpleSystem accessibility n) : Prop :=
  ∃ r : ℝ, 0 < r ∧ S = system n r

theorem system_admitted (n : ℕ) {r : ℝ} (hr : 0 < r) : Admitted (system n r) :=
  ⟨r, hr, rfl⟩

def memberAmount {n : ℕ} (S : SimpleSystem accessibility n) : ℝ :=
  (S.represent (0, 0)).2

theorem memberAmount_pos {n : ℕ} (S : SimpleSystem accessibility n)
    (hS : Admitted S) : 0 < memberAmount S := by
  obtain ⟨r, hr, rfl⟩ := hS
  exact hr

noncomputable def memberScale {n : ℕ} (S : SimpleSystem accessibility n)
    (hS : Admitted S) (s : ℝ≥0) (hs : 0 < s) : ScaledSimpleSystem S s where
  system := system n ((s : ℝ) * memberAmount S)
  domain_eq := by
    obtain ⟨r, _, rfl⟩ := hS
    exact (scaled n r s hs).domain_eq
  represent_eq := by
    obtain ⟨r, _, rfl⟩ := hS
    exact (scaled n r s hs).represent_eq

theorem memberScale_admitted {n : ℕ} (S : SimpleSystem accessibility n)
    (hS : Admitted S) (s : ℝ≥0) (hs : 0 < s) :
    Admitted (memberScale S hS s hs).system :=
  ⟨(s : ℝ) * memberAmount S, mul_pos (NNReal.coe_pos.mpr hs) (memberAmount_pos S hS), rfl⟩

noncomputable def memberJoin {n m : ℕ} (S : SimpleSystem accessibility n)
    (T : SimpleSystem accessibility m) (hS : Admitted S) (hT : Admitted T) :
    SimpleThermalJoin S T where
  thermalJoin :=
    { represent := fun z => (z.val.1, memberAmount S + memberAmount T)
      contact := by
        obtain ⟨r, _, rfl⟩ := hS
        obtain ⟨q, _, rfl⟩ := hT
        exact fun _ _ => le_rfl
      splitting := by
        obtain ⟨r, _, rfl⟩ := hS
        obtain ⟨q, _, rfl⟩ := hT
        exact (contact n m r q).splitting }
  system := system (n + m) (memberAmount S + memberAmount T)
  domain_eq := by
    obtain ⟨r, _, rfl⟩ := hS
    obtain ⟨q, _, rfl⟩ := hT
    exact join_domain n m r q
  represent_eq := by
    obtain ⟨r, _, rfl⟩ := hS
    obtain ⟨q, _, rfl⟩ := hT
    exact fun _ => rfl

/-- An inhabited thermal family, closed under positive scaling and all joins. -/
noncomputable def family : ThermalFamily accessibility where
  admitted := Admitted
  scale := memberScale
  scale_admitted := memberScale_admitted
  join := memberJoin
  join_admitted S T hS hT :=
    ⟨memberAmount S + memberAmount T, add_pos (memberAmount_pos S hS) (memberAmount_pos T hT), rfl⟩
  thermal := fun _ _ => True
  thermal_iff S T hS hT x y := by
    obtain ⟨r, _, rfl⟩ := hS
    obtain ⟨q, _, rfl⟩ := hT
    exact ⟨fun _ => le_rfl, fun _ => trivial⟩
  thermal_symm := by intros; trivial
  zeroth_law := by intros; trivial
  scaled_copy := by intros; trivial
  transversality {n} S hS x := by
    obtain ⟨r, _, rfl⟩ := hS
    have hxpos : 0 < x.val.1 := x.property
    let a : (system n r).domain := ⟨(x.val.1 / 2, x.val.2),
      div_pos (show 0 < x.val.1 from x.property) (show (0 : ℝ) < 2 by norm_num)⟩
    let b : (system n r).domain := ⟨(2 * x.val.1, x.val.2), mul_pos (show (0 : ℝ) < 2 by norm_num) x.property⟩
    refine ⟨a, b, trivial, ?_, ?_⟩
    · change (r = r ∧ x.val.1 / 2 ≤ x.val.1) ∧ ¬ (r = r ∧ x.val.1 ≤ x.val.1 / 2)
      constructor
      · exact ⟨rfl, by linarith⟩
      · rintro ⟨_, h⟩
        linarith
    · change (r = r ∧ x.val.1 ≤ 2 * x.val.1) ∧ ¬ (r = r ∧ 2 * x.val.1 ≤ x.val.1)
      constructor
      · exact ⟨rfl, by linarith⟩
      · rintro ⟨_, h⟩
        linarith

/-- The family contains an actual reservoir state, not just empty domains. -/
theorem family_nontrivial : family.Nontrivial :=
  ⟨0, system 0 1, system_admitted 0 (r := 1) (by norm_num), system_nonempty 0 1⟩

theorem represented_state : family.IsState (1, 1) :=
  ⟨0, system 0 1, system_admitted 0 (r := 1) (by norm_num), ⟨(1, 0), by norm_num [system, domain]⟩, rfl⟩

/-- The general physical calibrator theorem has actual reservoir instances. -/
theorem exists_calibrator (n m : ℕ) (r q : ℝ) (hr : 0 < r) (hq : 0 < q) :
    ∃ a b : (system n r).domain, ∃ c d : (system m q).domain,
      IsEntropyCalibrator accessibility
        ((system n r).represent a) ((system n r).represent b)
        ((system m q).represent c) ((system m q).represent d) :=
  family.hasCalibrators_of_axioms (system n r) (system m q)
    (system_admitted n hr) (system_admitted m hq) (system_nonempty n r) (system_nonempty m q)

/-- Finite-product comparison specializes to this populated thermal family. -/
theorem product_comparison {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (weight : ι → ℝ≥0)
    (x y : ∀ i, (system (n i) (r i)).domain) :
    accessibility.relation
        (∑ i, weight i • (system (n i) (r i)).represent (x i))
        (∑ i, weight i • (system (n i) (r i)).represent (y i)) ∨
      accessibility.relation
        (∑ i, weight i • (system (n i) (r i)).represent (y i))
        (∑ i, weight i • (system (n i) (r i)).represent (x i)) :=
  family.scaled_products_comparable family.hasCalibrators_of_axioms n
    (fun i => system (n i) (r i)) (fun i => system_admitted (n i) (hr i)) weight x y

end ProjectAInos.Thermodynamics.Physical.Reservoir
