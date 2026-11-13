module

public import ProjectAInos.Thermodynamics.ReservoirModel
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A populated thermal family with distinct temperatures

At fixed positive amount r the entropy is r log(U/r) plus the sum of
the work coordinates. Contact maximizes entropy at equal energy per amount.
Every admitted member has at least one work coordinate, so varying work at
fixed temperature gives states that bracket any given entropy.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped NNReal ContDiff Topology BigOperators

namespace ProjectAInos.Thermodynamics.Physical.LogarithmicThermal

def workSum {n : ℕ} : WorkCoordinates n →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i

@[simp] theorem workSum_apply {n : ℕ} (v : WorkCoordinates n) : workSum v = ∑ i, v i := by
  simp [workSum]

theorem workSum_append {n m : ℕ} (v : WorkCoordinates n) (w : WorkCoordinates m) :
    workSum (Fin.append v w) = workSum v + workSum w := by
  simp [Fin.sum_univ_add]

def entropy {n : ℕ} (r : ℝ) (x : SimpleCoordinates n) : ℝ :=
  r * Real.log (x.1 / r) + workSum x.2

/-- Preserve the extensive temperature coordinate as well as amount and entropy.
The accessibility order compares entropy at fixed amount. -/
abbrev State := SectorState × ℝ

def accessibility : Accessibility State where
  relation x y := Reservoir.accessibility.relation x.1 y.1
  refl x := Reservoir.accessibility.refl x.1
  trans := Reservoir.accessibility.trans
  add_mono := Reservoir.accessibility.add_mono
  scale_mono a {_ _} h := Reservoir.accessibility.scale_mono a h
  zero_scale := zero_smul _
  split a b x := Reservoir.accessibility.split a b x.1
  stable x y z w := Reservoir.accessibility.stable x.1 y.1 z.1 w.1

def represent {n : ℕ} (r : ℝ) (x : SimpleCoordinates n) : State :=
  ((entropy r x, r), x.1)

def thermal (x y : State) : Prop := x.2 / x.1.2 = y.2 / y.1.2

/-- The represented entropy, extended additively to compound states. -/
def stateEntropy : State →+ ℝ where
  toFun x := x.1.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem stateEntropy_mono (x y : State) (h : accessibility.relation x y) :
    stateEntropy x ≤ stateEntropy y := h.2

theorem relation_iff {n m : ℕ} (r s : ℝ) (x : SimpleCoordinates n) (y : SimpleCoordinates m) :
    accessibility.relation (represent r x) (represent s y) ↔
      r = s ∧ entropy r x ≤ entropy s y := Iff.rfl

def boundaryEnergy {n : ℕ} (r : ℝ) (x : SimpleCoordinates n) (v : WorkCoordinates n) : ℝ :=
  x.1 * Real.exp ((workSum x.2 - workSum v) / r)

theorem boundaryEnergy_pos {n : ℕ} (r : ℝ) {x : SimpleCoordinates n} (hx : 0 < x.1)
    (v : WorkCoordinates n) : 0 < boundaryEnergy r x v :=
  mul_pos hx (Real.exp_pos _)

@[simp] theorem boundaryEnergy_self {n : ℕ} (r : ℝ) (x : SimpleCoordinates n) :
    boundaryEnergy r x x.2 = x.1 := by simp [boundaryEnergy]

theorem entropy_le_iff {n : ℕ} {r : ℝ} (hr : 0 < r)
    {x y : SimpleCoordinates n} (hx : 0 < x.1) (hy : 0 < y.1) :
    entropy r x ≤ entropy r y ↔ boundaryEnergy r x y.2 ≤ y.1 := by
  have hlog : Real.log (y.1 / x.1) =
      Real.log (y.1 / r) - Real.log (x.1 / r) := by
    rw [Real.log_div hy.ne' hx.ne', Real.log_div hy.ne' hr.ne', Real.log_div hx.ne' hr.ne']
    ring
  unfold entropy boundaryEnergy
  rw [mul_comm x.1]
  rw [← le_div_iff₀ hx, ← Real.le_log_iff_exp_le (div_pos hy hx), hlog, div_le_iff₀ hr]
  constructor <;> intro h <;> linarith

theorem forwardSector_eq {n : ℕ} {r : ℝ} (hr : 0 < r)
    {x : SimpleCoordinates n} (hx : x ∈ Reservoir.domain n) :
    accessibility.forwardSector (Reservoir.domain n) (represent r) x =
      {y | boundaryEnergy r x y.2 ≤ y.1} := by
  ext y
  change (0 < y.1 ∧ (r = r ∧ entropy r x ≤ entropy r y)) ↔ _
  constructor
  · rintro ⟨hy, _, h⟩
    exact (entropy_le_iff hr hx hy).mp h
  · intro hy
    have hpos : 0 < y.1 := (boundaryEnergy_pos r hx y.2).trans_le hy
    exact ⟨hpos, rfl, (entropy_le_iff hr hx hpos).mpr hy⟩

def boundaryChart {n : ℕ} (r : ℝ) (x : SimpleCoordinates n) :
    SimpleCoordinates n ≃ₜ SimpleCoordinates n where
  toFun y := (y.1 - boundaryEnergy r x y.2, y.2)
  invFun y := (y.1 + boundaryEnergy r x y.2, y.2)
  left_inv y := by ext <;> simp
  right_inv y := by ext <;> simp
  continuous_toFun := by
    unfold boundaryEnergy
    fun_prop
  continuous_invFun := by
    unfold boundaryEnergy
    fun_prop

theorem boundary_pathConnected {n : ℕ} {r : ℝ} (hr : 0 < r)
    {x : SimpleCoordinates n} (hx : x ∈ Reservoir.domain n) :
    IsPathConnected (Reservoir.domain n ∩ frontier
      (accessibility.forwardSector (Reservoir.domain n) (represent r) x)) := by
  rw [forwardSector_eq hr hx]
  have hfront : frontier {y : SimpleCoordinates n | boundaryEnergy r x y.2 ≤ y.1} =
      {y | y.1 = boundaryEnergy r x y.2} := by
    have heq : {y : SimpleCoordinates n | boundaryEnergy r x y.2 ≤ y.1} =
        (Prod.fst ∘ boundaryChart r x) ⁻¹' Ici 0 := by
      ext y
      exact sub_nonneg.symm
    rw [heq]
    rw [← (isOpenMap_fst.comp (boundaryChart r x).isOpenMap).preimage_frontier_eq_frontier_preimage
      (continuous_fst.comp (boundaryChart r x).continuous), frontier_Ici]
    ext y
    change y.1 - boundaryEnergy r x y.2 = 0 ↔ _
    exact sub_eq_zero
  rw [hfront]
  have heq : Reservoir.domain n ∩ {y | y.1 = boundaryEnergy r x y.2} =
      (fun v => (boundaryEnergy r x v, v)) '' univ := by
    ext y
    constructor
    · rintro ⟨_, hy⟩
      exact ⟨y.2, mem_univ _, Prod.ext hy.symm rfl⟩
    · rintro ⟨v, _, rfl⟩
      exact ⟨boundaryEnergy_pos r hx v, rfl⟩
  rw [heq]
  exact isPathConnected_univ.image (by
    unfold boundaryEnergy
    fun_prop)

def pressure {n : ℕ} (r : ℝ) (x : SimpleCoordinates n) : WorkCoordinates n :=
  fun _ => x.1 / r

theorem pressureForm_apply {n : ℕ} (r : ℝ) (x d : SimpleCoordinates n) :
    pressureForm (pressure r x) d = d.1 + (x.1 / r) * workSum d.2 := by
  simp [pressureForm, pressure, Finset.mul_sum]

theorem pressure_support {n : ℕ} {r : ℝ}
    {x : SimpleCoordinates n} (hx : 0 < x.1) :
    SupportsAt {y | boundaryEnergy r x y.2 ≤ y.1} x (-pressureForm (pressure r x)) := by
  refine ⟨neg_ne_zero.mpr (pressureForm_ne_zero _), ?_⟩
  intro y hy
  have h := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp ((workSum x.2 - workSum y.2) / r)) hx.le
  change boundaryEnergy r x y.2 ≤ y.1 at hy
  unfold boundaryEnergy at hy
  simp only [LinearMap.neg_apply, pressureForm_apply]
  have ht := h.trans hy
  rw [mul_add, mul_one, sub_div, mul_sub] at ht
  have he (w : ℝ) : x.1 * (w / r) = x.1 / r * w := by ring
  rw [he, he] at ht
  linarith

theorem unique_support {n : ℕ} {r : ℝ}
    {x : SimpleCoordinates n}
    (f : SimpleCoordinates n →ₗ[ℝ] ℝ)
    (hf : SupportsAt {y | boundaryEnergy r x y.2 ≤ y.1} x f) :
    LinearMap.ker f = LinearMap.ker (pressureForm (pressure r x)) := by
  have hwork (v : WorkCoordinates n) : f (-(x.1 / r) * workSum v, v) = 0 := by
    let curve (t : ℝ) : SimpleCoordinates n :=
      (x.1 * Real.exp (t * (-workSum v / r)), x.2 + t • v)
    have h0 : curve 0 = x := by simp [curve]
    have hmax : IsMaxOn (f ∘ curve) univ 0 := by
      intro t _
      change f (curve t) ≤ f (curve 0)
      rw [h0]
      apply hf.2
      change boundaryEnergy r x (x.2 + t • v) ≤ _
      unfold boundaryEnergy curve
      rw [map_add, map_smul, smul_eq_mul]
      apply le_of_eq
      congr 2
      ring
    have hfirst : HasDerivAt (fun t : ℝ => x.1 * Real.exp (t * (-workSum v / r)))
        (-(x.1 / r) * workSum v) 0 := by
      have hlin : HasDerivAt (fun t : ℝ => t * (-workSum v / r)) (-workSum v / r) 0 := by
        simpa only [id, one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const (-workSum v / r)
      have hd : x.1 * (Real.exp (0 * (-workSum v / r)) * (-workSum v / r)) =
          -(x.1 / r) * workSum v := by
        rw [zero_mul, Real.exp_zero, one_mul]
        ring
      exact hd ▸ hlin.exp.const_mul x.1
    have hsecond : HasDerivAt (fun t : ℝ => x.2 + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x.2
    have hc : HasDerivAt curve (-(x.1 / r) * workSum v, v) 0 := hfirst.prodMk hsecond
    exact (hmax.isLocalMax univ_mem).hasDerivAt_eq_zero
      (f.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hc)
  have heval (d : SimpleCoordinates n) :
      f d = pressureForm (pressure r x) d * f (1, 0) := by
    have hd : d = pressureForm (pressure r x) d • (1, 0) +
        (-(x.1 / r) * workSum d.2, d.2) := by
      apply Prod.ext
      · simp [pressureForm_apply]
      · simp
    conv_lhs => rw [hd, map_add, map_smul, hwork, add_zero, smul_eq_mul]
  have henergy : f (1, 0) ≠ 0 := by
    intro hzero
    apply hf.1
    apply LinearMap.ext
    intro d
    change f d = 0
    rw [heval d, hzero, mul_zero]
  ext d
  change f d = 0 ↔ pressureForm (pressure r x) d = 0
  rw [heval d, mul_eq_zero]
  exact or_iff_left henergy

/-- The support and boundary axioms use the actual graph of the adiabat. -/
def system (n : ℕ) (r : ℝ) (hr : 0 < r) : SimpleSystem accessibility n where
  domain := Reservoir.domain n
  isOpen_domain := (Reservoir.system n r).isOpen_domain
  convex_domain := (Reservoir.system n r).convex_domain
  represent := represent r
  mixing x hx y hy a b hab := by
    have hab' : (a : ℝ) + b = 1 := congrArg (fun t : ℝ≥0 => (t : ℝ)) hab
    change 0 < x.1 at hx
    change 0 < y.1 at hy
    have hlog := strictConcaveOn_log_Ioi.concaveOn.2
      (show x.1 / r ∈ Ioi (0 : ℝ) from div_pos hx hr)
      (show y.1 / r ∈ Ioi (0 : ℝ) from div_pos hy hr)
      a.coe_nonneg b.coe_nonneg hab'
    change (a : ℝ) * Real.log (x.1 / r) + (b : ℝ) * Real.log (y.1 / r) ≤
      Real.log ((a : ℝ) * (x.1 / r) + (b : ℝ) * (y.1 / r)) at hlog
    change (a : ℝ) * r + (b : ℝ) * r = r ∧
      (a : ℝ) * entropy r x + (b : ℝ) * entropy r y ≤
        entropy r ((a : ℝ) • x + (b : ℝ) • y)
    constructor
    · rw [← add_mul, hab', one_mul]
    · have hU : ((a : ℝ) * x.1 + (b : ℝ) * y.1) / r =
          (a : ℝ) * (x.1 / r) + (b : ℝ) * (y.1 / r) := by ring
      simp only [entropy, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        map_add, map_smul, smul_eq_mul, hU]
      nlinarith [mul_le_mul_of_nonneg_left hlog hr.le]
  irreversible x hx := by
    have hx' : 0 < x.1 := hx
    have hy : 0 < x.1 + 1 := by linarith
    have hlt : entropy r x < entropy r (x.1 + 1, x.2) := by
      have h := Real.strictMonoOn_log (div_pos hx' hr) (div_pos hy hr)
        (show x.1 / r < (x.1 + 1) / r by gcongr; linarith)
      exact add_lt_add_left (mul_lt_mul_of_pos_left h hr) _
    refine ⟨(x.1 + 1, x.2), hy, ?_, ?_⟩
    · exact ⟨rfl, hlt.le⟩
    · exact fun h => (not_le_of_gt hlt) h.2
  pressure := pressure r
  pressure_support x hx := by
    rw [forwardSector_eq hr hx]
    exact Or.inr (pressure_support hx)
  unique_support x hx f hf := by
    rw [forwardSector_eq hr hx] at hf
    exact unique_support f hf
  pressure_locallyLipschitz := by
    apply ContDiffOn.locallyLipschitzOn (Reservoir.system n r).convex_domain
    exact (contDiff_pi.mpr fun _ => contDiff_fst.div_const r).contDiffOn
  boundary_pathConnected x hx := boundary_pathConnected hr hx

def scaled (n : ℕ) (r : ℝ) (hr : 0 < r) (a : ℝ≥0) (ha : 0 < a) :
    ScaledSimpleSystem (system n r hr) a where
  system := system n ((a : ℝ) * r) (mul_pos (NNReal.coe_pos.mpr ha) hr)
  domain_eq := (Reservoir.scaled n r a ha).domain_eq
  represent_eq x := by
    have ha' := NNReal.coe_ne_zero.mpr ha.ne'
    change (((a : ℝ) * r * Real.log (x.1 / ((a : ℝ) * r)) + workSum x.2,
        (a : ℝ) * r), x.1) =
      (((a : ℝ) * (r * Real.log (((a : ℝ)⁻¹ * x.1) / r) +
        workSum ((a : ℝ)⁻¹ • x.2)), (a : ℝ) * r), (a : ℝ) * ((a : ℝ)⁻¹ * x.1))
    rw [map_smul, smul_eq_mul, mul_inv_cancel_left₀ ha']
    have harg : x.1 / ((a : ℝ) * r) = ((a : ℝ)⁻¹ * x.1) / r := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [harg, mul_add, mul_inv_cancel_left₀ ha', mul_assoc]

/-- The unique maximizing split has equal energy per amount. -/
theorem allocation {r s u v : ℝ} (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) :
    r * Real.log (u / r) + s * Real.log (v / s) ≤
      (r + s) * Real.log ((u + v) / (r + s)) ∧
    (r * Real.log (u / r) + s * Real.log (v / s) =
      (r + s) * Real.log ((u + v) / (r + s)) ↔ u / r = v / s) := by
  have hrs := add_pos hr hs
  have ha := div_pos hr hrs
  have hb := div_pos hs hrs
  have hab : r / (r + s) + s / (r + s) = 1 := by rw [← add_div, div_self hrs.ne']
  have hu' : u / r ∈ Ioi (0 : ℝ) := div_pos hu hr
  have hv' : v / s ∈ Ioi (0 : ℝ) := div_pos hv hs
  have hmean : r / (r + s) * (u / r) + s / (r + s) * (v / s) =
      (u + v) / (r + s) := by
    field_simp
  have hnormalize (a b : ℝ) :
      (r + s) * (r / (r + s) * a + s / (r + s) * b) = r * a + s * b := by
    field_simp
  have hle := strictConcaveOn_log_Ioi.concaveOn.2 hu' hv' ha.le hb.le hab
  change r / (r + s) * Real.log (u / r) + s / (r + s) * Real.log (v / s) ≤
    Real.log (r / (r + s) * (u / r) + s / (r + s) * (v / s)) at hle
  rw [hmean] at hle
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hnormalize] using mul_le_mul_of_nonneg_left hle hrs.le
  · intro heq
    by_contra hne
    have hlt := strictConcaveOn_log_Ioi.2 hu' hv' hne ha hb hab
    change r / (r + s) * Real.log (u / r) + s / (r + s) * Real.log (v / s) <
      Real.log (r / (r + s) * (u / r) + s / (r + s) * (v / s)) at hlt
    rw [hmean] at hlt
    have hstrict := mul_lt_mul_of_pos_left hlt hrs
    rw [hnormalize, heq] at hstrict
    exact (lt_irrefl _ hstrict)
  · intro h
    have hE : (u + v) / (r + s) = v / s := by
      rw [← hmean, h, ← add_mul, hab, one_mul]
    rw [h, hE, add_mul]

def contact (n m : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    ThermalJoin accessibility (system n r hr).domain (system m s hs).domain
      (fun x => (system n r hr).represent x) (fun y => (system m s hs).represent y) where
  represent z := represent (r+s) (thermalJoinCoordinates n m z)
  contact x y := by
    change (r + s = r + s) ∧ entropy r x.val + entropy s y.val ≤
      entropy (r+s) (x.val.1 + y.val.1, Fin.append x.val.2 y.val.2)
    refine ⟨rfl, ?_⟩
    simp only [entropy, workSum_append]
    linarith [(allocation hr hs x.property y.property).1]
  splitting z := by
    obtain ⟨u, v, hu, hv, huv⟩ := z.property
    have hz : 0 < z.val.1 := huv ▸ add_pos hu hv
    let θ := z.val.1 / (r+s)
    have hθ : 0 < θ := div_pos hz (add_pos hr hs)
    have hsplit : r * θ + s * θ = z.val.1 := by
      rw [← add_mul]
      dsimp only [θ]
      field_simp
    have heq : (r * θ) / r = (s * θ) / s := by
      rw [mul_div_cancel_left₀ _ hr.ne', mul_div_cancel_left₀ _ hs.ne']
    have hru := mul_pos hr hθ
    have hsv := mul_pos hs hθ
    refine ⟨⟨(r*θ, z.val.2.1), hru⟩, ⟨(s*θ, z.val.2.2), hsv⟩, ?_, ?_⟩
    · exact Subtype.ext (Prod.ext hsplit rfl)
    · change (r + s = r + s) ∧
        entropy (r+s) (z.val.1, Fin.append z.val.2.1 z.val.2.2) ≤
          entropy r (r*θ, z.val.2.1) + entropy s (s*θ, z.val.2.2)
      refine ⟨rfl, ?_⟩
      have h := (allocation hr hs hru hsv).2.mpr heq
      rw [hsplit] at h
      simp only [entropy, workSum_append]
      linarith

theorem equilibrium_iff (n m : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (x : (system n r hr).domain) (y : (system m s hs).domain) :
    (contact n m r s hr hs).Equilibrium x y ↔ x.val.1 / r = y.val.1 / s := by
  change (r + s = r + s ∧
    entropy (r+s) (x.val.1 + y.val.1, Fin.append x.val.2 y.val.2) ≤
      entropy r x.val + entropy s y.val) ↔ _
  simp only [true_and, entropy, workSum_append]
  obtain ⟨hle, heq⟩ := allocation hr hs x.property y.property
  constructor
  · intro h
    exact heq.mp (le_antisymm hle (by linarith))
  · intro h
    linarith [heq.mpr h]

def join (n m : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    SimpleThermalJoin (system n r hr) (system m s hs) where
  thermalJoin := contact n m r s hr hs
  system := system (n + m) (r + s) (add_pos hr hs)
  domain_eq := Reservoir.join_domain n m r s
  represent_eq _ := rfl

def Admitted {n : ℕ} (S : SimpleSystem accessibility n) : Prop :=
  0 < n ∧ ∃ r : ℝ, ∃ hr : 0 < r, S = system n r hr

def memberScale {n : ℕ} (S : SimpleSystem accessibility n) (hS : Admitted S)
    (a : ℝ≥0) (ha : 0 < a) :
    {D : ScaledSimpleSystem S a // Admitted D.system} := by
  let r := hS.2.choose
  have hr : 0 < r := hS.2.choose_spec.choose
  have heq : S = system n r hr := hS.2.choose_spec.choose_spec
  rw [heq]
  refine ⟨scaled n r hr a ha, hS.1, (a : ℝ) * r, mul_pos (NNReal.coe_pos.mpr ha) hr, ?_⟩
  rfl

def memberJoin {n m : ℕ} (S : SimpleSystem accessibility n) (T : SimpleSystem accessibility m)
    (hS : Admitted S) (hT : Admitted T) :
    {J : SimpleThermalJoin S T // Admitted J.system ∧
      ∀ x : S.domain, ∀ y : T.domain,
        thermal (S.represent x) (T.represent y) ↔ J.thermalJoin.Equilibrium x y} := by
  let r := hS.2.choose
  have hr : 0 < r := hS.2.choose_spec.choose
  have heq : S = system n r hr := hS.2.choose_spec.choose_spec
  let s := hT.2.choose
  have hs : 0 < s := hT.2.choose_spec.choose
  have heq' : T = system m s hs := hT.2.choose_spec.choose_spec
  rw [heq, heq']
  refine ⟨join n m r s hr hs, ⟨Nat.add_pos_left hS.1 m, r+s, add_pos hr hs, rfl⟩, ?_⟩
  intro x y
  exact (equilibrium_iff n m r s hr hs x y).symm

/-- Full thermal axioms, including transversality by work changes at fixed energy. -/
def family : ThermalFamily accessibility where
  admitted := Admitted
  scale S hS a ha := (memberScale S hS a ha).val
  scale_admitted S hS a ha := (memberScale S hS a ha).property
  join S T hS hT := (memberJoin S T hS hT).val
  join_admitted S T hS hT := (memberJoin S T hS hT).property.1
  thermal := thermal
  thermal_iff S T hS hT := (memberJoin S T hS hT).property.2
  thermal_symm _ _ _ _ _ _ h := Eq.symm h
  zeroth_law _ _ _ _ _ _ _ _ _ h k := Eq.trans h k
  scaled_copy S hS x a ha ha₁ := by
    obtain ⟨_, r, hr, rfl⟩ := hS
    have hb : 0 < 1 - a := tsub_pos_of_lt ha₁
    change ((↑(1 - a) : ℝ) * x.val.1) / ((↑(1-a) : ℝ) * r) =
      ((a : ℝ) * x.val.1) / ((a : ℝ) * r)
    rw [mul_div_mul_left _ _ (NNReal.coe_ne_zero.mpr hb.ne'),
      mul_div_mul_left _ _ (NNReal.coe_ne_zero.mpr ha.ne')]
  transversality {n} S hS x := by
    obtain ⟨hn, r, hr, rfl⟩ := hS
    let e : WorkCoordinates n := Pi.single ⟨0, hn⟩ 1
    have he : workSum e = 1 := by simp [e]
    let a : (system n r hr).domain := ⟨(x.val.1, x.val.2 - e), x.property⟩
    let b : (system n r hr).domain := ⟨(x.val.1, x.val.2 + e), x.property⟩
    have ha : entropy r a.val = entropy r x.val - 1 := by
      simp only [a, entropy, map_sub, he]
      ring
    have hb : entropy r b.val = entropy r x.val + 1 := by
      simp only [b, entropy, map_add, he]
      ring
    refine ⟨a, b, rfl, ?_, ?_⟩
    · change (r = r ∧ entropy r a.val ≤ entropy r x.val) ∧
        ¬ (r = r ∧ entropy r x.val ≤ entropy r a.val)
      rw [ha]
      exact ⟨⟨rfl, by linarith⟩, fun h => by linarith [h.2]⟩
    · change (r = r ∧ entropy r x.val ≤ entropy r b.val) ∧
        ¬ (r = r ∧ entropy r b.val ≤ entropy r x.val)
      rw [hb]
      exact ⟨⟨rfl, by linarith⟩, fun h => by linarith [h.2]⟩

theorem system_admitted {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    family.admitted (system n r hr) := ⟨hn, r, hr, rfl⟩

theorem system_nonempty (n : ℕ) (r : ℝ) (hr : 0 < r) : (system n r hr).domain.Nonempty :=
  Reservoir.system_nonempty n r

theorem family_nontrivial : family.Nontrivial :=
  ⟨1, system 1 1 one_pos, system_admitted (by decide) one_pos, system_nonempty 1 1 one_pos⟩

/-- The joined state achieves the maximum over the actual admissible splits. -/
theorem join_entropy_maximum (n m : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (z : joinedDomain (system n r hr).domain (system m s hs).domain) :
    ∃ x : (system n r hr).domain, ∃ y : (system m s hs).domain,
      joinedState x y = z ∧ x.val.1 / r = y.val.1 / s ∧
      entropy (r + s) (thermalJoinCoordinates n m z) = entropy r x.val + entropy s y.val ∧
      ∀ u v, joinedState u v = z →
        entropy r u.val + entropy s v.val ≤ entropy (r + s) (thermalJoinCoordinates n m z) := by
  obtain ⟨x, y, hz, heq, hval, hmax⟩ :=
    (contact n m r s hr hs).entropy_maximum stateEntropy stateEntropy_mono z
  exact ⟨x, y, hz, (equilibrium_iff n m r s hr hs x y).mp heq, hval, hmax⟩

/-- An admitted joined system has states at temperatures one and two. -/
theorem joined_nonthermal :
    family.admitted (join 1 1 1 1 one_pos one_pos).system ∧
    ∃ x y : (join 1 1 1 1 one_pos one_pos).system.domain,
      ¬ family.thermal ((join 1 1 1 1 one_pos one_pos).system.represent x)
        ((join 1 1 1 1 one_pos one_pos).system.represent y) := by
  refine ⟨system_admitted (by decide) (add_pos one_pos one_pos),
    ⟨(2, 0), by norm_num [join, system, Reservoir.domain]⟩,
    ⟨(4, 0), by norm_num [join, system, Reservoir.domain]⟩, ?_⟩
  change ¬ (2 : ℝ) / (1 + 1) = 4 / (1 + 1)
  norm_num

/-- The physical calibrator theorem applies to the populated family. -/
theorem exists_calibrator (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    ∃ a b : (system n r hr).domain, ∃ c d : (system m s hs).domain,
      IsEntropyCalibrator accessibility
        ((system n r hr).represent a) ((system n r hr).represent b)
        ((system m s hs).represent c) ((system m s hs).represent d) :=
  family.hasCalibrators_of_axioms _ _ (system_admitted hn hr) (system_admitted hm hs)
    (system_nonempty n r hr) (system_nonempty m s hs)

end ProjectAInos.Thermodynamics.Physical.LogarithmicThermal
