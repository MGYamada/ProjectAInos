/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import ProjectAInos.QuantumFieldTheory.SmearedField
public import ProjectAInos.QuantumMechanics.Pauli
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Matrix.Hermitian

/-!
# Causal support witnesses and a noncommuting local field

Bump tests have closed balls as their closed supports, so spacelike separation
of two tests is decided by coordinates. A two-point field
`φ(f) = f(p) A + f(q) B` with symmetric `A` and `B` that do not commute is local
exactly when `p - q` is not spacelike. Its locality proof uses the separation
hypothesis, and the Pauli instance has an explicit nonzero commutator.

These are regression models for the locality predicate. They have no vacuum,
no covariance and no spectrum condition, and are not Wightman fields.
-/

@[expose] public section
noncomputable section

open scoped SchwartzMap

namespace ProjectAInos.QuantumFieldTheory

open SpecialRelativity SmoothGeometry SmoothGeometry.Minkowski

/-! ### Causal predicates in coordinates -/

/-- The interval with time first: positive on timelike vectors. -/
theorem intervalQuadratic_spacetime (v : Spacetime) :
    intervalQuadratic v = v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 := by
  rw [intervalQuadratic_apply]
  change minkowskiForm .timePositive 3 v v = _
  rw [minkowskiForm_apply]
  change ∑ i : Fin 4, lorentzSign .timePositive i * (v i * v i) = _
  rw [Fin.sum_univ_four]
  simp [lorentzSign]
  ring

theorem not_spacelike_zero {d : ℕ} : ¬ Spacelike (0 : MinkowskiModel d) := by
  simp [Spacelike]

@[simp] theorem spacelike_neg_iff {d : ℕ} (v : MinkowskiModel d) :
    Spacelike (-v) ↔ Spacelike v := by
  simp [Spacelike]

theorem continuous_intervalQuadratic {d : ℕ} :
    Continuous (fun v : MinkowskiModel d => intervalQuadratic v) :=
  (pair (d := d)).continuous₂.comp (continuous_id.prodMk continuous_id)

/-- Spacelike vectors form an open set. -/
theorem isOpen_spacelike {d : ℕ} : IsOpen {v : MinkowskiModel d | Spacelike v} :=
  isOpen_lt continuous_intervalQuadratic continuous_const

/-- The point at time `t` on the time axis. -/
def timePoint (t : ℝ) : Spacetime := Pi.single 0 t

/-- The point at coordinate `a` on the first spatial axis. -/
def spacePoint (a : ℝ) : Spacetime := Pi.single 1 a

theorem intervalQuadratic_timePoint (t : ℝ) : intervalQuadratic (timePoint t) = t ^ 2 := by
  simp [intervalQuadratic_spacetime, timePoint]

theorem intervalQuadratic_spacePoint (a : ℝ) : intervalQuadratic (spacePoint a) = -a ^ 2 := by
  simp [intervalQuadratic_spacetime, spacePoint]

theorem timelike_timePoint {t : ℝ} (ht : t ≠ 0) : Timelike (timePoint t) := by
  rw [Timelike, intervalQuadratic_timePoint]
  positivity

theorem spacelike_spacePoint {a : ℝ} (ha : a ≠ 0) : Spacelike (spacePoint a) := by
  rw [Spacelike, intervalQuadratic_spacePoint]
  have : 0 < a ^ 2 := by positivity
  linarith

theorem not_spacelike_timePoint (t : ℝ) : ¬ Spacelike (timePoint t) := by
  rw [Spacelike, intervalQuadratic_timePoint]
  exact not_lt.mpr (sq_nonneg t)

/-! ### Spacelike separation of tests -/

theorem SpacelikeSeparated.symm {f g : Test} (h : SpacelikeSeparated f g) :
    SpacelikeSeparated g f := fun y hy x hx => by
  rw [← neg_sub, spacelike_neg_iff]
  exact h x hx y hy

theorem spacelikeSeparated_comm (f g : Test) :
    SpacelikeSeparated f g ↔ SpacelikeSeparated g f :=
  ⟨SpacelikeSeparated.symm, SpacelikeSeparated.symm⟩

@[simp] theorem tsupport_conjugate (f : Test) : tsupport (conjugate f) = tsupport f := by
  have h : Function.support (conjugate f) = Function.support f := by
    ext x
    simp
  rw [tsupport, tsupport, h]

@[simp] theorem spacelikeSeparated_conjugate_left (f g : Test) :
    SpacelikeSeparated (conjugate f) g ↔ SpacelikeSeparated f g := by
  simp [SpacelikeSeparated]

@[simp] theorem spacelikeSeparated_conjugate_right (f g : Test) :
    SpacelikeSeparated f (conjugate g) ↔ SpacelikeSeparated f g := by
  simp [SpacelikeSeparated]

/-- Tests whose closed supports meet are not spacelike separated. -/
theorem not_spacelikeSeparated_of_mem {f g : Test} {x : Spacetime}
    (hf : x ∈ tsupport f) (hg : x ∈ tsupport g) : ¬ SpacelikeSeparated f g := fun h =>
  not_spacelike_zero (sub_self x ▸ h x hf x hg)

/-- Only the zero test is spacelike separated from itself. -/
theorem SpacelikeSeparated.eq_zero {f : Test} (h : SpacelikeSeparated f f) : f = 0 := by
  ext x
  by_contra hx
  exact not_spacelikeSeparated_of_mem (subset_tsupport _ hx) (subset_tsupport _ hx) h

/-! ### Bump tests -/

/-- A smooth test that is one at `p` and whose closed support is the closed ball
of radius `r` about `p`, in the supremum norm of the coordinates. -/
def bump (p : Spacetime) (r : ℝ) (hr : 0 < r) : Test :=
  let φ : ContDiffBump p := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  (φ.hasCompactSupport.comp_left (g := Complex.ofRealCLM) (map_zero _)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp φ.contDiff)

theorem bump_apply (p : Spacetime) (r : ℝ) (hr : 0 < r) (x : Spacetime) :
    bump p r hr x =
      (((⟨r / 2, r, half_pos hr, half_lt_self hr⟩ : ContDiffBump p) x : ℝ) : ℂ) := rfl

@[simp] theorem bump_self (p : Spacetime) (r : ℝ) (hr : 0 < r) : bump p r hr p = 1 := by
  rw [bump_apply, ContDiffBump.one_of_mem_closedBall]
  · rfl
  · exact Metric.mem_closedBall_self (half_pos hr).le

@[simp] theorem tsupport_bump (p : Spacetime) (r : ℝ) (hr : 0 < r) :
    tsupport (bump p r hr) = Metric.closedBall p r := by
  have h : Function.support (bump p r hr) =
      Function.support (⟨r / 2, r, half_pos hr, half_lt_self hr⟩ : ContDiffBump p) := by
    ext x
    simp [bump_apply]
  rw [tsupport, h]
  exact ContDiffBump.tsupport_eq _

theorem self_mem_tsupport_bump (p : Spacetime) (r : ℝ) (hr : 0 < r) :
    p ∈ tsupport (bump p r hr) := by
  rw [tsupport_bump]
  exact Metric.mem_closedBall_self hr.le

theorem bump_eq_zero {p x : Spacetime} {r : ℝ} (hr : 0 < r)
    (hx : x ∉ Metric.closedBall p r) : bump p r hr x = 0 :=
  image_eq_zero_of_notMem_tsupport (by rwa [tsupport_bump])

/-- Bump tests are separated when every pair of points of the two balls is. -/
theorem spacelikeSeparated_bump_iff (p q : Spacetime) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    SpacelikeSeparated (bump p r hr) (bump q s hs) ↔
      ∀ x ∈ Metric.closedBall p r, ∀ y ∈ Metric.closedBall q s, Spacelike (x - y) := by
  simp [SpacelikeSeparated]

/-- Centres whose difference is not spacelike never give separated bump tests. -/
theorem not_spacelikeSeparated_bump {p q : Spacetime} (h : ¬ Spacelike (p - q))
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    ¬ SpacelikeSeparated (bump p r hr) (bump q s hs) := fun hsep =>
  h (hsep p (self_mem_tsupport_bump p r hr) q (self_mem_tsupport_bump q s hs))

/-- Spacelike separated centres have spacelike separated small bump tests. -/
theorem exists_spacelikeSeparated_bump {p q : Spacetime} (h : Spacelike (p - q)) :
    ∃ (r : ℝ) (hr : 0 < r), SpacelikeSeparated (bump p r hr) (bump q r hr) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_spacelike (p - q) h
  refine ⟨ε / 4, by positivity, ?_⟩
  rw [spacelikeSeparated_bump_iff]
  intro x hx y hy
  apply hball
  rw [Metric.mem_ball]
  calc dist (x - y) (p - q) ≤ dist x p + dist y q := dist_sub_sub_le x y p q
    _ ≤ ε / 4 + ε / 4 := add_le_add (Metric.mem_closedBall.mp hx) (Metric.mem_closedBall.mp hy)
    _ < ε := by linarith

theorem abs_sub_le_of_mem_closedBall {p x : Spacetime} {r : ℝ} (hr : 0 ≤ r)
    (hx : x ∈ Metric.closedBall p r) (i : Fin 4) : |x i - p i| ≤ r := by
  have h := (dist_pi_le_iff hr).mp (Metric.mem_closedBall.mp hx) i
  rwa [Real.dist_eq] at h

/-- Unit bumps at the origin and five units along a spatial axis are spacelike
separated: every pair of support points has a spacelike difference. -/
theorem bump_spacePoint_spacelikeSeparated :
    SpacelikeSeparated (bump 0 1 one_pos) (bump (spacePoint 5) 1 one_pos) := by
  rw [spacelikeSeparated_bump_iff]
  intro x hx y hy
  have hx0 := abs_le.mp (abs_sub_le_of_mem_closedBall zero_le_one hx 0)
  have hx1 := abs_le.mp (abs_sub_le_of_mem_closedBall zero_le_one hx 1)
  have hy0 := abs_le.mp (abs_sub_le_of_mem_closedBall zero_le_one hy 0)
  have hy1 := abs_le.mp (abs_sub_le_of_mem_closedBall zero_le_one hy 1)
  simp only [spacePoint, Pi.zero_apply, sub_zero, Pi.single_eq_same, ne_eq, zero_ne_one,
    not_false_eq_true, Pi.single_eq_of_ne] at hx0 hx1 hy0 hy1
  rw [Spacelike, intervalQuadratic_spacetime]
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (x 2 - y 2), sq_nonneg (x 3 - y 3)]

/-- Unit bumps at the origin and ten units along the time axis: every pair of
support points has a timelike difference. -/
theorem bump_timePoint_timelike (x y : Spacetime) (hx : x ∈ tsupport (bump 0 1 one_pos))
    (hy : y ∈ tsupport (bump (timePoint 10) 1 one_pos)) : Timelike (x - y) := by
  rw [tsupport_bump] at hx hy
  have hx' := fun i => abs_le.mp (abs_sub_le_of_mem_closedBall zero_le_one hx i)
  have hy' := fun i => abs_le.mp (abs_sub_le_of_mem_closedBall zero_le_one hy i)
  have hx0 := hx' 0
  have hx1 := hx' 1
  have hx2 := hx' 2
  have hx3 := hx' 3
  have hy0 := hy' 0
  have hy1 := hy' 1
  have hy2 := hy' 2
  have hy3 := hy' 3
  simp [timePoint] at hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3
  rw [Timelike, intervalQuadratic_spacetime]
  simp only [Pi.sub_apply]
  nlinarith

/-- The same two tests are therefore not spacelike separated. -/
theorem bump_timePoint_not_spacelikeSeparated :
    ¬ SpacelikeSeparated (bump 0 1 one_pos) (bump (timePoint 10) 1 one_pos) :=
  not_spacelikeSeparated_bump
    (by rw [zero_sub, spacelike_neg_iff]; exact not_spacelike_timePoint 10) 1 1 one_pos one_pos

/-! ### The two-point field -/

section TwoPoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The smearing map `f ↦ f(p) A + f(q) B` on the full domain. -/
def twoPointSmear (p q : Spacetime) (A B : H →ₗ[ℂ] H) :
    Test →ₗ[ℂ] ((⊤ : Submodule ℂ H) →ₗ[ℂ] (⊤ : Submodule ℂ H)) :=
  (Submodule.topEquiv (R := ℂ) (M := H)).symm.conj.toLinearMap ∘ₗ
    ((TemperedDistribution.delta p).toLinearMap.smulRight A +
      (TemperedDistribution.delta q).toLinearMap.smulRight B)

@[simp] theorem twoPointSmear_coe (p q : Spacetime) (A B : H →ₗ[ℂ] H) (f : Test)
    (ψ : (⊤ : Submodule ℂ H)) :
    (twoPointSmear p q A B f ψ : H) = f p • A ψ + f q • B ψ := rfl

/-- A Hermitian field with two insertion points: `φ(f) = f(p) A + f(q) B` for
symmetric everywhere-defined `A` and `B`. The common domain is the whole space. -/
def twoPointField (p q : Spacetime) (A B : H →ₗ[ℂ] H) (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) : ScalarField H where
  domain := ⊤
  dense := by rw [Submodule.top_coe]; exact dense_univ
  smear := twoPointSmear p q A B
  continuous_orbit ψ := by
    simp only [twoPointSmear_coe]
    exact ((TemperedDistribution.delta p).continuous.smul continuous_const).add
      ((TemperedDistribution.delta q).continuous.smul continuous_const)
  hermitian f ψ χ := by
    simp only [twoPointSmear_coe, conjugate_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right]
    rw [hA (ψ : H) (χ : H), hB (ψ : H) (χ : H)]
    rfl

variable (p q : Spacetime) (A B : H →ₗ[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)

@[simp] theorem twoPointField_smear_coe (f : Test) (ψ : (twoPointField p q A B hA hB).domain) :
    ((twoPointField p q A B hA hB).smear f ψ : H) = f p • A ψ + f q • B ψ := rfl

/-- The commutator of two insertions is a multiple of the commutator of `A` and `B`. -/
theorem twoPointField_commutator (f g : Test) (ψ : (twoPointField p q A B hA hB).domain) :
    ((twoPointField p q A B hA hB).smear f ((twoPointField p q A B hA hB).smear g ψ) : H) -
        ((twoPointField p q A B hA hB).smear g ((twoPointField p q A B hA hB).smear f ψ) : H) =
      (f p * g q - f q * g p) • (A (B ψ) - B (A ψ)) := by
  simp only [twoPointField_smear_coe, map_add, map_smul]
  module

variable {p q A B}

/-- If the insertion points are not spacelike to each other the field is local.
Each term of the commutator needs one point in each support. -/
theorem twoPointField_isLocal (h : ¬ Spacelike (p - q)) :
    (twoPointField p q A B hA hB).IsLocal := by
  intro f g hfg ψ
  have h1 : f p * g q = 0 := by
    by_contra hne
    obtain ⟨hfp, hgq⟩ := mul_ne_zero_iff.mp hne
    exact h (hfg p (subset_tsupport _ hfp) q (subset_tsupport _ hgq))
  have h2 : f q * g p = 0 := by
    by_contra hne
    obtain ⟨hfq, hgp⟩ := mul_ne_zero_iff.mp hne
    apply h
    rw [← neg_sub, spacelike_neg_iff]
    exact hfg q (subset_tsupport _ hfq) p (subset_tsupport _ hgp)
  apply Subtype.ext
  rw [← sub_eq_zero, twoPointField_commutator, h1, h2, sub_zero, zero_smul]

/-- A bump at `p` and a test supported away from it see only the commutator of
`A` and `B`. -/
theorem twoPointField_commutator_bump {r : ℝ} (hr : 0 < r) (hq : q ∉ Metric.closedBall p r)
    (g : Test) (hg : g q = 1) (ψ : (twoPointField p q A B hA hB).domain) :
    ((twoPointField p q A B hA hB).smear (bump p r hr)
          ((twoPointField p q A B hA hB).smear g ψ) : H) -
        ((twoPointField p q A B hA hB).smear g
          ((twoPointField p q A B hA hB).smear (bump p r hr) ψ) : H) =
      A (B ψ) - B (A ψ) := by
  rw [twoPointField_commutator, bump_self, bump_eq_zero hr hq, hg]
  simp

/-- If `A` and `B` do not commute, spacelike insertion points violate locality. -/
theorem twoPointField_not_isLocal (hAB : A ∘ₗ B ≠ B ∘ₗ A) (h : Spacelike (p - q)) :
    ¬ (twoPointField p q A B hA hB).IsLocal := by
  intro hloc
  obtain ⟨r, hr, hsep⟩ := exists_spacelikeSeparated_bump h
  have hq : q ∉ Metric.closedBall p r := fun hq =>
    not_spacelikeSeparated_of_mem (by rwa [tsupport_bump]) (self_mem_tsupport_bump q r hr) hsep
  apply hAB
  ext v
  have hv := congrArg Subtype.val (hloc _ _ hsep ⟨v, Submodule.mem_top⟩)
  rw [← sub_eq_zero] at hv
  rw [twoPointField_commutator_bump hA hB hr hq _ (bump_self q r hr)] at hv
  exact sub_eq_zero.mp hv

/-- Locality of the two-point field is the causal relation of its two points. -/
theorem twoPointField_isLocal_iff (hAB : A ∘ₗ B ≠ B ∘ₗ A) :
    (twoPointField p q A B hA hB).IsLocal ↔ ¬ Spacelike (p - q) :=
  ⟨fun hloc h => twoPointField_not_isLocal hA hB hAB h hloc, twoPointField_isLocal hA hB⟩

end TwoPoint

/-! ### The Pauli instance -/

open QuantumMechanics

/-- The Pauli matrices as operators on the qubit Hilbert space. -/
def pauliOperator (axis : Fin 3) : Qubit.Hilbert →ₗ[ℂ] Qubit.Hilbert :=
  Matrix.toEuclideanLin (Qubit.pauli axis)

theorem pauliOperator_isSymmetric (axis : Fin 3) : (pauliOperator axis).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (Qubit.pauli_isHermitian axis)

/-- `[σ_x, σ_z]` sends the first basis vector to twice the second. -/
theorem pauliOperator_commutator :
    pauliOperator 0 (pauliOperator 2 (EuclideanSpace.single 0 1)) -
        pauliOperator 2 (pauliOperator 0 (EuclideanSpace.single 0 1)) =
      EuclideanSpace.single 1 2 := by
  ext i
  fin_cases i <;>
    simp [pauliOperator, Qubit.pauli, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two]
  norm_num

theorem pauliOperator_not_commute :
    pauliOperator 0 ∘ₗ pauliOperator 2 ≠ pauliOperator 2 ∘ₗ pauliOperator 0 := by
  intro h
  have h2 := pauliOperator_commutator
  rw [← LinearMap.comp_apply, h, LinearMap.comp_apply, sub_self] at h2
  have h3 := congrArg (fun v : Qubit.Hilbert => v 1) h2
  simp at h3

/-- The Pauli two-point field `φ(f) = f(p) σ_x + f(q) σ_z` on the qubit space. -/
def pauliField (p q : Spacetime) : ScalarField Qubit.Hilbert :=
  twoPointField p q (pauliOperator 0) (pauliOperator 2) (pauliOperator_isSymmetric 0)
    (pauliOperator_isSymmetric 2)

theorem pauliField_isLocal_iff (p q : Spacetime) :
    (pauliField p q).IsLocal ↔ ¬ Spacelike (p - q) :=
  twoPointField_isLocal_iff _ _ pauliOperator_not_commute

/-- Timelike insertion points: the field is local. -/
theorem pauliField_timePoint_isLocal : (pauliField 0 (timePoint 10)).IsLocal :=
  (pauliField_isLocal_iff 0 (timePoint 10)).mpr
    (by rw [zero_sub, spacelike_neg_iff]; exact not_spacelike_timePoint 10)

/-- Spacelike insertion points: the field is not local. -/
theorem pauliField_spacePoint_not_isLocal : ¬ (pauliField 0 (spacePoint 5)).IsLocal := fun h =>
  (pauliField_isLocal_iff 0 (spacePoint 5)).mp h
    (by rw [zero_sub, spacelike_neg_iff]; exact spacelike_spacePoint (by norm_num))

/-- The first basis vector of the qubit space, in the domain of a Pauli field. -/
def pauliUp (p q : Spacetime) : (pauliField p q).domain :=
  ⟨EuclideanSpace.single 0 1, Submodule.mem_top⟩

theorem timePoint_notMem_closedBall : timePoint 10 ∉ Metric.closedBall (0 : Spacetime) 1 := by
  intro h
  have h0 := abs_sub_le_of_mem_closedBall zero_le_one h 0
  simp [timePoint] at h0

theorem spacePoint_notMem_closedBall : spacePoint 5 ∉ Metric.closedBall (0 : Spacetime) 1 := by
  intro h
  have h1 := abs_sub_le_of_mem_closedBall zero_le_one h 1
  simp [spacePoint] at h1

/-- The local Pauli field has a nonzero commutator on two timelike separated
bump tests, so its insertions do not commute in general. -/
theorem pauliField_timePoint_commutator :
    ((pauliField 0 (timePoint 10)).smear (bump 0 1 one_pos)
          ((pauliField 0 (timePoint 10)).smear (bump (timePoint 10) 1 one_pos)
            (pauliUp 0 (timePoint 10))) : Qubit.Hilbert) -
        ((pauliField 0 (timePoint 10)).smear (bump (timePoint 10) 1 one_pos)
          ((pauliField 0 (timePoint 10)).smear (bump 0 1 one_pos)
            (pauliUp 0 (timePoint 10))) : Qubit.Hilbert) =
      EuclideanSpace.single 1 2 :=
  (twoPointField_commutator_bump _ _ one_pos timePoint_notMem_closedBall _
    (bump_self _ 1 one_pos) _).trans pauliOperator_commutator

/-- With spacelike insertion points the same commutator is nonzero on two
spacelike separated bump tests: an explicit violation of locality. -/
theorem pauliField_spacePoint_commutator :
    ((pauliField 0 (spacePoint 5)).smear (bump 0 1 one_pos)
          ((pauliField 0 (spacePoint 5)).smear (bump (spacePoint 5) 1 one_pos)
            (pauliUp 0 (spacePoint 5))) : Qubit.Hilbert) -
        ((pauliField 0 (spacePoint 5)).smear (bump (spacePoint 5) 1 one_pos)
          ((pauliField 0 (spacePoint 5)).smear (bump 0 1 one_pos)
            (pauliUp 0 (spacePoint 5))) : Qubit.Hilbert) =
      EuclideanSpace.single 1 2 :=
  (twoPointField_commutator_bump _ _ one_pos spacePoint_notMem_closedBall _
    (bump_self _ 1 one_pos) _).trans pauliOperator_commutator

theorem single_one_two_ne_zero : (EuclideanSpace.single 1 2 : Qubit.Hilbert) ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : Qubit.Hilbert => v 1) h
  simp at h1

/-- The two insertions of the local Pauli field do not commute on the common
domain. The tests are not spacelike separated, so locality is not contradicted. -/
theorem pauliField_timePoint_ne :
    (pauliField 0 (timePoint 10)).smear (bump 0 1 one_pos)
        ((pauliField 0 (timePoint 10)).smear (bump (timePoint 10) 1 one_pos)
          (pauliUp 0 (timePoint 10))) ≠
      (pauliField 0 (timePoint 10)).smear (bump (timePoint 10) 1 one_pos)
        ((pauliField 0 (timePoint 10)).smear (bump 0 1 one_pos)
          (pauliUp 0 (timePoint 10))) := by
  intro h
  have h2 := pauliField_timePoint_commutator
  rw [h, sub_self] at h2
  exact single_one_two_ne_zero h2.symm

/-- With spacelike insertion points two spacelike separated tests have
insertions that do not commute. -/
theorem pauliField_spacePoint_ne :
    (pauliField 0 (spacePoint 5)).smear (bump 0 1 one_pos)
        ((pauliField 0 (spacePoint 5)).smear (bump (spacePoint 5) 1 one_pos)
          (pauliUp 0 (spacePoint 5))) ≠
      (pauliField 0 (spacePoint 5)).smear (bump (spacePoint 5) 1 one_pos)
        ((pauliField 0 (spacePoint 5)).smear (bump 0 1 one_pos)
          (pauliUp 0 (spacePoint 5))) := by
  intro h
  have h2 := pauliField_spacePoint_commutator
  rw [h, sub_self] at h2
  exact single_one_two_ne_zero h2.symm

end ProjectAInos.QuantumFieldTheory
