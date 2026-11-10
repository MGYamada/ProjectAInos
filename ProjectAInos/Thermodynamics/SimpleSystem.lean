module

public import ProjectAInos.Thermodynamics.ForwardSector
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Simple systems and the interior of forward sectors

Supporting hyperplanes are unoriented: uniqueness identifies their kernels,
not a chosen sign of their defining linear forms. The pressure form is
normalized by its energy coefficient, which equals one. Boundary connectedness
refers to the boundary relative to the open equilibrium domain.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical

/-- A nonzero linear functional whose maximum over a set is attained at an anchor. -/
def SupportsAt {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : Set E) (x : E) (f : E →ₗ[ℝ] ℝ) : Prop :=
  f ≠ 0 ∧ ∀ y ∈ C, f y ≤ f x

/-- A convex set of empty interior lies in an affine hyperplane through each of
its points. No nontriviality assumption on the ambient space is needed. -/
theorem exists_annihilator_of_empty_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} (hC : Convex ℝ C) {x : E} (hx : x ∈ C)
    (hinterior : ¬ (interior C).Nonempty) :
    ∃ f : E →ₗ[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ C, f (y - x) = 0 := by
  have hspan : affineSpan ℝ C ≠ ⊤ := by
    intro h
    exact hinterior (hC.interior_nonempty_iff_affineSpan_eq_top.mpr h)
  have hdir : (affineSpan ℝ C).direction < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro heq
    exact hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty
      ⟨x, subset_affineSpan ℝ C hx⟩).mp heq)
  obtain ⟨f, hf, hker⟩ := (affineSpan ℝ C).direction.exists_le_ker_of_lt_top hdir
  refine ⟨f, hf, fun y hy => ?_⟩
  exact hker (AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hy)
    (subset_affineSpan ℝ C hx))

/-- Finite-dimensional supporting separation, also for convex sets with empty
ambient interior. The anchor must belong to the set. -/
theorem exists_support_of_not_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} (hC : Convex ℝ C) {x : E} (hx : x ∈ C)
    (hinterior : x ∉ interior C) :
    ∃ f : E →ₗ[ℝ] ℝ, SupportsAt C x f := by
  by_cases hnonempty : (interior C).Nonempty
  · obtain ⟨f, hf, hsupport⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hC hinterior hnonempty
    refine ⟨f.toLinearMap, ?_, hsupport⟩
    intro hzero
    apply hf
    ext y
    exact congrArg (fun g : E →ₗ[ℝ] ℝ => g y) hzero
  · obtain ⟨f, hf, hvanish⟩ := exists_annihilator_of_empty_interior hC hx hnonempty
    refine ⟨f, hf, fun y hy => le_of_eq ?_⟩
    exact sub_eq_zero.mp (by simpa only [map_sub] using hvanish y hy)

abbrev WorkCoordinates (n : ℕ) := Fin n → ℝ
abbrev SimpleCoordinates (n : ℕ) := ℝ × WorkCoordinates n

/-- The normalized finite-slope pressure form: `dU + Σ Pᵢ dVᵢ`. -/
def pressureForm {n : ℕ} (p : WorkCoordinates n) : SimpleCoordinates n →ₗ[ℝ] ℝ where
  toFun x := x.1 + ∑ i, p i * x.2 i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]; ring
  map_smul' a x := by simp [mul_left_comm, ← Finset.mul_sum]; ring

@[simp] theorem pressureForm_energy {n : ℕ} (p : WorkCoordinates n) :
    pressureForm p (1, 0) = 1 := by simp [pressureForm]

theorem pressureForm_ne_zero {n : ℕ} (p : WorkCoordinates n) : pressureForm p ≠ 0 := by
  intro h
  have := congrArg (fun f : SimpleCoordinates n →ₗ[ℝ] ℝ => f (1, 0)) h
  simp at this

/-- Linear coordinates on the normalized pressure hyperplane. -/
def pressureLift {n : ℕ} (p : WorkCoordinates n) : WorkCoordinates n →ₗ[ℝ] SimpleCoordinates n where
  toFun v := (-∑ i, p i * v i, v)
  map_add' v w := by ext <;> simp [mul_add, Finset.sum_add_distrib]; ring
  map_smul' a v := by ext <;> simp [mul_left_comm, ← Finset.mul_sum]

@[simp] theorem pressureLift_snd {n : ℕ} (p v : WorkCoordinates n) :
    (pressureLift p v).2 = v := rfl

@[simp] theorem pressureForm_lift {n : ℕ} (p v : WorkCoordinates n) :
    pressureForm p (pressureLift p v) = 0 := by simp [pressureForm, pressureLift]

theorem eq_pressureLift_of_mem_ker {n : ℕ} (p : WorkCoordinates n)
    (d : SimpleCoordinates n) (hd : pressureForm p d = 0) :
    d = pressureLift p d.2 := by
  apply Prod.ext
  · change d.1 = -∑ i, p i * d.2 i
    change d.1 + ∑ i, p i * d.2 i = 0 at hd
    linarith
  · rfl

/-- The affine chart of a finite-slope hyperplane through `x`. -/
def pressureChart {n : ℕ} (p : WorkCoordinates n) (x : SimpleCoordinates n) :
    WorkCoordinates n →ᵃ[ℝ] SimpleCoordinates n where
  toFun v := x + pressureLift p v
  linear := pressureLift p
  map_vadd' v w := by simp [map_add]; abel

@[simp] theorem pressureChart_zero {n : ℕ} (p : WorkCoordinates n) (x : SimpleCoordinates n) :
    pressureChart p x 0 = x := by simp [pressureChart]

/-- If a sector lies in a finite-slope hyperplane and has a unique supporting
hyperplane at its anchor, the anchor is interior in that hyperplane. -/
theorem pressureChart_anchor_mem_interior {n : ℕ}
    {C : Set (SimpleCoordinates n)} (hC : Convex ℝ C)
    {x : SimpleCoordinates n} (hx : x ∈ C) (p : WorkCoordinates n)
    (hplane : ∀ y ∈ C, pressureForm p (y - x) = 0)
    (hunique : ∀ f : SimpleCoordinates n →ₗ[ℝ] ℝ, SupportsAt C x f →
      LinearMap.ker f = LinearMap.ker (pressureForm p)) :
    (0 : WorkCoordinates n) ∈ interior ((pressureChart p x) ⁻¹' C) := by
  by_contra hnot
  have hconvex := hC.affine_preimage (pressureChart p x)
  have hzero : (0 : WorkCoordinates n) ∈ (pressureChart p x) ⁻¹' C := by simpa using hx
  obtain ⟨g, hg, hsupport⟩ := exists_support_of_not_mem_interior hconvex hzero hnot
  let f : SimpleCoordinates n →ₗ[ℝ] ℝ := g.comp (LinearMap.snd ℝ ℝ (WorkCoordinates n))
  have hf : f ≠ 0 := by
    intro hfzero
    apply hg
    apply LinearMap.ext
    intro v
    exact congrArg (fun k : SimpleCoordinates n →ₗ[ℝ] ℝ => k (0, v)) hfzero
  have hfsupport : SupportsAt C x f := by
    refine ⟨hf, fun y hy => ?_⟩
    have hychart : pressureChart p x (y.2 - x.2) = y := by
      have hylift := eq_pressureLift_of_mem_ker p (y - x) (hplane y hy)
      change y - x = pressureLift p (y.2 - x.2) at hylift
      change x + pressureLift p (y.2 - x.2) = y
      rw [← hylift]
      abel
    have hgv := hsupport (y.2 - x.2) (by simpa only [mem_preimage, hychart] using hy)
    change g y.2 ≤ g x.2
    simpa only [map_sub, map_zero, sub_nonpos] using hgv
  have hker := hunique f hfsupport
  have henergy : (1, 0) ∈ LinearMap.ker f := by simp [f]
  rw [hker] at henergy
  simp at henergy

/-- Simple-system physical premises. In S2, both sides of the tangent plane are
allowed until the same-sidedness theorem fixes the orientation. S3 is path
connectedness of the boundary relative to the equilibrium domain. -/
structure SimpleSystem {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    (P : Accessibility X) (n : ℕ) where
  domain : Set (SimpleCoordinates n)
  isOpen_domain : IsOpen domain
  convex_domain : Convex ℝ domain
  represent : SimpleCoordinates n → X
  mixing : ∀ x ∈ domain, ∀ y ∈ domain, ∀ a b : ℝ≥0, a + b = 1 →
    P.relation (a • represent x + b • represent y)
      (represent ((a : ℝ) • x + (b : ℝ) • y))
  irreversible : ∀ x ∈ domain, ∃ y ∈ domain,
    P.relation (represent x) (represent y) ∧ ¬ P.relation (represent y) (represent x)
  pressure : SimpleCoordinates n → WorkCoordinates n
  pressure_support : ∀ x ∈ domain,
    SupportsAt (P.forwardSector domain represent x) x (pressureForm (pressure x)) ∨
      SupportsAt (P.forwardSector domain represent x) x (-pressureForm (pressure x))
  unique_support : ∀ x ∈ domain, ∀ f : SimpleCoordinates n →ₗ[ℝ] ℝ,
    SupportsAt (P.forwardSector domain represent x) x f →
      LinearMap.ker f = LinearMap.ker (pressureForm (pressure x))
  pressure_locallyLipschitz : LocallyLipschitzOn domain pressure
  boundary_pathConnected : ∀ x ∈ domain,
    IsPathConnected (domain ∩ frontier (P.forwardSector domain represent x))

namespace SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- LY Theorem 3.2. Irreversibility and uniqueness of finite-slope supporting
planes force every forward sector to have nonempty ambient interior. The proof
works also with no work coordinates (`n = 0`). Stability is used through the
cancellation theorem in the collinear-accessibility lemma. -/
theorem forwardSector_interior_nonempty (S : SimpleSystem P n)
    (x : SimpleCoordinates n) (hx : x ∈ S.domain) :
    (interior (P.forwardSector S.domain S.represent x)).Nonempty := by
  let C := P.forwardSector S.domain S.represent x
  have hC : Convex ℝ C :=
    P.forwardSector_convex S.domain S.represent S.convex_domain S.mixing x
  have hxC : x ∈ C := ⟨hx, P.refl _⟩
  by_contra hnot
  obtain ⟨f, hf, hvanish⟩ := exists_annihilator_of_empty_interior hC hxC hnot
  have hfsupport : SupportsAt C x f := by
    refine ⟨hf, fun y hy => le_of_eq ?_⟩
    exact sub_eq_zero.mp (by simpa only [map_sub] using hvanish y hy)
  have hker := S.unique_support x hx f hfsupport
  have hplane : ∀ y ∈ C, pressureForm (S.pressure x) (y - x) = 0 := by
    intro y hy
    have hmem : y - x ∈ LinearMap.ker f := hvanish y hy
    rw [hker] at hmem
    exact hmem
  have hzero := pressureChart_anchor_mem_interior hC hxC (S.pressure x) hplane
    (S.unique_support x hx)
  obtain ⟨y, hy, hxy, hyx⟩ := S.irreversible x hx
  have hyC : y ∈ C := ⟨hy, hxy⟩
  let v : WorkCoordinates n := y.2 - x.2
  have hylift : y - x = pressureLift (S.pressure x) v :=
    eq_pressureLift_of_mem_ker _ _ (hplane y hyC)
  have hlim : Tendsto (fun t : ℝ => (-t) • v) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => (-t) • v) := continuous_id.neg.smul continuous_const
    simpa using hc.tendsto (0 : ℝ)
  obtain ⟨t, ht, htmem⟩ :=
    (hlim.eventually_mem (mem_interior_iff_mem_nhds.mp hzero)).exists_gt
  let z := pressureChart (S.pressure x) x ((-t) • v)
  have hzC : z ∈ C := htmem
  have hz : z = x + (-t) • (y - x) := by
    dsimp [z, pressureChart]
    rw [map_smul, ← hylift]
  let a : ℝ≥0 := ⟨t / (1 + t), by positivity⟩
  let b : ℝ≥0 := ⟨1 / (1 + t), by positivity⟩
  have ha : 0 < a := by change 0 < t / (1 + t); positivity
  have hden : (1 + t) ≠ 0 := ne_of_gt (by positivity)
  have hab : a + b = 1 := by
    apply Subtype.ext
    change t / (1 + t) + 1 / (1 + t) = 1
    field_simp
    ring
  have hcoeff₁ : (a : ℝ) - (b : ℝ) * t = 0 := by
    change t / (1 + t) - (1 / (1 + t)) * t = 0
    field_simp
    ring
  have hcoeff₂ : (b : ℝ) + (b : ℝ) * t = 1 := by
    change 1 / (1 + t) + (1 / (1 + t)) * t = 1
    field_simp
  have hcoords : x = (a : ℝ) • y + (b : ℝ) • z := by
    rw [hz]
    symm
    calc
      (a : ℝ) • y + (b : ℝ) • (x + (-t) • (y - x)) =
          ((a : ℝ) - (b : ℝ) * t) • y + ((b : ℝ) + (b : ℝ) * t) • x := by module
      _ = x := by rw [hcoeff₁, hcoeff₂, zero_smul, one_smul, zero_add]
  exact hyx (P.collinear_accessibility S.domain S.represent S.mixing
    hy hzC.1 ha hab hcoords hzC.2)

end SimpleSystem

end ProjectAInos.Thermodynamics.Physical
