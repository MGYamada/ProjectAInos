module

public import ProjectAInos.Thermodynamics.PhysicalComparison
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Topological closedness of forward sectors

Stability and the convex-combination premise imply relative closedness in an
open finite-dimensional equilibrium domain. Intrinsic interior handles forward
sectors contained in a proper affine subspace.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical.Accessibility

variable {X E : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- LY Theorem 3.1, including forward sectors of lower affine dimension. -/
theorem forwardSector_closure_inter (P : Accessibility X)
    (domain : Set E) (represent : E → X) (hopen : IsOpen domain)
    (hconvex : Convex ℝ domain)
    (mixing : ∀ x ∈ domain, ∀ y ∈ domain, ∀ a b : ℝ≥0, a + b = 1 →
      P.relation (a • represent x + b • represent y)
        (represent ((a : ℝ) • x + (b : ℝ) • y)))
    (x : E) (hx : x ∈ domain) :
    closure (P.forwardSector domain represent x) ∩ domain =
      P.forwardSector domain represent x := by
  let C := P.forwardSector domain represent x
  have hC : Convex ℝ C := P.forwardSector_convex domain represent hconvex mixing x
  have hnonempty : C.Nonempty := ⟨x, hx, P.refl _⟩
  apply Set.Subset.antisymm
  · rintro y ⟨hy, hydomain⟩
    refine ⟨hydomain, ?_⟩
    obtain ⟨w, hw⟩ := hnonempty.intrinsicInterior hC
    have hline : Filter.Tendsto (AffineMap.lineMap w y) (𝓝 (1 : ℝ)) (𝓝 y) := by
      simpa using (AffineMap.lineMap_continuous (R := ℝ) (p := w) (q := y)).tendsto (1 : ℝ)
    obtain ⟨t, ht, htdomain⟩ := (hline.eventually_mem (hopen.mem_nhds hydomain)).exists_gt
    let z := AffineMap.lineMap w y t
    have hz : z ∈ domain := htdomain
    have hδ : 0 < t - 1 := sub_pos.mpr ht
    let ε : ℕ → ℝ≥0 := fun n =>
      ⟨(1 / 2 : ℝ) ^ (n + 1) / (t - 1), by positivity⟩
    have hεpos (n) : 0 < ε n := by
      change 0 < (1 / 2 : ℝ) ^ (n + 1) / (t - 1)
      positivity
    have hεlim : Tendsto ε atTop (𝓝 0) := by
      apply NNReal.tendsto_coe.mp
      change Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) / (t - 1)) atTop (𝓝 (0 : ℝ))
      have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa only [pow_succ, zero_mul, zero_div] using
        (hp.mul_const (1 / 2 : ℝ)).div_const (t - 1)
    apply P.stable (represent x) (represent y) (represent z) (represent y) ε hεpos hεlim
    intro n
    let q : ℝ := (1 / 2 : ℝ) ^ (n + 1)
    have hq : 0 < q := by dsimp [q]; positivity
    have hq1 : q < 1 := by
      exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
    let yn : E := q • w + (1 - q) • y
    have hyn : yn ∈ C := by
      apply intrinsicInterior_subset (𝕜 := ℝ)
      apply hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hw
        (by simpa only [intrinsicClosure_eq_closure] using hy)
      exact ⟨q, 1 - q, hq, sub_pos.mpr hq1, by ring, rfl⟩
    let a : ℝ≥0 := (1 + ε n)⁻¹
    let b : ℝ≥0 := ε n / (1 + ε n)
    have hr : (1 + ε n) ≠ 0 := ne_of_gt (by positivity)
    have hab : a + b = 1 := by
      dsimp [a, b]
      rw [← one_div, ← add_div, div_self hr]
    have hden : 1 + q / (t - 1) ≠ 0 := by positivity
    have hcoeffw : (a : ℝ) * q + (b : ℝ) * (1 - t) = 0 := by
      change (1 + q / (t - 1))⁻¹ * q + (q / (t - 1) / (1 + q / (t - 1))) * (1 - t) = 0
      field_simp
      ring
    have hcoeffy : (a : ℝ) * (1 - q) + (b : ℝ) * t = 1 := by
      change (1 + q / (t - 1))⁻¹ * (1 - q) + (q / (t - 1) / (1 + q / (t - 1))) * t = 1
      field_simp
      ring
    have hmixcoord : (a : ℝ) • yn + (b : ℝ) • z = y := by
      calc
        (a : ℝ) • yn + (b : ℝ) • z =
            ((a : ℝ) * q + (b : ℝ) * (1 - t)) • w +
              ((a : ℝ) * (1 - q) + (b : ℝ) * t) • y := by
          dsimp [yn, z]
          rw [AffineMap.lineMap_apply_module]
          module
        _ = y := by rw [hcoeffw, hcoeffy, zero_smul, one_smul, zero_add]
    have hmix := mixing yn hyn.1 z hz a b hab
    rw [hmixcoord] at hmix
    have hscaled := P.scale_mono (1 + ε n) hmix
    have hfirst : (1 + ε n) * a = 1 := mul_inv_cancel₀ hr
    have hsecond : (1 + ε n) * b = ε n := by
      dsimp [b]
      exact mul_div_cancel₀ _ hr
    simp only [smul_add, smul_smul, hfirst, hsecond, one_smul] at hscaled
    have hsplit := (P.split 1 (ε n) (represent y)).1
    simp only [one_smul] at hsplit
    exact P.trans (P.add_mono hyn.2 (P.refl _)) (P.trans hscaled hsplit)
  · intro y hy
    exact ⟨subset_closure hy, hy.1⟩

/-- Forward sectors are closed in the relative topology of the state domain. -/
theorem forwardSector_isClosed_relative (P : Accessibility X)
    (domain : Set E) (represent : E → X) (hopen : IsOpen domain)
    (hconvex : Convex ℝ domain)
    (mixing : ∀ x ∈ domain, ∀ y ∈ domain, ∀ a b : ℝ≥0, a + b = 1 →
      P.relation (a • represent x + b • represent y)
        (represent ((a : ℝ) • x + (b : ℝ) • y)))
    (x : E) (hx : x ∈ domain) :
    IsClosed {y : domain | P.relation (represent x) (represent y)} := by
  have hclosed := (isClosed_closure : IsClosed (closure (P.forwardSector domain represent x))).preimage
    (continuous_subtype_val : Continuous (fun y : domain => (y : E)))
  have heq : (fun y : domain => (y : E)) ⁻¹'
      closure (P.forwardSector domain represent x) =
      {y : domain | P.relation (represent x) (represent y)} := by
    ext y
    constructor
    · intro hy
      have hmem : (y : E) ∈ closure (P.forwardSector domain represent x) ∩ domain :=
        ⟨hy, y.property⟩
      rw [P.forwardSector_closure_inter domain represent hopen hconvex mixing x hx] at hmem
      exact hmem.2
    · intro hy
      exact subset_closure ⟨y.property, hy⟩
  rwa [heq] at hclosed

end ProjectAInos.Thermodynamics.Physical.Accessibility
