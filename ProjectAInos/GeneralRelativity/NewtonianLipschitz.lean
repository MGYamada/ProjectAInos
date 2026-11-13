/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianTrajectoryComparison

/-! # Uniform Lipschitz estimates for relativistic phase fields -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open ContinuousLinearMap Matrix Set TopologicalSpace
open scoped ContDiff

namespace ProjectAInos.GeneralRelativity.NewtonianMetricFamily

local notation "E" => NewtonianCoordinates
local notation "S" => NewtonianSpace
variable {U : Opens E} (f : NewtonianMetricFamily U)

private theorem coordinateC2_sub_le {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {K : ℝ} (hg : ContDiffOn ℝ ∞ g U) (hK : CoordinateC2Bound U K g)
    {x y : E} (hseg : segment ℝ x y ⊆ U) :
    ‖g y - g x‖ ≤ K * ‖y - x‖ ∧ ‖fderiv ℝ g y - fderiv ℝ g x‖ ≤ K * ‖y - x‖ := by
  have hs (q : E) (hq : q ∈ segment ℝ x y) := hg.contDiffAt (U.isOpen.mem_nhds (hseg hq))
  have hconv : Convex ℝ (segment ℝ x y) := convex_segment x y
  refine ⟨hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun q hq => (hs q hq).differentiableAt (by simp)) (fun q hq => hK.first q (hseg hq))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y), ?_⟩
  exact hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun q hq => ((hs q hq).fderiv_right (m := 1) (by simp)).differentiableAt (by simp))
    (fun q hq => hK.second q (hseg hq)) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)

private theorem projected_sub_le {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {K : ℝ} (hg : ContDiffOn ℝ ∞ g U) (hK : CoordinateC2Bound U K g)
    (L : F →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) {x y : E} (hseg : segment ℝ x y ⊆ U) (k : Fin 4) :
    |L (g y) - L (g x)| ≤ K * ‖y - x‖ ∧
    |fderiv ℝ (fun q => L (g q)) y (Pi.single k 1) -
      fderiv ℝ (fun q => L (g q)) x (Pi.single k 1)| ≤ K * ‖y - x‖ := by
  have h := coordinateC2_sub_le hg hK hseg
  have hnorm (a : F) : ‖L a‖ ≤ ‖a‖ :=
    (L.le_opNorm a).trans (by simpa using mul_le_mul_of_nonneg_right hL (norm_nonneg a))
  have hD (q : E) (hq : q ∈ U) :
      fderiv ℝ (fun q => L (g q)) q = L.comp (fderiv ℝ g q) := by
    exact (L.hasFDerivAt.comp q
      ((hg.contDiffAt (U.isOpen.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt).fderiv
  constructor
  · rw [← map_sub, ← Real.norm_eq_abs]
    exact (hnorm _).trans h.1
  · rw [hD y (hseg (right_mem_segment ℝ x y)), hD x (hseg (left_mem_segment ℝ x y)),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← map_sub, ← Real.norm_eq_abs]
    refine (hnorm _).trans ?_
    exact ((fderiv ℝ g y - fderiv ℝ g x).le_opNorm (Pi.single k 1)).trans
      (by simpa [Pi.norm_single] using h.2)

private theorem proj_norm_le {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (i : Fin 3) :
    ‖(proj i : (Fin 3 → F) →L[ℝ] F)‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun z => by simpa using norm_le_pi_norm z i

private theorem coefficient_sub_bounds {c : ℝ} (hc : 1 ≤ c) {x y : E}
    (hseg : segment ℝ x y ⊆ U) (i j k : Fin 4) :
    |f.coefficient c y i j - f.coefficient c x i j| ≤ 3 * f.bound * ‖y - x‖ ∧
    |fderiv ℝ (fun q => f.coefficient c q i j) y (Pi.single k 1) -
      fderiv ℝ (fun q => f.coefficient c q i j) x (Pi.single k 1)| ≤ 3 * f.bound * ‖y - x‖ := by
  have hc' : 0 < c := by linarith
  have hx := hseg (left_mem_segment ℝ x y)
  have hy := hseg (right_mem_segment ℝ x y)
  have he := epsilon_nonneg c
  have hK := f.bound_nonneg
  have hcontract (r : ℝ) (hr : |r| ≤ f.bound * ‖y - x‖) :
      |epsilon c * r| ≤ f.bound * ‖y - x‖ := by
    rw [abs_mul, abs_of_nonneg he]
    calc
      _ ≤ epsilon c * (f.bound * ‖y - x‖) := mul_le_mul_of_nonneg_left hr he
      _ ≤ _ := by
        simpa using mul_le_mul_of_nonneg_right (epsilon_le_one hc)
          (mul_nonneg hK (norm_nonneg (y - x)))
  have hd {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) (q : E) (hq : q ∈ U) :
      DifferentiableAt ℝ g q := (hg.contDiffAt (U.isOpen.mem_nhds hq)).differentiableAt (by simp)
  have hscaled {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U)
      (h₀ : |g y - g x| ≤ f.bound * ‖y - x‖)
      (h₁ : |fderiv ℝ g y (Pi.single k 1) - fderiv ℝ g x (Pi.single k 1)| ≤
        f.bound * ‖y - x‖) (d : ℝ) :
      |(d + epsilon c * g y) - (d + epsilon c * g x)| ≤ 3 * f.bound * ‖y - x‖ ∧
      |fderiv ℝ (fun q => d + epsilon c * g q) y (Pi.single k 1) -
        fderiv ℝ (fun q => d + epsilon c * g q) x (Pi.single k 1)| ≤ 3 * f.bound * ‖y - x‖ := by
    have hpos := mul_nonneg hK (norm_nonneg (y - x))
    constructor
    · rw [show (d + epsilon c * g y) - (d + epsilon c * g x) =
          epsilon c * (g y - g x) by ring]
      linarith [hcontract _ h₀]
    · simp only [fderiv_const_add, fderiv_const_mul (hd hg y hy), fderiv_const_mul (hd hg x hx),
        _root_.smul_apply, smul_eq_mul, ← mul_sub]
      linarith [hcontract _ h₁]
  have hm (i : Fin 3) :=
    projected_sub_le (f.mixed_smooth c hc') (f.mixed_bound c hc) (proj i : S →L[ℝ] ℝ)
      (proj_norm_le i) hseg k
  have hs (i j : Fin 3) :
      |f.spatialCorrection c y i j - f.spatialCorrection c x i j| ≤ f.bound * ‖y - x‖ ∧
      |fderiv ℝ (fun q => f.spatialCorrection c q i j) y (Pi.single k 1) -
        fderiv ℝ (fun q => f.spatialCorrection c q i j) x (Pi.single k 1)| ≤ f.bound * ‖y - x‖ := by
    let L : NewtonianSpatialMatrix →L[ℝ] ℝ := (proj j : S →L[ℝ] ℝ).comp (proj i)
    have hL : ‖L‖ ≤ 1 := (opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul (proj_norm_le (F := ℝ) j) (proj_norm_le (F := S) i)
        (norm_nonneg _) zero_le_one)
    exact projected_sub_le (f.spatial_smooth c hc') (f.spatial_bound c hc) L hL hseg k
  have hmix (i : Fin 3) := hscaled (contDiffOn_pi.mp (f.mixed_smooth c hc') i)
    (hm i).1 (hm i).2 0
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · have hp := projected_sub_le f.potential_smooth f.potential_bound
        (ContinuousLinearMap.id ℝ ℝ) (by simp) hseg k
      have ha := projected_sub_le (f.time_smooth c hc') (f.time_bound c hc)
        (ContinuousLinearMap.id ℝ ℝ) (by simp) hseg k
      have hcombine (a b : ℝ) (hp : |a| ≤ f.bound * ‖y - x‖)
          (ha : |b| ≤ f.bound * ‖y - x‖) :
          |-2 * a + epsilon c * b| ≤ 3 * f.bound * ‖y - x‖ := by
        have h := abs_add_le (-2 * a) (epsilon c * b)
        rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num] at h
        linarith [hcontract b ha]
      have hD (q : E) (hq : q ∈ U) :
          fderiv ℝ (fun z => f.coefficient c z 0 0) q (Pi.single k 1) =
            -2 * fderiv ℝ f.potential q (Pi.single k 1) +
              epsilon c * fderiv ℝ (f.timeCorrection c) q (Pi.single k 1) := by
        have hb : DifferentiableAt ℝ (fun z => -c^2 - 2 * f.potential z) q :=
          (differentiableAt_const (-c^2)).sub ((hd f.potential_smooth q hq).const_mul 2)
        simp only [coefficient_time]
        rw [fderiv_fun_add hb ((hd (f.time_smooth c hc') q hq).const_mul (epsilon c)),
          fderiv_const_sub, fderiv_const_mul (hd f.potential_smooth q hq),
          fderiv_const_mul (hd (f.time_smooth c hc') q hq)]
        simp
      constructor
      · simp only [coefficient_time]
        rw [show (-c^2 - 2 * f.potential y + epsilon c * f.timeCorrection c y) -
            (-c^2 - 2 * f.potential x + epsilon c * f.timeCorrection c x) =
            -2 * (f.potential y - f.potential x) +
              epsilon c * (f.timeCorrection c y - f.timeCorrection c x) by ring]
        exact hcombine _ _ hp.1 ha.1
      · rw [hD y hy, hD x hx]
        rw [show ∀ a b d e : ℝ, (-2*a + epsilon c*b) - (-2*d + epsilon c*e) =
          -2*(a-d) + epsilon c*(b-e) by intros; ring]
        exact hcombine _ _ hp.2 ha.2
    · simpa [coefficient_mixed] using hmix j
  · refine Fin.cases ?_ (fun j => ?_) j
    · change |epsilon c * f.mixedCorrection c y i - epsilon c * f.mixedCorrection c x i| ≤ _ ∧ _
      simpa [coefficient, rowScale] using hmix i
    · simpa only [coefficient_spatial] using hscaled
        (contDiffOn_pi.mp (contDiffOn_pi.mp (f.spatial_smooth c hc') i) j)
        (hs i j).1 (hs i j).2 (if i = j then 1 else 0)

private theorem inverse_abs_le_two {c : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (q : U) (i j : Fin 4) : |(f.coefficient c q)⁻¹ i j| ≤ 2 := by
  obtain ⟨hcol, hrow, hsp⟩ := f.inverseComponent_bounds hc hlarge q
  have he := epsilon_le_one hc
  have hsmall : 24 * f.bound * epsilon c ≤ 1 := by
    have hc2 : 0 < c^2 := by positivity
    simpa only [epsilon, div_eq_mul_inv] using
      (div_le_iff₀ hc2).2 (by linarith : 24 * f.bound ≤ 1 * c^2)
  refine Fin.cases (by linarith [hrow j]) (fun i => ?_) i
  refine Fin.cases (by linarith [hcol i.succ]) (fun j => ?_) j
  have h := abs_sub_le ((f.coefficient c q)⁻¹ i.succ j.succ) (if i = j then 1 else 0) 0
  simp only [sub_zero] at h
  have hs := hsp i j
  by_cases hij : i = j <;> simp [hij] at h hs ⊢ <;> linarith

private theorem inverse_sub_bound {c : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    {x y : E} (hseg : segment ℝ x y ⊆ U) (i j : Fin 4) :
    |(f.coefficient c y)⁻¹ i j - (f.coefficient c x)⁻¹ i j| ≤
      192 * f.bound * ‖y - x‖ := by
  let A := f.coefficient c x
  let B := f.coefficient c y
  have hx : x ∈ U := hseg (left_mem_segment ℝ x y)
  have hy : y ∈ U := hseg (right_mem_segment ℝ x y)
  have hA : A * A⁻¹ = 1 := f.coefficient_mul_inverse hc (by linarith [f.bound_nonneg]) ⟨x, hx⟩
  have hB : B⁻¹ * B = 1 := mul_eq_one_comm.mp
    (f.coefficient_mul_inverse hc (by linarith [f.bound_nonneg]) ⟨y, hy⟩)
  have hId : B⁻¹ - A⁻¹ = B⁻¹ * (A - B) * A⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hB, Matrix.one_mul,
      Matrix.mul_assoc B⁻¹ A A⁻¹, hA, Matrix.mul_one]
  have hK := f.bound_nonneg
  change |B⁻¹ i j - A⁻¹ i j| ≤ _
  change |(B⁻¹ - A⁻¹) i j| ≤ _
  rw [hId, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
  calc
    _ ≤ ∑ l : Fin 4, ∑ k : Fin 4, |B⁻¹ i k * (A k l - B k l) * A⁻¹ l j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _l : Fin 4, ∑ _k : Fin 4, 2 * (3 * f.bound * ‖y - x‖) * 2 := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_mul]
      have hDiff : |A k l - B k l| ≤ 3 * f.bound * ‖y - x‖ := by
        rw [abs_sub_comm]
        exact (f.coefficient_sub_bounds hc hseg k l 0).1
      exact mul_le_mul
        (mul_le_mul (f.inverse_abs_le_two hc hlarge ⟨y, hy⟩ i k) hDiff (abs_nonneg _) (by norm_num))
        (f.inverse_abs_le_two hc hlarge ⟨x, hx⟩ l j) (abs_nonneg _) (by positivity)
    _ = _ := by simp; ring

private theorem abs_mul_sub_mul_le (a b x y : ℝ) :
    |a*x - b*y| ≤ |a-b| * |x| + |b| * |x-y| := by
  rw [show a*x-b*y = (a-b)*x+b*(x-y) by ring]
  simpa only [abs_mul] using abs_add_le ((a-b)*x) (b*(x-y))

/-- A common Lipschitz constant for the Christoffel coefficients. -/
def christoffelLipschitzConstant : ℝ := 4 * (192 * f.bound * (5 * f.bound) + 10 * f.bound)

private theorem lower_sub_bound {c : ℝ} (hc : 1 ≤ c) {x y : E}
    (hseg : segment ℝ x y ⊆ U) (l i j : Fin 4) :
    |f.lowerChristoffel c y l i j - f.lowerChristoffel c x l i j| ≤ 5 * f.bound * ‖y - x‖ := by
  let D := fun q a b k => fderiv ℝ (fun z => f.coefficient c z a b) q (Pi.single k 1)
  let a := D y j l i - D x j l i
  let b := D y l i j - D x l i j
  let d := D y i j l - D x i j l
  have ha : |a| ≤ 3 * f.bound * ‖y - x‖ := (f.coefficient_sub_bounds hc hseg j l i).2
  have hb : |b| ≤ 3 * f.bound * ‖y - x‖ := (f.coefficient_sub_bounds hc hseg l i j).2
  have hd : |d| ≤ 3 * f.bound * ‖y - x‖ := (f.coefficient_sub_bounds hc hseg i j l).2
  have hab := abs_add_le a b
  have habd : |a+b-d| ≤ |a+b| + |d| := by simpa [sub_eq_add_neg] using abs_add_le (a+b) (-d)
  have heq : f.lowerChristoffel c y l i j - f.lowerChristoffel c x l i j = (a+b-d)/2 := by
    unfold lowerChristoffel coordinatePartial
    dsimp [D,a,b,d]
    ring
  rw [heq, abs_div, show |(2 : ℝ)| = 2 by norm_num]
  linarith [mul_nonneg f.bound_nonneg (norm_nonneg (y-x))]

private theorem christoffel_sub_bound {c : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    {x y : E} (hseg : segment ℝ x y ⊆ U) (k i j : Fin 4) :
    |f.christoffel c y k i j - f.christoffel c x k i j| ≤
      f.christoffelLipschitzConstant * ‖y - x‖ := by
  let A := (f.coefficient c x)⁻¹
  let B := (f.coefficient c y)⁻¹
  let L := fun q l => f.lowerChristoffel c q l i j
  have hK := f.bound_nonneg
  have hx := hseg (left_mem_segment ℝ x y)
  have hy := hseg (right_mem_segment ℝ x y)
  have heq (q : E) : f.christoffel c q k i j =
      ∑ l, (f.coefficient c q)⁻¹ k l * L q l := by
    apply Finset.sum_congr rfl
    intro l _
    dsimp [L, lowerChristoffel, coordinatePartial]
    ring
  rw [heq y, heq x, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ l, |B k l * L y l - A k l * L x l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin 4, (192 * f.bound * (5 * f.bound) + 10 * f.bound) * ‖y - x‖ := by
      apply Finset.sum_le_sum
      intro l _
      have h₁ := mul_le_mul (f.inverse_sub_bound hc hlarge hseg k l)
        (f.abs_lowerChristoffel_le hc ⟨y,hy⟩ l i j) (abs_nonneg _)
        (show 0 ≤ 192 * f.bound * ‖y - x‖ by positivity)
      have h₂ := mul_le_mul (f.inverse_abs_le_two hc hlarge ⟨x,hx⟩ k l)
        (f.lower_sub_bound hc hseg l i j) (abs_nonneg _) (by norm_num)
      change |B k l - A k l| * |L y l| ≤ _ at h₁
      change |A k l| * |L y l - L x l| ≤ _ at h₂
      exact (abs_mul_sub_mul_le _ _ _ _).trans (by linarith)
    _ = _ := by simp [christoffelLipschitzConstant]; ring

private theorem christoffel_abs_le {c : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (q : U) (k i j : Fin 4) : |f.christoffel c q k i j| ≤ 40 * f.bound := by
  let L := fun l => f.lowerChristoffel c q l i j
  let A := (f.coefficient c q)⁻¹
  have heq : f.christoffel c q k i j = ∑ l, A k l * L l := by
    apply Finset.sum_congr rfl
    intro l _
    dsimp [L, lowerChristoffel, coordinatePartial]
    ring
  rw [heq]
  calc
    _ ≤ ∑ l, |A k l * L l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin 4, 2 * (5 * f.bound) := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      exact mul_le_mul (f.inverse_abs_le_two hc hlarge q k l)
        (f.abs_lowerChristoffel_le hc q l i j) (abs_nonneg _) (by norm_num)
    _ = _ := by simp; ring

/-- A common Lipschitz constant for position and velocity on the given speed ball. -/
def phaseLipschitzConstant (V : ℝ) : ℝ :=
  max 1 (16 * (f.christoffelLipschitzConstant + 120 * f.bound) * (1 + V)^3)

private theorem timeVelocity_bounds {v v' : S} {V : ℝ}
    (hv : ‖v‖ ≤ V) (i : Fin 4) :
    |timeVelocity v i| ≤ 1 + V ∧
      |timeVelocity v' i - timeVelocity v i| ≤ ‖v' - v‖ := by
  refine Fin.cases ?_ (fun i => ?_) i
  · change |(1 : ℝ)| ≤ 1 + V ∧ |(1 : ℝ) - 1| ≤ ‖v' - v‖
    have hV := (norm_nonneg v).trans hv
    simp [hV]
  · exact ⟨(spaceComponent_abs_le hv i).trans (by linarith),
      spaceComponent_abs_le (v := v' - v) le_rfl i⟩

/-- The relativistic phase field has a speed-dependent Lipschitz constant
uniform in the large-`c` tail. The coordinate segment stays in the common domain. -/
theorem relativisticPhaseField_sub_le {c : ℝ} (hc : 1 ≤ c)
    (hlarge : 24 * f.bound < c^2) (t : ℝ) (z w : S × S) {V : ℝ}
    (hz : ‖z.2‖ ≤ V) (hw : ‖w.2‖ ≤ V)
    (hseg : segment ℝ (Fin.cons t w.1 : E) (Fin.cons t z.1) ⊆ U) :
    ‖f.relativisticPhaseField c t z - f.relativisticPhaseField c t w‖ ≤
      f.phaseLipschitzConstant V * ‖z - w‖ := by
  let x : E := Fin.cons t w.1
  let y : E := Fin.cons t z.1
  let d := ‖z - w‖
  let R := 1 + V
  let A := 40 * f.bound
  let L := f.christoffelLipschitzConstant
  have hV := (norm_nonneg z.2).trans hz
  have hK := f.bound_nonneg
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL : 0 ≤ L := by dsimp [L, christoffelLipschitzConstant]; positivity
  have hd : 0 ≤ d := norm_nonneg _
  have hdx : ‖y - x‖ ≤ d := by
    have hp : ‖z.1 - w.1‖ ≤ d := le_max_left _ _
    exact (cons_sub_norm_le t z.1 w.1).trans hp
  have hdv : ‖z.2 - w.2‖ ≤ d := le_max_right _ _
  have hx : x ∈ U := hseg (left_mem_segment ℝ _ _)
  have hy : y ∈ U := hseg (right_mem_segment ℝ _ _)
  let P := fun k i j => f.christoffel c y k i j * timeVelocity z.2 i * timeVelocity z.2 j
  let Q := fun k i j => f.christoffel c x k i j * timeVelocity w.2 i * timeVelocity w.2 j
  have hP (k i j : Fin 4) : |P k i j| ≤ A * R^2 := by
    unfold P
    rw [abs_mul, abs_mul]
    have heq : A * R^2 = A * R * R := by ring
    rw [heq]
    exact mul_le_mul
      (mul_le_mul (f.christoffel_abs_le hc hlarge ⟨y,hy⟩ k i j)
        (timeVelocity_bounds (v' := w.2) hz i).1 (abs_nonneg _) hA)
      (timeVelocity_bounds (v' := w.2) hz j).1 (abs_nonneg _) (mul_nonneg hA hR)
  have hDiff (k i j : Fin 4) : |P k i j - Q k i j| ≤ (L * R^2 + 2*A*R) * d := by
    let a := f.christoffel c y k i j
    let b := f.christoffel c x k i j
    let p := timeVelocity z.2 i
    let q := timeVelocity w.2 i
    let r := timeVelocity z.2 j
    let s := timeVelocity w.2 j
    have hab : |a-b| ≤ L*d :=
      (f.christoffel_sub_bound hc hlarge hseg k i j).trans (mul_le_mul_of_nonneg_left hdx hL)
    have hb : |b| ≤ A := f.christoffel_abs_le hc hlarge ⟨x,hx⟩ k i j
    have hp : |p| ≤ R := (timeVelocity_bounds (v' := w.2) hz i).1
    have hs : |s| ≤ R := (timeVelocity_bounds (v' := z.2) hw j).1
    have hr : |r| ≤ R := (timeVelocity_bounds (v' := w.2) hz j).1
    have hpq : |p-q| ≤ d := (timeVelocity_bounds (v' := z.2) hw i).2.trans hdv
    have hrs : |r-s| ≤ d := (timeVelocity_bounds (v' := z.2) hw j).2.trans hdv
    have h₁ := mul_le_mul hab hp (abs_nonneg _) (mul_nonneg hL hd)
    have h₂ := mul_le_mul hb hpq (abs_nonneg _) hA
    have hap : |a*p-b*q| ≤ L*d*R+A*d :=
      (abs_mul_sub_mul_le _ _ _ _).trans (by linarith)
    have hbq : |b*q| ≤ A*R := by
      rw [abs_mul]
      exact mul_le_mul hb (timeVelocity_bounds (v' := z.2) hw i).1 (abs_nonneg _) hA
    have h₃ := mul_le_mul hap hr (abs_nonneg _)
      (add_nonneg (mul_nonneg (mul_nonneg hL hd) hR) (mul_nonneg hA hd))
    have h₄ := mul_le_mul hbq hrs (abs_nonneg _) (mul_nonneg hA hR)
    change |(a*p)*r-(b*q)*s| ≤ _
    exact (abs_mul_sub_mul_le _ _ _ _).trans (by nlinarith)
  let B := fun k => ∑ i : Fin 4, ∑ j : Fin 4, P k i j
  let B' := fun k => ∑ i : Fin 4, ∑ j : Fin 4, Q k i j
  have hsum (M : Fin 4 → Fin 4 → ℝ) {C : ℝ} (hM : ∀ i j, |M i j| ≤ C) :
      |∑ i, ∑ j, M i j| ≤ 16*C := by
    calc
      _ ≤ ∑ i, ∑ j, |M i j| := (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, C :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hM i j
      _ = _ := by simp; ring
  have hB (k : Fin 4) : |B k| ≤ 16*(A*R^2) := hsum (P k) (hP k)
  have hBdiff (k : Fin 4) : |B k - B' k| ≤ 16*((L*R^2+2*A*R)*d) := by
    unfold B B'
    simp_rw [← Finset.sum_sub_distrib]
    exact hsum (fun i j => P k i j - Q k i j) (hDiff k)
  have hmain : ‖f.acceleration c y z.2 - f.acceleration c x w.2‖ ≤
      16*(L+3*A)*R^3*d := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    rw [Pi.sub_apply, Real.norm_eq_abs]
    change |(-B k.succ + z.2 k * B 0) - (-B' k.succ + w.2 k * B' 0)| ≤ _
    rw [show (-B k.succ + z.2 k * B 0) - (-B' k.succ + w.2 k * B' 0) =
      -(B k.succ - B' k.succ) + (z.2 k * B 0 - w.2 k * B' 0) by ring]
    have hvel : |z.2 k - w.2 k| ≤ d := (spaceComponent_abs_le (v := z.2-w.2) le_rfl k).trans hdv
    have hm₁ := mul_le_mul hvel (hB 0) (abs_nonneg _) hd
    have hm₂ := mul_le_mul (spaceComponent_abs_le hw k) (hBdiff 0) (abs_nonneg _) hV
    have h := abs_mul_sub_mul_le (z.2 k) (w.2 k) (B 0) (B' 0)
    have hR₁ : 1 ≤ R := by dsimp [R]; linarith
    have hRR : R^2 ≤ R^3 := by nlinarith [mul_le_mul_of_nonneg_right hR₁ (sq_nonneg R)]
    have hpos := mul_le_mul_of_nonneg_right hRR (mul_nonneg hA hd)
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    dsimp only [R] at *
    nlinarith [hBdiff k.succ]
  change max ‖z.2-w.2‖ ‖f.acceleration c y z.2 - f.acceleration c x w.2‖ ≤ _
  apply max_le
  · exact hdv.trans (by
      simpa only [phaseLipschitzConstant, one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left 1 _) hd)
  · refine hmain.trans ?_
    have heq : 16*(L+3*A)*R^3 =
        16*(f.christoffelLipschitzConstant+120*f.bound)*(1+V)^3 := by
      dsimp [L,A,R]
      ring
    rw [heq, phaseLipschitzConstant]
    exact mul_le_mul_of_nonneg_right (le_max_right 1 _) hd

end ProjectAInos.GeneralRelativity.NewtonianMetricFamily
