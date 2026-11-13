/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianInverseBounds

/-! # Uniform acceleration error for time-dependent Newtonian families -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open ContinuousLinearMap TopologicalSpace
open scoped ContDiff Topology

namespace ProjectAInos.GeneralRelativity.NewtonianMetricFamily

local notation "E" => NewtonianCoordinates
local notation "S" => NewtonianSpace
variable {U : Opens E} (f : NewtonianMetricFamily U)

/-- Derivative along a unit coordinate direction. -/
def coordinatePartial (g : E → ℝ) (q : E) (i : Fin 4) : ℝ :=
  fderiv ℝ g q (Pi.single i 1)

private def correction (c : ℝ) (q : E) : Fin 4 → Fin 4 → ℝ :=
  Fin.cons (Fin.cons (f.timeCorrection c q) (f.mixedCorrection c q))
    (fun i => Fin.cons (f.mixedCorrection c q i) (f.spatialCorrection c q i))

/-- The indicator of the physical time coordinate. -/
def timeIndicator (i : Fin 4) : ℝ := if i = 0 then 1 else 0

private theorem abs_partial_le {g : E → ℝ} {q : E} {K : ℝ}
    (hg : ‖fderiv ℝ g q‖ ≤ K) (i : Fin 4) :
    |coordinatePartial g q i| ≤ K := by
  rw [coordinatePartial, ← Real.norm_eq_abs]
  exact ((fderiv ℝ g q).le_opNorm (Pi.single i 1)).trans (by simpa [Pi.norm_single] using hg)

private theorem abs_proj_partial_le {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {q : E} {K : ℝ} (L : F →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (hg : DifferentiableAt ℝ g q) (hK : ‖fderiv ℝ g q‖ ≤ K) (i : Fin 4) :
    |coordinatePartial (fun x => L (g x)) q i| ≤ K := by
  have h := (L.hasFDerivAt.comp q hg.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => L (g x)) q = _ at h
  apply abs_partial_le _ i
  rw [h]
  exact (L.opNorm_comp_le _).trans (by
    calc
      _ ≤ 1 * ‖fderiv ℝ g q‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      _ ≤ K := by simpa using hK)

private theorem abs_correction_partial_le {c : ℝ} (hc : 1 ≤ c) (q : U)
    (i j k : Fin 4) :
    |coordinatePartial (fun x => f.correction c x i j) q k| ≤ f.bound := by
  have hc' : 0 < c := by linarith
  have hm := ((f.mixed_smooth c hc').contDiffAt (U.isOpen.mem_nhds q.property)).differentiableAt
    (by simp)
  have hs := ((f.spatial_smooth c hc').contDiffAt (U.isOpen.mem_nhds q.property)).differentiableAt
    (by simp)
  have hproj {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (i : Fin 3) :
      ‖(proj i : (Fin 3 → F) →L[ℝ] F)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [proj_apply, one_mul] using norm_le_pi_norm x i
  have hb (j : Fin 3) : |coordinatePartial (fun x => f.mixedCorrection c x j) q k| ≤ f.bound :=
    abs_proj_partial_le (proj j : S →L[ℝ] ℝ) (hproj j) hm
      ((f.mixed_bound c hc).first q q.property) k
  refine Fin.cases ?_ (fun i => ?_) i
  · exact Fin.cases (abs_partial_le ((f.time_bound c hc).first q q.property) k) hb j
  · refine Fin.cases (hb i) (fun j => ?_) j
    let L : NewtonianSpatialMatrix →L[ℝ] ℝ := (proj j : S →L[ℝ] ℝ).comp (proj i)
    have hL : ‖L‖ ≤ 1 := (opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul (hproj (F := ℝ) j)
        (hproj (F := S) i) (norm_nonneg _) zero_le_one)
    exact abs_proj_partial_le L hL hs ((f.spatial_bound c hc).first q q.property) k

private theorem coefficient_partial {c : ℝ} (hc : 1 ≤ c) (q : U) (i j k : Fin 4) :
    coordinatePartial (fun x => f.coefficient c x i j) q k =
      -2 * coordinatePartial f.potential q k * timeIndicator i * timeIndicator j +
        epsilon c * coordinatePartial (fun x => f.correction c x i j) q k := by
  have hc' : 0 < c := by linarith
  have hd {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) : DifferentiableAt ℝ g (q : E) :=
    (hg.contDiffAt (U.isOpen.mem_nhds q.property)).differentiableAt (by simp)
  have hb (i : Fin 3) := hd (contDiffOn_pi.mp (f.mixed_smooth c hc') i)
  have hh (i j : Fin 3) := hd (contDiffOn_pi.mp (contDiffOn_pi.mp (f.spatial_smooth c hc') i) j)
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · change coordinatePartial (fun x => -c^2 - 2 * f.potential x + epsilon c * f.timeCorrection c x) q k = _
      simp only [timeIndicator, ite_true, mul_one, correction, Fin.cons_zero, coordinatePartial]
      have ha := hd (f.time_smooth c hc')
      have hp := hd f.potential_smooth
      have hb : DifferentiableAt ℝ (fun x => -c^2 - 2 * f.potential x) (q : E) :=
        (differentiableAt_const (-c^2)).sub (hp.const_mul 2)
      rw [fderiv_fun_add hb (ha.const_mul (epsilon c)),
        fderiv_const_sub, fderiv_const_mul hp, fderiv_const_mul ha]
      simp
    · change coordinatePartial (fun x => epsilon c * f.mixedCorrection c x j) q k = _
      simp [coordinatePartial, timeIndicator, Fin.succ_ne_zero, correction, fderiv_const_mul (hb j)]
  · refine Fin.cases ?_ (fun j => ?_) j
    · change coordinatePartial (fun x => epsilon c * f.mixedCorrection c x i) q k = _
      simp [coordinatePartial, timeIndicator, Fin.succ_ne_zero, correction, fderiv_const_mul (hb i)]
    · change coordinatePartial (fun x => (if i = j then 1 else 0) + epsilon c * f.spatialCorrection c x i j) q k = _
      simp [coordinatePartial, timeIndicator, Fin.succ_ne_zero, correction,
        fderiv_const_mul (hh i j)]

/-- The Christoffel expression before raising the first index. -/
def lowerChristoffel (c : ℝ) (q : E) (l i j : Fin 4) : ℝ :=
  (coordinatePartial (fun x => f.coefficient c x j l) q i +
   coordinatePartial (fun x => f.coefficient c x l i) q j -
   coordinatePartial (fun x => f.coefficient c x i j) q l) / 2

private def leadingLower (q : E) (l i j : Fin 4) : ℝ :=
  -(coordinatePartial f.potential q i * timeIndicator j * timeIndicator l) -
    coordinatePartial f.potential q j * timeIndicator l * timeIndicator i +
    coordinatePartial f.potential q l * timeIndicator i * timeIndicator j

private theorem lower_error {c : ℝ} (hc : 1 ≤ c) (q : U) (l i j : Fin 4) :
    |f.lowerChristoffel c q l i j - f.leadingLower q l i j| ≤
      (3 / 2) * f.bound * epsilon c := by
  unfold lowerChristoffel leadingLower
  rw [f.coefficient_partial hc q j l i, f.coefficient_partial hc q l i j,
    f.coefficient_partial hc q i j l]
  let a := coordinatePartial (fun x => f.correction c x j l) q i
  let b := coordinatePartial (fun x => f.correction c x l i) q j
  let d := coordinatePartial (fun x => f.correction c x i j) q l
  have he := epsilon_nonneg c
  have h : |a + b - d| ≤ 3 * f.bound := by
    have hab := abs_add_le a b
    have habd : |a + b - d| ≤ |a + b| + |d| := by
      simpa [sub_eq_add_neg] using abs_add_le (a + b) (-d)
    linarith [f.abs_correction_partial_le hc q j l i, f.abs_correction_partial_le hc q l i j,
      f.abs_correction_partial_le hc q i j l]
  calc
    _ = |epsilon c * (a + b - d) / 2| := by congr 1; dsimp [a, b, d]; ring
    _ = epsilon c * |a + b - d| / 2 := by rw [abs_div, abs_mul, abs_of_nonneg he, abs_of_pos (by norm_num : (0:ℝ)<2)]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h he]

private theorem abs_leadingLower_le (q : U) (l i j : Fin 4) :
    |f.leadingLower q l i j| ≤ 3 * f.bound := by
  have h (i : Fin 4) := abs_partial_le (f.potential_bound.first q q.property) i
  have hK := f.bound_nonneg
  unfold leadingLower timeIndicator
  split <;> split <;> split <;> simp_all only [mul_one, mul_zero, neg_zero,
    sub_zero, zero_add, add_zero, zero_sub, abs_neg, abs_zero] <;>
    first | positivity | (apply abs_le.mpr; constructor) <;>
    linarith [(abs_le.mp (h 0)).1, (abs_le.mp (h 0)).2, (abs_le.mp (h i)).1, (abs_le.mp (h i)).2,
      (abs_le.mp (h j)).1, (abs_le.mp (h j)).2, (abs_le.mp (h l)).1, (abs_le.mp (h l)).2]

theorem abs_lowerChristoffel_le {c : ℝ} (hc : 1 ≤ c) (q : U) (l i j : Fin 4) :
    |f.lowerChristoffel c q l i j| ≤ 5 * f.bound := by
  have h := abs_sub_le (f.lowerChristoffel c q l i j) (f.leadingLower q l i j) 0
  simp only [sub_zero] at h
  linarith [f.lower_error hc q l i j, f.abs_leadingLower_le q l i j,
    mul_le_mul_of_nonneg_left (epsilon_le_one hc)
      (show 0 ≤ (3 / 2) * f.bound by linarith [f.bound_nonneg]), f.bound_nonneg]

/-- Spatial gradient of the potential in the fixed physical coordinates. -/
def spatialGradient (q : E) : S := fun k => fderiv ℝ f.potential q (Pi.single k.succ 1)

private def spatialIdentity (k l : Fin 4) : ℝ :=
  if k = l ∧ k ≠ 0 then 1 else 0

private theorem inverse_error {c : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (q : U) (k l : Fin 4) :
    |(f.coefficient c q)⁻¹ k l - spatialIdentity k l| ≤ (2 + 24 * f.bound) * epsilon c := by
  obtain ⟨hcol, hrow, hsp⟩ := f.inverseComponent_bounds hc hlarge q
  have hnon := mul_nonneg f.bound_nonneg (epsilon_nonneg c)
  refine Fin.cases ?_ (fun k => ?_) k
  · simpa [spatialIdentity] using
      (hrow l).trans (show 2 * epsilon c ≤ (2 + 24 * f.bound) * epsilon c by linarith)
  · refine Fin.cases ?_ (fun l => ?_) l
    · simpa [spatialIdentity, Fin.succ_ne_zero] using
        (hcol k.succ).trans (show 2 * epsilon c ≤ (2 + 24 * f.bound) * epsilon c by linarith)
    · simpa [spatialIdentity, Fin.succ_ne_zero] using
        (hsp k l).trans (show 24 * f.bound * epsilon c ≤ (2 + 24 * f.bound) * epsilon c by
          linarith [epsilon_nonneg c])

/-- Coefficient of the uniform Christoffel error. -/
def christoffelErrorConstant : ℝ := 20 * f.bound * (2 + 24 * f.bound) + (3 / 2) * f.bound

private theorem christoffel_error {c : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (q : U) (k i j : Fin 4) :
    |f.christoffel c q k i j - ∑ l, spatialIdentity k l * f.leadingLower q l i j| ≤
      f.christoffelErrorConstant * epsilon c := by
  have hK := f.bound_nonneg
  have he := epsilon_nonneg c
  let A := (f.coefficient c q)⁻¹
  let L := fun l => f.lowerChristoffel c q l i j
  let P := fun l => f.leadingLower q l i j
  have hsum : f.christoffel c q k i j - ∑ l, spatialIdentity k l * P l =
      (∑ l, (A k l - spatialIdentity k l) * L l) +
        ∑ l, spatialIdentity k l * (L l - P l) := by
    change (∑ l, A k l * _ / 2) - _ = _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    dsimp [L, lowerChristoffel, coordinatePartial]
    ring
  rw [hsum]
  have h₁ : |∑ l, (A k l - spatialIdentity k l) * L l| ≤
      4 * ((2 + 24 * f.bound) * epsilon c * (5 * f.bound)) := by
    calc
      _ ≤ ∑ l, |(A k l - spatialIdentity k l) * L l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin 4, ((2 + 24 * f.bound) * epsilon c * (5 * f.bound)) := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        exact mul_le_mul (f.inverse_error hc hlarge q k l) (f.abs_lowerChristoffel_le hc q l i j)
          (abs_nonneg _) (by positivity)
      _ = _ := by simp
  have h₂ : |∑ l, spatialIdentity k l * (L l - P l)| ≤ (3 / 2) * f.bound * epsilon c := by
    by_cases hk : k = 0
    · simp [spatialIdentity, hk]; positivity
    · have hD (l : Fin 4) : spatialIdentity k l = if l = k then 1 else 0 := by
        simp [spatialIdentity, hk, eq_comm]
      simp_rw [hD, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq']
      simpa only [Finset.mem_univ, ite_true] using f.lower_error hc q k i j
  exact (abs_add_le _ _).trans (by
    unfold christoffelErrorConstant
    linear_combination h₁ + h₂)

/-- The time component is uniformly small, including for time-dependent potentials. -/
theorem christoffel_time_abs_le {c : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (q : U) (i j : Fin 4) :
    |f.christoffel c q 0 i j| ≤ f.christoffelErrorConstant * epsilon c := by
  simpa [spatialIdentity] using f.christoffel_error hc hlarge q 0 i j

/-- The leading spatial Christoffel coefficient is the spatial gradient in
the time-time slot. All other slots are uniformly small. -/
theorem christoffel_spatial_error {c : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (q : U) (k : Fin 3) (i j : Fin 4) :
    |f.christoffel c q k.succ i j - f.spatialGradient q k * timeIndicator i * timeIndicator j| ≤
      f.christoffelErrorConstant * epsilon c := by
  have hD (l : Fin 4) : spatialIdentity k.succ l = if l = k.succ then 1 else 0 := by
    simp [spatialIdentity, Fin.succ_ne_zero, eq_comm]
  have h := f.christoffel_error hc hlarge q k.succ i j
  simp_rw [hD, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  simpa [leadingLower, spatialGradient, coordinatePartial, timeIndicator, Fin.succ_ne_zero] using h

/-- A constant for the acceleration estimate on the spatial velocity ball. -/
def accelerationErrorConstant (V : ℝ) : ℝ :=
  16 * f.christoffelErrorConstant * (1 + V)^3

theorem accelerationErrorConstant_nonneg {V : ℝ} (hV : 0 ≤ V) :
    0 ≤ f.accelerationErrorConstant V := by
  have hK := f.bound_nonneg
  unfold accelerationErrorConstant christoffelErrorConstant
  positivity

private theorem timeVelocity_abs_le {v : S} {V : ℝ} (hV : 0 ≤ V)
    (hv : ‖v‖ ≤ V) (i : Fin 4) : |timeVelocity v i| ≤ 1 + V := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change |(1 : ℝ)| ≤ _
    rw [abs_one]
    linarith
  · exact (spaceComponent_abs_le hv j).trans (by linarith)

/-- The physical coordinate-time acceleration differs uniformly from
`-∇ₓΦ` by at most a constant times `c⁻²`. -/
theorem acceleration_error {c : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (q : U) {V : ℝ} (hV : 0 ≤ V) {v : S} (hv : ‖v‖ ≤ V) :
    ‖f.acceleration c q v + f.spatialGradient q‖ ≤ f.accelerationErrorConstant V * epsilon c := by
  have hK := f.bound_nonneg
  have he := epsilon_nonneg c
  have hC : 0 ≤ f.christoffelErrorConstant := by
    unfold christoffelErrorConstant
    positivity
  let w := timeVelocity v
  let C := f.christoffelErrorConstant * epsilon c
  have hC' : 0 ≤ C := mul_nonneg hC he
  have hsum (B : Fin 4 → Fin 4 → ℝ) (hB : ∀ i j, |B i j| ≤ C) :
      |∑ i, ∑ j, B i j * w i * w j| ≤ 16 * C * (1 + V)^2 := by
    calc
      _ ≤ ∑ i, ∑ j, |B i j * w i * w j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, C * (1 + V) * (1 + V) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (hB i j) (timeVelocity_abs_le hV hv i) (abs_nonneg _) hC')
          (timeVelocity_abs_le hV hv j) (abs_nonneg _) (by positivity)
      _ = _ := by simp; ring
  have ht := hsum (f.christoffel c q 0) (f.christoffel_time_abs_le hc hlarge q)
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (f.accelerationErrorConstant_nonneg hV) he)).mpr
  intro k
  let B := fun i j => f.christoffel c q k.succ i j -
    f.spatialGradient q k * timeIndicator i * timeIndicator j
  have hs := hsum B (f.christoffel_spatial_error hc hlarge q k)
  have hlead : (∑ i : Fin 4, ∑ j : Fin 4,
      f.spatialGradient q k * timeIndicator i * timeIndicator j * w i * w j) =
      f.spatialGradient q k := by
    simp [timeIndicator, w, timeVelocity]
  have hsplit : f.acceleration c q v k + f.spatialGradient q k =
      -(∑ i, ∑ j, B i j * w i * w j) +
        v k * (∑ i, ∑ j, f.christoffel c q 0 i j * w i * w j) := by
    unfold acceleration B
    change -(∑ i, ∑ j, f.christoffel c q k.succ i j * w i * w j) + _ + _ = _
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [hlead]
    ring
  rw [Pi.add_apply, Real.norm_eq_abs, hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_mul]
  have hm := mul_le_mul (spaceComponent_abs_le hv k) ht (abs_nonneg _) hV
  unfold accelerationErrorConstant
  dsimp only [C] at hs hm
  nlinarith

/-- One tail and one error constant work for the whole open domain and velocity ball. -/
theorem eventually_acceleration_error {V : ℝ} (hV : 0 ≤ V) :
    ∀ᶠ c : ℝ in Filter.atTop, ∀ q : U, ∀ v : S, ‖v‖ ≤ V →
      ‖f.acceleration c q v + f.spatialGradient q‖ ≤ f.accelerationErrorConstant V / c^2 := by
  apply Filter.eventually_atTop.mpr
  refine ⟨24 * f.bound + 2, fun c hc q v hv => ?_⟩
  have hK := f.bound_nonneg
  have hc₁ : 1 ≤ c := by linarith
  have hc₂ : 24 * f.bound < c^2 := by nlinarith [sq_nonneg (c - 1)]
  simpa only [epsilon, div_eq_mul_inv] using f.acceleration_error hc₁ hc₂ q hV hv

/-- The error estimate holds for the acceleration extracted from the actual
Levi-Civita connection of the family metric. -/
theorem native_acceleration_error {c : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (x q : U) {V : ℝ} (hV : 0 ≤ V) {v : S} (hv : ‖v‖ ≤ V) :
    ‖coordinateTimeAcceleration (f.lorentzMetric c hc
        (show 9 * f.bound < c^2 by linarith [f.bound_nonneg])) (physicalChart x) q v +
      f.spatialGradient q‖ ≤ f.accelerationErrorConstant V / c^2 := by
  rw [← f.acceleration_eq_native]
  simpa only [epsilon, div_eq_mul_inv] using f.acceleration_error hc hlarge q hV hv

end ProjectAInos.GeneralRelativity.NewtonianMetricFamily
