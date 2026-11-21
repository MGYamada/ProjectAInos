/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.CavityModes
public import ProjectAinos.SpecialFunctions.BesselZeros
import Mathlib.Tactic

/-! # An axisymmetric conducting cylindrical cavity

Take the axial potential `A_z = J₀(k r) cos(k t)`, constant along the cylinder axis. Its entire
squared-radius representation proves the vacuum equations even at the axis. A positive zero
of `J₀(k R)` imposes the conducting side wall, and both end plates can be placed at any height.
-/

@[expose] public section
noncomputable section

open scoped ContDiff
namespace ProjectAinos.Electrodynamics.CavityModes
open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity
open ProjectAinos.SpecialFunctions.Bessel

private abbrev coord (i : Fin 4) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i

private def radiusSq (x : Spacetime) := x 1 ^ 2 + x 2 ^ 2

private def product (a b : ℝ → ℝ) (x : Spacetime) := a (x 0) * b (radiusSq x)

private theorem smooth_product {a b : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (product a b) := by unfold product radiusSq; fun_prop

private theorem partial_product {a b da db : ℝ → ℝ} (ha : ∀ t, HasDerivAt a (da t) t)
    (hb : ∀ s, HasDerivAt b (db s) s) (i : Fin 4) (x : Spacetime) :
    partialAt (product a b) i x =
      (if i = 0 then da (x 0) * b (radiusSq x) else 0) +
        a (x 0) * db (radiusSq x) *
          (2 * x 1 * (if i = 1 then 1 else 0) + 2 * x 2 * (if i = 2 then 1 else 0)) := by
  have hq := (((coord 1).hasFDerivAt (x := x)).mul (coord 1).hasFDerivAt).add
    ((coord 2).hasFDerivAt.mul (coord 2).hasFDerivAt)
  have hr := hq
  change HasFDerivAt (fun y : Spacetime => y 1 * y 1 + y 2 * y 2) _ x at hr
  simp only [← sq] at hr
  have h := ((ha (x 0)).comp_hasFDerivAt x (coord 0).hasFDerivAt).mul
    ((hb (radiusSq x)).comp_hasFDerivAt x hr)
  change HasFDerivAt (product a b) _ x at h
  rw [partialAt, h.fderiv]
  fin_cases i <;> norm_num [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply, coord, Pi.single_apply, Function.comp_apply] <;> ring

private theorem partial_coord (i j : Fin 4) (x : Spacetime) :
    partialAt (fun y => y j) i x = if i = j then 1 else 0 := by
  change (fderiv ℝ (coord j) x) (Pi.single i 1) = _
  rw [(coord j).hasFDerivAt.fderiv]
  simp [coord, Pi.single_apply, eq_comm]

private theorem box_product {a b : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (x : Spacetime) :
    box (product a b) x = -(deriv (deriv a) (x 0)) * b (radiusSq x) +
      a (x 0) * (4 * radiusSq x * deriv (deriv b) (radiusSq x) + 4 * deriv b (radiusSq x)) := by
  have ha' : ContDiff ℝ ∞ (deriv a) := (show ContDiff ℝ (∞ + 1) a by simpa using ha).deriv'
  have hb' : ContDiff ℝ ∞ (deriv b) := (show ContDiff ℝ (∞ + 1) b by simpa using hb).deriv'
  have d {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) := (hf.differentiable (by simp) t).hasDerivAt
  have h₀ : partialAt (product a b) 0 = product (deriv a) b := by
    funext t
    simp [partial_product (d ha) (d hb), product]
  have h₃ : partialAt (product a b) 3 = fun _ => 0 := by
    funext t
    simp [partial_product (d ha) (d hb)]
  have hᵢ (i : Fin 4) (hi : i = 1 ∨ i = 2) :
      partialAt (product a b) i = fun t => product a (deriv b) t * (2 * t i) := by
    funext t
    rcases hi with rfl | rfl <;> simp [partial_product (d ha) (d hb), product]
  have dg t := (smooth_product ha hb').differentiable (by simp) t
  rw [box, Fin.sum_univ_three]
  change -partialAt (partialAt _ 0) 0 x + (partialAt (partialAt _ 1) 1 x +
    partialAt (partialAt _ 2) 2 x + partialAt (partialAt _ 3) 3 x) = _
  rw [h₀, h₃, hᵢ 1 (Or.inl rfl), hᵢ 2 (Or.inr rfl)]
  have hd (j : Fin 4) : DifferentiableAt ℝ (fun t : Spacetime => 2 * t j) x := by fun_prop
  have de (j : Fin 4) : partialAt (fun t : Spacetime => 2 * t j) j x = 2 := by
    rw [partialAt_const_mul 2 (by fun_prop), partial_coord]
    simp
  rw [partialAt_mul (dg x) (hd 1), partialAt_mul (dg x) (hd 2), de, de]
  simp only [partialAt_const, partial_product (d ha') (d hb),
    partial_product (d ha) (d hb'), product]
  norm_num
  unfold radiusSq
  ring

/-- The axial Coulomb-gauge potential of the cylindrical transverse magnetic mode. -/
def cylinderMode (k : ℝ) : Potential :=
  potentialOf (fun _ => 0) fun x i =>
    if i = 2 then Real.cos (k * x 0) * radialProfile 1 k (x 1 ^ 2 + x 2 ^ 2) else 0

private abbrev axial (k : ℝ) := product (fun t => Real.cos (k * t)) (radialProfile 1 k)

private theorem components (k : ℝ) :
    potentialComponent (cylinderMode k) 0 = (fun _ => 0) ∧
    potentialComponent (cylinderMode k) 1 = (fun _ => 0) ∧
    potentialComponent (cylinderMode k) 2 = (fun _ => 0) ∧
    potentialComponent (cylinderMode k) 3 = axial k := by
  refine ⟨potentialComponent_potentialOf_zero .. |>.trans (by simp), ?_, ?_, ?_⟩
  · exact (potentialComponent_potentialOf_succ _ _ 0).trans (by rfl)
  · exact (potentialComponent_potentialOf_succ _ _ 1).trans (by rfl)
  · exact (potentialComponent_potentialOf_succ _ _ 2).trans (by rfl)

private theorem smooth_cylinder (k : ℝ) : ContDiff ℝ 2 (cylinderMode k) := by
  apply contDiff_potentialOf contDiff_const
  intro i
  fin_cases i <;> simp <;> try exact contDiff_const
  exact (smooth_product (a := fun t => Real.cos (k * t)) (by fun_prop)
    (contDiff_radialProfile 1 k)).of_le (show (2 : ℕ∞ω) ≤ ∞ by norm_num)

private theorem time_deriv (k t : ℝ) :
    HasDerivAt (fun s => Real.cos (k * s)) (-Real.sin (k * t) * k) t := by
  simpa using ((hasDerivAt_id t).const_mul k).cos

private theorem axial_partial (k : ℝ) (i : Fin 4) (x : Spacetime) :
    partialAt (axial k) i x =
      (if i = 0 then -Real.sin (k * x 0) * k * radialProfile 1 k (radiusSq x) else 0) +
      Real.cos (k * x 0) * (-(k ^ 2) / 4 * radialProfile (1 + 1) k (radiusSq x)) *
        (2 * x 1 * (if i = 1 then 1 else 0) + 2 * x 2 * (if i = 2 then 1 else 0)) :=
  partial_product (time_deriv k) (hasDerivAt_radialProfile 1 k) i x

/-- The mode solves all four vacuum Maxwell equations everywhere, including the axis. -/
theorem cylinderMode_maxwell (k : ℝ) (x : Spacetime) : VacuumMaxwellAt (cylinderMode k) x := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := components k
  have hdiv y : lorenzDivergence (cylinderMode k) y = 0 := by
    simp [lorenzDivergence, Fin.sum_univ_three, h₀, h₁, h₂, h₃, partialAt_const, axial_partial]
  apply (vacuumMaxwellAt_iff_box (smooth_cylinder k) hdiv).2 _ x
  intro y i
  have hc : box (fun _ => 0) y = 0 := by
    have e (j : Fin 4) : partialAt (fun _ => 0) j = fun _ => 0 := funext (partialAt_const 0 j)
    simp [box, e]
  fin_cases i
  · exact (congrArg (fun f => box f y) h₀).trans hc
  · exact (congrArg (fun f => box f y) h₁).trans hc
  · exact (congrArg (fun f => box f y) h₂).trans hc
  change box (potentialComponent (cylinderMode k) 3) y = 0
  rw [h₃]
  rw [box_product (by fun_prop) (contDiff_radialProfile 1 k)]
  have h := radialProfile_equation 1 k (radiusSq y)
  have dt := funext (fun t => (time_deriv k t).deriv)
  have ddt := ((((hasDerivAt_id (y 0)).const_mul k).sin.neg).mul_const k).deriv
  simp only [id_eq, Pi.neg_apply] at ddt
  rw [dt, ddt]
  simp only [mul_one] at *
  linear_combination Real.cos (k * y 0) * h

private theorem fields (k : ℝ) (x : Spacetime) :
    let E := electricField (fieldTensor (cylinderMode k))
    let B := magneticField (fieldTensor (cylinderMode k))
    E 0 x = 0 ∧ E 1 x = 0 ∧
    E 2 x = Real.sin (k * x 0) * k * radialProfile 1 k (radiusSq x) ∧
    x 1 * B 0 x + x 2 * B 1 x = 0 ∧ B 2 x = 0 := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := components k
  have hₐ := (smooth_cylinder k).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have he i := electricField_of_coulomb hₐ (fun y => congrFun h₀ y) i x
  obtain ⟨b₀,b₁,b₂⟩ := magneticField_fieldTensor_apply hₐ x
  dsimp only
  rw [he, he, he, b₀, b₁, b₂]
  change -partialAt (potentialComponent _ 1) 0 x = 0 ∧
    -partialAt (potentialComponent _ 2) 0 x = 0 ∧ -partialAt (potentialComponent _ 3) 0 x = _ ∧ _
  simp [h₁, h₂, h₃, partialAt_const, axial_partial]
  ring

/-- On both end plates the tangential electric field and normal magnetic field vanish. -/
theorem cylinderMode_endPlates (k : ℝ) (x : Spacetime) :
    electricField (fieldTensor (cylinderMode k)) 0 x = 0 ∧
    electricField (fieldTensor (cylinderMode k)) 1 x = 0 ∧
    magneticField (fieldTensor (cylinderMode k)) 2 x = 0 := by
  obtain ⟨e₀,e₁,_,_,b₂⟩ := fields k x
  exact ⟨e₀,e₁,b₂⟩

/-- At a Bessel zero on the cylindrical wall the electric field and normal magnetic field vanish. -/
theorem cylinderMode_side {k R : ℝ} (hk : Complex.besselJ 0 ((k * R : ℝ) : ℂ) = 0)
    (x : Spacetime) (hx : x 1 ^ 2 + x 2 ^ 2 = R ^ 2) :
    (∀ i, electricField (fieldTensor (cylinderMode k)) i x = 0) ∧
      x 1 * magneticField (fieldTensor (cylinderMode k)) 0 x +
      x 2 * magneticField (fieldTensor (cylinderMode k)) 1 x = 0 := by
  obtain ⟨e₀,e₁,e₂,b,_⟩ := fields k x
  refine ⟨?_, b⟩
  have hr : radialProfile 1 k (radiusSq x) = 0 := by
    rw [radiusSq, hx, radialProfile_one_sq]
    simp only [← Complex.ofReal_mul, hk, Complex.zero_re]
  intro i
  fin_cases i
  · exact e₀
  · exact e₁
  · change electricField (fieldTensor (cylinderMode k)) 2 x = 0
    simpa only [hr, mul_zero] using e₂

/-- Cylinders of every positive radius admit arbitrarily high conducting frequencies.
At a quarter period the on-axis electric field has amplitude `k`. -/
theorem exists_cylinderMode {R : ℝ} (hR : 0 < R) (a : ℝ) :
    ∃ k : ℝ, a < k ∧ 0 < k ∧ Complex.besselJ 0 ((k * R : ℝ) : ℂ) = 0 ∧
      electricField (fieldTensor (cylinderMode k)) 2 ![Real.pi / (2 * k), 0, 0, 0] = k := by
  obtain ⟨r,hr,hj⟩ := exists_zero_Ioo (0 : ℤ) (a := max (a * R) 3)
    (by simpa using lt_of_lt_of_le (by norm_num : (2 : ℝ) < 3) (le_max_right (a * R) 3))
  have hrpos : 0 < r := lt_trans (by positivity : 0 < max (a * R) 3) hr.1
  let k := r / R
  have hk : 0 < k := div_pos hrpos hR
  refine ⟨k, (lt_div_iff₀ hR).mpr ((le_max_left _ _).trans_lt hr.1), hk, ?_, ?_⟩
  · simpa [k, hR.ne'] using hj
  · obtain ⟨_,_,he,_,_⟩ := fields k ![Real.pi / (2 * k), 0, 0, 0]
    have hp : radialProfile 1 k 0 = 1 := by
      simpa [Complex.besselJ_zero] using radialProfile_one_sq k 0
    simpa [radiusSq, hp, show k * (Real.pi / (2 * k)) = Real.pi / 2 by field_simp,
      Real.sin_pi_div_two] using he

end ProjectAinos.Electrodynamics.CavityModes
