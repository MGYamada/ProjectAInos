/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateScalarField
public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorAlgebra

/-!
# The energy-momentum pseudotensor in co-ordinates

Landau–Lifshitz, §96. For a metric given by coefficients on an open set `U`, with `|g|` the
absolute value of its determinant,

* `superpotentialDensity`: `λ^{iklm} = |g| (g^{ik} g^{lm} − g^{il} g^{km})`, and
  `superpotential`: `h^{ikl} = ∂_m λ^{iklm}`, antisymmetric in `k, l`
  (`superpotential_antisymm`), so that `∂_k ∂_l h^{ikl} = 0` identically
  (`divergence_divergence_superpotential`);
* `divergence_superpotential_eq`: **at a point where the first derivatives of the coefficients
  vanish, `∂_l h^{ikl} = 2 |g| G^{ik}`** with the raised Einstein tensor `G^{ik}`
  (`raisedEinstein`), the identity (96.5);
* `pseudotensor`: `t^{ik}` defined by `2 |g| (G^{ik} + t^{ik}) = ∂_l h^{ikl}`, which vanishes at
  such a point (`pseudotensor_eq_zero`) and is symmetric (`pseudotensor_symm`); with the Einstein
  equations `G^{ik} = κ T^{ik}` the total `|g| (κ T^{ik} + t^{ik})` is conserved in the ordinary
  sense (`divergence_total_eq_zero`), the conservation (96.8).
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

/-! ### The product rule at a critical point -/

section Critical

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- At a point where both factors are critical, the second derivative of a product is
`(∂_a ∂_b u) v + u (∂_a ∂_b v)`. -/
theorem fderiv_fderiv_mul_of_critical {u v : F → ℝ} {x : F} (hu : ContDiffAt ℝ 2 u x)
    (hv : ContDiffAt ℝ 2 v x) (hu0 : fderiv ℝ u x = 0) (hv0 : fderiv ℝ v x = 0) (a b : F) :
    fderiv ℝ (fun w => fderiv ℝ (fun y => u y * v y) w b) x a =
      fderiv ℝ (fun w => fderiv ℝ u w b) x a * v x +
        u x * fderiv ℝ (fun w => fderiv ℝ v w b) x a := by
  have hu1 := (hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)
  have hv1 := (hv.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)
  have heq : (fun w => fderiv ℝ (fun y => u y * v y) w b) =ᶠ[𝓝 x]
      fun w => u w * fderiv ℝ v w b + v w * fderiv ℝ u w b := by
    filter_upwards [hu1, hv1] with w hwu hwv
    rw [fderiv_fun_mul (hwu.differentiableAt one_ne_zero) (hwv.differentiableAt one_ne_zero)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hdu : DifferentiableAt ℝ (fun w => fderiv ℝ u w b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const b)
  have hdv : DifferentiableAt ℝ (fun w => fderiv ℝ v w b) x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const b)
  have hd : HasFDerivAt (fun w => u w * fderiv ℝ v w b + v w * fderiv ℝ u w b)
      (u x • fderiv ℝ (fun w => fderiv ℝ v w b) x + fderiv ℝ v x b • fderiv ℝ u x +
        (v x • fderiv ℝ (fun w => fderiv ℝ u w b) x + fderiv ℝ u x b • fderiv ℝ v x)) x :=
    ((hu.differentiableAt (by norm_num)).hasFDerivAt.mul hdv.hasFDerivAt).add
      ((hv.differentiableAt (by norm_num)).hasFDerivAt.mul hdu.hasFDerivAt)
  rw [heq.fderiv_eq, hd.fderiv, hu0, hv0]
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply]
  ring

/-- A product of critical factors is critical. -/
theorem fderiv_mul_of_critical {u v : F → ℝ} {x : F} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (hu0 : fderiv ℝ u x = 0) (hv0 : fderiv ℝ v x = 0) :
    fderiv ℝ (fun y => u y * v y) x = 0 := by
  rw [fderiv_fun_mul hu hv, hu0, hv0, smul_zero, smul_zero, add_zero]

/-- The second derivative of a difference. -/
theorem fderiv_fderiv_sub {u v : F → ℝ} {x : F} (hu : ContDiffAt ℝ 2 u x)
    (hv : ContDiffAt ℝ 2 v x) (a b : F) :
    fderiv ℝ (fun w => fderiv ℝ (fun y => u y - v y) w b) x a =
      fderiv ℝ (fun w => fderiv ℝ u w b) x a - fderiv ℝ (fun w => fderiv ℝ v w b) x a := by
  have hu1 := (hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)
  have hv1 := (hv.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)
  have heq : (fun w => fderiv ℝ (fun y => u y - v y) w b) =ᶠ[𝓝 x]
      fun w => fderiv ℝ u w b - fderiv ℝ v w b := by
    filter_upwards [hu1, hv1] with w hwu hwv
    rw [fderiv_fun_sub (hwu.differentiableAt one_ne_zero) (hwv.differentiableAt one_ne_zero),
      sub_apply]
  have hdu : DifferentiableAt ℝ (fun w => fderiv ℝ u w b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const b)
  have hdv : DifferentiableAt ℝ (fun w => fderiv ℝ v w b) x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const b)
  rw [heq.fderiv_eq, fderiv_fun_sub hdu hdv, sub_apply]

end Critical

/-- A continuous linear functional on the model that vanishes on the coordinate vectors
vanishes. -/
theorem clm_eq_zero_of_single {d : ℕ} {f : MinkowskiModel d →L[ℝ] ℝ}
    (h : ∀ c, f (Pi.single c 1) = 0) : f = 0 := by
  ext v
  have hv : v = ∑ c, v c • (Pi.single c 1 : MinkowskiModel d) := by
    ext j
    simp [Pi.single_apply]
  rw [hv, map_sum]
  simp [h]

namespace CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}
  (g : CoordinateMetric σ d U)

/-! ### The superpotential -/

/-- `λ^{iklm} = |g| (g^{ik} g^{lm} − g^{il} g^{km})`. -/
def superpotentialDensity (z : MinkowskiModel d) (i k l m : Fin (d + 1)) : ℝ :=
  densityOf g.coefficient z ^ 2 *
    ((g.coefficient z)⁻¹ i k * (g.coefficient z)⁻¹ l m -
      (g.coefficient z)⁻¹ i l * (g.coefficient z)⁻¹ k m)

/-- `h^{ikl} = ∂_m λ^{iklm}`. -/
def superpotential (z : MinkowskiModel d) (i k l : Fin (d + 1)) : ℝ :=
  ∑ m, fderiv ℝ (fun w => g.superpotentialDensity w i k l m) z (Pi.single m 1)

/-- The raised Einstein tensor `G^{ik} = g^{ia} g^{kb} (R_{ab} − ½ g_{ab} R)`. -/
def raisedEinstein (z : MinkowskiModel d) (i k : Fin (d + 1)) : ℝ :=
  ∑ a, ∑ b, (g.coefficient z)⁻¹ i a * (g.coefficient z)⁻¹ k b *
    (ricciOf g.coefficient z a b - g.coefficient z a b * scalarOf g.coefficient z / 2)

/-- The pseudotensor `t^{ik}`, defined by `2 |g| (G^{ik} + t^{ik}) = ∂_l h^{ikl}`. -/
def pseudotensor (z : MinkowskiModel d) (i k : Fin (d + 1)) : ℝ :=
  (∑ l, fderiv ℝ (fun w => g.superpotential w i k l) z (Pi.single l 1)) /
      (2 * densityOf g.coefficient z ^ 2) - g.raisedEinstein z i k

theorem superpotentialDensity_antisymm (z : MinkowskiModel d) (i k l m : Fin (d + 1)) :
    g.superpotentialDensity z i k l m = -g.superpotentialDensity z i l k m := by
  unfold superpotentialDensity
  ring

/-- **The superpotential is antisymmetric**: `h^{ikl} = −h^{ilk}`. -/
theorem superpotential_antisymm (z : MinkowskiModel d) (i k l : Fin (d + 1)) :
    g.superpotential z i k l = -g.superpotential z i l k := by
  unfold superpotential
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hf : (fun w => g.superpotentialDensity w i k l m) =
      fun w => -g.superpotentialDensity w i l k m :=
    funext fun w => g.superpotentialDensity_antisymm w i k l m
  rw [hf, fderiv_fun_neg, neg_apply]

theorem contDiffOn_superpotentialDensity (i k l m : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun w => g.superpotentialDensity w i k l m) U :=
  (g.contDiffOn_densityOf.pow 2).mul
    (((g.contDiffOn_coefficient_inv i k).mul (g.contDiffOn_coefficient_inv l m)).sub
      ((g.contDiffOn_coefficient_inv i l).mul (g.contDiffOn_coefficient_inv k m)))

theorem contDiffOn_superpotential (i k l : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun w => g.superpotential w i k l) U :=
  ContDiffOn.sum fun m _ =>
    ((g.contDiffOn_superpotentialDensity i k l m).fderiv_of_isOpen U.isOpen (m := ∞)
      (by simp)).clm_apply contDiffOn_const

/-- **The conservation identity**: `∂_k ∂_l h^{ikl} = 0` on `U`. -/
theorem divergence_divergence_superpotential {z : MinkowskiModel d} (hz : z ∈ U)
    (i : Fin (d + 1)) :
    ∑ k, fderiv ℝ (fun w => ∑ l, fderiv ℝ (fun v => g.superpotential v i k l) w
      (Pi.single l 1)) z (Pi.single k 1) = 0 := by
  have hd (k l : Fin (d + 1)) : DifferentiableAt ℝ
      (fun w => fderiv ℝ (fun v => g.superpotential v i k l) w (Pi.single l 1)) z :=
    ((((g.contDiffOn_superpotential i k l).fderiv_of_isOpen U.isOpen (m := ∞)
      (by simp)).clm_apply contDiffOn_const).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt
      (by simp)
  set R : Fin (d + 1) → Fin (d + 1) → ℝ := fun k l =>
    fderiv ℝ (fun w => fderiv ℝ (fun v => g.superpotential v i k l) w (Pi.single l 1)) z
      (Pi.single k 1) with hR
  have hanti (k l : Fin (d + 1)) : R k l = -R l k := by
    simp only [hR]
    rw [fderiv_fderiv_comm (g.contDiffOn_superpotential i k l) hz k l]
    have hf : (fun v => g.superpotential v i k l) = fun v => -g.superpotential v i l k :=
      funext fun v => g.superpotential_antisymm v i k l
    have hf' : (fun w => fderiv ℝ (fun v => -g.superpotential v i l k) w (Pi.single k 1)) =
        fun w => -fderiv ℝ (fun v => g.superpotential v i l k) w (Pi.single k 1) :=
      funext fun w => by rw [fderiv_fun_neg, neg_apply]
    rw [hf, hf', fderiv_fun_neg, neg_apply]
  have hsum : ∑ k, fderiv ℝ (fun w => ∑ l, fderiv ℝ (fun v => g.superpotential v i k l) w
      (Pi.single l 1)) z (Pi.single k 1) = ∑ k, ∑ l, R k l := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fderiv_fun_sum fun l _ => hd k l, _root_.sum_apply]
  rw [hsum]
  have h2 : ∑ k, ∑ l, R k l = -∑ k, ∑ l, R k l :=
    calc ∑ k, ∑ l, R k l = ∑ l, ∑ k, R k l := Finset.sum_comm
      _ = ∑ l, ∑ k, -R l k :=
          Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => hanti k l
      _ = -∑ l, ∑ k, R l k := by simp only [Finset.sum_neg_distrib]
  linarith

/-! ### At a point where the first derivatives vanish -/

/-- The second derivatives `S_{ab,ce} = ∂_c ∂_e g_{ab}` of the coefficients. -/
def secondDerivative (x : MinkowskiModel d) (a b c e : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun w => fderiv ℝ (fun v => g.coefficient v a b) w (Pi.single e 1)) x
    (Pi.single c 1)

variable {g} {x : MinkowskiModel d}

theorem secondDerivative_symm_left (hx : x ∈ U) (a b c e : Fin (d + 1)) :
    g.secondDerivative x a b c e = g.secondDerivative x b a c e := by
  unfold secondDerivative
  have h : (fun w => fderiv ℝ (fun v => g.coefficient v a b) w (Pi.single e 1)) =ᶠ[𝓝 x]
      fun w => fderiv ℝ (fun v => g.coefficient v b a) w (Pi.single e 1) := by
    filter_upwards [U.isOpen.mem_nhds hx] with w hw
    have hev : (fun v => g.coefficient v a b) =ᶠ[𝓝 w] fun v => g.coefficient v b a :=
      eventually_of_mem (U.isOpen.mem_nhds hw) fun v hv => g.coefficient_symmetric hv a b
    rw [hev.fderiv_eq]
  rw [h.fderiv_eq]

theorem secondDerivative_symm_right (hx : x ∈ U) (a b c e : Fin (d + 1)) :
    g.secondDerivative x a b c e = g.secondDerivative x a b e c :=
  fderiv_fderiv_comm (g.coefficient_contDiffOn a b) hx c e

variable (hx : x ∈ U)
  (hc : ∀ a b c, fderiv ℝ (fun w => g.coefficient w a b) x (Pi.single c 1) = 0)
include hx hc

omit hx in
theorem christoffel_eq_zero_of_critical (k i j : Fin (d + 1)) :
    christoffelOf g.coefficient x k i j = 0 := by
  unfold christoffelOf
  simp [hc]

theorem fderiv_coefficient_inv_eq_zero (b c : Fin (d + 1)) :
    fderiv ℝ (fun z => (g.coefficient z)⁻¹ b c) x = 0 :=
  clm_eq_zero_of_single fun k => by
    rw [g.fderiv_coefficient_inv hx]
    simp [christoffel_eq_zero_of_critical hc]

theorem fderiv_densityOf_eq_zero : fderiv ℝ (fun z => densityOf g.coefficient z) x = 0 :=
  clm_eq_zero_of_single fun k => by
    rw [g.fderiv_densityOf hx]
    simp [christoffel_eq_zero_of_critical hc]

/-- The derivative of the Christoffel symbols:
`∂_m Γ^k_{ij} = ½ g^{kl} (S_{jl,mi} + S_{li,mj} − S_{ij,ml})`. -/
theorem fderiv_christoffel_of_critical (k i j m : Fin (d + 1)) :
    fderiv ℝ (fun w => christoffelOf g.coefficient w k i j) x (Pi.single m 1) =
      ∑ l, (g.coefficient x)⁻¹ k l * (g.secondDerivative x j l m i +
        g.secondDerivative x l i m j - g.secondDerivative x i j m l) / 2 := by
  have hU := U.isOpen.mem_nhds hx
  have hD (a b e : Fin (d + 1)) :
      DifferentiableAt ℝ (fun w => fderiv ℝ (fun v => g.coefficient v a b) w (Pi.single e 1)) x :=
    ((((g.coefficient_contDiffOn a b).fderiv_of_isOpen U.isOpen (m := ∞) (by simp)).clm_apply
      contDiffOn_const).contDiffAt hU).differentiableAt (by simp)
  have hI (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun w => (g.coefficient w)⁻¹ a b) x :=
    ((g.contDiffOn_coefficient_inv a b).contDiffAt hU).differentiableAt (by simp)
  have hterm (l : Fin (d + 1)) : HasFDerivAt (fun w => (g.coefficient w)⁻¹ k l *
      (fderiv ℝ (fun v => g.coefficient v j l) w (Pi.single i 1) +
        fderiv ℝ (fun v => g.coefficient v l i) w (Pi.single j 1) -
        fderiv ℝ (fun v => g.coefficient v i j) w (Pi.single l 1)) / 2)
      ((1 / 2 : ℝ) • ((g.coefficient x)⁻¹ k l •
        (fderiv ℝ (fun w => fderiv ℝ (fun v => g.coefficient v j l) w (Pi.single i 1)) x +
          fderiv ℝ (fun w => fderiv ℝ (fun v => g.coefficient v l i) w (Pi.single j 1)) x -
          fderiv ℝ (fun w => fderiv ℝ (fun v => g.coefficient v i j) w (Pi.single l 1)) x) +
        (fderiv ℝ (fun v => g.coefficient v j l) x (Pi.single i 1) +
          fderiv ℝ (fun v => g.coefficient v l i) x (Pi.single j 1) -
          fderiv ℝ (fun v => g.coefficient v i j) x (Pi.single l 1)) •
          fderiv ℝ (fun w => (g.coefficient w)⁻¹ k l) x)) x := by
    have h := (((hI k l).hasFDerivAt.mul
      (((hD j l i).hasFDerivAt.add (hD l i j).hasFDerivAt).sub (hD i j l).hasFDerivAt)).const_mul
      (1 / 2 : ℝ))
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
    ring
  unfold christoffelOf
  rw [fderiv_fun_sum fun l _ => (hterm l).differentiableAt, _root_.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(hterm l).fderiv, g.fderiv_coefficient_inv_eq_zero hx hc, hc, hc, hc]
  simp only [smul_apply, add_apply, sub_apply, smul_eq_mul, smul_zero, add_zero,
    secondDerivative]
  ring

/-- The second derivatives of the inverse: `∂_l ∂_m g^{bc} = −g^{ba} g^{ce} S_{ae,lm}`. -/
theorem fderiv_fderiv_coefficient_inv (b c l m : Fin (d + 1)) :
    fderiv ℝ (fun w => fderiv ℝ (fun v => (g.coefficient v)⁻¹ b c) w (Pi.single m 1)) x
        (Pi.single l 1) =
      -∑ a, ∑ e, (g.coefficient x)⁻¹ b a * (g.coefficient x)⁻¹ c e *
        g.secondDerivative x a e l m := by
  have hU := U.isOpen.mem_nhds hx
  have hΓ (k i j : Fin (d + 1)) :
      DifferentiableAt ℝ (fun w => christoffelOf g.coefficient w k i j) x :=
    ((g.contDiffOn_christoffelOf k i j).contDiffAt hU).differentiableAt (by simp)
  have hI (a b' : Fin (d + 1)) : DifferentiableAt ℝ (fun w => (g.coefficient w)⁻¹ a b') x :=
    ((g.contDiffOn_coefficient_inv a b').contDiffAt hU).differentiableAt (by simp)
  have heq : (fun w => fderiv ℝ (fun v => (g.coefficient v)⁻¹ b c) w (Pi.single m 1)) =ᶠ[𝓝 x]
      fun w => -∑ e, (christoffelOf g.coefficient w b m e * (g.coefficient w)⁻¹ e c +
        christoffelOf g.coefficient w c m e * (g.coefficient w)⁻¹ b e) :=
    eventually_of_mem hU fun w hw => g.fderiv_coefficient_inv hw b c m
  have hprod (k i j a b' : Fin (d + 1)) :
      fderiv ℝ (fun w => christoffelOf g.coefficient w k i j * (g.coefficient w)⁻¹ a b') x
        (Pi.single l 1) =
      fderiv ℝ (fun w => christoffelOf g.coefficient w k i j) x (Pi.single l 1) *
        (g.coefficient x)⁻¹ a b' := by
    rw [fderiv_fun_mul (hΓ k i j) (hI a b'), add_apply, smul_apply, smul_apply, smul_eq_mul,
      smul_eq_mul, christoffel_eq_zero_of_critical hc]
    ring
  have hmul (k i j a b' : Fin (d + 1)) : DifferentiableAt ℝ
      (fun w => christoffelOf g.coefficient w k i j * (g.coefficient w)⁻¹ a b') x :=
    (hΓ k i j).mul (hI a b')
  have hadd (e : Fin (d + 1)) : DifferentiableAt ℝ
      (fun w => christoffelOf g.coefficient w b m e * (g.coefficient w)⁻¹ e c +
        christoffelOf g.coefficient w c m e * (g.coefficient w)⁻¹ b e) x :=
    (hmul b m e e c).add (hmul c m e b e)
  rw [heq.fderiv_eq, fderiv_fun_neg, neg_apply, fderiv_fun_sum fun e _ => hadd e,
    _root_.sum_apply]
  simp only [fderiv_fun_add (hmul _ _ _ _ _) (hmul _ _ _ _ _), add_apply,
    hprod, fderiv_christoffel_of_critical hx hc]
  exact inverse_second_algebra (fun a b => (g.coefficient x)⁻¹ a b) (g.secondDerivative x)
    (g.coefficient_inv_symmetric hx) (secondDerivative_symm_left hx) b c l m

/-- The second derivatives of the density: `∂_l ∂_m √|g| = ½ √|g| g^{ce} S_{ce,lm}`. -/
theorem fderiv_fderiv_densityOf (l m : Fin (d + 1)) :
    fderiv ℝ (fun w => fderiv ℝ (fun v => densityOf g.coefficient v) w (Pi.single m 1)) x
        (Pi.single l 1) =
      densityOf g.coefficient x *
        ((∑ c, ∑ e, (g.coefficient x)⁻¹ c e * g.secondDerivative x c e l m) / 2) := by
  have hU := U.isOpen.mem_nhds hx
  have hΓ (k i j : Fin (d + 1)) :
      DifferentiableAt ℝ (fun w => christoffelOf g.coefficient w k i j) x :=
    ((g.contDiffOn_christoffelOf k i j).contDiffAt hU).differentiableAt (by simp)
  have hD : DifferentiableAt ℝ (fun w => densityOf g.coefficient w) x :=
    ((g.contDiffOn_densityOf).contDiffAt hU).differentiableAt (by simp)
  have hsum : DifferentiableAt ℝ (fun w => ∑ c, christoffelOf g.coefficient w c c m) x :=
    DifferentiableAt.fun_sum fun c _ => hΓ c c m
  have heq : (fun w => fderiv ℝ (fun v => densityOf g.coefficient v) w (Pi.single m 1)) =ᶠ[𝓝 x]
      fun w => densityOf g.coefficient w * ∑ c, christoffelOf g.coefficient w c c m :=
    eventually_of_mem hU fun w hw => g.fderiv_densityOf hw m
  rw [heq.fderiv_eq, fderiv_fun_mul hD hsum, add_apply, smul_apply, smul_apply, smul_eq_mul,
    smul_eq_mul, fderiv_fun_sum fun c _ => hΓ c c m, _root_.sum_apply]
  simp only [christoffel_eq_zero_of_critical hc, Finset.sum_const_zero, zero_mul, add_zero,
    fderiv_christoffel_of_critical hx hc]
  rw [density_second_algebra (fun a b => (g.coefficient x)⁻¹ a b) (g.secondDerivative x)
    (g.coefficient_inv_symmetric hx) (secondDerivative_symm_left hx) l m]

/-- The Ricci tensor at the point, in the second derivatives of the coefficients. -/
theorem ricciOf_of_critical (a b : Fin (d + 1)) :
    ricciOf g.coefficient x a b =
      ∑ c, ∑ e, (g.coefficient x)⁻¹ c e * (g.secondDerivative x b e c a +
        g.secondDerivative x e a c b - g.secondDerivative x a b c e -
        g.secondDerivative x c e a b) / 2 := by
  unfold ricciOf
  simp only [christoffel_eq_zero_of_critical hc, mul_zero, sub_self, Finset.sum_const_zero,
    add_zero, fderiv_christoffel_of_critical hx hc]
  exact ricci_algebra (fun a b => (g.coefficient x)⁻¹ a b) (g.secondDerivative x)
    (g.coefficient_inv_symmetric hx) (secondDerivative_symm_left hx)
    (secondDerivative_symm_right hx) a b

omit hc in
theorem sum_inv_mul_coefficient (i k : Fin (d + 1)) :
    ∑ a, ∑ b, (g.coefficient x)⁻¹ i a * (g.coefficient x)⁻¹ k b * g.coefficient x a b =
      (g.coefficient x)⁻¹ i k := by
  have hinv : (g.coefficient x)⁻¹ * g.coefficient x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (g.coefficient_det_ne_zero ⟨x, hx⟩))
  calc ∑ a, ∑ b, (g.coefficient x)⁻¹ i a * (g.coefficient x)⁻¹ k b * g.coefficient x a b =
        ∑ b, (∑ a, (g.coefficient x)⁻¹ i a * g.coefficient x a b) * (g.coefficient x)⁻¹ k b := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ b, (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i b * (g.coefficient x)⁻¹ k b :=
        Finset.sum_congr rfl fun b _ => by rw [← Matrix.mul_apply, hinv]
    _ = (g.coefficient x)⁻¹ k i := by simp [Matrix.one_apply]
    _ = (g.coefficient x)⁻¹ i k := g.coefficient_inv_symmetric hx k i

/-- **The identity of the superpotential at a point where the first derivatives vanish**:
`∂_l h^{ikl} = 2 |g| G^{ik}`. -/
theorem divergence_superpotential_eq (i k : Fin (d + 1)) :
    ∑ l, fderiv ℝ (fun w => g.superpotential w i k l) x (Pi.single l 1) =
      2 * densityOf g.coefficient x ^ 2 * g.raisedEinstein x i k := by
  have hU := U.isOpen.mem_nhds hx
  have hDc : ContDiffAt ℝ 2 (fun w => densityOf g.coefficient w) x :=
    (g.contDiffOn_densityOf.contDiffAt hU).of_le (by simp)
  have hIc (a b : Fin (d + 1)) : ContDiffAt ℝ 2 (fun w => (g.coefficient w)⁻¹ a b) x :=
    ((g.contDiffOn_coefficient_inv a b).contDiffAt hU).of_le (by simp)
  have hD0 := fderiv_densityOf_eq_zero hx hc
  have hI0 (a b : Fin (d + 1)) := fderiv_coefficient_inv_eq_zero hx hc a b
  have hII (p q r t l m : Fin (d + 1)) :
      fderiv ℝ (fun w => fderiv ℝ (fun y => (g.coefficient y)⁻¹ p q * (g.coefficient y)⁻¹ r t) w
        (Pi.single m 1)) x (Pi.single l 1) =
      (-∑ a, ∑ e, (g.coefficient x)⁻¹ p a * (g.coefficient x)⁻¹ q e *
          g.secondDerivative x a e l m) * (g.coefficient x)⁻¹ r t +
        (g.coefficient x)⁻¹ p q * (-∑ a, ∑ e, (g.coefficient x)⁻¹ r a *
          (g.coefficient x)⁻¹ t e * g.secondDerivative x a e l m) := by
    rw [fderiv_fderiv_mul_of_critical (hIc p q) (hIc r t) (hI0 p q) (hI0 r t),
      fderiv_fderiv_coefficient_inv hx hc, fderiv_fderiv_coefficient_inv hx hc]
  have hmulc (p q r t : Fin (d + 1)) : ContDiffAt ℝ 2
      (fun y => (g.coefficient y)⁻¹ p q * (g.coefficient y)⁻¹ r t) x := (hIc p q).mul (hIc r t)
  have hQc (l m : Fin (d + 1)) : ContDiffAt ℝ 2 (fun y => (g.coefficient y)⁻¹ i k *
      (g.coefficient y)⁻¹ l m - (g.coefficient y)⁻¹ i l * (g.coefficient y)⁻¹ k m) x :=
    (hmulc i k l m).sub (hmulc i l k m)
  have hQ0 (l m : Fin (d + 1)) : fderiv ℝ (fun y => (g.coefficient y)⁻¹ i k *
      (g.coefficient y)⁻¹ l m - (g.coefficient y)⁻¹ i l * (g.coefficient y)⁻¹ k m) x = 0 := by
    rw [fderiv_fun_sub ((hmulc i k l m).differentiableAt (by norm_num))
      ((hmulc i l k m).differentiableAt (by norm_num)),
      fderiv_mul_of_critical ((hIc i k).differentiableAt (by norm_num))
        ((hIc l m).differentiableAt (by norm_num)) (hI0 i k) (hI0 l m),
      fderiv_mul_of_critical ((hIc i l).differentiableAt (by norm_num))
        ((hIc k m).differentiableAt (by norm_num)) (hI0 i l) (hI0 k m), sub_zero]
  have hsq : (fun y => densityOf g.coefficient y ^ 2) =
      fun y => densityOf g.coefficient y * densityOf g.coefficient y := funext fun y => sq _
  have hD2c : ContDiffAt ℝ 2 (fun y => densityOf g.coefficient y ^ 2) x := hDc.pow 2
  have hDD0 : fderiv ℝ (fun y => densityOf g.coefficient y ^ 2) x = 0 := by
    rw [hsq]
    exact fderiv_mul_of_critical (hDc.differentiableAt (by norm_num))
      (hDc.differentiableAt (by norm_num)) hD0 hD0
  have hDD (l m : Fin (d + 1)) : fderiv ℝ (fun w => fderiv ℝ (fun y =>
      densityOf g.coefficient y ^ 2) w (Pi.single m 1)) x (Pi.single l 1) =
      densityOf g.coefficient x ^ 2 *
        ∑ c, ∑ e, (g.coefficient x)⁻¹ c e * g.secondDerivative x c e l m := by
    rw [hsq, fderiv_fderiv_mul_of_critical hDc hDc hD0 hD0, fderiv_fderiv_densityOf hx hc]
    ring
  have hLam (l m : Fin (d + 1)) : fderiv ℝ (fun w => fderiv ℝ (fun y =>
      g.superpotentialDensity y i k l m) w (Pi.single m 1)) x (Pi.single l 1) =
      densityOf g.coefficient x ^ 2 *
        ((∑ c, ∑ e, (g.coefficient x)⁻¹ c e * g.secondDerivative x c e l m) *
            ((g.coefficient x)⁻¹ i k * (g.coefficient x)⁻¹ l m -
              (g.coefficient x)⁻¹ i l * (g.coefficient x)⁻¹ k m) +
          (-∑ a, ∑ e, (g.coefficient x)⁻¹ i a * (g.coefficient x)⁻¹ k e *
            g.secondDerivative x a e l m) * (g.coefficient x)⁻¹ l m +
          (g.coefficient x)⁻¹ i k * (-∑ a, ∑ e, (g.coefficient x)⁻¹ l a *
            (g.coefficient x)⁻¹ m e * g.secondDerivative x a e l m) -
          (-∑ a, ∑ e, (g.coefficient x)⁻¹ i a * (g.coefficient x)⁻¹ l e *
            g.secondDerivative x a e l m) * (g.coefficient x)⁻¹ k m -
          (g.coefficient x)⁻¹ i l * (-∑ a, ∑ e, (g.coefficient x)⁻¹ k a *
            (g.coefficient x)⁻¹ m e * g.secondDerivative x a e l m)) := by
    unfold superpotentialDensity
    rw [fderiv_fderiv_mul_of_critical hD2c (hQc l m) hDD0 (hQ0 l m), hDD,
      fderiv_fderiv_sub (hmulc i k l m) (hmulc i l k m), hII, hII]
    ring
  have hLamd (l m : Fin (d + 1)) : DifferentiableAt ℝ
      (fun w => fderiv ℝ (fun y => g.superpotentialDensity y i k l m) w (Pi.single m 1)) x :=
    ((((g.contDiffOn_superpotentialDensity i k l m).fderiv_of_isOpen U.isOpen (m := ∞)
      (by simp)).clm_apply contDiffOn_const).contDiffAt hU).differentiableAt (by simp)
  have hdiv : ∑ l, fderiv ℝ (fun w => g.superpotential w i k l) x (Pi.single l 1) =
      ∑ l, ∑ m, fderiv ℝ (fun w => fderiv ℝ (fun y => g.superpotentialDensity y i k l m) w
        (Pi.single m 1)) x (Pi.single l 1) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold superpotential
    rw [fderiv_fun_sum fun m _ => hLamd l m, _root_.sum_apply]
  have halg := pseudotensor_algebra (fun a b => (g.coefficient x)⁻¹ a b) (g.secondDerivative x)
    (g.coefficient_inv_symmetric hx) (secondDerivative_symm_left hx)
    (secondDerivative_symm_right hx) i k
  have hscal : scalarOf g.coefficient x = ∑ a, ∑ b, (g.coefficient x)⁻¹ a b *
      ricciOf g.coefficient x a b := by
    unfold scalarOf
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hE : g.raisedEinstein x i k = ∑ a, ∑ b, (g.coefficient x)⁻¹ i a *
      (g.coefficient x)⁻¹ k b * ricciOf g.coefficient x a b -
      (g.coefficient x)⁻¹ i k * scalarOf g.coefficient x / 2 := by
    unfold raisedEinstein
    rw [← sum_inv_mul_coefficient hx i k, Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hdiv, Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => hLam l m]
  simp only [← Finset.mul_sum]
  rw [halg, hE, hscal]
  simp only [ricciOf_of_critical hx hc]
  ring

/-- **The pseudotensor vanishes at a point where the first derivatives vanish.** -/
theorem pseudotensor_eq_zero (i k : Fin (d + 1)) : g.pseudotensor x i k = 0 := by
  have hpos := g.densityOf_pos hx
  unfold pseudotensor
  rw [divergence_superpotential_eq hx hc, mul_div_cancel_left₀ _ (by positivity), sub_self]

omit hx hc in
/-- **The conservation of the total energy and momentum**: if `G^{ik} = κ T^{ik}` on `U`, then
`∂_k (|g| (κ T^{ik} + t^{ik})) = 0` on `U`. -/
theorem divergence_total_eq_zero {κ : ℝ} {T : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {z : MinkowskiModel d}
    (hz : z ∈ U) (i : Fin (d + 1)) :
    ∑ k, fderiv ℝ (fun w => densityOf g.coefficient w ^ 2 *
      (κ * T w i k + g.pseudotensor w i k)) z (Pi.single k 1) = 0 := by
  have hU := U.isOpen.mem_nhds hz
  have hev (k : Fin (d + 1)) : (fun w => densityOf g.coefficient w ^ 2 *
      (κ * T w i k + g.pseudotensor w i k)) =ᶠ[𝓝 z]
      fun w => (1 / 2 : ℝ) *
        ∑ l, fderiv ℝ (fun v => g.superpotential v i k l) w (Pi.single l 1) :=
    eventually_of_mem hU fun w hw => by
      have hpos := g.densityOf_pos hw
      simp only
      rw [← hT w hw i k]
      unfold pseudotensor
      field_simp
      ring
  have hd (k : Fin (d + 1)) : DifferentiableAt ℝ
      (fun w => ∑ l, fderiv ℝ (fun v => g.superpotential v i k l) w (Pi.single l 1)) z :=
    DifferentiableAt.fun_sum fun l _ =>
      ((((g.contDiffOn_superpotential i k l).fderiv_of_isOpen U.isOpen (m := ∞)
        (by simp)).clm_apply contDiffOn_const).contDiffAt hU).differentiableAt (by simp)
  have h := g.divergence_divergence_superpotential hz i
  calc ∑ k, fderiv ℝ (fun w => densityOf g.coefficient w ^ 2 *
        (κ * T w i k + g.pseudotensor w i k)) z (Pi.single k 1) =
        ∑ k, (1 / 2 : ℝ) * fderiv ℝ (fun w => ∑ l, fderiv ℝ (fun v => g.superpotential v i k l) w
          (Pi.single l 1)) z (Pi.single k 1) :=
        Finset.sum_congr rfl fun k _ => by
          rw [(hev k).fderiv_eq, fderiv_const_mul (hd k), smul_apply, smul_eq_mul]
    _ = 0 := by rw [← Finset.mul_sum, h, mul_zero]

omit hx hc in
/-- **The divergence of the superpotential is symmetric**: `∂_l h^{ikl} = ∂_l h^{kil}` on `U`. -/
theorem divergence_superpotential_symm {z : MinkowskiModel d} (hz : z ∈ U) (i k : Fin (d + 1)) :
    ∑ l, fderiv ℝ (fun w => g.superpotential w i k l) z (Pi.single l 1) =
      ∑ l, fderiv ℝ (fun w => g.superpotential w k i l) z (Pi.single l 1) := by
  have hU := U.isOpen.mem_nhds hz
  have hLc (p q l m : Fin (d + 1)) :
      ContDiffAt ℝ 2 (fun w => g.superpotentialDensity w p q l m) z :=
    ((g.contDiffOn_superpotentialDensity p q l m).contDiffAt hU).of_le (by simp)
  have hdiv (p q : Fin (d + 1)) :
      ∑ l, fderiv ℝ (fun w => g.superpotential w p q l) z (Pi.single l 1) =
        ∑ l, ∑ m, fderiv ℝ (fun w => fderiv ℝ (fun y => g.superpotentialDensity y p q l m) w
          (Pi.single m 1)) z (Pi.single l 1) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold superpotential
    rw [fderiv_fun_sum fun m _ => (((hLc p q l m).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num), _root_.sum_apply]
  set N : Fin (d + 1) → Fin (d + 1) → MinkowskiModel d → ℝ := fun l m w =>
    densityOf g.coefficient w ^ 2 * ((g.coefficient w)⁻¹ k l * (g.coefficient w)⁻¹ i m -
      (g.coefficient w)⁻¹ i l * (g.coefficient w)⁻¹ k m) with hN
  have hNc (l m : Fin (d + 1)) : ContDiffOn ℝ ∞ (N l m) U :=
    (g.contDiffOn_densityOf.pow 2).mul
      (((g.contDiffOn_coefficient_inv k l).mul (g.contDiffOn_coefficient_inv i m)).sub
        ((g.contDiffOn_coefficient_inv i l).mul (g.contDiffOn_coefficient_inv k m)))
  have hdiff (l m : Fin (d + 1)) :
      (fun w => g.superpotentialDensity w i k l m - g.superpotentialDensity w k i l m) =ᶠ[𝓝 z]
        N l m :=
    eventually_of_mem hU fun w hw => by
      simp only [hN, superpotentialDensity]
      rw [g.coefficient_inv_symmetric hw k i]
      ring
  set R : Fin (d + 1) → Fin (d + 1) → ℝ := fun l m =>
    fderiv ℝ (fun w => fderiv ℝ (N l m) w (Pi.single m 1)) z (Pi.single l 1) with hR
  have hterm (l m : Fin (d + 1)) :
      fderiv ℝ (fun w => fderiv ℝ (fun y => g.superpotentialDensity y i k l m) w
          (Pi.single m 1)) z (Pi.single l 1) -
        fderiv ℝ (fun w => fderiv ℝ (fun y => g.superpotentialDensity y k i l m) w
          (Pi.single m 1)) z (Pi.single l 1) = R l m := by
    rw [← fderiv_fderiv_sub (hLc i k l m) (hLc k i l m)]
    have h2 : (fun w => fderiv ℝ (fun y => g.superpotentialDensity y i k l m -
        g.superpotentialDensity y k i l m) w (Pi.single m 1)) =ᶠ[𝓝 z]
        fun w => fderiv ℝ (N l m) w (Pi.single m 1) := by
      filter_upwards [(hdiff l m).eventuallyEq_nhds] with w hw
      rw [hw.fderiv_eq]
    rw [h2.fderiv_eq]
  have hanti (l m : Fin (d + 1)) : R l m = -R m l := by
    simp only [hR]
    rw [fderiv_fderiv_comm (hNc l m) hz l m]
    have hf : N l m = fun w => -N m l w := funext fun w => by simp only [hN]; ring
    have hf' : (fun w => fderiv ℝ (fun v => -N m l v) w (Pi.single l 1)) =
        fun w => -fderiv ℝ (N m l) w (Pi.single l 1) :=
      funext fun w => by rw [fderiv_fun_neg, neg_apply]
    rw [hf, hf', fderiv_fun_neg, neg_apply]
  have hsum : ∑ l, ∑ m, R l m = 0 := by
    have h2 : ∑ l, ∑ m, R l m = -∑ l, ∑ m, R l m :=
      calc ∑ l, ∑ m, R l m = ∑ m, ∑ l, R l m := Finset.sum_comm
        _ = ∑ m, ∑ l, -R m l :=
            Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => hanti l m
        _ = -∑ m, ∑ l, R m l := by simp only [Finset.sum_neg_distrib]
    linarith
  rw [hdiv, hdiv, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun l _ => (Finset.sum_sub_distrib _ _).symm]
  simp only [hterm]
  exact hsum

omit hx hc in
/-- The raised Einstein tensor is symmetric on `U`. -/
theorem raisedEinstein_symm {z : MinkowskiModel d} (hz : z ∈ U) (i k : Fin (d + 1)) :
    g.raisedEinstein z i k = g.raisedEinstein z k i := by
  have hric (a b : Fin (d + 1)) : ricciOf g.coefficient z a b = ricciOf g.coefficient z b a := by
    have h := g.toLorentzMetric.ricci_symmetric (⟨z, hz⟩ : U)
      (LorentzMetric.chartField (physicalChart ⟨z, hz⟩) (Pi.single a 1) ⟨z, hz⟩)
      (LorentzMetric.chartField (physicalChart ⟨z, hz⟩) (Pi.single b 1) ⟨z, hz⟩)
    rwa [toLorentzMetric_ricci_chartField, toLorentzMetric_ricci_chartField] at h
  unfold raisedEinstein
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    rw [hric b a, g.coefficient_symmetric hz b a]
    ring

omit hx hc in
/-- **The pseudotensor is symmetric**: `t^{ik} = t^{ki}` on `U`. -/
theorem pseudotensor_symm {z : MinkowskiModel d} (hz : z ∈ U) (i k : Fin (d + 1)) :
    g.pseudotensor z i k = g.pseudotensor z k i := by
  unfold pseudotensor
  rw [g.divergence_superpotential_symm hz i k, g.raisedEinstein_symm hz i k]

end CoordinateMetric

end ProjectAinos.SmoothGeometry
