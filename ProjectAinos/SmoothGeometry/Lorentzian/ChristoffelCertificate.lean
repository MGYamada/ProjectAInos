/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateCurvature
public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorChristoffel
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-!
# Curvature from a certified table of Christoffel symbols

The Christoffel symbols of a coordinate metric are `Γ^k_{ij} = ½ g^{kl}(∂_i g_{jl} + ∂_j g_{li}
− ∂_l g_{ij})`. For an explicit metric it is easier to guess a table `Γ` and to check the lowered
identity `g_{lq} Γ^q_{ij} = ½(∂_i g_{jl} + ∂_j g_{li} − ∂_l g_{ij})`, which needs no inverse
matrix (`christoffelOf_eq_of_lowered`). The curvature and the Ricci tensor are then computed from
the table:

* `ricciOfChristoffel`, `curvatureOf`: the formulas of `ricciOf` and of the chart curvature with a
  table `G` in place of the Christoffel symbols;
* `ricciOf_eq_ricciOfChristoffel`, `toLorentzMetric_chartCurvature_eq_curvatureOf`: a table that
  agrees with the Christoffel symbols near a point gives the Ricci tensor and the curvature there;
* `ricciOfChristoffel_eq_sum_curvatureOf`: `Ric_{jk} = R^i_{ijk}`;
* `fderiv_single_eq_deriv_update`: a partial derivative is a one-variable derivative.

The instances: the zero table for the Minkowski metric (`minkowski_christoffelOf`), and the plane
`−dt² + e^{2t} dx²` of two-dimensional de Sitter space, whose table `Γ^0_{11} = e^{2t}`,
`Γ^1_{01} = Γ^1_{10} = 1` is certified (`DeSitterPlane.christoffelOf_eq`) and gives
`Ric = g` (`DeSitterPlane.ricciOf_eq`, `DeSitterPlane.ricci_chartField`).
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric Matrix

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

/-! ### Curvature from a table -/

/-- The Ricci formula `Ric_{jk} = ∂_i G^i_{jk} − ∂_j G^i_{ik} + G^i_{ia} G^a_{jk} −
G^i_{ja} G^a_{ik}` for a table `G` of Christoffel symbols. -/
def ricciOfChristoffel (G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (y : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  ∑ i, (fderiv ℝ (fun z => G z i j k) y (Pi.single i 1) -
    fderiv ℝ (fun z => G z i i k) y (Pi.single j 1) +
    ∑ a, (G y i i a * G y a j k - G y i j a * G y a i k))

/-- The curvature formula `R^l_{ijk} = ∂_i G^l_{jk} − ∂_j G^l_{ik} + G^l_{ia} G^a_{jk} −
G^l_{ja} G^a_{ik}` for a table `G` of Christoffel symbols. -/
def curvatureOf (G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (y : MinkowskiModel d) (l i j k : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun z => G z l j k) y (Pi.single i 1) -
    fderiv ℝ (fun z => G z l i k) y (Pi.single j 1) +
    ∑ a, (G y l i a * G y a j k - G y l j a * G y a i k)

/-- `Ric_{jk} = R^i_{ijk}` for the formulas of a table. -/
theorem ricciOfChristoffel_eq_sum_curvatureOf
    (G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (y : MinkowskiModel d) (j k : Fin (d + 1)) :
    ricciOfChristoffel G y j k = ∑ i, curvatureOf G y i i j k := rfl

/-- A table that agrees with the Christoffel symbols of `C` near `y` gives the Ricci tensor
of `C` at `y`. -/
theorem ricciOf_eq_ricciOfChristoffel
    {C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ} {y : MinkowskiModel d}
    (hG : ∀ᶠ z in 𝓝 y, ∀ k i j, christoffelOf C z k i j = G z k i j) (j k : Fin (d + 1)) :
    ricciOf C y j k = ricciOfChristoffel G y j k := by
  have he (a b c : Fin (d + 1)) :
      (fun z => christoffelOf C z a b c) =ᶠ[𝓝 y] fun z => G z a b c := by
    filter_upwards [hG] with z hz using hz a b c
  have hy := hG.self_of_nhds
  unfold ricciOf ricciOfChristoffel
  simp only [(he _ _ _).fderiv_eq, hy]

/-- A table that agrees with the Christoffel symbols near `y` gives the curvature components in
the inclusion chart at `y`. -/
theorem toLorentzMetric_chartCurvature_eq_curvatureOf {U : Opens (MinkowskiModel d)}
    (g : CoordinateMetric σ d U) (x y : U)
    {G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    (hG : ∀ᶠ z in 𝓝 (y : MinkowskiModel d), ∀ k i j,
      christoffelOf g.coefficient z k i j = G z k i j) (l i j k : Fin (d + 1)) :
    g.toLorentzMetric.chartCurvature (physicalChart x) y l i j k = curvatureOf G y l i j k := by
  have he (a b c : Fin (d + 1)) :
      (fun z => christoffelOf g.coefficient z a b c) =ᶠ[𝓝 (y : MinkowskiModel d)]
        fun z => G z a b c := by
    filter_upwards [hG] with z hz using hz a b c
  have hy := hG.self_of_nhds
  rw [g.toLorentzMetric_chartCurvature x y, curvatureOf]
  simp only [(he _ _ _).fderiv_eq, hy]

/-! ### The certificate -/

/-- **A certified table of Christoffel symbols.** A table whose lowering
`g_{lq} Γ^q_{ij}` is `½(∂_i g_{jl} + ∂_j g_{li} − ∂_l g_{ij})` is the table of the
Christoffel symbols; no inverse matrix is computed. -/
theorem christoffelOf_eq_of_lowered {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
    {z : MinkowskiModel d} (hz : z ∈ U) (Γ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (hΓ : ∀ l i j, ∑ q, g.coefficient z l q * Γ q i j =
      (fderiv ℝ (fun w => g.coefficient w j l) z (Pi.single i 1) +
        fderiv ℝ (fun w => g.coefficient w l i) z (Pi.single j 1) -
        fderiv ℝ (fun w => g.coefficient w i j) z (Pi.single l 1)) / 2)
    (k i j : Fin (d + 1)) : christoffelOf g.coefficient z k i j = Γ k i j := by
  set A := g.coefficient z with hA
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (g.coefficient_det_ne_zero ⟨z, hz⟩).isUnit
  have hrec (X : Fin (d + 1) → ℝ) : X = A⁻¹ *ᵥ (A *ᵥ X) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hlow : A *ᵥ (fun q => christoffelOf g.coefficient z q i j) = A *ᵥ (fun q => Γ q i j) := by
    funext l
    simp only [Matrix.mulVec, dotProduct]
    rw [hA, g.sum_coefficient_mul_christoffelOf hz l i j, hΓ l i j]
  have h := congrFun (congrArg (fun X => A⁻¹ *ᵥ X) hlow) k
  simp only [← hrec] at h
  exact h

/-- A partial derivative is the derivative of the function of one co-ordinate. -/
theorem fderiv_single_eq_deriv_update {f : MinkowskiModel d → ℝ} {y : MinkowskiModel d}
    (hf : DifferentiableAt ℝ f y) (i : Fin (d + 1)) :
    fderiv ℝ f y (Pi.single i 1) = deriv (fun s => f (Function.update y i s)) (y i) := by
  have hf' : DifferentiableAt ℝ f (Function.update y i (y i)) := by
    rwa [Function.update_eq_self]
  have h := (hf'.hasFDerivAt.comp_hasDerivAt (y i) (hasDerivAt_update y i (y i))).deriv
  rw [Function.update_eq_self] at h
  exact h.symm

/-! ### Instances -/

/-- The Christoffel symbols of the Minkowski metric vanish: the zero table is certified. -/
theorem minkowski_christoffelOf {U : Opens (MinkowskiModel d)} {z : MinkowskiModel d}
    (hz : z ∈ U) (k i j : Fin (d + 1)) :
    christoffelOf (minkowski σ d U).coefficient z k i j = 0 := by
  have hc (a b : Fin (d + 1)) : (fun w => (minkowski σ d U).coefficient w a b) =
      fun _ => (minkowski σ d U).coefficient z a b := rfl
  refine christoffelOf_eq_of_lowered (minkowski σ d U) hz (fun _ _ _ => 0) (fun l i j => ?_) k i j
  simp [hc]

/-- The Ricci tensor of the Minkowski metric vanishes. -/
theorem minkowski_ricciOf {U : Opens (MinkowskiModel d)} {z : MinkowskiModel d}
    (hz : z ∈ U) (j k : Fin (d + 1)) : ricciOf (minkowski σ d U).coefficient z j k = 0 := by
  have hG : ∀ᶠ w in 𝓝 z, ∀ k i j,
      christoffelOf (minkowski σ d U).coefficient w k i j = (fun _ _ _ _ => 0) w k i j := by
    filter_upwards [U.isOpen.mem_nhds hz] with w hw using minkowski_christoffelOf hw
  rw [ricciOf_eq_ricciOfChristoffel hG]
  simp [ricciOfChristoffel]

namespace DeSitterPlane

/-- The form `−dt² + e^{2t} dx²` at the point `q = (t, x)` of the plane. -/
def form (q : MinkowskiModel 1) : MinkowskiModel 1 →L[ℝ] MinkowskiModel 1 →L[ℝ] ℝ :=
  (-1 : ℝ) • (ContinuousLinearMap.proj 0 : MinkowskiModel 1 →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj 0 : MinkowskiModel 1 →L[ℝ] ℝ) +
    Real.exp (2 * q 0) • (ContinuousLinearMap.proj 1 : MinkowskiModel 1 →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj 1 : MinkowskiModel 1 →L[ℝ] ℝ)

/-- The form evaluated on two vectors. -/
theorem form_apply (q v w : MinkowskiModel 1) :
    form q v w = -(v 0 * w 0) + Real.exp (2 * q 0) * (v 1 * w 1) := by
  simp [form]

/-- The form is smooth on the whole plane. -/
theorem contDiff_form : ContDiff ℝ ∞ form := by
  refine contDiff_clm_apply_iff.mpr fun v => contDiff_clm_apply_iff.mpr fun w => ?_
  simp only [form_apply]
  fun_prop

/-- The plane `−dt² + e^{2t} dx²`: the flat slicing of two-dimensional de Sitter space of unit
radius, on the whole plane. -/
def metric : CoordinateMetric .timeNegative 1 ⊤ :=
  ofCriterion form contDiff_form.contDiffOn
    (fun _ _ v w => by rw [form_apply, form_apply]; ring)
    (fun x _ => by rw [form_apply]; simp [LorentzConvention.timeSign])
    (fun x _ v hv => by
      have h0 : v 0 ≠ 0 := fun h => hv (funext fun i => by fin_cases i; exact h)
      rw [form_apply]
      simp only [LorentzConvention.timeSign, Fin.cons_zero, Fin.cons_one, mul_zero, neg_zero,
        zero_add, neg_neg, one_mul]
      exact mul_pos (Real.exp_pos _) (mul_self_pos.mpr h0))

/-- The coefficients of the plane are the values of the form on the basis vectors. -/
theorem coefficient_apply (q : MinkowskiModel 1) (a b : Fin 2) :
    metric.coefficient q a b = form q (Pi.single a 1) (Pi.single b 1) := rfl

/-- The table `Γ^0_{11} = e^{2t}`, `Γ^1_{01} = Γ^1_{10} = 1`, the other symbols zero. -/
def christoffel (q : MinkowskiModel 1) : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  ![![![0, 0], ![0, Real.exp (2 * q 0)]], ![![0, 1], ![1, 0]]]

/-- The derivative of `e^{2t}` along `v` is `2 e^{2t} v⁰`. -/
theorem fderiv_exp (q v : MinkowskiModel 1) :
    fderiv ℝ (fun w : MinkowskiModel 1 => Real.exp (2 * w 0)) q v =
      2 * Real.exp (2 * q 0) * v 0 := by
  have h : HasFDerivAt (fun w : MinkowskiModel 1 => w 0)
      (ContinuousLinearMap.proj 0 : MinkowskiModel 1 →L[ℝ] ℝ) q := hasFDerivAt_apply 0 q
  rw [((h.const_mul 2).exp).fderiv]
  simp
  ring

/-- **The table is certified**: the Christoffel symbols of the plane are `Γ^0_{11} = e^{2t}`,
`Γ^1_{01} = Γ^1_{10} = 1`, the others zero. -/
theorem christoffelOf_eq (z : MinkowskiModel 1) (k i j : Fin 2) :
    christoffelOf metric.coefficient z k i j = christoffel z k i j :=
  christoffelOf_eq_of_lowered metric trivial (christoffel z) (fun l i j => by
    fin_cases l <;> fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_two, coefficient_apply, form_apply, christoffel, fderiv_exp]
    all_goals ring)
    k i j

/-- The Ricci tensor of the plane is `Ric = g`: two-dimensional de Sitter space. -/
theorem ricciOf_eq (q : MinkowskiModel 1) (j k : Fin 2) :
    ricciOf metric.coefficient q j k = metric.coefficient q j k := by
  rw [ricciOf_eq_ricciOfChristoffel (G := christoffel)
    (Eventually.of_forall fun z => christoffelOf_eq z)]
  fin_cases j <;> fin_cases k <;>
    simp [ricciOfChristoffel, Fin.sum_univ_two, christoffel, fderiv_exp, coefficient_apply,
      form_apply]
  all_goals ring

/-- The Ricci tensor of the Lorentz metric of the plane on co-ordinate fields is `g`. -/
theorem ricci_chartField (x y : (⊤ : Opens (MinkowskiModel 1))) (j k : Fin 2) :
    metric.toLorentzMetric.ricci y (chartField (physicalChart x) (Pi.single j 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = metric.coefficient y j k := by
  rw [metric.toLorentzMetric_ricci_chartField x y, ricciOf_eq]

end DeSitterPlane

end CoordinateMetric

end ProjectAinos.SmoothGeometry
