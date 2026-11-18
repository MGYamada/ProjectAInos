/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFamily
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateVariation
public import ProjectAinos.SmoothGeometry.Lorentzian.PalatiniAlgebra
public import ProjectAinos.SmoothGeometry.MetricDensityDerivative

/-!
# The variation `g + ε h` of a coordinate metric

For a coordinate metric `g` on an open set `U` and a family of forms `h`, the coefficients of
`g + ε h` form the family `variationFamily g h`. This file gives its derivatives in `ε` at `0`
and the relations of the unvaried metric that the first variation of the scalar curvature uses:

* `hasDerivAt_variationFamily_inv`: `δ g^{ac} = −g^{am} h_{mn} g^{nc}`;
* `hasDerivAt_variationFamily_density`: `δ √|g| = ½ g^{ab} h_{ab} √|g|`;
* `fderiv_coefficient_inv`, `fderiv_densityOf`: `∂_k g^{bc} = −Γ^b_{kd} g^{dc} − Γ^c_{kd} g^{bd}`
  and `∂_k √|g| = Γ^c_{ck} √|g|`, from metric compatibility;
* the symmetry of the Christoffel symbols and of their variation in the lower indices.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

/-- The coefficient matrix `h(eᵢ, eⱼ)` of a family of forms. -/
def formCoeff (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (z : MinkowskiModel d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun i j => h z (Pi.single i 1) (Pi.single j 1)

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
  (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)

/-- The coefficients of `g + ε h`, as a function of `(ε, z)`. -/
def variationFamily (p : ℝ × MinkowskiModel d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  g.coefficient p.2 + p.1 • formCoeff h p.2

theorem variationFamily_apply (p : ℝ × MinkowskiModel d) (i j : Fin (d + 1)) :
    g.variationFamily h p i j = g.coefficient p.2 i j + p.1 * formCoeff h p.2 i j := by
  simp [variationFamily]

theorem variationFamily_zero : (fun z => g.variationFamily h (0, z)) = g.coefficient := by
  funext z
  simp [variationFamily]

theorem addVariation_coefficient (hh : ContDiffOn ℝ ∞ h U) (ε : ℝ) (hε : g.IsAdmissible h ε) :
    (g.addVariation h hh ε hε).coefficient = fun z => g.variationFamily h (ε, z) := by
  funext z
  ext i j
  simp [coefficient, variationFamily, formCoeff]

variable {g h}

theorem contDiffAt_variationFamily (hh : ContDiff ℝ ∞ h) {p : ℝ × MinkowskiModel d}
    (hp : p.2 ∈ U) (i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => g.variationFamily h q i j) p := by
  have e : (fun q => g.variationFamily h q i j) =
      fun q => g.coefficient q.2 i j + q.1 * h q.2 (Pi.single i 1) (Pi.single j 1) :=
    funext fun q => g.variationFamily_apply h q i j
  rw [e]
  have h1 : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => g.coefficient q.2 i j) p :=
    ((g.coefficient_contDiffOn i j).contDiffAt (U.isOpen.mem_nhds hp)).comp p contDiffAt_snd
  have h2 : ContDiff ℝ ∞ (fun z => h z (Pi.single i 1) (Pi.single j 1)) :=
    (hh.clm_apply contDiff_const).clm_apply contDiff_const
  exact h1.add (contDiffAt_fst.mul (h2.contDiffAt.comp p contDiffAt_snd))

theorem variationFamily_det_zero {x : MinkowskiModel d} (hx : x ∈ U) :
    (g.variationFamily h (0, x)).det ≠ 0 := by
  simpa [variationFamily] using g.coefficient_det_ne_zero ⟨x, hx⟩

theorem contDiffAt_variationChristoffel (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d}
    (hx : x ∈ U) (k i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => familyChristoffel (g.variationFamily h) q k i j) ((0 : ℝ), x) :=
  contDiffAt_familyChristoffel (fun i j => contDiffAt_variationFamily (g := g) hh hx i j)
    (variationFamily_det_zero hx) k i j

/-- **The variation of the inverse metric**, `δ g^{ac} = −g^{am} h_{mn} g^{nc}`. -/
theorem hasDerivAt_variationFamily_inv (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d}
    (hx : x ∈ U) (a c : Fin (d + 1)) :
    HasDerivAt (fun ε => (g.variationFamily h (ε, x))⁻¹ a c)
      (-((g.coefficient x)⁻¹ * formCoeff h x * (g.coefficient x)⁻¹) a c) 0 := by
  set A := g.coefficient x
  set H := formCoeff h x
  have hC := fun i j => contDiffAt_variationFamily (g := g) hh (p := ((0 : ℝ), x)) hx i j
  have hdet := variationFamily_det_zero (g := g) (h := h) hx
  set M' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.of fun a c =>
    fderiv ℝ (fun q => (g.variationFamily h q)⁻¹ a c) ((0 : ℝ), x) (1, 0)
  have hM (a c : Fin (d + 1)) :
      HasDerivAt (fun ε => (g.variationFamily h (ε, x))⁻¹ a c) (M' a c) 0 :=
    hasDerivAt_slice ((contDiffAt_familyInv hC hdet a c).differentiableAt (by simp))
  have hfam (ε : ℝ) : g.variationFamily h (ε, x) = A + ε • H := rfl
  have hA : A.det ≠ 0 := by simpa [hfam] using hdet
  have hcont : Continuous (fun ε : ℝ => (A + ε • H).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), (A + ε • H).det ≠ 0 :=
    hcont.continuousAt.eventually_ne (by simpa using hA)
  have hprod (a b : Fin (d + 1)) : HasDerivAt
      (fun ε => ∑ m, (g.variationFamily h (ε, x))⁻¹ a m * (A m b + ε * H m b))
      (∑ m, (M' a m * A m b + A⁻¹ a m * H m b)) 0 := by
    refine HasDerivAt.fun_sum fun m _ => ?_
    have h2 : HasDerivAt (fun ε : ℝ => A m b + ε * H m b) (H m b) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (H m b)).const_add (A m b)
    convert (hM a m).mul h2 using 1
    simp [hfam]
  have hzero (a b : Fin (d + 1)) : ∑ m, (M' a m * A m b + A⁻¹ a m * H m b) = 0 := by
    have hconst : (fun ε => ∑ m, (g.variationFamily h (ε, x))⁻¹ a m * (A m b + ε * H m b))
        =ᶠ[𝓝 0] fun _ => (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) a b := by
      filter_upwards [hev] with ε hε
      have hi := Matrix.nonsing_inv_mul (A + ε • H) (isUnit_iff_ne_zero.mpr hε)
      have h' := congrFun (congrFun hi a) b
      rw [Matrix.mul_apply] at h'
      simpa [hfam] using h'
    exact (hprod a b).unique ((hasDerivAt_const _ _).congr_of_eventuallyEq hconst)
  have hmat : M' * A = -(A⁻¹ * H) := by
    ext a b
    have := hzero a b
    simp only [Matrix.mul_apply, Matrix.neg_apply, Finset.sum_add_distrib] at this ⊢
    linarith
  have hsol : M' = -(A⁻¹ * H * A⁻¹) := by
    have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)
    calc M' = M' * (A * A⁻¹) := by rw [hAA, Matrix.mul_one]
      _ = (M' * A) * A⁻¹ := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hmat, Matrix.neg_mul]
  have := hM a c
  rwa [show M' a c = (-(A⁻¹ * H * A⁻¹)) a c by rw [hsol]] at this

theorem coefficient_transpose {x : MinkowskiModel d} (hx : x ∈ U) :
    (g.coefficient x).transpose = g.coefficient x :=
  Matrix.ext fun i j => g.coefficient_symmetric hx j i

theorem coefficient_inv_symmetric {x : MinkowskiModel d} (hx : x ∈ U) (a b : Fin (d + 1)) :
    (g.coefficient x)⁻¹ a b = (g.coefficient x)⁻¹ b a := by
  have h := Matrix.transpose_nonsing_inv (g.coefficient x)
  rw [g.coefficient_transpose hx] at h
  exact congrFun (congrFun h b) a

/-- **The variation of the density**, `δ √|g| = ½ g^{ab} h_{ab} √|g|`. -/
theorem hasDerivAt_variationFamily_density (hs : ∀ z v w, h z v w = h z w v)
    {x : MinkowskiModel d} (hx : x ∈ U) :
    HasDerivAt (fun ε => familyDensity (g.variationFamily h) (ε, x))
      ((∑ a, ∑ b, (g.coefficient x)⁻¹ a b * formCoeff h x a b) / 2 *
        densityOf g.coefficient x) 0 := by
  set A := g.coefficient x
  set H := formCoeff h x
  let Af : Fin (d + 1) → Fin (d + 1) → ℝ := fun i j => A i j
  let Hf : Fin (d + 1) → Fin (d + 1) → ℝ := fun i j => H i j
  have hA : (Matrix.of Af).det ≠ 0 := g.coefficient_det_ne_zero ⟨x, hx⟩
  let D : (Fin (d + 1) → Fin (d + 1) → ℝ) → ℝ := fun B => Real.sqrt |Matrix.det (Matrix.of B)|
  have hD := MetricDensity.differentiableAt_density Af hA
  have hpath : HasDerivAt (fun ε : ℝ => Af + ε • Hf) Hf 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const Hf).const_add Af
  have hcomp := hD.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  -- the direction `H` is `B A + A Bᵀ` with `B = ½ H A⁻¹`
  have hHT : H.transpose = H := Matrix.ext fun i j => hs x _ _
  have hAiT : (A⁻¹).transpose = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, g.coefficient_transpose hx]
  have hAA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)
  have hAA' : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)
  let B : Fin (d + 1) → Fin (d + 1) → ℝ := fun i j => ((1 / 2 : ℝ) • (H * A⁻¹)) i j
  have hdir : Hf = Matrix.of B * Matrix.of Af + Matrix.of Af * (Matrix.of B).transpose := by
    change H = ((1 / 2 : ℝ) • (H * A⁻¹)) * A + A * ((1 / 2 : ℝ) • (H * A⁻¹)).transpose
    rw [Matrix.transpose_smul, Matrix.transpose_mul, hAiT, hHT, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, hAA, ← Matrix.mul_assoc, hAA', Matrix.mul_one,
      Matrix.one_mul, ← add_smul]
    norm_num
  have htr : Matrix.trace (Matrix.of B) = (∑ a, ∑ b, A⁻¹ a b * H a b) / 2 := by
    simp only [B, Matrix.trace, Matrix.diag, Matrix.of_apply, Matrix.smul_apply,
      Matrix.mul_apply, smul_eq_mul]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [g.coefficient_inv_symmetric hx b a]
    ring
  have hval : fderiv ℝ D Af Hf =
      (∑ a, ∑ b, A⁻¹ a b * H a b) / 2 * densityOf g.coefficient x := by
    rw [hdir, MetricDensity.fderiv_density_compatible Af B hA]
    rw [htr]
    rfl
  rw [hval] at hcomp
  exact hcomp

/-! ### Relations of the unvaried metric -/

/-- The Christoffel symbols of coefficients that are symmetric near a point are symmetric in
the lower indices. -/
theorem christoffelOf_symm {C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {y : MinkowskiModel d} (hC : ∀ᶠ z in 𝓝 y, ∀ i j, C z i j = C z j i) (k i j : Fin (d + 1)) :
    christoffelOf C y k i j = christoffelOf C y k j i := by
  have hd (a b : Fin (d + 1)) : fderiv ℝ (fun z => C z a b) y = fderiv ℝ (fun z => C z b a) y :=
    Filter.EventuallyEq.fderiv_eq (hC.mono fun z hz => hz a b)
  unfold christoffelOf
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hd i l, hd l j, hd j i]
  ring

theorem variationFamily_symm (hs : ∀ z v w, h z v w = h z w v) {p : ℝ × MinkowskiModel d}
    (hp : p.2 ∈ U) (i j : Fin (d + 1)) :
    g.variationFamily h p i j = g.variationFamily h p j i := by
  rw [g.variationFamily_apply, g.variationFamily_apply, g.coefficient_symmetric hp i j]
  simp only [formCoeff, Matrix.of_apply, hs p.2 (Pi.single i 1)]

/-- The variation of the Christoffel symbols is symmetric in the lower indices. -/
theorem christoffelVariation_symm (hs : ∀ z v w, h z v w = h z w v) {x : MinkowskiModel d}
    (hx : x ∈ U) (k i j : Fin (d + 1)) :
    familyChristoffelDeriv (g.variationFamily h) x k i j =
      familyChristoffelDeriv (g.variationFamily h) x k j i := by
  have hU : ∀ᶠ q : ℝ × MinkowskiModel d in 𝓝 ((0 : ℝ), x), q.2 ∈ U :=
    continuousAt_snd.eventually (U.isOpen.mem_nhds hx)
  have heq : (fun q => familyChristoffel (g.variationFamily h) q k i j) =ᶠ[𝓝 ((0 : ℝ), x)]
      fun q => familyChristoffel (g.variationFamily h) q k j i := by
    filter_upwards [hU] with q hq
    refine christoffelOf_symm ?_ k i j
    filter_upwards [U.isOpen.mem_nhds hq] with z hz i j
    exact variationFamily_symm hs (p := (q.1, z)) hz i j
  unfold familyChristoffelDeriv
  rw [heq.fderiv_eq]

theorem christoffelOf_coefficient_symm {x : MinkowskiModel d} (hx : x ∈ U) (k i j : Fin (d + 1)) :
    christoffelOf g.coefficient x k i j = christoffelOf g.coefficient x k j i := by
  refine christoffelOf_symm ?_ k i j
  filter_upwards [U.isOpen.mem_nhds hx] with z hz i j
  exact g.coefficient_symmetric hz i j

/-- The inverse metric in the inclusion chart is the inverse matrix. -/
theorem chartInverse_physicalChart (x y : U) (i j : Fin (d + 1)) :
    g.toLorentzMetric.chartInverse (physicalChart x) y i j = (g.coefficient y)⁻¹ i j := by
  have hc (a : Fin (d + 1)) : Tensor.coordinateCovector y
      (chartTangentEquiv (physicalChart_mem x) (by simp : y ∈ (physicalChart x).source)) a =
        chartCovector (physicalChart x) y a := by
    ext v
    exact congrFun (chartTangentEquiv_apply (physicalChart_mem x)
      (by simp : y ∈ (physicalChart x).source) v) a
  rw [← g.toLorentzMetric_inverseComponent x y i j, inverseComponent, hc]
  rfl

theorem contDiffAt_densityOf {x : MinkowskiModel d} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (fun z => densityOf g.coefficient z) x := by
  have hC (i j : Fin (d + 1)) : ContDiffAt ℝ ∞
      (fun q : ℝ × MinkowskiModel d => g.coefficient q.2 i j) ((0 : ℝ), x) :=
    ((g.coefficient_contDiffOn i j).contDiffAt (U.isOpen.mem_nhds hx)).comp ((0 : ℝ), x)
      contDiffAt_snd
  have h0 := contDiffAt_familyDensity (Cp := fun q => g.coefficient q.2) hC
    (g.coefficient_det_ne_zero ⟨x, hx⟩)
  have hin : ContDiffAt ℝ ∞ (fun z : MinkowskiModel d => ((0 : ℝ), z)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  exact h0.comp x hin

/-- **Metric compatibility for the inverse**, `∂_k g^{bc} = −Γ^b_{kd} g^{dc} − Γ^c_{kd} g^{bd}`. -/
theorem fderiv_coefficient_inv {x : MinkowskiModel d} (hx : x ∈ U) (b c k : Fin (d + 1)) :
    fderiv ℝ (fun z => (g.coefficient z)⁻¹ b c) x (Pi.single k 1) =
      -∑ e, (christoffelOf g.coefficient x b k e * (g.coefficient x)⁻¹ e c +
        christoffelOf g.coefficient x c k e * (g.coefficient x)⁻¹ b e) := by
  let y : U := ⟨x, hx⟩
  have hnat := g.toLorentzMetric.mvfderiv_chartInverse_chartField (physicalChart_mem y)
    (by simp : y ∈ (physicalChart y).source) b c k
  have hfun : (fun z : U => g.toLorentzMetric.chartInverse (physicalChart y) z b c) =
      fun z : U => (g.coefficient z)⁻¹ b c :=
    funext fun z => g.chartInverse_physicalChart y z b c
  rw [hfun, mvfderiv_val y y (((g.contDiffOn_coefficient_inv b c).contDiffAt
    (U.isOpen.mem_nhds hx)).differentiableAt (by simp))] at hnat
  rw [hnat]
  simp only [g.toLorentzMetric_chartChristoffel, g.chartInverse_physicalChart]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [g.coefficient_inv_symmetric hx c e]

/-- The derivative of the density, `∂_k √|g| = Γ^c_{ck} √|g|`. -/
theorem fderiv_densityOf {x : MinkowskiModel d} (hx : x ∈ U) (k : Fin (d + 1)) :
    fderiv ℝ (fun z => densityOf g.coefficient z) x (Pi.single k 1) =
      densityOf g.coefficient x * ∑ c, christoffelOf g.coefficient x c c k := by
  let y : U := ⟨x, hx⟩
  have hnat := g.toLorentzMetric.chartDensity_derivative (physicalChart_mem y)
    (by simp : y ∈ (physicalChart y).source) k
  have hfun : g.toLorentzMetric.chartDensity (physicalChart y) =
      fun z : U => densityOf g.coefficient z :=
    funext fun z => g.toLorentzMetric_chartDensity y z
  rw [hfun, mvfderiv_val y y ((g.contDiffAt_densityOf hx).differentiableAt (by simp))] at hnat
  rw [hnat]
  simp only [g.toLorentzMetric_chartChristoffel]
  ring

end CoordinateMetric

end ProjectAinos.SmoothGeometry
