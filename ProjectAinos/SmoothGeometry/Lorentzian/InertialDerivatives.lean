/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CurvatureDerivative
public import ProjectAinos.SmoothGeometry.Lorentzian.CurvatureSymmetry
public import ProjectAinos.SmoothGeometry.Lorentzian.LocalInertial
public import ProjectAinos.SmoothGeometry.Lorentzian.Ricci
public import ProjectAinos.SmoothGeometry.Lorentzian.TwoFormRaised

/-! # Contractions in a chart and derivatives at the centre of an inertial chart

The inverse metric, the Ricci tensor and the scalar curvature have component formulas on the
source of any chart. The inverse metric is written as `g^{ij} = dx^i(♯dx^j)`, a function of the
point that carries no membership proof, so it can be differentiated.

* `contract_chart`, `ricci_chartField`, `scalarCurvature_chart`: the contraction
  `g^{ac} B_{ac}`, `Ric_{jk} = R^i_{ijk}` and `R = g^{ac} Ric_{ac}` in a chart.
* `chartCurvature_contract`: `R^i_{jmk} g^{mk} = g^{il} Ric_{lj}`, from the pair symmetry of the
  curvature.
* At the centre `p` of an inertial chart the Christoffel symbols vanish, so the coordinate
  fields are parallel at `p` (`IsInertialChartAt.leviCivita_chartField`), the inverse metric
  has zero derivative (`IsInertialChartAt.mvfderiv_chartInverse`), and covariant derivatives
  of tensor components are their partial derivatives
  (`IsInertialChartAt.bilinearCovariantDerivative_chartField`,
  `IsInertialChartAt.chartCurvatureDerivative_eq`).
-/

@[expose] public section
noncomputable section

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

omit [IsManifold I ∞ M] in
/-- The derivative of a finite sum of scalar functions is the sum of their derivatives. -/
theorem mvfderiv_finset_sum {ι : Type} (s : Finset ι) {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (f i) x) :
    mvfderiv I (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, mvfderiv I (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mvfderiv_const («I» := I) (0 : ℝ) (x := x)
  | insert a s ha ih =>
    rw [Finset.forall_mem_insert] at hf
    have hs : MDifferentiableAt I 𝓘(ℝ) (fun y => ∑ i ∈ s, f i y) x := by
      simpa only [Finset.sum_fn] using MDifferentiableAt.sum hf.2
    simp only [Finset.sum_insert ha]
    rw [mvfderiv_fun_add hf.1 hs, ih hf.2]

omit [IsManifold I ∞ M] in
/-- A sum of products whose second factors have zero derivative at `x` differentiates through
its first factors. -/
theorem mvfderiv_sum_mul_of_mvfderiv_eq_zero {ι : Type} (s : Finset ι)
    {f k : ι → M → ℝ} {x : M} (hf : ∀ n ∈ s, MDifferentiableAt I 𝓘(ℝ) (f n) x)
    (hk : ∀ n ∈ s, MDifferentiableAt I 𝓘(ℝ) (k n) x)
    (hk0 : ∀ n ∈ s, mvfderiv I (k n) x = 0) :
    mvfderiv I (fun y => ∑ n ∈ s, f n y * k n y) x =
      ∑ n ∈ s, k n x • mvfderiv I (f n) x := by
  rw [mvfderiv_finset_sum s (f := fun n y => f n y * k n y) fun n hn =>
    (hf n hn).mul (hk n hn)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [mvfderiv_fun_mul (hf n hn) (hk n hn), hk0 n hn, smul_zero, zero_add]

omit [IsManifold I ∞ M] in
/-- The double-sum version of `mvfderiv_sum_mul_of_mvfderiv_eq_zero`. -/
theorem mvfderiv_sum_sum_mul_of_mvfderiv_eq_zero {f k : Fin (d + 1) → Fin (d + 1) → M → ℝ}
    {x : M} (hf : ∀ a c, MDifferentiableAt I 𝓘(ℝ) (f a c) x)
    (hk : ∀ a c, MDifferentiableAt I 𝓘(ℝ) (k a c) x)
    (hk0 : ∀ a c, mvfderiv I (k a c) x = 0) :
    mvfderiv I (fun y => ∑ a, ∑ c, f a c y * k a c y) x =
      ∑ a, ∑ c, k a c x • mvfderiv I (f a c) x := by
  have hs (a : Fin (d + 1)) :
      MDifferentiableAt I 𝓘(ℝ) (fun y => ∑ c, f a c y * k a c y) x := by
    simpa only [Finset.sum_fn, Pi.mul_apply] using
      MDifferentiableAt.sum fun c (_ : c ∈ Finset.univ) => (hf a c).mul (hk a c)
  rw [mvfderiv_finset_sum Finset.univ (f := fun a y => ∑ c, f a c y * k a c y)
    fun a _ => hs a]
  exact Finset.sum_congr rfl fun a _ => mvfderiv_sum_mul_of_mvfderiv_eq_zero Finset.univ
    (fun c _ => hf a c) (fun c _ => hk a c) fun c _ => hk0 a c

omit [IsManifold I ∞ M] in
/-- Two continuous linear maps on a tangent space that agree on the coordinate basis of a chart
are equal. -/
theorem ext_chartField {F : Type} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) {L L' : TM x →L[ℝ] F}
    (h : ∀ k, L (chartField e (Pi.single k 1) x) = L' (chartField e (Pi.single k 1) x)) :
    L = L' := by
  ext u
  rw [← chartField_tangentMap he hx u, chartField_eq_sum]
  simp only [map_sum, map_smul, h]

variable (g : LorentzMetric σ d M)

/-- Components `g^{ij} = dx^i(♯dx^j)` of the inverse metric in a chart. -/
def chartInverse (e : OpenPartialHomeomorph M E) (x : M) (i j : Fin (d + 1)) : ℝ :=
  chartCovector e x i (g.chartRaisedCovector e x j)

theorem chartInverse_symmetric (e : OpenPartialHomeomorph M E) (x : M) (i j : Fin (d + 1)) :
    g.chartInverse e x i j = g.chartInverse e x j i :=
  g.sharp_pairing_symm x (chartCovector e x i) (chartCovector e x j)

theorem chartInverse_contMDiffAt {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (i j : Fin (d + 1)) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => g.chartInverse e y i j) x :=
  (proj i : E →L[ℝ] ℝ).contMDiff.contMDiffAt.comp x
    (chartTangentMap_contMDiffAt he hx (g.chartRaisedCovector_contMDiffAt he hx j))

/-- The raised coordinate covector `♯dx^i` in the coordinate basis. -/
theorem chartRaisedCovector_eq_sum {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (i : Fin (d + 1)) :
    g.chartRaisedCovector e x i =
      ∑ l, g.chartInverse e x l i • chartField e (Pi.single l 1) x := by
  rw [← chartField_tangentMap he hx (g.chartRaisedCovector e x i), chartField_eq_sum]
  rfl

/-- The metric contraction `g^{ac} B_{ac}` in a chart. -/
theorem contract_chart {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (B : TM x →L[ℝ] TM x →L[ℝ] ℝ) :
    g.contract x B = ∑ a, ∑ c,
      B (chartField e (Pi.single a 1) x) (chartField e (Pi.single c 1) x) *
        g.chartInverse e x a c := by
  have hc (i : Fin (d + 1)) :
      Tensor.coordinateCovector x (chartTangentEquiv he hx) i = chartCovector e x i := by
    ext v
    exact congrFun (chartTangentEquiv_apply he hx v) i
  rw [g.contract_eq_sum_components x (chartTangentEquiv he hx)]
  simp only [chartTangentEquiv_symm, inverseComponent, hc]
  rfl

/-- The Ricci components `Ric_{jk} = R^i_{ijk}` in a chart. -/
theorem ricci_chartField {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (j k : Fin (d + 1)) :
    g.ricci x (chartField e (Pi.single j 1) x) (chartField e (Pi.single k 1) x) =
      ∑ i, g.chartCurvature e x i i j k := by
  rw [g.ricci_eq_sum x (chartTangentEquiv he hx)]
  simp only [chartTangentEquiv_symm, chartTangentEquiv_apply]
  rfl

/-- The scalar curvature `R = g^{ac} Ric_{ac}` in a chart. -/
theorem scalarCurvature_chart {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) :
    g.scalarCurvature x = ∑ a, ∑ c,
      g.ricci x (chartField e (Pi.single a 1) x) (chartField e (Pi.single c 1) x) *
        g.chartInverse e x a c := by
  rw [scalarCurvature_apply, g.contract_chart he hx]

theorem contract_sub (x : M) (B C : TM x →L[ℝ] TM x →L[ℝ] ℝ) :
    g.contract x (B - C) = g.contract x B - g.contract x C := by
  simp [contract, comp_sub]

/-- Lowering the output of an endomorphism and contracting gives its trace. -/
theorem contract_comp_form (x : M) (A : TM x →L[ℝ] TM x) :
    g.contract x ((g.form x).comp A) = LinearMap.trace ℝ (TM x) A.toLinearMap := by
  have h : (g.sharp x).toContinuousLinearMap.comp ((g.form x).comp A) = A := by
    ext v
    exact g.sharp_flat x (A v)
  rw [contract, h]

/-- Contracting `α(R(w, a)b)` over `a` and `b` gives `Ric(♯α, w)`. -/
theorem contract_curvature_covector (x : M) (α : TM x →L[ℝ] ℝ) (w : TM x) :
    g.contract x ((compL ℝ (TM x) (TM x) ℝ α).comp (g.curvature x w)) =
      g.ricci x (g.sharp x α) w := by
  have h : (compL ℝ (TM x) (TM x) ℝ α).comp (g.curvature x w) =
      ((g.form x).comp (g.curvatureEndomorphism x (g.sharp x α) w)).flip := by
    ext a b
    simp only [comp_apply, compL_apply, flip_apply, curvatureEndomorphism_apply]
    rw [← g.form_sharp_left x α, g.symmetric x (g.sharp x α),
      g.curvature_pair_interchange x w a b]
  rw [h, g.contract_flip, g.contract_comp_form, ricci_apply]

/-- The contraction `R^i_{jmk} g^{mk} = g^{il} Ric_{lj}` in a chart. -/
theorem chartCurvature_contract {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (i j : Fin (d + 1)) :
    ∑ m, ∑ k, g.chartCurvature e x i j m k * g.chartInverse e x m k =
      ∑ l, g.ricci x (chartField e (Pi.single l 1) x) (chartField e (Pi.single j 1) x) *
        g.chartInverse e x l i := by
  have h := g.contract_curvature_covector x (chartCovector e x i)
    (chartField e (Pi.single j 1) x)
  rw [g.contract_chart he hx] at h
  change _ = g.ricci x (g.chartRaisedCovector e x i) _ at h
  rw [g.chartRaisedCovector_eq_sum he hx] at h
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul] at h
  rw [show (∑ l, g.ricci x (chartField e (Pi.single l 1) x) (chartField e (Pi.single j 1) x) *
      g.chartInverse e x l i) = ∑ l, g.chartInverse e x l i *
        g.ricci x (chartField e (Pi.single l 1) x) (chartField e (Pi.single j 1) x) from
    Finset.sum_congr rfl fun l _ => mul_comm _ _, ← h]
  rfl

/-- The derivative of the inverse metric in a chart: metric compatibility gives
`∂_k g^{ij} = −Γ^i_{kb} g^{jb} − Γ^j_{kb} g^{ib}`. -/
theorem mvfderiv_chartInverse_chartField {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (i j k : Fin (d + 1)) :
    mvfderiv I (fun y => g.chartInverse e y i j) x (chartField e (Pi.single k 1) x) =
      -∑ b, (g.chartChristoffel e x i k b * g.chartInverse e x j b +
        g.chartChristoffel e x j k b * g.chartInverse e x i b) := by
  have hα (a : Fin (d + 1)) :=
    (chartCovector_contMDiffAt he hx a).mdifferentiableAt (by simp)
  have hd := g.inversePairing_derivative (hα i) (hα j) (chartField e (Pi.single k 1) x)
  change mvfderiv I (fun y => chartCovector e y i (g.sharp y (chartCovector e y j))) x _ = _
  rw [hd]
  change chartCovector e x j (g.leviCivita (fun y => g.chartRaisedCovector e y i) x
      (chartField e (Pi.single k 1) x)) + chartCovector e x i (g.leviCivita
        (fun y => g.chartRaisedCovector e y j) x (chartField e (Pi.single k 1) x)) = _
  rw [g.leviCivita_chartRaisedCovector he hx, g.leviCivita_chartRaisedCovector he hx]
  simp only [map_neg, map_sum, map_smul, smul_eq_mul, Finset.sum_add_distrib, neg_add]
  rfl

section Inertial

variable {g} {e : OpenPartialHomeomorph M (MinkowskiModel d)} {p : M}

/-- The coordinate fields of an inertial chart are parallel at its centre. -/
theorem IsInertialChartAt.leviCivita_chartField (h : g.IsInertialChartAt e p) (w : E) :
    g.leviCivita (chartField e w) p = 0 := by
  refine ext_chartField h.smooth h.mem_source fun k => ?_
  apply (chartTangentEquiv h.smooth h.mem_source).injective
  rw [zero_apply, map_zero, chartTangentEquiv_apply,
    ← g.chartChristoffelBilinear_eq h.smooth h.mem_source]
  ext l
  simp [chartChristoffelBilinear_apply, h.christoffel_zero]

/-- The raised coordinate covectors of an inertial chart are parallel at its centre. -/
theorem IsInertialChartAt.leviCivita_chartRaisedCovector (h : g.IsInertialChartAt e p)
    (i : Fin (d + 1)) :
    g.leviCivita (fun y => g.chartRaisedCovector e y i) p = 0 := by
  refine ext_chartField h.smooth h.mem_source fun k => ?_
  rw [g.leviCivita_chartRaisedCovector h.smooth h.mem_source]
  simp [h.christoffel_zero]

/-- **The inverse metric has zero derivative at the centre of an inertial chart.** -/
theorem IsInertialChartAt.mvfderiv_chartInverse (h : g.IsInertialChartAt e p)
    (i j : Fin (d + 1)) :
    mvfderiv I (fun y => g.chartInverse e y i j) p = 0 := by
  have hα (k : Fin (d + 1)) :=
    (chartCovector_contMDiffAt h.smooth h.mem_source k).mdifferentiableAt (by simp)
  ext u
  have hd := g.inversePairing_derivative (hα i) (hα j) u
  change mvfderiv I (fun y => chartCovector e y i (g.sharp y (chartCovector e y j))) p u = 0
  rw [hd]
  change chartCovector e p j (g.leviCivita (fun y => g.chartRaisedCovector e y i) p u) +
    chartCovector e p i (g.leviCivita (fun y => g.chartRaisedCovector e y j) p u) = 0
  rw [h.leviCivita_chartRaisedCovector, h.leviCivita_chartRaisedCovector]
  simp

/-- At the centre of an inertial chart the covariant derivative of a smooth bilinear tensor
on coordinate fields is the derivative of its component. -/
theorem IsInertialChartAt.bilinearCovariantDerivative_chartField (h : g.IsInertialChartAt e p)
    (B : Tensor.SmoothBilinear («I» := I) (M := M)) (a c : E) (u : TM p) :
    Tensor.bilinearCovariantDerivative g.leviCivita B p (chartField e a p) (chartField e c p) u =
      mvfderiv I (fun y => B y (chartField e a y) (chartField e c y)) p u := by
  rw [Tensor.bilinearCovariantDerivative_apply _ _
    (chartField_mdifferentiableAt h.smooth h.mem_source a)
    (chartField_mdifferentiableAt h.smooth h.mem_source c),
    h.leviCivita_chartField, h.leviCivita_chartField]
  simp

/-- At the centre of an inertial chart, `∇_m R^l_{ijk} = ∂_m R^l_{ijk}`. -/
theorem IsInertialChartAt.chartCurvatureDerivative_eq (h : g.IsInertialChartAt e p)
    (l i j k m : Fin (d + 1)) :
    g.chartCurvatureDerivative e p l i j k m =
      mvfderiv I (fun y => g.chartCurvature e y l i j k) p (chartField e (Pi.single m 1) p) := by
  rw [g.chartCurvatureDerivative_eq h.smooth h.mem_source]
  simp [h.christoffel_zero]

end Inertial

end ProjectAinos.SmoothGeometry.LorentzMetric
