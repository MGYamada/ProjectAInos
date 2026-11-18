/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Tensor.TrilinearDerivative
public import ProjectAinos.SmoothGeometry.Lorentzian.ChartCurvature

/-! # The covariant derivative of the curvature and the second Bianchi identity

The covariant derivative of the Riemann tensor of a Lorentz metric is the Leibniz correction of
`Tensor.trilinearCovariantDerivative` applied to the smooth curvature tensor. The direction
comes last: `g.curvatureDerivative x v w z u = (∇_u R)(v, w)z`. Landau–Lifshitz write the
transported vector first and the antisymmetric pair last, so this is their `R^i_{klm;n}` with
`k` the slot of `z`, `(l, m)` the pair `(v, w)` and `n` the direction; the library's
`R^l_{ijk} = (R(∂_i, ∂_j)∂_k)^l` is their `R^l_{kij}`.

* `curvatureDerivative_apply`: on locally `C¹` fields, `(∇_u R)(X, Y)Z` is
  `∇_u(R(X, Y)Z) − R(∇_u X, Y)Z − R(X, ∇_u Y)Z − R(X, Y)∇_u Z`.
* `leviCivita_chart_components`, `bilinearCovariantDerivative_chart`: the components of the
  covariant derivative of a vector field and of a covariant two-tensor in a chart.
* `chartCurvatureDerivative_eq`: in a chart, `∇_m R^l_{ijk}` is `∂_m R^l_{ijk}` plus
  `Γ^l_{ma} R^a_{ijk} − Γ^a_{mi} R^l_{ajk} − Γ^a_{mj} R^l_{iak} − Γ^a_{mk} R^l_{ija}`.
* `curvature_second_bianchi`: `(∇_u R)(v, w) + (∇_v R)(w, u) + (∇_w R)(u, v) = 0` on any
  tangent vectors (§92), and `chartCurvatureDerivative_bianchi` in components.

The proof of the Bianchi identity takes the coordinate fields of a chart as a frame. Their
brackets vanish, so on them `R(B, C) = [∇_B, ∇_C]`, and the cyclic sum of the triple covariant
derivatives cancels in pairs. It uses no inertial chart and no second partial derivatives.
-/

@[expose] public section
noncomputable section

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- The covariant derivative of the curvature, `(∇_u R)(v, w)z`, with the direction `u` in the
last slot. -/
def curvatureDerivative (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x :=
  Tensor.trilinearCovariantDerivative g.leviCivita g.curvature g.curvature_smooth x

/-- Applying the curvature to fields preserves their local regularity. -/
theorem contMDiffAt_curvature_apply {n : ℕ∞} {X Y Z : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) n (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) n (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) n (T% Z) x) :
    ContMDiffAt I ((I).prod I) n (T% (fun y => g.curvature y (X y) (Y y) (Z y))) x :=
  ((((g.curvature_smooth x).of_le (by exact_mod_cast le_top)).clm_bundle_apply
    hX).clm_bundle_apply hY).clm_bundle_apply hZ

/-- On locally `C¹` fields, the covariant derivative of the curvature is the Leibniz
correction. -/
theorem curvatureDerivative_apply {X Y Z : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) 1 (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) 1 (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) 1 (T% Z) x) (u : TM x) :
    g.curvatureDerivative x (X x) (Y x) (Z x) u =
      g.leviCivita (fun y => g.curvature y (X y) (Y y) (Z y)) x u -
        g.curvature x (g.leviCivita X x u) (Y x) (Z x) -
        g.curvature x (X x) (g.leviCivita Y x u) (Z x) -
        g.curvature x (X x) (Y x) (g.leviCivita Z x u) :=
  Tensor.trilinearCovariantDerivative_apply g.leviCivita g.curvature_smooth hX hY hZ u

/-- The covariant derivative of the curvature does not depend on the overall sign of the
metric. -/
@[simp] theorem curvatureDerivative_opposite (x : M) :
    g.opposite.curvatureDerivative x = g.curvatureDerivative x := by
  have hR : g.opposite.curvature = g.curvature := funext g.curvature_opposite
  unfold curvatureDerivative
  rw [leviCivita_opposite]
  congr 1

/-- The components of `∇_v V` in a chart: the derivative of the components of `V` and the
Christoffel term. -/
theorem leviCivita_chart_components {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) {V : ∀ x, TM x}
    (hV : ContMDiffAt I ((I).prod I) 1 (T% V) x) (v : E) (k : Fin (d + 1)) :
    chartTangentMap e x (g.leviCivita V x (chartField e v x)) k =
      mvfderiv I (fun y => chartTangentMap e y (V y) k) x (chartField e v x) +
        ∑ i, ∑ j, g.chartChristoffel e x k i j * v i * chartTangentMap e x (V x) j := by
  let C : M → E := fun y => chartTangentMap e y (V y)
  have hC : MDifferentiableAt I I C x :=
    (chartTangentMap_contMDiffAt (n := 1) he hx hV).mdifferentiableAt (by simp)
  have heq : ∀ᶠ y in 𝓝 x, (fun y => chartField e (C y) y) y = V y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact chartField_tangentMap he hy (V y)
  have hW : MDifferentiableAt I ((I).prod I) (T% (fun y => chartField e (C y) y)) x := by
    apply (hV.mdifferentiableAt (by simp)).congr_of_eventuallyEq
    filter_upwards [heq] with y hy
    exact congrArg (fun v => TotalSpace.mk' E y v) hy
  have hcov := g.leviCivita.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hW (hV.mdifferentiableAt (by simp)) Filter.univ_mem heq
  have hd : mvfderiv I (fun y => chartTangentMap e y (V y) k) x =
      (proj k : E →L[ℝ] ℝ).comp (mvfderiv I C x) := by
    change mvfderiv I ((proj k : E →L[ℝ] ℝ) ∘ C) x = _
    rw [mvfderiv_comp x (proj k : E →L[ℝ] ℝ).mdifferentiableAt hC,
      mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl
  have h := g.leviCivita_chart_coordinates he hx hC v k
  rw [hcov] at h
  rw [hd]
  simpa [C] using h

/-- Components `∇_m R^l_{ijk} = ((∇_{∂m} R)(∂i, ∂j)∂k)^l` of the covariant derivative of
the curvature in a chart. -/
def chartCurvatureDerivative (e : OpenPartialHomeomorph M E) (x : M)
    (l i j k m : Fin (d + 1)) : ℝ :=
  chartTangentMap e x (g.curvatureDerivative x (chartField e (Pi.single i 1) x)
    (chartField e (Pi.single j 1) x) (chartField e (Pi.single k 1) x)
    (chartField e (Pi.single m 1) x)) l

/-- The covariant derivative of a coordinate field, expanded in the coordinate fields. -/
theorem leviCivita_chartField_eq_sum {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (a b : Fin (d + 1)) :
    g.leviCivita (chartField e (Pi.single b 1)) x (chartField e (Pi.single a 1) x) =
      ∑ l, g.chartChristoffel e x l a b • chartField e (Pi.single l 1) x := by
  rw [← chartField_tangentMap he hx
    (g.leviCivita (chartField e (Pi.single b 1)) x (chartField e (Pi.single a 1) x)),
    chartField_eq_sum]
  rfl

/-- Components `∇_k B_{ij}` of the covariant derivative of a smooth covariant two-tensor in a
chart. -/
theorem bilinearCovariantDerivative_chart (B : Tensor.SmoothBilinear («I» := I) (M := M))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (i j k : Fin (d + 1)) :
    Tensor.bilinearCovariantDerivative g.leviCivita B x (chartField e (Pi.single i 1) x)
        (chartField e (Pi.single j 1) x) (chartField e (Pi.single k 1) x) =
      mvfderiv I (fun y => B y (chartField e (Pi.single i 1) y)
        (chartField e (Pi.single j 1) y)) x (chartField e (Pi.single k 1) x) -
      ∑ l, g.chartChristoffel e x l k i *
        B x (chartField e (Pi.single l 1) x) (chartField e (Pi.single j 1) x) -
      ∑ l, g.chartChristoffel e x l k j *
        B x (chartField e (Pi.single i 1) x) (chartField e (Pi.single l 1) x) := by
  rw [Tensor.bilinearCovariantDerivative_apply _ _ (chartField_mdifferentiableAt he hx _)
    (chartField_mdifferentiableAt he hx _), g.leviCivita_chartField_eq_sum he hx k i,
    g.leviCivita_chartField_eq_sum he hx k j]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]

/-- The coordinate formula for the covariant derivative of the curvature. -/
theorem chartCurvatureDerivative_eq {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (l i j k m : Fin (d + 1)) :
    g.chartCurvatureDerivative e x l i j k m =
      mvfderiv I (fun y => g.chartCurvature e y l i j k) x (chartField e (Pi.single m 1) x) +
      ∑ a, g.chartChristoffel e x l m a * g.chartCurvature e x a i j k -
      ∑ a, g.chartChristoffel e x a m i * g.chartCurvature e x l a j k -
      ∑ a, g.chartChristoffel e x a m j * g.chartCurvature e x l i a k -
      ∑ a, g.chartChristoffel e x a m k * g.chartCurvature e x l i j a := by
  have h1 (b : Fin (d + 1)) := (chartField_contMDiffAt he hx (Pi.single b 1)).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)
  rw [chartCurvatureDerivative, g.curvatureDerivative_apply (h1 i) (h1 j) (h1 k),
    g.leviCivita_chartField_eq_sum he hx m i, g.leviCivita_chartField_eq_sum he hx m j,
    g.leviCivita_chartField_eq_sum he hx m k]
  have hR : ContMDiffAt I ((I).prod I) 1 (T% (fun y => g.curvature y
      (chartField e (Pi.single i 1) y) (chartField e (Pi.single j 1) y)
      (chartField e (Pi.single k 1) y))) x :=
    g.contMDiffAt_curvature_apply (h1 i) (h1 j) (h1 k)
  simp only [map_sub, Pi.sub_apply, g.leviCivita_chart_components he hx hR, map_sum,
    map_smul, sum_apply, smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp [chartCurvature, Pi.single_apply]

/-- Coordinate fields commute under the Levi-Civita connection at every point of the chart
source. -/
theorem covariantField_chartField_comm {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (a b : E) :
    g.covariantField (chartField e a) (chartField e b) x =
      g.covariantField (chartField e b) (chartField e a) x :=
  sub_eq_zero.mp ((g.covariantField_commutator (chartField_mdifferentiableAt he hx a)
    (chartField_mdifferentiableAt he hx b)).trans (chartField_bracket he hx a b))

/-- On coordinate fields `(∇_A R)(B, C)W` is a difference of triple covariant derivatives and
two curvature terms. -/
private theorem curvatureDerivative_chartField {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (a b c k : E) :
    g.curvatureDerivative x (chartField e b x) (chartField e c x) (chartField e k x)
        (chartField e a x) =
      g.covariantField (chartField e a)
          (g.covariantField (chartField e b) (g.covariantField (chartField e c)
            (chartField e k))) x -
        g.covariantField (chartField e a)
          (g.covariantField (chartField e c) (g.covariantField (chartField e b)
            (chartField e k))) x -
        g.curvature x (g.covariantField (chartField e a) (chartField e b) x)
          (chartField e c x) (chartField e k x) -
        g.curvature x (chartField e b x)
          (g.covariantField (chartField e a) (chartField e c) x) (chartField e k x) -
        (g.covariantField (chartField e b)
            (g.covariantField (chartField e c) (g.covariantField (chartField e a)
              (chartField e k))) x -
          g.covariantField (chartField e c)
            (g.covariantField (chartField e b) (g.covariantField (chartField e a)
              (chartField e k))) x) := by
  have hinf (v : E) (y : M) (hy : y ∈ e.source) := chartField_contMDiffAt he hy v
  have h1 (v : E) := (hinf v x hx).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have h2 (v : E) (y : M) (hy : y ∈ e.source) :=
    (hinf v y hy).of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hcov (v : E) {Z : ∀ y, TM y} (hZ : ContMDiffAt I ((I).prod I) ∞ (T% Z) x) :
      ContMDiffAt I ((I).prod I) ∞ (T% (g.covariantField (chartField e v) Z)) x :=
    g.contMDiffAt_covariantField (n := ⊤) (hinf v x hx) (by simpa using hZ)
  rw [g.curvatureDerivative_apply (h1 b) (h1 c) (h1 k)]
  change g.covariantField (chartField e a)
        (fun y => g.curvature y (chartField e b y) (chartField e c y) (chartField e k y)) x -
      g.curvature x (g.covariantField (chartField e a) (chartField e b) x)
        (chartField e c x) (chartField e k x) -
      g.curvature x (chartField e b x)
        (g.covariantField (chartField e a) (chartField e c) x) (chartField e k x) -
      g.curvature x (chartField e b x) (chartField e c x)
        (g.covariantField (chartField e a) (chartField e k) x) = _
  have hbracket (y : M) (hy : y ∈ e.source) (Z : ∀ y, TM y) :
      g.covariantField (mlieBracket I (chartField e b) (chartField e c)) Z y = 0 := by
    simp only [covariantField, chartField_bracket he hy, map_zero]
  have hfield : ∀ᶠ y in 𝓝 x,
      (fun y => g.curvature y (chartField e b y) (chartField e c y) (chartField e k y)) y =
        (g.covariantField (chartField e b) (g.covariantField (chartField e c) (chartField e k)) -
          g.covariantField (chartField e c)
            (g.covariantField (chartField e b) (chartField e k))) y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    rw [g.curvature_apply (h2 b y hy) (h2 c y hy) (h2 k y hy), curvatureField,
      hbracket y hy, sub_zero]
    rfl
  have hBCW := hcov b (hcov c (hinf k x hx))
  have hCBW := hcov c (hcov b (hinf k x hx))
  rw [g.covariantField_congr_right
      ((g.contMDiffAt_curvature_apply (hinf b x hx) (hinf c x hx)
        (hinf k x hx)).mdifferentiableAt (by simp))
      (mdifferentiableAt_sub_section (hBCW.mdifferentiableAt (by simp))
        (hCBW.mdifferentiableAt (by simp))) hfield,
    g.covariantField_sub_right (hBCW.mdifferentiableAt (by simp))
      (hCBW.mdifferentiableAt (by simp)),
    g.curvature_apply ((hinf b x hx).of_le (by simp)) ((hinf c x hx).of_le (by simp))
      ((hcov a (hinf k x hx)).of_le (by simp)), curvatureField, hbracket x hx, sub_zero]

/-- **The second Bianchi identity.** For any tangent vectors,
`(∇_u R)(v, w)z + (∇_v R)(w, u)z + (∇_w R)(u, v)z = 0`. -/
theorem curvature_second_bianchi (x : M) (u v w z : TM x) :
    g.curvatureDerivative x v w z u + g.curvatureDerivative x w u z v +
      g.curvatureDerivative x u v z w = 0 := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  suffices h : ∀ a b c k : E,
      g.curvatureDerivative x (chartField e b x) (chartField e c x) (chartField e k x)
          (chartField e a x) +
        g.curvatureDerivative x (chartField e c x) (chartField e a x) (chartField e k x)
          (chartField e b x) +
        g.curvatureDerivative x (chartField e a x) (chartField e b x) (chartField e k x)
          (chartField e c x) = 0 by
    simpa only [chartField_tangentMap he hx] using
      h (chartTangentMap e x u) (chartTangentMap e x v) (chartTangentMap e x w)
        (chartTangentMap e x z)
  intro a b c k
  rw [curvatureDerivative_chartField g he hx a b c k,
    curvatureDerivative_chartField g he hx b c a k,
    curvatureDerivative_chartField g he hx c a b k,
    g.covariantField_chartField_comm he hx b a, g.covariantField_chartField_comm he hx c b,
    g.covariantField_chartField_comm he hx a c,
    g.curvature_swap x (chartField e c x) (g.covariantField (chartField e a) (chartField e b) x),
    g.curvature_swap x (chartField e b x) (g.covariantField (chartField e c) (chartField e a) x),
    g.curvature_swap x (chartField e a x) (g.covariantField (chartField e b) (chartField e c) x)]
  abel

/-- The second Bianchi identity in components:
`∇_m R^l_{ijk} + ∇_i R^l_{jmk} + ∇_j R^l_{mik} = 0`. -/
theorem chartCurvatureDerivative_bianchi (e : OpenPartialHomeomorph M E) (x : M)
    (l i j k m : Fin (d + 1)) :
    g.chartCurvatureDerivative e x l i j k m + g.chartCurvatureDerivative e x l j m k i +
      g.chartCurvatureDerivative e x l m i k j = 0 := by
  have h := congrArg (fun v => chartTangentMap e x v l)
    (g.curvature_second_bianchi x (chartField e (Pi.single m 1) x)
      (chartField e (Pi.single i 1) x) (chartField e (Pi.single j 1) x)
      (chartField e (Pi.single k 1) x))
  simpa only [chartCurvatureDerivative, map_add, map_zero, Pi.add_apply, Pi.zero_apply] using h

end ProjectAinos.SmoothGeometry.LorentzMetric
