/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormDerivative
public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeExteriorDerivative

/-! # Exterior and covariant differentiation of two-forms -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

omit [IsManifold I ∞ M] in
/-- Actual inverse-chart coefficients are evaluations on pulled-back constant fields. -/
theorem chartCoefficients_chartFields {k : ℕ} (α : NativeForm I M k)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (v : Fin k → E) :
    chartCoefficients e α (e x) v = α x (fun i => chartField e (v i) x) := by
  have h := congrArg (fun A : TM x [⋀^Fin k]→L[ℝ] ℝ =>
    A (fun i => chartField e (v i) x)) (chartLift_chartCoefficients he α hx)
  change chartCoefficients e α (e x)
    (fun i => chartTangentMap e x (chartField e (v i) x)) = _ at h
  simpa only [chartTangentMap_field he hx] using h

/-- Scalar differentiation of two-form coefficients is the native directional derivative. -/
theorem twoForm_chart_derivative (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (u v w : E) :
    mvfderiv I (fun y => F y ![chartField e v y, chartField e w y]) x (chartField e u x) =
      fderiv ℝ (fun y => chartCoefficients e (fun z => F z) y ![v, w]) (e x) u := by
  have hf := Tensor.SmoothBilinear.mdifferentiableAt_apply (smoothTwoFormBilinear F)
    (chartField_mdifferentiableAt he hx v) (chartField_mdifferentiableAt he hx w)
  simp only [smoothTwoFormBilinear_apply] at hf
  rw [mvfderiv_chartField he hx hf]
  have hcoeff : (fun y => chartCoefficients e (fun z => F z) y ![v, w]) =ᶠ[𝓝 (e x)]
      (fun y => F y ![chartField e v y, chartField e w y]) ∘ e.symm := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    have h := chartCoefficients_chartFields (fun z => F z) he (e.map_target hy) ![v, w]
    rw [e.right_inv hy] at h
    have hv : (fun i : Fin 2 => chartField e (![v, w] i) (e.symm y)) =
        ![chartField e v (e.symm y), chartField e w (e.symm y)] := by
      ext i
      fin_cases i <;> rfl
    rw [hv] at h
    exact h
  exact congrArg (fun L : E →L[ℝ] ℝ => L u) hcoeff.fderiv_eq.symm

/-- The exterior derivative is the three alternating scalar derivatives in any chart. -/
theorem exteriorDerivative_chartFields (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (u v w : E) :
    smoothExteriorDerivative F x ![chartField e u x, chartField e v x, chartField e w x] =
      mvfderiv I (fun y => F y ![chartField e v y, chartField e w y]) x (chartField e u x) -
      mvfderiv I (fun y => F y ![chartField e u y, chartField e w y]) x (chartField e v x) +
      mvfderiv I (fun y => F y ![chartField e u y, chartField e v y]) x (chartField e w x) := by
  rw [twoForm_chart_derivative F he hx, twoForm_chart_derivative F he hx,
    twoForm_chart_derivative F he hx]
  have h := chartCoefficients_chartFields (fun y => smoothExteriorDerivative F y) he hx ![u, v, w]
  rw [chartCoefficients_smoothExteriorDerivative F he (e.map_source hx),
    extDeriv_two ((F.chartCoefficients_contDiffAt he (e.map_source hx)).differentiableAt (by simp))] at h
  convert h.symm using 1
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Torsion-freeness cancels the connection corrections in the exterior derivative. -/
theorem exteriorDerivative_eq_covariant (g : LorentzMetric σ d M)
    (F : SmoothForm I M 2) (x : M) (u v w : TM x) :
    smoothExteriorDerivative F x ![u, v, w] =
      g.twoFormDerivative F x v w u - g.twoFormDerivative F x u w v +
        g.twoFormDerivative F x u v w := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  suffices h : ∀ a b c : E,
      smoothExteriorDerivative F x ![chartField e a x, chartField e b x, chartField e c x] =
        g.twoFormDerivative F x (chartField e b x) (chartField e c x) (chartField e a x) -
        g.twoFormDerivative F x (chartField e a x) (chartField e c x) (chartField e b x) +
        g.twoFormDerivative F x (chartField e a x) (chartField e b x) (chartField e c x) by
    simpa only [chartField_tangentMap he hx] using
      h (chartTangentMap e x u) (chartTangentMap e x v) (chartTangentMap e x w)
  intro a b c
  have hs (a b : E) :
      g.leviCivita (chartField e b) x (chartField e a x) =
      g.leviCivita (chartField e a) x (chartField e b x) := by
    have h := (CovariantDerivative.torsion_eq_zero_iff g.leviCivita).mp g.leviCivita_torsion
      (chartField_mdifferentiableAt he hx a) (chartField_mdifferentiableAt he hx b)
    rwa [chartField_bracket he hx, sub_eq_zero] at h
  rw [exteriorDerivative_chartFields F he hx,
    g.twoFormDerivative_apply F (chartField_mdifferentiableAt he hx _) (chartField_mdifferentiableAt he hx _),
    g.twoFormDerivative_apply F (chartField_mdifferentiableAt he hx _) (chartField_mdifferentiableAt he hx _),
    g.twoFormDerivative_apply F (chartField_mdifferentiableAt he hx _) (chartField_mdifferentiableAt he hx _)]
  rw [hs a b, hs a c, hs b c]
  have hsk := twoFormBilinear_skew (F x) (chartField e b x)
    (g.leviCivita (chartField e a) x (chartField e c x))
  rw [twoFormBilinear_apply, twoFormBilinear_apply] at hsk
  rw [hsk]
  ring

/-- The homogeneous equation is the cyclic covariant derivative identity. -/
theorem exteriorDerivative_zero_iff_covariant (g : LorentzMetric σ d M)
    (F : SmoothForm I M 2) :
    smoothExteriorDerivative F = 0 ↔
      ∀ x (u v w : TM x), g.twoFormDerivative F x v w u +
        g.twoFormDerivative F x w u v + g.twoFormDerivative F x u v w = 0 := by
  constructor
  · intro h x u v w
    have hx := congrArg (fun A : SmoothForm I M 3 => A x ![u, v, w]) h
    change smoothExteriorDerivative F x ![u, v, w] = 0 at hx
    rw [g.exteriorDerivative_eq_covariant, g.twoFormDerivative_skew F x u w v,
      sub_neg_eq_add] at hx
    exact hx
  · intro h
    ext x z
    have hz : z = ![z 0, z 1, z 2] := by ext i; fin_cases i <;> rfl
    rw [hz, g.exteriorDerivative_eq_covariant, g.twoFormDerivative_skew F x (z 0) (z 2) (z 1),
      sub_neg_eq_add]
    exact h x (z 0) (z 1) (z 2)

/-- Closedness is equivalent to the cyclic covariant component equation in every smooth chart. -/
theorem exteriorDerivative_zero_iff_components (g : LorentzMetric σ d M)
    (F : SmoothForm I M 2) :
    smoothExteriorDerivative F = 0 ↔
      ∀ (e : OpenPartialHomeomorph M E), e ∈ IsManifold.maximalAtlas I ∞ M →
        ∀ x ∈ e.source, ∀ i j k : Fin (d + 1),
          g.twoFormCovariantComponent F e x i j k +
          g.twoFormCovariantComponent F e x j k i +
          g.twoFormCovariantComponent F e x k i j = 0 := by
  constructor
  · intro h e _ x _ i j k
    exact (g.exteriorDerivative_zero_iff_covariant F).mp h x
      (chartField e (Pi.single i 1) x) (chartField e (Pi.single j 1) x)
      (chartField e (Pi.single k 1) x)
  · intro h
    ext x : 1
    let e := chartAt E x
    have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas x
    have hx : x ∈ e.source := mem_chart_source E x
    apply nativeForm_eq_of_chartCoefficients he hx
      (α := fun y => smoothExteriorDerivative F y) (β := fun _ => 0)
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    apply Module.Basis.ext_alternating (Pi.basisFun ℝ (Fin (d + 1)))
    intro f _
    simp only [Pi.basisFun_apply]
    change chartCoefficients e (fun y => smoothExteriorDerivative F y) (e x)
      (fun i => Pi.single (f i) 1) = 0
    rw [chartCoefficients_chartFields _ he hx]
    have hd := g.exteriorDerivative_eq_covariant F x
      (chartField e (Pi.single (f 0) 1) x) (chartField e (Pi.single (f 1) 1) x)
      (chartField e (Pi.single (f 2) 1) x)
    rw [g.twoFormDerivative_skew F x (chartField e (Pi.single (f 0) 1) x)
      (chartField e (Pi.single (f 2) 1) x), sub_neg_eq_add] at hd
    have hz := hd.trans (h e he x hx (f 0) (f 1) (f 2))
    convert hz using 1
    congr 1
    ext i
    fin_cases i <;> rfl

end ProjectAInos.SmoothGeometry.LorentzMetric
