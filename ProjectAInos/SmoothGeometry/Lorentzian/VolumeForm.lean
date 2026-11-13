/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.VolumeDensity
public import ProjectAInos.SmoothGeometry.Manifold.OrientedAtlas
public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeChart
public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeGluing
public import ProjectAInos.SmoothGeometry.DifferentialForm.Coordinates

/-! # Oriented Lorentz volume form from local density

Compatible signed charts supply only the orientation. The metric supplies
the positive density. Local normalized forms agree and glue to an actual
smooth, nowhere-zero top form.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Module Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

omit [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M] in
/-- Equality of native top forms can be tested on one actual tangent basis. -/
theorem nativeTopForm_ext_basis {x : M}
    (b : Basis (Fin (d + 1)) ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x))
    {α β : TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin (d + 1)]→L[ℝ] ℝ}
    (h : α b = β b) : α = β := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [α.toAlternatingMap.eq_smul_basis_det b, β.toAlternatingMap.eq_smul_basis_det b]
  exact congrArg (fun r : ℝ => r • b.det) h

/-- Local volume representative with a chosen constant orientation sign. -/
def localVolume (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M (MinkowskiModel d))
    (s : ℝ) : NativeForm 𝓘(ℝ, MinkowskiModel d) M (d + 1) :=
  fun x => (s * g.chartDensity e x) • chartLift e (fun _ => coordinateForm id) x

/-- Pointwise determinant formula, with tangent vectors as matrix columns. -/
theorem localVolume_apply (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M (MinkowskiModel d)) (s : ℝ) (x : M)
    (v : Fin (d + 1) → TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.localVolume e s x v = s * g.chartDensity e x *
      Matrix.det (fun i j => chartTangentMap e x (v j) i) := by
  change s * g.chartDensity e x *
    coordinateForm id (fun i => mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) e x (v i)) = _
  rw [coordinateForm_apply]
  congr 1
  rw [← Matrix.det_transpose]
  rfl

theorem localVolume_contMDiffAt (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) (s : ℝ)
    {x : M} (hx : x ∈ e.source) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d [⋀^Fin (d + 1)]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (MinkowskiModel d [⋀^Fin (d + 1)]→L[ℝ] ℝ) y
        (g.localVolume e s y)) x :=
  (contMDiffAt_const.mul (g.chartDensity_contMDiffAt he hx)).smul_section
    (chartLift_contMDiffAt he hx contDiffAt_const)

theorem localVolume_chartBasis (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) (s : ℝ)
    {x : M} (hx : x ∈ e.source) :
    g.localVolume e s x (chartBasis he hx) = s * g.chartDensity e x := by
  rw [g.localVolume_apply]
  have h : (fun i j => chartTangentMap e x (chartBasis he hx j) i) =
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
    ext i j
    simp [chartBasis_apply, chartTangentMap_field he hx, Matrix.one_apply, Pi.single_apply]
  rw [h, Matrix.det_one, mul_one]

theorem localVolume_otherChartBasis (g : LorentzMetric σ d M)
    {e e' : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) (s : ℝ)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    g.localVolume e' s x (chartBasis he hx) = s * g.chartDensity e' x *
      Matrix.det (fun i j => fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single j 1) i) := by
  rw [g.localVolume_apply]
  simp only [chartBasis_apply, chartTangentMap_transition he he' hx hx', chartTangentMap_field he hx]

/-- Compatible orientation signs make the local normalized forms agree. -/
theorem localVolume_eq_of_sign (g : LorentzMetric σ d M)
    {e e' : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) (s s' : ℝ)
    (hs : s' * Matrix.det (fun i j => fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single j 1) i) =
      s * |Matrix.det (fun i j => fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single j 1) i)|) :
    g.localVolume e s x = g.localVolume e' s' x := by
  apply nativeTopForm_ext_basis (chartBasis he hx)
  rw [g.localVolume_chartBasis he s hx, g.localVolume_otherChartBasis he he' s' hx hx',
    g.chartDensity_transition he he' hx hx']
  have h := congrArg (fun r : ℝ => r * g.chartDensity e' x) hs
  nlinarith

/-- Local orientation compatibility and density covariance prove equality on overlaps. -/
theorem localVolume_compatible (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (p q x : M) (hp : x ∈ (o.chart p).source) (hq : x ∈ (o.chart q).source) :
    g.localVolume (o.chart p) (o.sign p) x = g.localVolume (o.chart q) (o.sign q) x :=
  g.localVolume_eq_of_sign (o.mem_atlas p) (o.mem_atlas q) hp hq (o.sign p) (o.sign q)
    (o.compatible p q x hp hq)

/-- The smooth oriented volume form, constructed by gluing the normalized local forms. -/
def volumeForm (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) :
    SmoothForm 𝓘(ℝ, MinkowskiModel d) M (d + 1) :=
  smoothGlue 𝓘(ℝ, MinkowskiModel d) (fun p => (o.chart p).source)
    (fun p => (o.chart p).open_source) o.covers
    (fun p => g.localVolume (o.chart p) (o.sign p))
    (fun p _x hx => (g.localVolume_contMDiffAt (o.mem_atlas p) (o.sign p) hx).contMDiffWithinAt)
    (fun p q x hx => g.localVolume_compatible o p q x hx.1 hx.2)

theorem volumeForm_apply (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    {p x : M} (hx : x ∈ (o.chart p).source) :
    g.volumeForm o x = g.localVolume (o.chart p) (o.sign p) x :=
  smoothGlue_apply _ _ _ _ _ _ _ hx

/-- In each selected oriented chart the coefficient is its sign times the positive density. -/
theorem chartCoefficients_volumeForm (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (p : M) {y : MinkowskiModel d} (hy : y ∈ (o.chart p).target) :
    chartCoefficients (o.chart p) (fun x => g.volumeForm o x) y =
      (o.sign p * g.chartDensity (o.chart p) ((o.chart p).symm y)) • coordinateForm id := by
  ext v
  change g.volumeForm o ((o.chart p).symm y)
    (fun i => mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (o.chart p).symm y (v i)) = _
  rw [g.volumeForm_apply o ((o.chart p).map_target hy)]
  have h := chartCoefficients_chartLift (o.mem_atlas p) (fun _ => coordinateForm (n := d + 1) id) hy
  exact congrArg (fun r : ℝ => (o.sign p * g.chartDensity (o.chart p) ((o.chart p).symm y)) * r)
    (congrArg (fun A => A v) h)

/-- The absolute value of oriented volume is exactly the intrinsic density. -/
theorem abs_volumeForm (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M)
    (v : Fin (d + 1) → TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    |g.volumeForm o x v| = g.volumeDensity x v := by
  rw [g.volumeForm_apply o (o.mem_source x), g.localVolume_apply,
    abs_mul, abs_mul, o.abs_sign, one_mul,
    abs_of_pos (g.chartDensity_pos (o.mem_atlas x) (o.mem_source x)),
    g.volumeDensity_eq_chart (o.mem_atlas x) (o.mem_source x)]
  ring

/-- The constructed volume is nonzero in every tangent fibre. -/
theorem volumeForm_ne_zero (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M) :
    g.volumeForm o x ≠ 0 := by
  intro h
  have hp := g.volumeDensity_basis_pos x (chartBasis (o.mem_atlas x) (o.mem_source x))
  rw [← g.abs_volumeForm o, h] at hp
  simp at hp

/-- Reversing the orientation negates volume, while its absolute density is unchanged. -/
theorem volumeForm_reverse (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) :
    g.volumeForm o.reverse = -g.volumeForm o := by
  ext x v
  change g.volumeForm o.reverse x v = -(g.volumeForm o x v)
  rw [g.volumeForm_apply o.reverse (o.reverse.mem_source x),
    g.volumeForm_apply o (o.mem_source x)]
  change g.localVolume (o.chart x) (-o.sign x) x v = -g.localVolume (o.chart x) (o.sign x) x v
  rw [g.localVolume_apply, g.localVolume_apply]
  ring

/-- The result depends on the orientation, not on its particular signed chart cover. -/
theorem volumeForm_eq_of_compatible (g : LorentzMetric σ d M) (o o' : OrientedAtlas (d + 1) M)
    (h : o.Compatible o') : g.volumeForm o = g.volumeForm o' := by
  ext x : 1
  rw [g.volumeForm_apply o (o.mem_source x), g.volumeForm_apply o' (o'.mem_source x)]
  exact g.localVolume_eq_of_sign (o.mem_atlas x) (o'.mem_atlas x) (o.mem_source x) (o'.mem_source x)
    (o.sign x) (o'.sign x) (h x x x (o.mem_source x) (o'.mem_source x))

/-- Reversing the entire metric leaves the oriented volume unchanged. -/
theorem opposite_volumeForm (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) :
    g.opposite.volumeForm o = g.volumeForm o := by
  ext x v
  rw [g.opposite.volumeForm_apply o (o.mem_source x), g.volumeForm_apply o (o.mem_source x),
    g.opposite.localVolume_apply, g.localVolume_apply, g.opposite_chartDensity]

/-- In the standard orientation, model volume is the positive density times the coordinate top form. -/
theorem volumeForm_standard (g : LorentzMetric σ d (MinkowskiModel d)) (x : MinkowskiModel d) :
    g.volumeForm (OrientedAtlas.standard (d + 1)) x =
      g.chartDensity (OpenPartialHomeomorph.refl (MinkowskiModel d)) x • coordinateForm id := by
  have h := g.chartCoefficients_volumeForm (OrientedAtlas.standard (d + 1)) x
    (y := x) (by trivial)
  change chartCoefficients (OpenPartialHomeomorph.refl (MinkowskiModel d))
    (fun y => g.volumeForm (OrientedAtlas.standard (d + 1)) y) x =
    (1 * g.chartDensity (OpenPartialHomeomorph.refl (MinkowskiModel d)) x) • coordinateForm id at h
  rw [chartCoefficients_refl, one_mul] at h
  exact h

end ProjectAInos.SmoothGeometry.LorentzMetric
