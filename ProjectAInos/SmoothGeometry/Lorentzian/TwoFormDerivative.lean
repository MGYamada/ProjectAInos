/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.CovariantDerivative
public import ProjectAInos.SmoothGeometry.DifferentialForm.TwoForm
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartDerivatives

/-! # The intrinsic Levi-Civita derivative of a native two-form -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- The last argument is the derivative direction: `twoFormDerivative F x v w u = ∇ᵤF(v,w)`. -/
def twoFormDerivative (F : SmoothForm I M 2) (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  Tensor.bilinearCovariantDerivative g.leviCivita (smoothTwoFormBilinear F) x

/-- The intrinsic derivative has the tensor Leibniz formula on locally differentiable fields. -/
theorem twoFormDerivative_apply (F : SmoothForm I M 2) {X Y : ∀ x, TM x} {x : M}
    (hX : MDifferentiableAt I ((I).prod I) (T% X) x)
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x) (u : TM x) :
    g.twoFormDerivative F x (X x) (Y x) u =
      mvfderiv I (fun y => F y ![X y, Y y]) x u -
        F x ![g.leviCivita X x u, Y x] - F x ![X x, g.leviCivita Y x u] := by
  simpa only [twoFormDerivative, smoothTwoFormBilinear_apply] using
    Tensor.bilinearCovariantDerivative_apply g.leviCivita (smoothTwoFormBilinear F) hX hY u

/-- The derivative preserves antisymmetry in the two form slots. -/
theorem twoFormDerivative_skew (F : SmoothForm I M 2) (x : M) (v w u : TM x) :
    g.twoFormDerivative F x v w u = -g.twoFormDerivative F x w v u :=
  Tensor.bilinearCovariantDerivative_skew g.leviCivita (smoothTwoFormBilinear F)
    (fun y v w => twoFormBilinear_skew (F y) v w) x v w u

/-- The packaged hom model retains the recursively constructed coordinate norms and topologies. -/
abbrev twoFormDerivativeBundle : Tensor.SmoothBundle I (M := M) :=
  Tensor.SmoothBundle.hom I (Tensor.SmoothBundle.tangent I)
    (Tensor.SmoothBundle.hom I (Tensor.SmoothBundle.tangent I)
      (Tensor.SmoothBundle.hom I (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.scalar I)))

/-- The intrinsic derivative is a smooth section of the actual three-covariant hom bundle. -/
theorem twoFormDerivative_contMDiffAt (F : SmoothForm I M 2) (x : M) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, (twoFormDerivativeBundle (d := d) (M := M)).Model)) ∞
      (fun y => TotalSpace.mk' (twoFormDerivativeBundle (d := d) (M := M)).Model
        («E» := (twoFormDerivativeBundle (d := d) (M := M)).Fiber) y
        (g.twoFormDerivative F y)) x := by
  let T := Tensor.SmoothBundle.tangent I (M := M)
  let S := Tensor.SmoothBundle.scalar I (M := M)
  apply Tensor.SmoothBundle.contMDiffAt_of_apply T
    (Tensor.SmoothBundle.hom I T (Tensor.SmoothBundle.hom I T S))
  intro X hX
  apply Tensor.SmoothBundle.contMDiffAt_of_apply T (Tensor.SmoothBundle.hom I T S)
  intro Y hY
  apply Tensor.SmoothBundle.contMDiffAt_of_apply T S
  intro U hU
  apply contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_id, ?_⟩
  have hB := (smoothTwoFormBilinear F).contMDiff x
  have h₀ := hB.clm_bundle_apply₂ hX hY
  rw [contMDiffAt_totalSpace] at h₀
  have hd := contMDiffAt_directionalDerivative (n := ⊤) (by simpa using h₀.2) hU
  have hCX := (g.contMDiffAt_leviCivita (n := ⊤) (by simpa using hX)).clm_bundle_apply hU
  have hCY := (g.contMDiffAt_leviCivita (n := ⊤) (by simpa using hY)).clm_bundle_apply hU
  have h₁ := hB.clm_bundle_apply₂ hCX hY
  have h₂ := hB.clm_bundle_apply₂ hX hCY
  rw [contMDiffAt_totalSpace] at h₁ h₂
  apply ((hd.sub h₁.2).sub h₂.2).congr_of_eventuallyEq
  have hXn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hX.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hYn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hY.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  filter_upwards [hXn, hYn] with y hyX hyY
  simpa [S, Tensor.SmoothBundle.scalar] using
    g.twoFormDerivative_apply F (hyX.mdifferentiableAt (by norm_num))
      (hyY.mdifferentiableAt (by norm_num)) (U y)

/-- Bundle the covariant derivative, preserving the existing tangent-bundle topology. -/
def smoothTwoFormDerivative (F : SmoothForm I M 2) :
    (twoFormDerivativeBundle (d := d) (M := M)).Section I :=
  ⟨g.twoFormDerivative F, g.twoFormDerivative_contMDiffAt F⟩

@[simp] theorem smoothTwoFormDerivative_apply (F : SmoothForm I M 2) (x : M)
    (v w u : TM x) : g.smoothTwoFormDerivative F x v w u = g.twoFormDerivative F x v w u := rfl

/-- Native two-form components, evaluated on actual coordinate vector fields. -/
def twoFormComponent (F : NativeForm I M 2) (e : OpenPartialHomeomorph M E)
    (x : M) (i j : Fin (d + 1)) : ℝ :=
  F x ![chartField e (Pi.single i 1) x, chartField e (Pi.single j 1) x]

/-- Covariant components `∇ᵢFⱼₖ`, extracted from the actual three-covariant tensor. -/
def twoFormCovariantComponent (F : SmoothForm I M 2) (e : OpenPartialHomeomorph M E)
    (x : M) (i j k : Fin (d + 1)) : ℝ :=
  g.twoFormDerivative F x (chartField e (Pi.single j 1) x)
    (chartField e (Pi.single k 1) x) (chartField e (Pi.single i 1) x)

/-- The usual two Christoffel corrections follow from the constructed connection. -/
theorem twoFormDerivative_chart (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (i j k : Fin (d + 1)) :
    g.twoFormDerivative F x (chartField e (Pi.single i 1) x)
      (chartField e (Pi.single j 1) x) (chartField e (Pi.single k 1) x) =
      mvfderiv I (fun y => twoFormComponent (fun z => F z) e y i j) x
        (chartField e (Pi.single k 1) x) -
      ∑ l, g.chartChristoffel e x l k i * twoFormComponent (fun z => F z) e x l j -
      ∑ l, g.chartChristoffel e x l k j * twoFormComponent (fun z => F z) e x i l := by
  rw [twoFormDerivative, Tensor.bilinearCovariantDerivative_apply _ _
    (chartField_mdifferentiableAt he hx _) (chartField_mdifferentiableAt he hx _)]
  have hexpand (a b : Fin (d + 1)) :
      g.leviCivita (chartField e (Pi.single b 1)) x (chartField e (Pi.single a 1) x) =
      ∑ l, g.chartChristoffel e x l a b • chartField e (Pi.single l 1) x := by
    rw [← chartField_tangentMap he hx
      (g.leviCivita (chartField e (Pi.single b 1)) x (chartField e (Pi.single a 1) x)),
      chartField_eq_sum]
    rfl
  rw [hexpand k i, hexpand k j]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    smoothTwoFormBilinear_apply, twoFormComponent]

theorem twoFormCovariantComponent_eq (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (i j k : Fin (d + 1)) :
    g.twoFormCovariantComponent F e x i j k =
      mvfderiv I (fun y => twoFormComponent (fun z => F z) e y j k) x
        (chartField e (Pi.single i 1) x) -
      ∑ l, g.chartChristoffel e x l i j * twoFormComponent (fun z => F z) e x l k -
      ∑ l, g.chartChristoffel e x l i k * twoFormComponent (fun z => F z) e x j l :=
  g.twoFormDerivative_chart F he hx j k i

end ProjectAInos.SmoothGeometry.LorentzMetric
