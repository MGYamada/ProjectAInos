/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Curvature
public import ProjectAInos.SmoothGeometry.Lorentzian.Naturality

/-! # Curvature under smooth metric-preserving maps

Curvature is natural on actual tangent fibres. The underlying maps need not
be globally bijective, and vector-field hypotheses are local at the target point.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]
  (g : LorentzMetric σ d M) (h : LorentzMetric σ d N)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

variable {f : M → N}
  (hf : ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ f)
  (hinv : ∀ y, (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y).IsInvertible)
  (hmetric : ∀ y v w, g.form y v w =
    h.form (f y) (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y v)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y w))
  {X Y Z : ∀ y : N, TangentSpace 𝓘(ℝ, MinkowskiModel d) y} {x : M}

include hf hinv hmetric

/-- A local form of connection naturality, expressed as equality with pullback. -/
theorem covariantField_mpullback
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) (f x)) :
    g.covariantField (mpullback I I f X) (mpullback I I f Y) x =
      mpullback I I f (h.covariantField X Y) x := by
  have he := g.leviCivita_naturality h hf hinv hmetric hY (mpullback I I f X x)
  have hi := congrArg (mfderiv I I f x).inverse he
  simpa only [mpullback_apply, ContinuousLinearMap.IsInvertible.inverse_apply_self (hinv x),
    ContinuousLinearMap.IsInvertible.self_apply_inverse (hinv x), covariantField] using hi

omit hinv hmetric [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M] in
private theorem eventually_mdiff_target
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) (f x)) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I ((I).prod I) (T% Z) (f y) := by
  have hz := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hZ.of_le (by norm_num))
  exact hf.continuous.continuousAt.eventually
    (hz.mono fun y hy => hy.mdifferentiableAt (by norm_num))

/-- Differentiating the naturality identity requires only local `C²` fields. -/
theorem covariantField_mpullback_twice
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) (f x))
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) (f x)) :
    g.covariantField (mpullback I I f X)
        (g.covariantField (mpullback I I f Y) (mpullback I I f Z)) x =
      mpullback I I f (h.covariantField X (h.covariantField Y Z)) x := by
  have hpY := hY.mpullback_vectorField_preimage (hf x) (hinv x) (by simp)
  have hpZ := hZ.mpullback_vectorField_preimage (hf x) (hinv x) (by simp)
  have hYZ := h.contMDiffAt_covariantField (n := 1) (hY.of_le (by norm_num)) hZ
  have hpYZ := hYZ.mpullback_vectorField_preimage (hf x) (hinv x) (by simp)
  have hlocal : ∀ᶠ y in 𝓝 x,
      g.covariantField (mpullback I I f Y) (mpullback I I f Z) y =
        mpullback I I f (h.covariantField Y Z) y := by
    filter_upwards [eventually_mdiff_target hf hZ] with y hy
    exact g.covariantField_mpullback h hf hinv hmetric hy
  rw [g.covariantField_congr_right
    ((g.contMDiffAt_covariantField (n := 1) (hpY.of_le (by norm_num)) hpZ).mdifferentiableAt
      (by norm_num)) (hpYZ.mdifferentiableAt (by norm_num)) hlocal]
  exact g.covariantField_mpullback h hf hinv hmetric (hYZ.mdifferentiableAt (by norm_num))

/-- The connection commutator intertwines pullback of locally `C²` fields. -/
theorem curvatureField_naturality
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) (f x))
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) (f x))
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) (f x)) :
    mfderiv I I f x
      (g.curvatureField (mpullback I I f X) (mpullback I I f Y) (mpullback I I f Z) x) =
      h.curvatureField X Y Z (f x) := by
  let : IsManifold I (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using (inferInstance : IsManifold I 2 M)
  let : IsManifold I (minSmoothness ℝ 2) N := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using (inferInstance : IsManifold I 2 N)
  simp only [curvatureField, map_sub]
  rw [g.covariantField_mpullback_twice h hf hinv hmetric hY hZ,
    g.covariantField_mpullback_twice h hf hinv hmetric hX hZ]
  simp only [mpullback_apply, ContinuousLinearMap.IsInvertible.self_apply_inverse (hinv x)]
  congr 1
  simp only [covariantField]
  rw [g.leviCivita_naturality h hf hinv hmetric (hZ.mdifferentiableAt (by norm_num)),
    ← mpullback_mlieBracket (hX.mdifferentiableAt (by norm_num))
      (hY.mdifferentiableAt (by norm_num)) (hf x) (by simp)]
  simp only [mpullback_apply, ContinuousLinearMap.IsInvertible.self_apply_inverse (hinv x)]

/-- Naturality of the curvature tensor for arbitrary tangent vectors. -/
theorem curvature_naturality (x : M)
    (u v w : TangentSpace I x) :
    mfderiv I I f x (g.curvature x u v w) =
      h.curvature (f x) (mfderiv I I f x u) (mfderiv I I f x v) (mfderiv I I f x w) := by
  let X := extend (MinkowskiModel d) (mfderiv I I f x u)
  let Y := extend (MinkowskiModel d) (mfderiv I I f x v)
  let Z := extend (MinkowskiModel d) (mfderiv I I f x w)
  have hX : ContMDiffAt I ((I).prod I) 2 (T% X) (f x) := contMDiffAt_extend ..
  have hY : ContMDiffAt I ((I).prod I) 2 (T% Y) (f x) := contMDiffAt_extend ..
  have hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) (f x) := contMDiffAt_extend ..
  have he := g.curvatureField_naturality h hf hinv hmetric hX hY hZ
  rw [← g.curvature_apply
    (hX.mpullback_vectorField_preimage (hf x) (hinv x) (by simp))
    (hY.mpullback_vectorField_preimage (hf x) (hinv x) (by simp))
    (hZ.mpullback_vectorField_preimage (hf x) (hinv x) (by simp)),
    ← h.curvature_apply hX hY hZ] at he
  simpa only [X, Y, Z, mpullback_apply, extend_apply_self,
    ContinuousLinearMap.IsInvertible.inverse_apply_self (hinv x)] using he

omit hinv in
/-- Invertibility follows from metric preservation and equal dimension. -/
theorem curvature_naturality_of_metric (x : M)
    (u v w : TangentSpace I x) :
    mfderiv I I f x (g.curvature x u v w) =
      h.curvature (f x) (mfderiv I I f x u) (mfderiv I I f x v) (mfderiv I I f x w) :=
  g.curvature_naturality h hf
    (fun y => g.isInvertible_of_metric h y (f y) _ (hmetric y)) hmetric x u v w

omit hmetric in
/-- Pulling back a Lorentz metric pulls back its curvature tensor. -/
theorem curvature_pullback (x : M) (u v w : TangentSpace I x) :
    mfderiv I I f x ((h.pullback f hf hinv).curvature x u v w) =
      h.curvature (f x) (mfderiv I I f x u) (mfderiv I I f x v) (mfderiv I I f x w) :=
  (h.pullback f hf hinv).curvature_naturality h hf hinv
    (h.pullback_form f hf hinv) x u v w

end ProjectAInos.SmoothGeometry.LorentzMetric
