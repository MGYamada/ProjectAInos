/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Regularity
public import ProjectAInos.SmoothGeometry.Lorentzian.Pullback

/-! # Naturality of the Lorentz Levi-Civita connection

Metric-preserving smooth maps with invertible tangent derivatives intertwine
the native connections. The map need not be globally bijective, so the result
also applies to restrictions and local coordinate identifications.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]
  (g : LorentzMetric σ d M) (h : LorentzMetric σ d N)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- In equal-dimensional Lorentz fibres, preserving the nondegenerate metric
already makes a continuous linear map invertible. -/
theorem isInvertible_of_metric (x : M) (y : N)
    (L : TangentSpace I x →L[ℝ] TangentSpace I y)
    (hL : ∀ v w, g.form x v w = h.form y (L v) (L w)) : L.IsInvertible := by
  have hi : Function.Injective L := by
    intro v w hvw
    apply (g.flat x).injective
    ext z
    change g.form x v z = g.form x w z
    rw [hL, hL, hvw]
  obtain ⟨e, _⟩ := g.signature x
  obtain ⟨e', _⟩ := h.signature y
  have hdim := e.toLinearEquiv.finrank_eq.trans e'.toLinearEquiv.finrank_eq.symm
  exact ⟨(L.toLinearMap.linearEquivOfInjective hi hdim).toContinuousLinearEquiv, rfl⟩

variable {f : M → N}
  (hf : ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ f)
  (hinv : ∀ y, (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y).IsInvertible)
  (hmetric : ∀ y v w, g.form y v w =
    h.form (f y) (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y v)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y w))
  {X Y Z : ∀ y : N, TangentSpace 𝓘(ℝ, MinkowskiModel d) y} {x : M}

include hinv hmetric

/-- Pulling back both vector arguments turns metric evaluation into scalar pullback. -/
theorem pairing_mpullback (V W : ∀ y : N, TangentSpace I y) :
    (fun y => g.form y (mpullback I I f V y) (mpullback I I f W y)) =
      (fun z => h.form z (V z) (W z)) ∘ f := by
  funext y
  rw [hmetric]
  simp only [mpullback_apply, IsInvertible.self_apply_inverse (hinv y), Function.comp_apply]

include hf

/-- Koszul commutes with a smooth metric-preserving local identification.
All vector fields need only be differentiable at the target evaluation point. -/
theorem koszul_naturality
    (hX : MDifferentiableAt I ((I).prod I) (T% X) (f x))
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) (f x))
    (hZ : MDifferentiableAt I ((I).prod I) (T% Z) (f x)) :
    g.koszul (mpullback I I f X) (mpullback I I f Y) (mpullback I I f Z) x =
      h.koszul X Y Z (f x) := by
  let : IsManifold I (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold I 2 M)
  let : IsManifold I (minSmoothness ℝ 2) N := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold I 2 N)
  have hd (V W U : ∀ y : N, TangentSpace I y)
      (hV : MDifferentiableAt I ((I).prod I) (T% V) (f x))
      (hW : MDifferentiableAt I ((I).prod I) (T% W) (f x)) :
      mvfderiv I (fun y => g.form y (mpullback I I f V y)
        (mpullback I I f W y)) x (mpullback I I f U x) =
      mvfderiv I (fun y => h.form y (V y) (W y)) (f x) (U (f x)) := by
    rw [g.pairing_mpullback h hinv hmetric,
      mvfderiv_comp x (h.mdifferentiableAt_pairing hV hW)
        (hf.mdifferentiableAt (by simp))]
    simp only [comp_apply, mpullback_apply, IsInvertible.self_apply_inverse (hinv x)]
  simp only [koszul]
  rw [hd Y Z X hY hZ, hd Z X Y hZ hX, hd X Y Z hX hY,
    ← mpullback_mlieBracket hX hZ (hf x) (by simp),
    ← mpullback_mlieBracket hY hX (hf x) (by simp),
    ← mpullback_mlieBracket hZ hY (hf x) (by simp)]
  simp only [hmetric, mpullback_apply, IsInvertible.self_apply_inverse (hinv x)]

/-- The derivative of a metric-preserving local identification intertwines
Levi-Civita on a pulled-back differentiable field, for every source tangent vector. -/
theorem leviCivita_naturality
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) (f x))
    (v : TangentSpace I x) :
    mfderiv I I f x (g.leviCivita (mpullback I I f Y) x v) =
      h.leviCivita Y (f x) (mfderiv I I f x v) := by
  apply h.injective_form_mdifferentiableAt
  funext Z hZ
  let X := extend (MinkowskiModel d) (mfderiv I I f x v)
  have hX := mdifferentiableAt_extend I (MinkowskiModel d) (mfderiv I I f x v)
  have hpX := hX.mpullback_vectorField (hf x) (hinv x) (by simp)
  have hpY := hY.mpullback_vectorField (hf x) (hinv x) (by simp)
  have hpZ := hZ.mpullback_vectorField (hf x) (hinv x) (by simp)
  have hv : mpullback I I f X x = v := by
    simp only [mpullback_apply, X, extend_apply_self, IsInvertible.inverse_apply_self (hinv x)]
  have hz : mfderiv I I f x (mpullback I I f Z x) = Z (f x) := by
    simp only [mpullback_apply, IsInvertible.self_apply_inverse (hinv x)]
  change h.form (f x)
    (mfderiv I I f x (g.leviCivita (mpullback I I f Y) x v)) (Z (f x)) =
    h.form (f x) (h.leviCivita Y (f x) (mfderiv I I f x v)) (Z (f x))
  calc
    _ = g.form x (g.leviCivita (mpullback I I f Y) x v) (mpullback I I f Z x) := by
      rw [hmetric, hz]
    _ = g.koszul (mpullback I I f X) (mpullback I I f Y) (mpullback I I f Z) x := by
      rw [← hv]
      exact g.leviCivita_pairing hpX hpY hpZ
    _ = h.koszul X Y Z (f x) := g.koszul_naturality h hf hinv hmetric hX hY hZ
    _ = _ := by simpa only [X, extend_apply_self] using (h.leviCivita_pairing hX hY hZ).symm

omit hinv in
/-- A smooth metric-preserving map between manifolds of the same Lorentz
dimension intertwines their connections. Invertibility is derived from the metric. -/
theorem leviCivita_naturality_of_metric
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) (f x))
    (v : TangentSpace I x) :
    mfderiv I I f x (g.leviCivita (mpullback I I f Y) x v) =
      h.leviCivita Y (f x) (mfderiv I I f x v) :=
  g.leviCivita_naturality h hf
    (fun y => g.isInvertible_of_metric h y (f y) _ (hmetric y)) hmetric hY v

omit hmetric in
/-- Pulling back a Lorentz metric also pulls back its constructed connection. -/
theorem leviCivita_pullback
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) (f x))
    (v : TangentSpace I x) :
    mfderiv I I f x ((h.pullback f hf hinv).leviCivita (mpullback I I f Y) x v) =
      h.leviCivita Y (f x) (mfderiv I I f x v) :=
  (h.pullback f hf hinv).leviCivita_naturality h hf hinv
    (h.pullback_form f hf hinv) hY v

end ProjectAInos.SmoothGeometry.LorentzMetric
