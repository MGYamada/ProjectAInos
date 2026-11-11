/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.LeviCivita
public import ProjectAInos.SmoothGeometry.Tensor.Regularity

/-! # Smoothness of the Lorentz Levi-Civita connection -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)
  {X Y Z : ∀ x : M, TangentSpace 𝓘(ℝ, MinkowskiModel d) x} {x : M}

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Smoothness of the metric pairing holds locally, without global extensions. -/
theorem contMDiffAt_pairing
    (hX : ContMDiffAt I ((I).prod I) ∞ (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) ∞ (T% Y) x) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => g.form y (X y) (Y y)) x := by
  have h := (g.smooth x).clm_bundle_apply₂ hX hY
  rw [contMDiffAt_totalSpace] at h
  exact h.2

/-- Differentiating a smooth scalar function along a locally smooth field is smooth. -/
theorem contMDiffAt_directionalDerivative {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ) ∞ f x)
    (hX : ContMDiffAt I ((I).prod I) ∞ (T% X) x) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => mvfderiv I f y (X y)) x := by
  have hd := hf.mfderiv_const (m := ∞) (by simp)
  have hc : ContMDiffAt I 𝓘(ℝ, MinkowskiModel d →L[ℝ] ℝ) ∞
      (fun y => inCoordinates (MinkowskiModel d) (TangentSpace I) ℝ
        (TangentSpace 𝓘(ℝ)) x y (f x) (f y) (mfderiv I 𝓘(ℝ) f y)) x := by
    convert! hd using 1
  have ha := hc.clm_apply_of_inCoordinates hX hf
  rw [contMDiffAt_totalSpace] at ha
  simpa [mvfderiv, NormedSpace.fromTangentSpace, tangentSpaceCastModel, TangentBundle.trivializationAt_apply] using ha.2

/-- All terms of the Koszul formula are smooth for locally smooth fields. -/
theorem contMDiffAt_koszul
    (hX : ContMDiffAt I ((I).prod I) ∞ (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) ∞ (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) ∞ (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => g.koszul X Y Z y) x := by
  let : IsManifold I (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold I 2 M)
  let : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have h₁ := contMDiffAt_directionalDerivative (g.contMDiffAt_pairing hY hZ) hX
  have h₂ := contMDiffAt_directionalDerivative (g.contMDiffAt_pairing hZ hX) hY
  have h₃ := contMDiffAt_directionalDerivative (g.contMDiffAt_pairing hX hY) hZ
  have h₄ := g.contMDiffAt_pairing hY
    (hX.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hZ (by simp))
  have h₅ := g.contMDiffAt_pairing hZ
    (hY.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hX (by simp))
  have h₆ := g.contMDiffAt_pairing hX
    (hZ.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hY (by simp))
  exact (((((h₁.add h₂).sub h₃).sub h₄).sub h₅).add h₆).div_const 2

private theorem eventually_mdifferentiableAt_field
    (hX : ContMDiffAt I ((I).prod I) ∞ (T% X) x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I ((I).prod I) (T% X) y := by
  have h₁ := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hX.of_le (by simp))
  exact h₁.mono fun _ hy => hy.mdifferentiableAt (by norm_num)

/-- Smoothness of the connection applied to a locally smooth vector field.
The proof tests its metric dual against local fields and uses the Koszul formula. -/
theorem contMDiffAt_leviCivita
    (hY : ContMDiffAt I ((I).prod I) ∞ (T% Y) x) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d)) ∞
      (fun y => TotalSpace.mk' (MinkowskiModel d →L[ℝ] MinkowskiModel d)
        y (g.leviCivita Y y)) x := by
  apply Tensor.SmoothBundle.contMDiffAt_of_apply
    (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.tangent I)
  intro X hX
  have hα : ContMDiffAt I ((I).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (MinkowskiModel d →L[ℝ] ℝ)
        y (g.form y (g.leviCivita Y y (X y)))) x := by
    apply Tensor.SmoothBundle.contMDiffAt_of_apply
      (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.scalar I)
    intro Z hZ
    apply contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_id, ?_⟩
    apply (g.contMDiffAt_koszul hX hY hZ).congr_of_eventuallyEq
    filter_upwards [eventually_mdifferentiableAt_field hX,
      eventually_mdifferentiableAt_field hY,
      eventually_mdifferentiableAt_field hZ] with y hyX hyY hyZ
    exact g.leviCivita_pairing hyX hyY hyZ
  have h := (g.sharp_smooth x).clm_bundle_apply hα
  simpa only [← flat_toContinuousLinearMap, ContinuousLinearEquiv.coe_coe, sharp_flat] using h

/-- The constructed Lorentz connection is smooth in mathlib's native sense. -/
instance leviCivita_contMDiff : CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita ∞ where
  contMDiff := ⟨by
    intro Y hY
    rw [contMDiffOn_univ] at hY ⊢
    intro x
    exact g.contMDiffAt_leviCivita (by simpa using hY x)⟩

end ProjectAInos.SmoothGeometry.LorentzMetric
