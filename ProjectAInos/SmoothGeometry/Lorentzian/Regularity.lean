/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.LeviCivita
public import ProjectAInos.SmoothGeometry.Tensor.Regularity

/-! # Finite regularity and smoothness of the Lorentz Levi-Civita connection -/

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

/-- Pairing locally `C^n` fields with the smooth metric preserves their regularity. -/
theorem contMDiffAt_pairing {n : ℕ∞}
    (hX : ContMDiffAt I ((I).prod I) n (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) n (T% Y) x) :
    ContMDiffAt I 𝓘(ℝ) n (fun y => g.form y (X y) (Y y)) x := by
  have h := ((g.smooth x).of_le (by simp)).clm_bundle_apply₂ hX hY
  rw [contMDiffAt_totalSpace] at h
  exact h.2

/-- A directional derivative of a `C^(n+1)` function along a `C^n` field is `C^n`. -/
theorem contMDiffAt_directionalDerivative {n : ℕ∞} {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x)
    (hX : ContMDiffAt I ((I).prod I) n (T% X) x) :
    ContMDiffAt I 𝓘(ℝ) n (fun y => mvfderiv I f y (X y)) x := by
  have hd := hf.mfderiv_const (m := n) le_rfl
  have hc : ContMDiffAt I 𝓘(ℝ, MinkowskiModel d →L[ℝ] ℝ) n
      (fun y => inCoordinates (MinkowskiModel d) (TangentSpace I) ℝ
        (TangentSpace 𝓘(ℝ)) x y (f x) (f y) (mfderiv I 𝓘(ℝ) f y)) x := by
    convert! hd using 1
  have ha := hc.clm_apply_of_inCoordinates hX (hf.of_le (self_le_add_right _ _))
  rw [contMDiffAt_totalSpace] at ha
  simpa [mvfderiv, NormedSpace.fromTangentSpace, tangentSpaceCastModel,
    TangentBundle.trivializationAt_apply] using ha.2

/-- Koszul loses at most one derivative on locally `C^(n+1)` fields. -/
theorem contMDiffAt_koszul {n : ℕ∞}
    (hX : ContMDiffAt I ((I).prod I) (n + 1) (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) (n + 1) (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) (n + 1) (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ) n (fun y => g.koszul X Y Z y) x := by
  let : IsManifold I (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold I 2 M)
  let : IsManifold I (((n + 1 : ℕ∞) : ℕ∞ω) + 1) M :=
    IsManifold.of_le (n := ∞) (by simp)
  have hn : (n : ℕ∞ω) ≤ n + 1 := self_le_add_right _ _
  have hXn := hX.of_le hn
  have hYn := hY.of_le hn
  have hZn := hZ.of_le hn
  have h₁ := contMDiffAt_directionalDerivative (g.contMDiffAt_pairing hY hZ) hXn
  have h₂ := contMDiffAt_directionalDerivative (g.contMDiffAt_pairing hZ hX) hYn
  have h₃ := contMDiffAt_directionalDerivative (g.contMDiffAt_pairing hX hY) hZn
  have h₄ := g.contMDiffAt_pairing hYn
    (hX.mlieBracket_vectorField (m := n) (n := n + 1) hZ (by simp))
  have h₅ := g.contMDiffAt_pairing hZn
    (hY.mlieBracket_vectorField (m := n) (n := n + 1) hX (by simp))
  have h₆ := g.contMDiffAt_pairing hXn
    (hZ.mlieBracket_vectorField (m := n) (n := n + 1) hY (by simp))
  exact (((((h₁.add h₂).sub h₃).sub h₄).sub h₅).add h₆).div_const 2

private theorem eventually_mdifferentiableAt_field
    (hX : ContMDiffAt I ((I).prod I) 1 (T% X) x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I ((I).prod I) (T% X) y := by
  have h₁ := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    hX
  exact h₁.mono fun _ hy => hy.mdifferentiableAt (by norm_num)

/-- The connection maps locally `C^(n+1)` fields to locally `C^n` hom sections.
This includes smooth fields at `n = ∞`.
The proof tests its metric dual against local fields and uses the Koszul formula. -/
theorem contMDiffAt_leviCivita {n : ℕ∞}
    (hY : ContMDiffAt I ((I).prod I) (n + 1) (T% Y) x) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d)) n
      (fun y => TotalSpace.mk' (MinkowskiModel d →L[ℝ] MinkowskiModel d)
        y (g.leviCivita Y y)) x := by
  apply Tensor.SmoothBundle.contMDiffAt_of_apply
    (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.tangent I)
  intro X hX
  have hα : ContMDiffAt I ((I).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] ℝ)) n
      (fun y => TotalSpace.mk' (MinkowskiModel d →L[ℝ] ℝ)
        y (g.form y (g.leviCivita Y y (X y)))) x := by
    apply Tensor.SmoothBundle.contMDiffAt_of_apply
      (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.scalar I)
    intro Z hZ
    apply contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_id, ?_⟩
    apply (g.contMDiffAt_koszul (hX.of_le (by simp)) hY (hZ.of_le (by simp))).congr_of_eventuallyEq
    filter_upwards [eventually_mdifferentiableAt_field (hX.of_le (by simp)),
      eventually_mdifferentiableAt_field (hY.of_le (self_le_add_left 1 (n : ℕ∞ω))),
      eventually_mdifferentiableAt_field (hZ.of_le (by simp))] with y hyX hyY hyZ
    exact g.leviCivita_pairing hyX hyY hyZ
  have h := ((g.sharp_smooth x).of_le (by simp)).clm_bundle_apply hα
  simpa only [← flat_toContinuousLinearMap, ContinuousLinearEquiv.coe_coe, sharp_flat] using h

/-- The native connection regularity holds at every finite order and at infinity. -/
instance leviCivita_contMDiff (n : ℕ∞) :
    CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita n where
  contMDiff := ⟨by
    intro Y hY
    rw [contMDiffOn_univ] at hY ⊢
    intro x
    exact g.contMDiffAt_leviCivita (hY x)⟩

end ProjectAInos.SmoothGeometry.LorentzMetric
