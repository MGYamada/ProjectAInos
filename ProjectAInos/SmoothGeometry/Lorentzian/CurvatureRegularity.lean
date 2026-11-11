/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Curvature

/-! # Smoothness of the Lorentz curvature tensor -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Bundle FiberBundle VectorField
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- The curvature expression preserves local smoothness of its field arguments. -/
theorem contMDiffAt_curvatureField {X Y Z : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) ∞ (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) ∞ (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) ∞ (T% Z) x) :
    ContMDiffAt I ((I).prod I) ∞ (T% (g.curvatureField X Y Z)) x := by
  let : IsManifold I (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using (inferInstance : IsManifold I 2 M)
  let : IsManifold I (((⊤ : ℕ∞) : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have hXY := hX.mlieBracket_vectorField (m := ⊤) (n := ⊤) hY (by simp)
  have hXZ := g.contMDiffAt_covariantField (n := ⊤) hX (by simpa using hZ)
  have hYZ := g.contMDiffAt_covariantField (n := ⊤) hY (by simpa using hZ)
  exact ((g.contMDiffAt_covariantField (n := ⊤) hX (by simpa using hYZ)).sub_section
    (g.contMDiffAt_covariantField (n := ⊤) hY (by simpa using hXZ))).sub_section
      (g.contMDiffAt_covariantField (n := ⊤) hXY (by simpa using hZ))

private theorem eventually_Ctwo {X : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) ∞ (T% X) x) :
    ∀ᶠ y in 𝓝 x, ContMDiffAt I ((I).prod I) 2 (T% X) y :=
  (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by norm_num)).mp (hX.of_le (by simp))

/-- The native bundle of tangent-valued trilinear tensors. Its packaged model
retains the recursively constructed norm and topology on the hom spaces. -/
abbrev curvatureBundle : Tensor.SmoothBundle I (M := M) :=
  Tensor.SmoothBundle.hom I (Tensor.SmoothBundle.tangent I)
    (Tensor.SmoothBundle.hom I (Tensor.SmoothBundle.tangent I)
      (Tensor.SmoothBundle.hom I (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.tangent I)))

/-- The trilinear curvature maps form a smooth section of the native iterated
hom bundle. Smoothness is tested on local smooth fields, without a global frame. -/
theorem curvature_smooth :
    ContMDiff I ((I).prod 𝓘(ℝ, (curvatureBundle (d := d) (M := M)).Model)) ∞
      (fun x => TotalSpace.mk' (curvatureBundle (d := d) (M := M)).Model x (g.curvature x)) := by
  intro x
  apply Tensor.SmoothBundle.contMDiffAt_of_apply (n := ⊤)
    (Tensor.SmoothBundle.tangent I (M := M))
    (Tensor.SmoothBundle.hom I (Tensor.SmoothBundle.tangent I (M := M))
      (Tensor.SmoothBundle.hom I (Tensor.SmoothBundle.tangent I (M := M))
        (Tensor.SmoothBundle.tangent I (M := M))))
  intro X hX
  apply Tensor.SmoothBundle.contMDiffAt_of_apply (n := ⊤)
    (Tensor.SmoothBundle.tangent I (M := M))
    (Tensor.SmoothBundle.hom I (Tensor.SmoothBundle.tangent I (M := M))
      (Tensor.SmoothBundle.tangent I (M := M)))
  intro Y hY
  apply Tensor.SmoothBundle.contMDiffAt_of_apply (n := ⊤)
    (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.tangent I)
  intro Z hZ
  apply (g.contMDiffAt_curvatureField hX hY hZ).congr_of_eventuallyEq
  filter_upwards [eventually_Ctwo hX, eventually_Ctwo hY, eventually_Ctwo hZ] with y hyX hyY hyZ
  exact congrArg (fun v => TotalSpace.mk' E y v) (g.curvature_apply hyX hyY hyZ)

/-- Curvature bundled with its proved smoothness. -/
def curvatureTensor : (curvatureBundle (d := d) (M := M)).Section I :=
  ⟨g.curvature, g.curvature_smooth⟩

end ProjectAInos.SmoothGeometry.LorentzMetric
