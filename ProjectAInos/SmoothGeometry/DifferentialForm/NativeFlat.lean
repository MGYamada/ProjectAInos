/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.NativePullback
public import ProjectAInos.SmoothGeometry.DifferentialForm.Flat

/-! # Agreement of native forms with the flat API -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- In the model manifold the native coefficients are the original flat form. -/
@[simp] theorem trivializationCoefficients_flat (α : Form E k) (x₀ : E) :
    trivializationCoefficients 𝓘(ℝ, E) α x₀ = α := by
  funext x
  ext v
  simp only [trivializationCoefficients, TangentBundle.symmL_model_space]
  rfl

/-- Flat smoothness gives exactly the native smooth-section regularity. -/
theorem contMDiff_flat_iff (α : Form E k) {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) r
      (fun x => (⟨x, α x⟩ : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ)
        (fun x : E => TangentSpace 𝓘(ℝ, E) x [⋀^Fin k]→L[ℝ] ℝ))) ↔ ContDiff ℝ r α := by
  constructor
  · intro h
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hx := (contMDiffAt_form_iff 𝓘(ℝ, E)).mp (h x)
    simpa only [trivializationCoefficients_flat, contMDiffAt_iff_contDiffAt] using hx
  · intro h x
    apply (contMDiffAt_form_iff 𝓘(ℝ, E)).mpr
    rw [trivializationCoefficients_flat]
    exact h.contDiffAt.contMDiffAt

/-- Regard an existing smooth flat form as a native form on the model manifold. -/
def ofFlat (α : Form E k) (hα : ContDiff ℝ ∞ α) : SmoothForm 𝓘(ℝ, E) E k :=
  ⟨α, (contMDiff_flat_iff α).mpr hα⟩

@[simp] theorem ofFlat_apply (α : Form E k) (hα : ContDiff ℝ ∞ α) (x : E) :
    ofFlat α hα x = α x := rfl

/-- Native pullback specializes exactly to the existing flat pullback. -/
theorem nativePullback_flat (f : E → F) (α : Form F k) :
    nativePullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α = pullback f α := by
  funext x
  unfold nativePullback pullback
  rw [mfderiv_eq_fderiv]
  rfl

theorem smoothPullback_flat (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯)
    (α : Form F k) (hα : ContDiff ℝ ∞ α) :
    (fun x => smoothPullback 𝓘(ℝ, E) 𝓘(ℝ, F) f (ofFlat α hα) x) = pullback f α :=
  nativePullback_flat f α

end ProjectAInos.SmoothGeometry.DifferentialForm
