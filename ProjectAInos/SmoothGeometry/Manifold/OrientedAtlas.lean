/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Orientation specified by compatible signed charts

One smooth chart is selected around each point. A constant sign in each
selected chart records its orientation; signs agree under actual transition
Jacobians. This is local orientation data, with no metric or global frame.
-/

@[expose] public section
noncomputable section
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry

/-- A smooth orientation given by local charts and compatible choices of sign.
Allowing either sign for each chart avoids assuming the supplied charts were
already chosen positively oriented. -/
structure OrientedAtlas (n : ℕ) (M : Type*) [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
    [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] where
  chart : M → OpenPartialHomeomorph M (Fin n → ℝ)
  mem_atlas : ∀ p, chart p ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ M
  mem_source : ∀ p, p ∈ (chart p).source
  sign : M → ℝ
  sign_sq : ∀ p, sign p ^ 2 = 1
  compatible : ∀ p q x, x ∈ (chart p).source → x ∈ (chart q).source →
    sign q * Matrix.det (fun i j => fderiv ℝ (chart q ∘ (chart p).symm) (chart p x)
      (Pi.single j 1) i) =
    sign p * |Matrix.det (fun i j => fderiv ℝ (chart q ∘ (chart p).symm) (chart p x)
      (Pi.single j 1) i)|

namespace OrientedAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

theorem sign_ne_zero (o : OrientedAtlas n M) (p : M) : o.sign p ≠ 0 := by
  intro h
  have hs := o.sign_sq p
  simp [h] at hs

theorem abs_sign (o : OrientedAtlas n M) (p : M) : |o.sign p| = 1 := by
  have h := o.sign_sq p
  nlinarith [sq_abs (o.sign p), abs_nonneg (o.sign p)]

/-- Reverse every local orientation, leaving the selected charts unchanged. -/
def reverse (o : OrientedAtlas n M) : OrientedAtlas n M where
  chart := o.chart
  mem_atlas := o.mem_atlas
  mem_source := o.mem_source
  sign p := -o.sign p
  sign_sq p := by simpa only [neg_sq] using o.sign_sq p
  compatible p q x hp hq := by
    simpa only [neg_mul] using congrArg Neg.neg (o.compatible p q x hp hq)

@[simp] theorem reverse_sign (o : OrientedAtlas n M) (p : M) : o.reverse.sign p = -o.sign p := rfl

/-- The chosen chart sources cover the manifold. -/
theorem covers (o : OrientedAtlas n M) (x : M) : ∃ p, x ∈ (o.chart p).source :=
  ⟨x, o.mem_source x⟩

/-- Two choices of signed covering charts describe the same orientation. -/
def Compatible (o o' : OrientedAtlas n M) : Prop :=
  ∀ p q x, x ∈ (o.chart p).source → x ∈ (o'.chart q).source →
    o'.sign q * Matrix.det (fun i j => fderiv ℝ (o'.chart q ∘ (o.chart p).symm)
      (o.chart p x) (Pi.single j 1) i) =
    o.sign p * |Matrix.det (fun i j => fderiv ℝ (o'.chart q ∘ (o.chart p).symm)
      (o.chart p x) (Pi.single j 1) i)|

theorem compatible_self (o : OrientedAtlas n M) : o.Compatible o := o.compatible

/-- Standard orientation of the real finite coordinate model. -/
def standard (n : ℕ) : OrientedAtlas n (Fin n → ℝ) where
  chart _ := OpenPartialHomeomorph.refl (Fin n → ℝ)
  mem_atlas p := by
    simpa only [chartAt_self_eq] using
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) p)
  mem_source _ := Set.mem_univ _
  sign _ := 1
  sign_sq _ := one_pow 2
  compatible _ _ x _ _ := by
    change 1 * Matrix.det (fun i j => fderiv ℝ (id : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single j 1) i) =
      1 * |Matrix.det (fun i j => fderiv ℝ (id : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single j 1) i)|
    simp only [fderiv_id, ContinuousLinearMap.id_apply, one_mul]
    have h : (fun i j : Fin n => (Pi.single j (1 : ℝ) : Fin n → ℝ) i) =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp [Matrix.one_apply, Pi.single_apply]
    rw [h, Matrix.det_one, abs_one]

end OrientedAtlas
end ProjectAInos.SmoothGeometry
