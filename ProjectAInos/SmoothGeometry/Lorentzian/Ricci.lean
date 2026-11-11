/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.CurvatureRegularity
public import ProjectAInos.SmoothGeometry.Lorentzian.Tensor

/-! # Ricci and scalar curvature by intrinsic contraction

The convention is `Ric(u,v) = trace (w ↦ R(w,u)v)`. The trace and inverse
metric contraction use the actual tangent spaces, without choosing a basis.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Bundle FiberBundle
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- The endomorphism whose trace defines `Ric(u,v)` with the chosen sign. -/
def curvatureEndomorphism (x : M) (u v : TM x) : TM x →L[ℝ] TM x :=
  have : T2Space (TM x) := FiberBundle.t2Space E TM x
  have : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  LinearMap.toContinuousLinearMap {
    toFun w := g.curvature x w u v
    map_add' w z := by simp
    map_smul' a w := by simp }

@[simp] theorem curvatureEndomorphism_apply (x : M) (u v w : TM x) :
    g.curvatureEndomorphism x u v w = g.curvature x w u v := rfl

theorem curvatureEndomorphism_add_left (x : M) (u v w : TM x) :
    g.curvatureEndomorphism x (u + v) w =
      g.curvatureEndomorphism x u w + g.curvatureEndomorphism x v w := by
  ext z
  simp

theorem curvatureEndomorphism_smul_left (x : M) (a : ℝ) (u v : TM x) :
    g.curvatureEndomorphism x (a • u) v = a • g.curvatureEndomorphism x u v := by
  ext w
  simp

theorem curvatureEndomorphism_add_right (x : M) (u v w : TM x) :
    g.curvatureEndomorphism x u (v + w) =
      g.curvatureEndomorphism x u v + g.curvatureEndomorphism x u w := by
  ext z
  simp

theorem curvatureEndomorphism_smul_right (x : M) (a : ℝ) (u v : TM x) :
    g.curvatureEndomorphism x u (a • v) = a • g.curvatureEndomorphism x u v := by
  ext w
  simp

/-- The Ricci contraction with its first argument fixed. -/
def ricciCovector (x : M) (u : TM x) : TM x →L[ℝ] ℝ :=
  have : T2Space (TM x) := FiberBundle.t2Space E TM x
  have : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  LinearMap.toContinuousLinearMap {
    toFun v := Tensor.fiberTrace E x (g.curvatureEndomorphism x u v)
    map_add' v w := by rw [curvatureEndomorphism_add_right, map_add]
    map_smul' a v := by simp only [curvatureEndomorphism_smul_right, map_smul,
      RingHom.id_apply] }

/-- The Ricci tensor as a bilinear form on the native tangent space. -/
def ricci (x : M) : TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  have : T2Space (TM x) := FiberBundle.t2Space E TM x
  have : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  LinearMap.toContinuousLinearMap {
    toFun u := g.ricciCovector x u
    map_add' u v := by
      ext w
      change Tensor.fiberTrace E x (g.curvatureEndomorphism x (u + v) w) = _
      rw [curvatureEndomorphism_add_left, map_add]
      rfl
    map_smul' a u := by
      ext v
      change Tensor.fiberTrace E x (g.curvatureEndomorphism x (a • u) v) = _
      rw [curvatureEndomorphism_smul_left, map_smul]
      rfl }

/-- This trace formula fixes the contraction order and hence the Ricci sign. -/
theorem ricci_apply (x : M) (u v : TM x) :
    g.ricci x u v = LinearMap.trace ℝ (TM x) (g.curvatureEndomorphism x u v).toLinearMap :=
  Tensor.fiberTrace_apply E x _

/-- Ricci is the same trace in every tangent-coordinate equivalence. -/
theorem ricci_eq_sum (x : M) (e : TM x ≃L[ℝ] E) (u v : TM x) :
    g.ricci x u v = ∑ i, e (g.curvature x (e.symm (Pi.single i 1)) u v) i := by
  have h := Tensor.traceL_eq_sum E (Pi.basisFun ℝ (Fin (d + 1)))
    (e.toContinuousLinearMap.comp
      ((g.curvatureEndomorphism x u v).comp e.symm.toContinuousLinearMap))
  have hc : Tensor.traceL E
      (e.toContinuousLinearMap.comp
        ((g.curvatureEndomorphism x u v).comp e.symm.toContinuousLinearMap)) =
      g.ricci x u v := by
    rw [Tensor.traceL_apply, ricci_apply]
    exact LinearMap.trace_conj' (g.curvatureEndomorphism x u v).toLinearMap e.toLinearEquiv
  rw [hc] at h
  simpa using h

theorem contMDiffAt_curvatureEndomorphism {X Y : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) ∞ (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) ∞ (T% Y) x) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] E) y (g.curvatureEndomorphism y (X y) (Y y))) x := by
  apply Tensor.SmoothBundle.contMDiffAt_of_apply (n := ⊤)
    (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.tangent I)
  intro Z hZ
  exact (((g.curvature_smooth x).clm_bundle_apply hZ).clm_bundle_apply hX).clm_bundle_apply hY

/-- Smoothness of Ricci follows from smoothness of the curvature and of trace. -/
theorem ricci_smooth :
    ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (g.ricci x)) := by
  intro x
  apply Tensor.SmoothBundle.contMDiffAt_of_apply (n := ⊤)
    (Tensor.SmoothBundle.tangent I)
    (Tensor.SmoothBundle.hom I (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.scalar I))
  intro X hX
  apply Tensor.SmoothBundle.contMDiffAt_of_apply (n := ⊤)
    (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.scalar I)
  intro Y hY
  exact (Tensor.contMDiff_fiberTrace E (V := TM) («I» := I) x).clm_bundle_apply
    (g.contMDiffAt_curvatureEndomorphism hX hY)

/-- Ricci as a smooth covariant two-tensor, ready for further contractions. -/
def ricciTensor : CovariantTwoTensor d M := ⟨g.ricci, g.ricci_smooth⟩

/-- Scalar curvature is the inverse-metric trace of Ricci. -/
def scalarCurvature : C^∞⟮I, M; ℝ⟯ := g.contractField g.ricciTensor

@[simp] theorem scalarCurvature_apply (x : M) :
    g.scalarCurvature x = g.contract x (g.ricci x) := rfl

/-- The scalar curvature is the usual inverse-metric contraction in any
chosen tangent coordinates. No smooth global frame is required. -/
theorem scalarCurvature_eq_sum (x : M) (e : TM x ≃L[ℝ] E) :
    g.scalarCurvature x = ∑ i, ∑ j,
      g.ricci x (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1)) *
        g.inverseComponent x e i j :=
  g.contract_eq_sum_components x e (g.ricci x)

/-- Vanishing curvature implies vanishing Ricci, without a coordinate choice. -/
theorem ricci_eq_zero_of_curvature_eq_zero (x : M) (hx : g.curvature x = 0) :
    g.ricci x = 0 := by
  have hz (u v : TM x) : g.curvatureEndomorphism x u v = 0 := by ext w; simp [hx]
  ext u v
  simp [ricci_apply, hz]

@[simp] theorem curvatureEndomorphism_opposite (x : M) (u v : TM x) :
    g.opposite.curvatureEndomorphism x u v = g.curvatureEndomorphism x u v := by
  ext w
  simp

@[simp] theorem ricci_opposite (x : M) : g.opposite.ricci x = g.ricci x := by
  ext u v
  simp only [ricci_apply, curvatureEndomorphism_opposite]

/-- Overall metric sign reversal reverses scalar curvature, but not Ricci. -/
@[simp] theorem scalarCurvature_opposite (x : M) :
    g.opposite.scalarCurvature x = -g.scalarCurvature x := by
  simp only [scalarCurvature_apply, ricci_opposite, contract_opposite]

section Naturality

variable {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]

/-- Intrinsic trace commutes with every tangent isomorphism intertwining
curvature, so the Ricci contraction is independent of tangent coordinates. -/
theorem ricci_naturality (h : LorentzMetric σ d N) (x : M) (y : N)
    (e : TM x ≃L[ℝ] TangentSpace I y)
    (hR : ∀ u v w, e (g.curvature x u v w) = h.curvature y (e u) (e v) (e w))
    (u v : TM x) : g.ricci x u v = h.ricci y (e u) (e v) := by
  have hc : e.toLinearEquiv.conj (g.curvatureEndomorphism x u v).toLinearMap =
      (h.curvatureEndomorphism y (e u) (e v)).toLinearMap := by
    ext w
    change e (g.curvature x (e.symm w) u v) = h.curvature y w (e u) (e v)
    rw [hR, e.apply_symm_apply]
  rw [ricci_apply, ricci_apply, ← hc, LinearMap.trace_conj']

/-- Scalar contraction is invariant when tangent coordinates preserve the
metric and intertwine curvature. -/
theorem scalarCurvature_naturality (h : LorentzMetric σ d N) (x : M) (y : N)
    (e : TM x ≃L[ℝ] TangentSpace I y)
    (he : ∀ u v, g.form x u v = h.form y (e u) (e v))
    (hR : ∀ u v w, e (g.curvature x u v w) = h.curvature y (e u) (e v) (e w)) :
    g.scalarCurvature x = h.scalarCurvature y :=
  g.contract_naturality h x y e he (g.ricci x) (h.ricci y)
    (g.ricci_naturality h x y e hR)

end Naturality

end ProjectAInos.SmoothGeometry.LorentzMetric
