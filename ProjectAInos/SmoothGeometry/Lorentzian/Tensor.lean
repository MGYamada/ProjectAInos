/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Dual
public import ProjectAInos.SmoothGeometry.Tensor.Contraction

/-! # Raising tensor indices and metric contraction

Covariant two-tensors and endomorphisms are smooth sections of the actual
iterated hom bundles. Raising an index and taking the intrinsic trace gives
metric contraction, with smoothness and coordinate invariance proved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff BigOperators

namespace ProjectAInos.SmoothGeometry

variable (d : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

/-- Smooth covariant two-tensors on the tangent bundle. -/
abbrev CovariantTwoTensor :=
  Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ,
    (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ)⟯

/-- Smooth tensors with one tangent output and one tangent input. -/
abbrev TangentEndomorphism :=
  Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] MinkowskiModel d,
    (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x)⟯

namespace Tensor

variable {d M}

/-- The coordinate covectors induced by a chosen tangent-coordinate equivalence. -/
def coordinateCovector (x : M)
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d)
    (i : Fin (d + 1)) : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap

omit [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M] in
@[simp] theorem coordinateCovector_apply (x : M)
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d)
    (i : Fin (d + 1)) (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    coordinateCovector x e i v = e v i := rfl

omit [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M] in
theorem covector_eq_sum (x : M)
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d)
    (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    α = ∑ i, α (e.symm (Pi.single i 1)) • coordinateCovector x e i := by
  ext v
  have hv : (∑ i, (e v) i • e.symm (Pi.single i 1)) = v := by
    apply e.injective
    simp only [map_sum, map_smul, ContinuousLinearEquiv.apply_symm_apply]
    ext i
    simp [Pi.single_apply, mul_ite]
  calc
    α v = α (∑ i, (e v) i • e.symm (Pi.single i 1)) := congrArg α hv.symm
    _ = _ := by simp [mul_comm]

end Tensor

namespace LorentzMetric

variable {d M} {σ : LorentzConvention} (g : LorentzMetric σ d M)

/-- View the metric as a smooth covariant tensor, retaining its actual fibres. -/
def toTensor : CovariantTwoTensor d M := ⟨g.form, g.smooth⟩

/-- Raise the covector output of a covariant two-tensor. -/
def raiseIndex (B : CovariantTwoTensor d M) : TangentEndomorphism d M :=
  ⟨fun x => (g.sharp x).toContinuousLinearMap.comp (B x),
    Tensor.contMDiff_comp g.sharp_smooth B.contMDiff⟩

/-- Lower the vector output of a tangent endomorphism. -/
def lowerIndex (A : TangentEndomorphism d M) : CovariantTwoTensor d M :=
  Tensor.comp g.toTensor A

@[simp] theorem raiseIndex_apply (B : CovariantTwoTensor d M) (x : M)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.raiseIndex B x v = g.sharp x (B x v) := rfl

@[simp] theorem lowerIndex_apply (A : TangentEndomorphism d M) (x : M)
    (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.lowerIndex A x v w = g.form x (A x v) w := rfl

@[simp] theorem lowerIndex_raiseIndex (B : CovariantTwoTensor d M) :
    g.lowerIndex (g.raiseIndex B) = B := by
  ext x v w
  exact g.form_sharp_left x (B x v) w

@[simp] theorem raiseIndex_lowerIndex (A : TangentEndomorphism d M) :
    g.raiseIndex (g.lowerIndex A) = A := by
  ext x v
  exact g.sharp_flat x (A x v)

/-- Pointwise inverse-metric contraction, defined intrinsically by trace. -/
def contract (x : M)
    (B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) : ℝ :=
  LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x)
    ((g.sharp x).toContinuousLinearMap.comp B).toLinearMap

/-- Contract a smooth covariant two-tensor to a smooth real scalar field. -/
def contractField (B : CovariantTwoTensor d M) : C^∞⟮𝓘(ℝ, MinkowskiModel d), M; ℝ⟯ :=
  Tensor.trace (MinkowskiModel d) (g.raiseIndex B)

@[simp] theorem contractField_apply (B : CovariantTwoTensor d M) (x : M) :
    g.contractField B x = g.contract x (B x) := rfl

@[simp] theorem contract_metric (x : M) : g.contract x (g.form x) = d + 1 := by
  have hid : ((g.sharp x).toContinuousLinearMap.comp (g.form x)) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x) := by
    ext v
    exact g.sharp_flat x v
  rw [contract, hid]
  simp [LinearMap.trace_id, TangentSpace, MinkowskiModel]

theorem contract_add (x : M)
    (B C : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.contract x (B + C) = g.contract x B + g.contract x C := by
  simp [contract, comp_add]

theorem contract_smul (x : M) (r : ℝ)
    (B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.contract x (r • B) = r * g.contract x B := by
  simp [contract]

@[simp] theorem contract_smulRight (x : M)
    (α β : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.contract x (α.smulRight β) = α (g.sharp x β) := by
  have h : (g.sharp x).toContinuousLinearMap.comp (α.smulRight β) =
      α.smulRight (g.sharp x β) := by
    ext v
    simp
  rw [contract, h]
  exact LinearMap.trace_smulRight α.toLinearMap (g.sharp x β)

@[simp] theorem contract_opposite (x : M)
    (B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.opposite.contract x B = -g.contract x B := by
  have h : (g.opposite.sharp x).toContinuousLinearMap =
      -(g.sharp x).toContinuousLinearMap := by
    ext α
    exact g.opposite_sharp_apply x α
  simp [contract, h]

/-- Coordinate trace in any chosen tangent basis. The choice is pointwise. -/
theorem contract_eq_sum (x : M)
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d)
    (B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.contract x B = ∑ i, e (g.sharp x (B (e.symm (Pi.single i 1)))) i := by
  have h := Tensor.traceL_eq_sum (MinkowskiModel d) (Pi.basisFun ℝ (Fin (d + 1)))
    (e.toContinuousLinearMap.comp
      (((g.sharp x).toContinuousLinearMap.comp B).comp e.symm.toContinuousLinearMap))
  have hc : Tensor.traceL (MinkowskiModel d)
      (e.toContinuousLinearMap.comp
        (((g.sharp x).toContinuousLinearMap.comp B).comp e.symm.toContinuousLinearMap)) =
      g.contract x B :=
    LinearMap.trace_conj' ((g.sharp x).toContinuousLinearMap.comp B).toLinearMap
      e.toLinearEquiv
  rw [hc] at h
  simpa [contract, Tensor.traceL_apply] using h

/-- Components of the inverse metric, derived by raising the coordinate covectors. -/
def inverseComponent (x : M)
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d)
    (i j : Fin (d + 1)) : ℝ := e (g.sharp x (Tensor.coordinateCovector x e j)) i

/-- The intrinsic metric contraction agrees with the inverse-metric component sum. -/
theorem contract_eq_sum_components (x : M)
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d)
    (B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.contract x B = ∑ i, ∑ j,
      B (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1)) * g.inverseComponent x e i j := by
  rw [g.contract_eq_sum x e]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [Tensor.covector_eq_sum x e (B (e.symm (Pi.single i 1)))]
  simp [inverseComponent]

section Naturality

variable {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]

/-- Metric contraction is independent of metric-preserving tangent coordinates. -/
theorem contract_naturality (h : LorentzMetric σ d N) (x : M) (y : N)
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (he : ∀ v w, g.form x v w = h.form y (e v) (e w))
    (B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ)
    (C : TangentSpace 𝓘(ℝ, MinkowskiModel d) y →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) y →L[ℝ] ℝ)
    (hBC : ∀ v w, B v w = C (e v) (e w)) :
    g.contract x B = h.contract y C := by
  have hc : e.toLinearEquiv.conj
      ((g.sharp x).toContinuousLinearMap.comp B).toLinearMap =
      ((h.sharp y).toContinuousLinearMap.comp C).toLinearMap := by
    ext v
    change e (g.sharp x (B (e.symm v))) = h.sharp y (C v)
    have hb : B (e.symm v) = (C v).comp e.toContinuousLinearMap := by
      ext w
      simpa using hBC (e.symm v) w
    rw [hb, g.sharp_naturality h x y e he]
    exact e.apply_symm_apply _
  rw [contract, contract, ← hc, LinearMap.trace_conj']

end Naturality

end LorentzMetric
end ProjectAInos.SmoothGeometry
