/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.BundleOperations
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Smooth tensor contraction by trace

The contraction of one tangent and one cotangent index is the intrinsic
trace of an endomorphism. Its coordinate invariance proves smoothness on
any finite-dimensional vector bundle, without a choice of global frame.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace ProjectAInos.SmoothGeometry.Tensor

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Trace as a continuous linear functional on the model endomorphisms. -/
def traceL : (F →L[ℝ] F) →L[ℝ] ℝ :=
  ({ toFun A := LinearMap.trace ℝ F A.toLinearMap
     map_add' A B := by simp
     map_smul' r A := by simp } : (F →L[ℝ] F) →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] theorem traceL_apply (A : F →L[ℝ] F) :
    traceL F A = LinearMap.trace ℝ F A.toLinearMap := rfl

theorem traceL_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ F) (A : F →L[ℝ] F) :
    traceL F A = ∑ i, b.repr (A (b i)) i := by
  rw [traceL_apply, LinearMap.trace_eq_matrix_trace ℝ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

/-- Contraction of the elementary tensor `v ⊗ α` is evaluation `α(v)`. -/
@[simp] theorem traceL_smulRight (α : F →L[ℝ] ℝ) (v : F) :
    traceL F (α.smulRight v) = α v :=
  LinearMap.trace_smulRight α.toLinearMap v

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem traceL_conjugate [FiniteDimensional ℝ G] (e : F ≃L[ℝ] G) (A : F →L[ℝ] F) :
    traceL G (e.toContinuousLinearMap.comp (A.comp e.symm.toContinuousLinearMap)) =
      traceL F A :=
  LinearMap.trace_conj' A.toLinearMap e.toLinearEquiv

section Bundles

variable {M E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

theorem trace_inCoordinates (x₀ x : M)
    (hx : x ∈ (trivializationAt F V x₀).baseSet) (A : V x →L[ℝ] V x) :
    traceL F (inCoordinates F V F V x₀ x x₀ x A) =
      LinearMap.trace ℝ (V x) A.toLinearMap := by
  rw [traceL_apply, inCoordinates_eq hx hx]
  exact LinearMap.trace_conj' A.toLinearMap
    ((trivializationAt F V x₀).continuousLinearEquivAt ℝ x hx).toLinearEquiv

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- The intrinsic trace functional on a fibre. A local trivialization supplies
continuity; `fiberTrace_apply` proves the value independent of this choice. -/
def fiberTrace (x : M) : (V x →L[ℝ] V x) →L[ℝ] ℝ :=
  let e := (trivializationAt F V x).continuousLinearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)
  (traceL F).comp (e.arrowCongr e).toContinuousLinearMap

@[simp] theorem fiberTrace_apply (x : M) (A : V x →L[ℝ] V x) :
    fiberTrace F x A = LinearMap.trace ℝ (V x) A.toLinearMap :=
  LinearMap.trace_conj' A.toLinearMap
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv

theorem fiberTrace_inCoordinates (x₀ x : M)
    (hx : x ∈ (trivializationAt F V x₀).baseSet) :
    inCoordinates (F →L[ℝ] F) (fun y => V y →L[ℝ] V y) ℝ (Bundle.Trivial M ℝ)
      x₀ x x₀ x (fiberTrace F x) = traceL F := by
  have he : x ∈ (trivializationAt (F →L[ℝ] F) (fun y => V y →L[ℝ] V y) x₀).baseSet :=
    by simpa using hx
  let e := (trivializationAt (F →L[ℝ] F) (fun y => V y →L[ℝ] V y) x₀).continuousLinearEquivAt
    ℝ x he
  rw [inCoordinates_eq he (by simp)]
  ext A
  change fiberTrace F x (e.symm A) = traceL F A
  rw [fiberTrace_apply, ← trace_inCoordinates F x₀ x hx (e.symm A)]
  have h : inCoordinates F V F V x₀ x x₀ x (e.symm A) = A := e.apply_symm_apply A
  rw [h]

/-- Trace is itself a smooth hom-bundle section. This permits partial
contraction while retaining any uncontracted tensor arguments. -/
theorem contMDiff_fiberTrace :
    ContMDiff I (I.prod 𝓘(ℝ, (F →L[ℝ] F) →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' ((F →L[ℝ] F) →L[ℝ] ℝ) x (fiberTrace F (V := V) x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply (contMDiffAt_const (c := traceL F)).congr_of_eventuallyEq
  have h : (trivializationAt F V x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
  filter_upwards [h] with x hx
  exact fiberTrace_inCoordinates F x₀ x hx

def traceSection :
    Cₛ^∞⟮I; (F →L[ℝ] F) →L[ℝ] ℝ, (fun x => (V x →L[ℝ] V x) →L[ℝ] ℝ)⟯ :=
  ⟨fiberTrace F, contMDiff_fiberTrace F⟩

/-- The contraction of a smooth endomorphism section is a smooth scalar. -/
theorem contMDiff_trace {n : WithTop ℕ∞} {A : ∀ x, V x →L[ℝ] V x}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun x => TotalSpace.mk' (F →L[ℝ] F) x (A x))) :
    ContMDiff I 𝓘(ℝ) n (fun x => LinearMap.trace ℝ (V x) (A x).toLinearMap) := by
  intro x₀
  have hAc := ((contMDiffAt_hom_bundle _).mp (hA x₀)).2
  have ht := (traceL F).contDiff.contMDiff.contMDiffAt.comp x₀ hAc
  apply ht.congr_of_eventuallyEq
  have h : (trivializationAt F V x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
  filter_upwards [h] with x hx
  exact (trace_inCoordinates F x₀ x hx (A x)).symm

/-- Contract the tangent/cotangent index pair of a smooth endomorphism field. -/
def trace (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x => V x →L[ℝ] V x)⟯) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x => LinearMap.trace ℝ (V x) (A x).toLinearMap, contMDiff_trace F A.contMDiff⟩

@[simp] theorem trace_apply
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x => V x →L[ℝ] V x)⟯) (x : M) :
    trace F A x = LinearMap.trace ℝ (V x) (A x).toLinearMap := rfl

end Bundles
end ProjectAInos.SmoothGeometry.Tensor
