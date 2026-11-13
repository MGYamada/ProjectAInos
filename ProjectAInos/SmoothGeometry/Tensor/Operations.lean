/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.CovariantPullback
public import ProjectAInos.SmoothGeometry.Tensor.Regularity
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-! # Products and permutations of tensor slots

Scalar-valued tensors can be given by a list of input shapes. Concatenation
gives the slot order of a tensor product. A typed permutation records both
the input and output orders, including when tangent and cotangent slots mix.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.Tensor

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]

namespace SmoothBundle

/-- Smoothness at a point of a section of the given bundle. -/
abbrev SmoothAt (A : SmoothBundle I (M := M)) (s : ∀ x, A.Fiber x) (x : M) :=
  ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) ∞ (fun y => TotalSpace.mk' A.Model y (s y)) x

/-- Finite-dimensional bundle fibres have normable topologies. -/
theorem fiberNormable (A : SmoothBundle I (M := M)) (x : M) :
    IsNormableSpace ℝ (A.Fiber x) := by
  have : FiniteDimensional ℝ (A.Fiber x) := VectorBundle.finiteDimensional ℝ A.Model A.Fiber x
  exact isNormableSpace_of_finiteDimensional

/-- Exchange the two input slots of a bilinear bundle homomorphism. -/
def swapFiber (A B C : SmoothBundle I (M := M)) (x : M) :
    (A.Fiber x →L[ℝ] B.Fiber x →L[ℝ] C.Fiber x) →L[ℝ]
      B.Fiber x →L[ℝ] A.Fiber x →L[ℝ] C.Fiber x := by
  letI := fiberNormable I A x
  letI := fiberNormable I B x
  letI := fiberNormable I C x
  let D := hom I A (hom I B C)
  letI : T2Space (A.Fiber x →L[ℝ] B.Fiber x →L[ℝ] C.Fiber x) :=
    FiberBundle.t2Space D.Model D.Fiber x
  letI : FiniteDimensional ℝ (A.Fiber x →L[ℝ] B.Fiber x →L[ℝ] C.Fiber x) :=
    VectorBundle.finiteDimensional ℝ D.Model D.Fiber x
  exact LinearMap.toContinuousLinearMap
    { toFun := fun T => T.flip
      map_add' := flip_add
      map_smul' := flip_smul }

end SmoothBundle

namespace Shape

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- A scalar-valued tensor with the given argument shapes, in order. -/
@[reducible] def slots : List Shape → Shape
  | [] => .scalar
  | a :: as => .hom a (slots as)

@[simp] theorem slots_replicate_tangent (n : ℕ) :
    slots (List.replicate n .tangent) = covariant n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ]; exact congrArg (Shape.hom .tangent) ih

@[simp] theorem slots_mixed (r s : ℕ) :
    slots (List.replicate r cotangent ++ List.replicate s .tangent) = mixed r s := by
  induction r with
  | zero => exact slots_replicate_tangent s
  | succ r ih => rw [List.replicate_succ]; exact congrArg (Shape.hom cotangent) ih

/-- Arguments for all slots of a tensor at one point. -/
@[reducible] def Arguments (x : M) : List Shape → Type
  | [] => Unit
  | a :: as => (a.bundle I).Fiber x × Arguments x as

/-- Evaluate all arguments of a tensor in order. -/
def evaluate {x : M} : (as : List Shape) → ((slots as).bundle I).Fiber x →
    Arguments I x as → ℝ
  | [], T, _ => T
  | _ :: as, T, v => evaluate as (T v.1) v.2

@[simp] theorem evaluate_nil {x : M} (T : ℝ) (v : Arguments I x []) :
    evaluate I [] T v = T := rfl

@[simp] theorem evaluate_cons {x : M} (a : Shape) (as : List Shape)
    (T : ((slots (a :: as)).bundle I).Fiber x) (v : Arguments I x (a :: as)) :
    evaluate I (a :: as) T v = evaluate I as (T v.1) v.2 := rfl

theorem evaluate_injective {x : M} (as : List Shape) :
    Function.Injective (evaluate I (x := x) as) := by
  induction as with
  | nil =>
    intro T U h
    exact congrFun h ()
  | cons a as ih =>
    intro T U h
    apply ContinuousLinearMap.ext
    intro v
    apply ih
    funext vs
    exact congrFun h (v, vs)

@[simp] theorem evaluate_smul {x : M} (as : List Shape)
    (r : ℝ) (T : ((slots as).bundle I).Fiber x) (v : Arguments I x as) :
    evaluate I as (r • T) v = r * evaluate I as T v := by
  induction as with
  | nil => rfl
  | cons a as ih => exact ih (T v.1) v.2

/-- Concatenate two lists of arguments at the same point. -/
def appendArguments {x : M} (bs : List Shape) :
    (as : List Shape) → Arguments I x as → Arguments I x bs → Arguments I x (as ++ bs)
  | [], _, v => v
  | _ :: as, u, v => (u.1, appendArguments bs as u.2 v)

/-- Tensor product in concatenated slot order, linear in the left factor. -/
def tensorProduct {x : M} (bs : List Shape) (U : ((slots bs).bundle I).Fiber x) :
    (as : List Shape) → ((slots as).bundle I).Fiber x →L[ℝ]
      ((slots (as ++ bs)).bundle I).Fiber x
  | [] => toSpanSingleton ℝ U
  | a :: as => postcomp ((a.bundle I).Fiber x) (tensorProduct bs U as)

@[simp] theorem tensorProduct_nil {x : M} (bs : List Shape)
    (T : ℝ) (U : ((slots bs).bundle I).Fiber x) :
    tensorProduct I bs U [] T = T • U := rfl

@[simp] theorem tensorProduct_cons_apply {x : M} (a : Shape) (as bs : List Shape)
    (T : ((slots (a :: as)).bundle I).Fiber x) (U : ((slots bs).bundle I).Fiber x)
    (v : (a.bundle I).Fiber x) :
    let L : (a.bundle I).Fiber x →L[ℝ] ((slots (as ++ bs)).bundle I).Fiber x :=
      tensorProduct I bs U (a :: as) T
    L v = tensorProduct I bs U as (T v) := rfl

theorem tensorProduct_add_right {x : M} (as bs : List Shape)
    (T : ((slots as).bundle I).Fiber x) (U V : ((slots bs).bundle I).Fiber x) :
    tensorProduct I bs (U + V) as T =
      tensorProduct I bs U as T + tensorProduct I bs V as T := by
  induction as with
  | nil => exact smul_add T U V
  | cons a as ih =>
    apply ContinuousLinearMap.ext
    intro v
    exact ih (T v)

theorem tensorProduct_smul_right {x : M} (as bs : List Shape) (r : ℝ)
    (T : ((slots as).bundle I).Fiber x) (U : ((slots bs).bundle I).Fiber x) :
    tensorProduct I bs (r • U) as T = r • tensorProduct I bs U as T := by
  induction as with
  | nil => exact smul_comm T r U
  | cons a as ih =>
    apply ContinuousLinearMap.ext
    intro v
    exact ih (T v)

theorem evaluate_tensorProduct {x : M} (as bs : List Shape)
    (T : ((slots as).bundle I).Fiber x) (U : ((slots bs).bundle I).Fiber x)
    (u : Arguments I x as) (v : Arguments I x bs) :
    evaluate I (as ++ bs) (tensorProduct I bs U as T) (appendArguments I bs as u v) =
      evaluate I as T u * evaluate I bs U v := by
  induction as with
  | nil => exact evaluate_smul I bs T U v
  | cons a as ih => exact ih (T u.1) u.2

theorem contMDiffAt_tensorProduct (as bs : List Shape) {x : M}
    {T : ∀ y : M, ((slots as).bundle I).Fiber y}
    {U : ∀ y : M, ((slots bs).bundle I).Fiber y}
    (hT : SmoothBundle.SmoothAt I ((slots as).bundle I) T x)
    (hU : SmoothBundle.SmoothAt I ((slots bs).bundle I) U x) :
    SmoothBundle.SmoothAt I ((slots (as ++ bs)).bundle I)
      (fun y => tensorProduct I bs (U y) as (T y)) x := by
  induction as with
  | nil =>
    have hs : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ T x := by
      rw [SmoothBundle.SmoothAt, contMDiffAt_section] at hT
      exact hT
    exact hs.smul_section hU
  | cons a as ih =>
    apply SmoothBundle.contMDiffAt_of_apply (a.bundle I) ((slots (as ++ bs)).bundle I)
    intro v hv
    exact ih (hT.clm_bundle_apply hv)

section Transport

variable {N : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- Tensor product commutes with invertible tangent transport. -/
theorem map_tensorProduct {x : M} {y : N} (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    (as bs : List Shape) (T : ((slots as).bundle I).Fiber x)
    (U : ((slots bs).bundle I).Fiber x) :
    map I (slots (as ++ bs)) e (tensorProduct I bs U as T) =
      tensorProduct I bs (map I (slots bs) e U) as (map I (slots as) e T) := by
  induction as with
  | nil => exact (map I (slots bs) e).map_smul T U
  | cons a as ih =>
    apply ContinuousLinearMap.ext
    intro v
    exact ih (T ((map I a e).symm v))

end Transport

/-- The tensor product of two smooth tensor fields. -/
def tensorProductField (as bs : List Shape)
    (T : ((slots as).bundle I (M := M)).Section I)
    (U : ((slots bs).bundle I (M := M)).Section I) :
    ((slots (as ++ bs)).bundle I (M := M)).Section I :=
  ⟨fun x => tensorProduct I bs (U x) as (T x),
    fun x => contMDiffAt_tensorProduct I as bs (T.contMDiff x) (U.contMDiff x)⟩

@[simp] theorem tensorProductField_apply (as bs : List Shape)
    (T : ((slots as).bundle I (M := M)).Section I)
    (U : ((slots bs).bundle I (M := M)).Section I) (x : M) :
    tensorProductField I as bs T U x = tensorProduct I bs (U x) as (T x) := rfl

/-- A permutation of slots generated by adjacent exchanges. Constructors
track each argument type, including permutations between unlike slots. -/
inductive SlotPermutation : List Shape → List Shape → Type
  | nil : SlotPermutation [] []
  | cons (a : Shape) {as bs} : SlotPermutation as bs → SlotPermutation (a :: as) (a :: bs)
  | swap (a b : Shape) (as : List Shape) : SlotPermutation (a :: b :: as) (b :: a :: as)
  | trans {as bs cs} : SlotPermutation as bs → SlotPermutation bs cs → SlotPermutation as cs

namespace SlotPermutation

/-- Every list permutation can be expressed as typed adjacent exchanges. -/
theorem ofPerm {as bs : List Shape} (h : as.Perm bs) : Nonempty (SlotPermutation as bs) := by
  induction h with
  | nil => exact ⟨.nil⟩
  | cons a _ ih => exact ⟨.cons a ih.some⟩
  | swap a b as => exact ⟨.swap b a as⟩
  | trans _ _ ih₁ ih₂ => exact ⟨.trans ih₁.some ih₂.some⟩

/-- Reorder the arguments of the output tensor for evaluation of the input tensor. -/
def arguments {x : M} {as bs : List Shape} :
    SlotPermutation as bs → Arguments I x bs → Arguments I x as
  | .nil, _ => ()
  | .cons _ p, v => (v.1, arguments p v.2)
  | .swap _ _ _, v => (v.2.1, v.1, v.2.2)
  | .trans p q, v => arguments p (arguments q v)

/-- Permute tensor slots on the actual fibre. -/
def tensorMap {x : M} {as bs : List Shape} :
    SlotPermutation as bs →
      ((slots as).bundle I).Fiber x →L[ℝ] ((slots bs).bundle I).Fiber x
  | .nil => ContinuousLinearMap.id ℝ ℝ
  | .cons a p => postcomp ((a.bundle I).Fiber x) (tensorMap p)
  | .swap a b as => SmoothBundle.swapFiber I (a.bundle I) (b.bundle I) ((slots as).bundle I) x
  | .trans p q => (tensorMap q).comp (tensorMap p)

@[simp] theorem tensorMap_cons_apply {x : M} (a : Shape) {as bs : List Shape}
    (p : SlotPermutation as bs) (T : ((slots (a :: as)).bundle I).Fiber x)
    (v : (a.bundle I).Fiber x) :
    tensorMap I (.cons a p) T v = tensorMap I p (T v) := rfl

@[simp] theorem tensorMap_swap_apply {x : M} (a b : Shape) (as : List Shape)
    (T : ((slots (a :: b :: as)).bundle I).Fiber x)
    (u : (a.bundle I).Fiber x) (v : (b.bundle I).Fiber x) :
    tensorMap I (.swap a b as) T v u = T u v := rfl

@[simp] theorem tensorMap_trans_apply {x : M} {as bs cs : List Shape}
    (p : SlotPermutation as bs) (q : SlotPermutation bs cs)
    (T : ((slots as).bundle I).Fiber x) :
    tensorMap I (.trans p q) T = tensorMap I q (tensorMap I p T) := rfl

theorem evaluate_tensorMap {x : M} {as bs : List Shape}
    (p : SlotPermutation as bs) (T : ((slots as).bundle I).Fiber x)
    (v : Arguments I x bs) :
    evaluate I bs (tensorMap I p T) v = evaluate I as T (arguments I p v) := by
  induction p with
  | nil => rfl
  | cons a p ih => exact ih (T v.1) v.2
  | swap a b as => rfl
  | trans p q ihp ihq => exact (ihq (tensorMap I p T) v).trans (ihp T _)

theorem contMDiffAt_tensorMap {as bs : List Shape} (p : SlotPermutation as bs) {x : M}
    {T : ∀ y : M, ((slots as).bundle I).Fiber y}
    (hT : SmoothBundle.SmoothAt I ((slots as).bundle I) T x) :
    SmoothBundle.SmoothAt I ((slots bs).bundle I) (fun y => tensorMap I p (T y)) x := by
  induction p with
  | nil => exact hT
  | @cons a as bs p ih =>
    apply SmoothBundle.contMDiffAt_of_apply (a.bundle I) ((slots bs).bundle I)
    intro v hv
    exact ih (hT.clm_bundle_apply hv)
  | swap a b as =>
    apply SmoothBundle.contMDiffAt_of_apply (b.bundle I) ((slots (a :: as)).bundle I)
    intro v hv
    apply SmoothBundle.contMDiffAt_of_apply (a.bundle I) ((slots as).bundle I)
    intro u hu
    exact (hT.clm_bundle_apply hu).clm_bundle_apply hv
  | trans p q ihp ihq => exact ihq (ihp hT)

section Transport

variable {N : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- Permuting slots commutes with invertible tangent transport. -/
theorem map_tensorMap {x : M} {y : N} (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    {as bs : List Shape} (p : SlotPermutation as bs)
    (T : ((slots as).bundle I).Fiber x) :
    map I (slots bs) e (tensorMap I p T) = tensorMap I p (map I (slots as) e T) := by
  induction p with
  | nil => rfl
  | @cons a as bs p ih =>
    apply ContinuousLinearMap.ext
    intro v
    exact ih (T ((map I a e).symm v))
  | swap a b as =>
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro u
    rfl
  | trans p q ihp ihq =>
    rw [tensorMap_trans_apply, tensorMap_trans_apply, ihq, ihp]

end Transport

/-- Leave every slot in its original position. -/
def refl : (as : List Shape) → SlotPermutation as as
  | [] => .nil
  | a :: as => .cons a (refl as)

@[simp] theorem tensorMap_refl {x : M} (as : List Shape)
    (T : ((slots as).bundle I).Fiber x) :
    tensorMap I (refl as) T = T := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    apply ContinuousLinearMap.ext
    intro v
    exact ih (T v)

/-- Undo a slot permutation by reversing its adjacent exchanges. -/
def symm {as bs : List Shape} : SlotPermutation as bs → SlotPermutation bs as
  | .nil => .nil
  | .cons a p => .cons a (symm p)
  | .swap a b as => .swap b a as
  | .trans p q => .trans (symm q) (symm p)

@[simp] theorem arguments_symm {x : M} {as bs : List Shape}
    (p : SlotPermutation as bs) (v : Arguments I x as) :
    arguments I p (arguments I p.symm v) = v := by
  induction p with
  | nil => exact Subsingleton.elim _ _
  | cons a p ih => exact Prod.ext rfl (ih v.2)
  | swap a b as => rfl
  | trans p q ihp ihq =>
    change arguments I p (arguments I q (arguments I q.symm (arguments I p.symm v))) = v
    rw [ihq, ihp]

@[simp] theorem tensorMap_symm {x : M} {as bs : List Shape}
    (p : SlotPermutation as bs) (T : ((slots as).bundle I).Fiber x) :
    tensorMap I p.symm (tensorMap I p T) = T := by
  apply evaluate_injective I as
  funext v
  rw [evaluate_tensorMap, evaluate_tensorMap, arguments_symm]

/-- Permute the slots of a smooth tensor field. -/
def tensorField {as bs : List Shape} (p : SlotPermutation as bs)
    (T : ((slots as).bundle I (M := M)).Section I) :
    ((slots bs).bundle I (M := M)).Section I :=
  ⟨fun x => tensorMap I p (T x), fun x => contMDiffAt_tensorMap I p (T.contMDiff x)⟩

@[simp] theorem tensorField_apply {as bs : List Shape} (p : SlotPermutation as bs)
    (T : ((slots as).bundle I (M := M)).Section I) (x : M) :
    tensorField I p T x = tensorMap I p (T x) := rfl

end SlotPermutation
section Contraction

/-- Evaluate a prefix of a tensor's slots and retain the remaining slots. -/
def applyPrefix {x : M} (bs : List Shape) :
    (as : List Shape) → ((slots (as ++ bs)).bundle I).Fiber x →
      Arguments I x as → ((slots bs).bundle I).Fiber x
  | [], T, _ => T
  | a :: as, T, v =>
    let L : (a.bundle I).Fiber x →L[ℝ] ((slots (as ++ bs)).bundle I).Fiber x := T
    applyPrefix bs as (L v.1) v.2

/-- Contract the final cotangent and tangent slots by tracing the induced
endomorphism of the cotangent fibre. -/
def traceSlots {x : M} :
    (as : List Shape) → ((slots (as ++ [cotangent, .tangent])).bundle I).Fiber x →L[ℝ]
      ((slots as).bundle I).Fiber x
  | [] => Tensor.fiberTrace (cotangent.bundle I (M := M)).Model x
  | a :: as => postcomp ((a.bundle I).Fiber x) (traceSlots as)

theorem evaluate_traceSlots {x : M} (as : List Shape)
    (T : ((slots (as ++ [cotangent, .tangent])).bundle I).Fiber x)
    (v : Arguments I x as) :
    evaluate I as (traceSlots I as T) v =
      LinearMap.trace ℝ ((cotangent.bundle I).Fiber x)
        (applyPrefix I [cotangent, .tangent] as T v).toLinearMap := by
  induction as with
  | nil => exact Tensor.fiberTrace_apply (cotangent.bundle I (M := M)).Model x T
  | cons a as ih =>
    let L : (a.bundle I).Fiber x →L[ℝ]
        ((slots (as ++ [cotangent, .tangent])).bundle I).Fiber x := T
    exact ih (L v.1) v.2

theorem contMDiffAt_traceSlots (as : List Shape) {x : M}
    {T : ∀ y : M, ((slots (as ++ [cotangent, .tangent])).bundle I).Fiber y}
    (hT : SmoothBundle.SmoothAt I ((slots (as ++ [cotangent, .tangent])).bundle I) T x) :
    SmoothBundle.SmoothAt I ((slots as).bundle I) (fun y => traceSlots I as (T y)) x := by
  induction as with
  | nil =>
    have h := Tensor.contMDiff_fiberTrace (cotangent.bundle I (M := M)).Model
      (I := I) (V := (cotangent.bundle I (M := M)).Fiber) x
    exact h.clm_bundle_apply hT
  | cons a as ih =>
    apply SmoothBundle.contMDiffAt_of_apply (a.bundle I) ((slots as).bundle I)
    intro v hv
    exact ih (hT.clm_bundle_apply hv)

/-- Contract any opposite-variance pair selected by a typed slot permutation.
The other slots retain the order specified by the permutation. -/
def contractSlots {x : M} {as bs : List Shape}
    (p : SlotPermutation as (bs ++ [cotangent, .tangent])) :
    ((slots as).bundle I).Fiber x →L[ℝ] ((slots bs).bundle I).Fiber x :=
  (traceSlots I bs).comp (p.tensorMap I)

/-- Contract the selected pair in a smooth tensor field. -/
def contractSlotsField {as bs : List Shape}
    (p : SlotPermutation as (bs ++ [cotangent, .tangent]))
    (T : ((slots as).bundle I (M := M)).Section I) : ((slots bs).bundle I (M := M)).Section I :=
  ⟨fun x => contractSlots I p (T x), fun x => contMDiffAt_traceSlots I bs
    (p.contMDiffAt_tensorMap I (T.contMDiff x))⟩

@[simp] theorem contractSlotsField_apply {as bs : List Shape}
    (p : SlotPermutation as (bs ++ [cotangent, .tangent]))
    (T : ((slots as).bundle I (M := M)).Section I) (x : M) :
    contractSlotsField I p T x = contractSlots I p (T x) := rfl

variable {N : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- The trace of a pair commutes with invertible tangent transport. -/
theorem map_traceSlots {x : M} {y : N} (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    (as : List Shape) (T : ((slots (as ++ [cotangent, .tangent])).bundle I).Fiber x) :
    map I (slots as) e (traceSlots I as T) =
      traceSlots I as (map I (slots (as ++ [cotangent, .tangent])) e T) := by
  induction as with
  | nil =>
    change Tensor.fiberTrace (cotangent.bundle I (M := M)).Model
      (V := (cotangent.bundle I (M := M)).Fiber) x T =
      Tensor.fiberTrace (cotangent.bundle I (M := N)).Model
        (V := (cotangent.bundle I (M := N)).Fiber) y (map I (.hom cotangent cotangent) e T)
    rw [Tensor.fiberTrace_apply, Tensor.fiberTrace_apply]
    exact (trace_map I cotangent e T).symm
  | cons a as ih =>
    apply ContinuousLinearMap.ext
    intro v
    let L : (a.bundle I).Fiber x →L[ℝ]
        ((slots (as ++ [cotangent, .tangent])).bundle I).Fiber x := T
    exact ih (L ((map I a e).symm v))

theorem map_contractSlots {x : M} {y : N} (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    {as bs : List Shape} (p : SlotPermutation as (bs ++ [cotangent, .tangent]))
    (T : ((slots as).bundle I).Fiber x) :
    map I (slots bs) e (contractSlots I p T) =
      contractSlots I p (map I (slots as) e T) := by
  change map I (slots bs) e (traceSlots I bs (p.tensorMap I T)) =
    traceSlots I bs (p.tensorMap I (map I (slots as) e T))
  rw [map_traceSlots, SlotPermutation.map_tensorMap]

section Components

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- In any tangent basis, a contracted pair is summed over the basis and its
dual, with the same index in both slots. -/
theorem evaluate_contractSlots_eq_sum {x : M} {as bs : List Shape}
    (p : SlotPermutation as (bs ++ [cotangent, .tangent]))
    (T : ((slots as).bundle I).Fiber x) (v : Arguments I x bs)
    (b : Module.Basis ι ℝ (TangentSpace I x)) :
    evaluate I bs (contractSlots I p T) v =
      ∑ i, applyPrefix I [cotangent, .tangent] bs (p.tensorMap I T) v
        (b.coord i).toContinuousLinearMap (b i) := by
  change evaluate I bs (traceSlots I bs (p.tensorMap I T)) v = _
  rw [evaluate_traceSlots]
  let d := b.dualBasis.map
    (LinearMap.toContinuousLinearMap : Module.Dual ℝ (TangentSpace I x) ≃ₗ[ℝ]
      (cotangent.bundle I).Fiber x)
  rw [LinearMap.trace_eq_matrix_trace ℝ d, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  let L := applyPrefix I [cotangent, .tangent] bs (p.tensorMap I T) v
  let α : (cotangent.bundle I).Fiber x := LinearMap.toContinuousLinearMap (b.dualBasis i)
  let β : (cotangent.bundle I).Fiber x := L α
  change b.dualBasis.repr (ContinuousLinearMap.toLinearMap β) i = _
  rw [Module.Basis.dualBasis_repr]
  change L α (b i) = L (b.coord i).toContinuousLinearMap (b i)
  rw [show α = (b.coord i).toContinuousLinearMap by
    ext w
    exact b.dualBasis_apply i w]

end Components
end Contraction
section Pullback

variable {N : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  (f : M ≃ₘ⟮I, I⟯ N)

theorem pullbackField_tensorProduct (as bs : List Shape)
    (T : ((slots as).bundle I (M := N)).Section I)
    (U : ((slots bs).bundle I (M := N)).Section I) :
    pullbackField I (slots (as ++ bs)) f (tensorProductField I as bs T U) =
      tensorProductField I as bs (pullbackField I (slots as) f T)
        (pullbackField I (slots bs) f U) := by
  ext x : 1
  exact map_tensorProduct I (tangentEquiv I f x).symm as bs (T (f x)) (U (f x))

theorem pullbackField_tensorPermutation {as bs : List Shape} (p : SlotPermutation as bs)
    (T : ((slots as).bundle I (M := N)).Section I) :
    pullbackField I (slots bs) f (p.tensorField I T) =
      p.tensorField I (pullbackField I (slots as) f T) := by
  ext x : 1
  exact p.map_tensorMap I (tangentEquiv I f x).symm (T (f x))

theorem pullbackField_contractSlots {as bs : List Shape}
    (p : SlotPermutation as (bs ++ [cotangent, .tangent]))
    (T : ((slots as).bundle I (M := N)).Section I) :
    pullbackField I (slots bs) f (contractSlotsField I p T) =
      contractSlotsField I p (pullbackField I (slots as) f T) := by
  ext x : 1
  exact map_contractSlots I (tangentEquiv I f x).symm p (T (f x))

end Pullback

section CovariantPullback

variable {F H' N : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] (J : ModelWithCorners ℝ F H')
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Pullback preserves the product of two covectors even for singular or
dimension-changing maps. -/
theorem covariantPullbackField_tensorProduct_one (f : C^∞⟮I, M; J, N⟯)
    (T U : (cotangent.bundle J (M := N)).Section J) :
    covariantPullbackField I J 2 f (tensorProductField J [.tangent] [.tangent] T U) =
      tensorProductField I [.tangent] [.tangent]
        (covariantPullbackField I J 1 f T) (covariantPullbackField I J 1 f U) := rfl

end CovariantPullback
end Shape
end ProjectAInos.SmoothGeometry.Tensor
