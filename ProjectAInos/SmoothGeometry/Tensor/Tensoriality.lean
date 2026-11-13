/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.Bundle
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-! # Tensoriality for operations on locally Cⁿ sections

Higher differential operators such as curvature need more than one derivative
of their input sections. This finite-regularity variant of mathlib's
`TensorialAt` constructs fibre maps from operations linear over scalar germs.
The proof uses local bundle frames and does not require global extensions or
a global frame. The locality and pointwise arguments follow mathlib's
`Geometry.Manifold.VectorBundle.Tensoriality`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle Module
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.Tensor

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (B : SmoothBundle I (M := M)) (n : ℕ∞)
  {A : Type} [AddCommGroup A] [Module ℝ A]

/-- Linearity over germs of `Cⁿ` scalar functions, on locally `Cⁿ` sections. -/
structure ContMDiffTensorialAt (Φ : (∀ y, B.Fiber y) → A) (x : M) : Prop where
  smul : ∀ {f : M → ℝ} {s : ∀ y, B.Fiber y},
    ContMDiffAt I 𝓘(ℝ) n f x →
    ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (s y)) x →
    Φ (f • s) = f x • Φ s
  add : ∀ {s t : ∀ y, B.Fiber y},
    ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (s y)) x →
    ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x →
    Φ (s + t) = Φ s + Φ t

namespace ContMDiffTensorialAt

variable {B n} {Φ : (∀ y, B.Fiber y) → A} {x : M}

/-- Tensorial operations depend only on the germ of a locally `Cⁿ` section. -/
theorem congr_of_eventuallyEq (hΦ : ContMDiffTensorialAt B n Φ x)
    {s t : ∀ y, B.Fiber y}
    (hs : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (s y)) x)
    (ht : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x)
    (hst : ∀ᶠ y in 𝓝 x, s y = t y) : Φ s = Φ t := by
  classical
  let f : M → ℝ := fun y => if s y = t y then 1 else 0
  have hfx : f x = 1 := by simp [f, hst.self_of_nhds]
  have hf : ContMDiffAt I 𝓘(ℝ) n f x :=
    (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
      (hst.mono fun y hy => by simp [f, hy])
  have heq : f • s = f • t := by
    funext y
    dsimp [f]
    split_ifs with h <;> simp [h]
  calc
    Φ s = Φ (f • s) := by rw [hΦ.smul hf hs, hfx, one_smul]
    _ = Φ (f • t) := congrArg Φ heq
    _ = Φ t := by rw [hΦ.smul hf ht, hfx, one_smul]

theorem zero (hΦ : ContMDiffTensorialAt B n Φ x) : Φ 0 = 0 := by
  have h := hΦ.smul (f := fun _ => 0) (s := 0)
    contMDiffAt_const (contMDiffAt_zeroSection ..)
  simpa using h

theorem sum (hΦ : ContMDiffTensorialAt B n Φ x) {ι : Type} (a : Finset ι)
    (s : ι → ∀ y, B.Fiber y)
    (hs : ∀ i ∈ a, ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n
      (fun y => TotalSpace.mk' B.Model y (s i y)) x) :
    Φ (fun y => ∑ i ∈ a, s i y) = ∑ i ∈ a, Φ (s i) := by
  classical
  induction a using Finset.induction_on with
  | empty => simpa using! hΦ.zero
  | insert i a hi ih =>
    rw [Finset.forall_mem_insert] at hs
    simp only [Finset.sum_insert hi, ← ih hs.2]
    exact hΦ.add hs.1 (ContMDiffAt.sum_section hs.2)

/-- Linearity over scalar germs forces dependence only on the fibre value. -/
theorem pointwise (hΦ : ContMDiffTensorialAt B n Φ x) {s t : ∀ y, B.Fiber y}
    (hs : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (s y)) x)
    (ht : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x)
    (hst : s x = t x) : Φ s = Φ t := by
  let e := trivializationAt B.Model B.Fiber x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt B.Model B.Fiber x
  let b := Basis.ofVectorSpace ℝ B.Model
  let v := e.localFrame b
  let c := e.localFrameCoeff I b
  have hv (i) : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n
      (fun y => TotalSpace.mk' B.Model y (v i y)) x :=
    contMDiffAt_localFrame_of_mem n e b i hx
  have hc {s : ∀ y, B.Fiber y}
      (hs : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n
        (fun y => TotalSpace.mk' B.Model y (s y)) x) (i) :
      ContMDiffAt I 𝓘(ℝ) n (LinearMap.piApply (c i) s) x :=
    contMDiffAt_localFrameCoeff b hx hs i
  have hexpand {s : ∀ y, B.Fiber y}
      (hs : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n
        (fun y => TotalSpace.mk' B.Model y (s y)) x) :
      Φ s = Φ (fun y => ∑ i, c i y (s y) • v i y) :=
    hΦ.congr_of_eventuallyEq hs
      (.sum_section fun i _ => (hc hs i).smul_section (hv i))
      (e.eventually_eq_localFrame_sum_coeff_smul b hx)
  rw [hexpand hs, hexpand ht, hΦ.sum, hΦ.sum]
  · apply Finset.sum_congr rfl
    intro i _
    calc
      _ = c i x (s x) • Φ (v i) := by simpa using! hΦ.smul (hc hs i) (hv i)
      _ = c i x (t x) • Φ (v i) := congrArg (fun w => c i x w • Φ (v i)) hst
      _ = _ := by simpa using! (hΦ.smul (hc ht i) (hv i)).symm
  · exact fun i _ => (hc ht i).smul_section (hv i)
  · exact fun i _ => (hc hs i).smul_section (hv i)

variable [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]

/-- Construct a continuous linear map on the actual fibre from a tensorial
operation on locally `Cⁿ` sections. -/
def mkHom (Φ : (∀ y, B.Fiber y) → A) (x : M) (hΦ : ContMDiffTensorialAt B n Φ x) :
    B.Fiber x →L[ℝ] A :=
  have : T2Space (B.Fiber x) := FiberBundle.t2Space B.Model B.Fiber x
  have : FiniteDimensional ℝ (B.Fiber x) := VectorBundle.finiteDimensional ℝ B.Model B.Fiber x
  LinearMap.toContinuousLinearMap {
    toFun v := Φ (extend B.Model v)
    map_add' v w := by
      rw [← hΦ.add (contMDiffAt_extend ..) (contMDiffAt_extend ..)]
      apply hΦ.pointwise (contMDiffAt_extend ..)
        ((contMDiffAt_extend ..).add_section (contMDiffAt_extend ..))
      simp
    map_smul' a v := by
      dsimp
      rw [← hΦ.smul (f := fun _ => a) contMDiffAt_const (contMDiffAt_extend ..)]
      apply hΦ.pointwise (contMDiffAt_extend ..)
        (contMDiffAt_const.smul_section (contMDiffAt_extend ..))
      simp }

theorem mkHom_apply (hΦ : ContMDiffTensorialAt B n Φ x) {s : ∀ y, B.Fiber y}
    (hs : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n
      (fun y => TotalSpace.mk' B.Model y (s y)) x) :
    mkHom Φ x hΦ (s x) = Φ s :=
  hΦ.pointwise (contMDiffAt_extend ..) hs (by simp)

@[simp] theorem mkHom_apply_eq_extend (hΦ : ContMDiffTensorialAt B n Φ x) (v : B.Fiber x) :
    mkHom Φ x hΦ v = Φ (extend B.Model v) := rfl

end ContMDiffTensorialAt
end ProjectAInos.SmoothGeometry.Tensor
