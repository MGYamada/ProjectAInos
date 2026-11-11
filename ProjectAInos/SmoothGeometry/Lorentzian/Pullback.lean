/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Tensor
public import ProjectAInos.SmoothGeometry.Tensor.Pullback

/-! # Pullback Lorentz metrics

A smooth map whose tangent derivatives are invertible pulls back a Lorentz
metric of the same dimension. Smoothness and signature are proved on the
actual tangent bundle; global bijectivity is not required.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]
  (h : LorentzMetric σ d N)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Lorentz metrics are determined by their bilinear forms. -/
@[ext] theorem ext {g g' : LorentzMetric σ d M}
    (he : ∀ x v w, g.form x v w = g'.form x v w) : g = g' := by
  have hform : g.form = g'.form := by
    funext x
    ext v w
    exact he x v w
  cases g
  cases g'
  cases hform
  rfl

/-- Pull back a Lorentz metric by a smooth map with invertible tangent derivative. -/
def pullback (f : M → N) (hf : ContMDiff I I ∞ f)
    (hinv : ∀ x, (mfderiv I I f x).IsInvertible) : LorentzMetric σ d M := by
  let e (x : M) : TangentSpace I x ≃L[ℝ] TangentSpace I (f x) := (hinv x).choose
  have he (x : M) : (e x).toContinuousLinearMap = mfderiv I I f x := (hinv x).choose_spec
  refine
    { form := fun x => Tensor.Shape.pullback I (.mixed 0 2) (e x) (h.form (f x))
      smooth := ?_
      signature := ?_ }
  · intro x
    have hs : Tensor.Shape.SmoothTransportAt I .tangent id f e x := by
      change ContMDiffAt I 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d) ∞
        (fun y => inCoordinates (MinkowskiModel d) (TangentSpace I (M := M))
          (MinkowskiModel d) (TangentSpace I (M := N))
          x y (f x) (f y) (e y).toContinuousLinearMap) x
      simp_rw [he]
      convert! (hf x).mfderiv_const (m := ∞) (by simp) using 1
    have ht := (Tensor.Shape.smoothTransportAt_of_tangent
      (M := M) (N := N) (P := M) I (.mixed 0 2) (a := id) (b := f) (p := x) e
      contMDiffAt_id (hf x) hs).2
    exact ht.clm_apply_of_inCoordinates ((h.toTensor.contMDiff.comp hf) x) contMDiffAt_id
  · intro x
    obtain ⟨j, hj⟩ := h.signature (f x)
    refine ⟨(e x).trans j, ?_⟩
    intro v w
    change h.form (f x) ((e x).symm.symm v) ((e x).symm.symm w) = _
    simpa only [ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.trans_apply] using hj (e x v) (e x w)

/-- Pullback coefficients are evaluations against the actual manifold derivative. -/
@[simp] theorem pullback_form (f : M → N) (hf : ContMDiff I I ∞ f)
    (hinv : ∀ x, (mfderiv I I f x).IsInvertible) (x : M)
    (v w : TangentSpace I x) :
    (h.pullback f hf hinv).form x v w =
      h.form (f x) (mfderiv I I f x v) (mfderiv I I f x w) := by
  change h.form (f x) ((hinv x).choose.symm.symm v) ((hinv x).choose.symm.symm w) = _
  simp only [ContinuousLinearEquiv.symm_symm, ← ContinuousLinearEquiv.coe_coe,
    (hinv x).choose_spec]

/-- The identity map pulls a metric back to itself. -/
@[simp] theorem pullback_id :
    h.pullback id contMDiff_id (fun (x : N) =>
      ⟨ContinuousLinearEquiv.refl ℝ (TangentSpace I x), by rw [mfderiv_id]; rfl⟩) = h := by
  apply LorentzMetric.ext
  intro x v w
  simp [pullback_form, mfderiv_id]

/-- Pullback of a metric commutes with reversal of its overall sign. -/
@[simp] theorem pullback_opposite (f : M → N) (hf : ContMDiff I I ∞ f)
    (hinv : ∀ x, (mfderiv I I f x).IsInvertible) :
    h.opposite.pullback f hf hinv = (h.pullback f hf hinv).opposite := by
  apply LorentzMetric.ext
  intro x v w
  simp [pullback_form]

/-- Pulling back successively is the same metric as pulling back the composite. -/
theorem pullback_comp {P : Type} [TopologicalSpace P]
    [ChartedSpace (MinkowskiModel d) P] [IsManifold I ∞ P]
    (k : LorentzMetric σ d P) (f : M → N) (q : N → P)
    (hf : ContMDiff I I ∞ f) (hq : ContMDiff I I ∞ q)
    (hfinv : ∀ x, (mfderiv I I f x).IsInvertible)
    (hqinv : ∀ y, (mfderiv I I q y).IsInvertible) :
    (k.pullback q hq hqinv).pullback f hf hfinv =
      k.pullback (q ∘ f) (hq.comp hf) (fun x => by
        rw [mfderiv_comp x ((hq (f x)).mdifferentiableAt (by simp))
          ((hf x).mdifferentiableAt (by simp))]
        exact (hqinv (f x)).comp (hfinv x)) := by
  apply LorentzMetric.ext
  intro x v w
  simp only [pullback_form, Function.comp_apply,
    mfderiv_comp x ((hq (f x)).mdifferentiableAt (by simp))
      ((hf x).mdifferentiableAt (by simp)), comp_apply]

end ProjectAInos.SmoothGeometry.LorentzMetric
