/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Pullback and contraction of covariant bilinear tensors

These fibrewise operations are independent of a metric or a physical theory.
Their smoothness allows them to be used in vector-bundle charts.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ProjectAInos.SmoothGeometry.BilinearTensor

variable {E F G X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Pull a covariant bilinear tensor back in both slots. -/
def pullback (B : F →L[ℝ] F →L[ℝ] ℝ) (A : E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E F ℝ).flip A).comp (B.comp A)

@[simp] theorem pullback_apply (B : F →L[ℝ] F →L[ℝ] ℝ) (A : E →L[ℝ] F)
    (v w : E) : pullback B A v w = B (A v) (A w) := rfl

@[simp] theorem pullback_id (B : E →L[ℝ] E →L[ℝ] ℝ) :
    pullback B (ContinuousLinearMap.id ℝ E) = B := by ext; rfl

theorem pullback_comp (B : G →L[ℝ] G →L[ℝ] ℝ) (A : F →L[ℝ] G) (C : E →L[ℝ] F) :
    pullback B (A.comp C) = pullback (pullback B A) C := by ext; rfl

theorem pullback_symmetric (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (A : E →L[ℝ] F) (v w : E) :
    pullback B A v w = pullback B A w v := hB _ _

/-- Pullback of smoothly varying tensors by smoothly varying linear maps is smooth. -/
theorem contDiff_pullback {n : WithTop ℕ∞}
    {B : X → F →L[ℝ] F →L[ℝ] ℝ} {A : X → E →L[ℝ] F}
    (hB : ContDiff ℝ n B) (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (fun x => pullback (B x) (A x)) := by
  simpa only [pullback, Function.comp_def] using
    (((ContinuousLinearMap.compL ℝ E F ℝ).flip.contDiff).comp hA).clm_comp
      (hB.clm_comp hA)

/-- Evaluating both covariant slots against smooth vectors is smooth. -/
theorem contDiff_contract {n : WithTop ℕ∞}
    {B : X → E →L[ℝ] E →L[ℝ] ℝ} {v w : X → E}
    (hB : ContDiff ℝ n B) (hv : ContDiff ℝ n v) (hw : ContDiff ℝ n w) :
    ContDiff ℝ n (fun x => B x (v x) (w x)) :=
  (hB.clm_apply hv).clm_apply hw

end ProjectAInos.SmoothGeometry.BilinearTensor
