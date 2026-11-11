/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.RealSpectrum
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Real evaluation and the topology of the C∞ spectrum -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ProjectAInos.SmoothGeometry.RealSpectrum

open SmoothAlgebra TopologicalSpace
open scoped ContDiff

variable {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]

/-- Evaluation of any ring element is a continuous real-valued function. -/
theorem continuous_eval (a : A) : Continuous (fun x : RealSpectrum A => x a) := by
  rw [continuous_def]
  intro U hU
  obtain ⟨g, hg, hgd, -⟩ := hU.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  let f : SmoothOperation 1 := SmoothOperation.ofContDiff (fun t : Fin 1 → ℝ => g (t 0))
    (hgd.comp (contDiff_apply ℝ (fun _ => ℝ) 0))
  have heq : (fun x : RealSpectrum A => x a) ⁻¹' U =
      (basicOpen (SmoothRing.op f ![a]) : Set (RealSpectrum A)) := by
    ext x
    change x a ∈ U ↔ x.hom (SmoothRing.op f ![a]) ≠ 0
    rw [x.hom.map_op, real_op]
    change x a ∈ U ↔ g (x a) ≠ 0
    rw [← hg]
    rfl
  rw [heq]
  exact (basicOpen _).isOpen

/-- The real-spectrum topology is the initial topology of all evaluations. -/
theorem continuous_iff_eval {X : Type*} [TopologicalSpace X] (f : X → RealSpectrum A) :
    Continuous f ↔ ∀ a : A, Continuous (fun x => f x a) := by
  constructor
  · intro h a
    exact (continuous_eval a).comp h
  · intro h
    apply continuous_generateFrom_iff.mpr
    rintro _ ⟨a, rfl⟩
    exact isOpen_ne.preimage (h a)

/-- The spectrum of the free C∞-ring on finitely many coordinates is Euclidean
space, with its usual topology. -/
def euclideanHomeomorph (n : ℕ) : RealSpectrum (SmoothOperation n) ≃ₜ (Fin n → ℝ) where
  toFun x i := x (SmoothOperation.proj i)
  invFun x := SmoothOperation.eval x
  left_inv x := by
    apply SmoothOperation.hom_ext
    intro i
    rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi (fun i => continuous_eval (SmoothOperation.proj i))
  continuous_invFun := (continuous_iff_eval _).mpr (fun f => f.contMDiff.continuous)

end ProjectAInos.SmoothGeometry.RealSpectrum
