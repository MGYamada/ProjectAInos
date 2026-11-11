/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Causal
public import ProjectAInos.SmoothGeometry.Minkowski.Dual
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-! # Lorentz transformations and their time and space orientations -/

@[expose] public section
noncomputable section
namespace ProjectAInos.SmoothGeometry.Minkowski

/-- The group preserving the Minkowski pairing. This group is independent of convention. -/
def LorentzGroup (d : ℕ) : Subgroup (MinkowskiModel d ≃ₗ[ℝ] MinkowskiModel d) where
  carrier := {L | ∀ v w, pair (L v) (L w) = pair v w}
  one_mem' := by intro v w; rfl
  mul_mem' := by intro L K hL hK v w; exact (hL (K v) (K w)).trans (hK v w)
  inv_mem' := by
    intro L hL v w
    simpa using (hL (L.symm v) (L.symm w)).symm

theorem mem_lorentzGroup_iff (σ : LorentzConvention) {d : ℕ}
    (L : MinkowskiModel d ≃ₗ[ℝ] MinkowskiModel d) :
    L ∈ LorentzGroup d ↔ ∀ v w, minkowskiForm σ d (L v) (L w) = minkowskiForm σ d v w := by
  change (∀ v w, pair (L v) (L w) = pair v w) ↔ _
  simp only [metric_eq]
  constructor
  · intro h v w
    rw [h]
  · intro h v w
    exact mul_left_cancel₀ σ.timeSign_ne_zero (h v w)

variable {d : ℕ}

namespace LorentzGroup

def toContinuousLinearEquiv (L : LorentzGroup d) : MinkowskiModel d ≃L[ℝ] MinkowskiModel d :=
  L.val.toContinuousLinearEquiv

theorem preserves_pair (L : LorentzGroup d) (v w : MinkowskiModel d) :
    pair (L.val v) (L.val w) = pair v w := L.property v w

theorem preserves_metric (L : LorentzGroup d) (σ : LorentzConvention)
    (v w : MinkowskiModel d) :
    minkowskiForm σ d (L.val v) (L.val w) = minkowskiForm σ d v w := by
  simp only [metric_eq, preserves_pair L]

@[simp] theorem preserves_interval (L : LorentzGroup d) (v : MinkowskiModel d) :
    intervalQuadratic (L.val v) = intervalQuadratic v := L.property v v

def toQuadraticIsometry (L : LorentzGroup d) :
    (intervalQuadratic (d := d)).IsometryEquiv (intervalQuadratic (d := d)) where
  toLinearEquiv := L.val
  map_app' := preserves_interval L

theorem timelike_iff (L : LorentzGroup d) (v : MinkowskiModel d) :
    Timelike (L.val v) ↔ Timelike v := by simp only [Timelike, preserves_interval]

theorem spacelike_iff (L : LorentzGroup d) (v : MinkowskiModel d) :
    Spacelike (L.val v) ↔ Spacelike v := by simp only [Spacelike, preserves_interval]

theorem lightlike_iff (L : LorentzGroup d) (v : MinkowskiModel d) :
    Lightlike (L.val v) ↔ Lightlike v := by simp only [Lightlike, preserves_interval, ne_eq, LinearEquiv.map_eq_zero_iff]

/-- Active covector transformation is pullback by the inverse. -/
theorem flat_natural (L : LorentzGroup d) (σ : LorentzConvention) (v w : MinkowskiModel d) :
    flat σ (L.val v) w = flat σ v (L.val.symm w) := by
  have h := preserves_metric L σ v (L.val.symm w)
  simpa using h

end LorentzGroup

/-- Proper transformations preserve spacetime orientation. -/
def properLorentzGroup (d : ℕ) : Subgroup (LorentzGroup d) :=
  (LinearEquiv.det.comp (LorentzGroup d).subtype).ker

/-- Time orientation is independent of spacetime orientation. -/
def orthochronousLorentzGroup (d : ℕ) : Subgroup (LorentzGroup d) where
  carrier := {L | ∀ v, FutureCausal (L.val v) ↔ FutureCausal v}
  one_mem' := by intro v; rfl
  mul_mem' := by intro L K hL hK v; exact (hL (K.val v)).trans (hK v)
  inv_mem' := by
    intro L hL v
    simpa using (hL (L.val.symm v)).symm

def properOrthochronousLorentzGroup (d : ℕ) : Subgroup (LorentzGroup d) :=
  properLorentzGroup d ⊓ orthochronousLorentzGroup d

end ProjectAInos.SmoothGeometry.Minkowski
