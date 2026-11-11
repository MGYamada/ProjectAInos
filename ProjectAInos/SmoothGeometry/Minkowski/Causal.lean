/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-! # Causal cones and affine event separation -/

@[expose] public section
noncomputable section
namespace ProjectAInos.SmoothGeometry.Minkowski

variable {d : ℕ}

def Timelike (v : MinkowskiModel d) : Prop := 0 < intervalQuadratic v
def Spacelike (v : MinkowskiModel d) : Prop := intervalQuadratic v < 0
def Lightlike (v : MinkowskiModel d) : Prop := v ≠ 0 ∧ intervalQuadratic v = 0
def Causal (v : MinkowskiModel d) : Prop := 0 ≤ intervalQuadratic v
/-- The closed future cone contains zero. -/
def FutureCausal (v : MinkowskiModel d) : Prop := ‖space v‖ ≤ time v
def FutureTimelike (v : MinkowskiModel d) : Prop := ‖space v‖ < time v

theorem timelike_convention (σ : LorentzConvention) (v : MinkowskiModel d) :
    Timelike v ↔ 0 < σ.timeSign * minkowskiForm σ d v v := by
  rw [intervalQuadratic_convention]
  rfl

theorem spacelike_convention (σ : LorentzConvention) (v : MinkowskiModel d) :
    Spacelike v ↔ σ.timeSign * minkowskiForm σ d v v < 0 := by
  rw [intervalQuadratic_convention]
  rfl

theorem lightlike_convention (σ : LorentzConvention) (v : MinkowskiModel d) :
    Lightlike v ↔ v ≠ 0 ∧ minkowskiForm σ d v v = 0 := by
  rw [Lightlike, ← intervalQuadratic_convention σ v]
  simp only [mul_eq_zero, σ.timeSign_ne_zero, false_or]

theorem futureCausal_iff (v : MinkowskiModel d) :
    FutureCausal v ↔ Causal v ∧ 0 ≤ time v := by
  simp only [FutureCausal, Causal, intervalQuadratic_coordinates]
  have hn := norm_nonneg (space v)
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨h, ht⟩; nlinarith

theorem futureTimelike_iff (v : MinkowskiModel d) :
    FutureTimelike v ↔ Timelike v ∧ 0 < time v := by
  simp only [FutureTimelike, Timelike, intervalQuadratic_coordinates]
  have hn := norm_nonneg (space v)
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨h, ht⟩; nlinarith

@[simp] theorem futureCausal_zero : FutureCausal (0 : MinkowskiModel d) := by
  simp [FutureCausal]

theorem FutureTimelike.futureCausal {v : MinkowskiModel d} (h : FutureTimelike v) :
    FutureCausal v := le_of_lt h

theorem FutureCausal.add {v w : MinkowskiModel d} (hv : FutureCausal v)
    (hw : FutureCausal w) : FutureCausal (v + w) := by
  simp only [FutureCausal, map_add] at *
  exact (norm_add_le _ _).trans (add_le_add hv hw)

theorem FutureCausal.smul {v : MinkowskiModel d} (hv : FutureCausal v)
    {a : ℝ} (ha : 0 ≤ a) : FutureCausal (a • v) := by
  simp only [FutureCausal, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
    smul_eq_mul] at *
  exact mul_le_mul_of_nonneg_left hv ha

theorem futureCausal_convex : Convex ℝ {v : MinkowskiModel d | FutureCausal v} := by
  intro v hv w hw a b ha hb _
  exact (hv.smul ha).add (hw.smul hb)

theorem eq_zero_of_futureCausal_neg {v : MinkowskiModel d}
    (hv : FutureCausal v) (hn : FutureCausal (-v)) : v = 0 := by
  simp only [FutureCausal, map_neg, norm_neg] at hv hn
  have ht : time v = 0 := by have := norm_nonneg (space v); linarith
  have hs : space v = 0 := norm_eq_zero.mp (by have := norm_nonneg (space v); linarith)
  rw [← vector_time_space v, ht, hs]
  ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem time_pos_of_futureCausal_ne_zero {v : MinkowskiModel d}
    (hv : FutureCausal v) (hne : v ≠ 0) : 0 < time v := by
  have ht := (futureCausal_iff v).mp hv |>.2
  rcases ht.eq_or_lt with h | h
  · exfalso; apply hne
    apply eq_zero_of_futureCausal_neg hv
    change ‖space (-v)‖ ≤ time (-v)
    rw [map_neg, map_neg, norm_neg, ← h, neg_zero]
    exact hv.trans h.symm.le
  · exact h

section Affine
variable {P : Type*} [AddTorsor (MinkowskiModel d) P]

def intervalSq (σ : LorentzConvention) (p q : P) : ℝ :=
  minkowskiForm σ d (q -ᵥ p) (q -ᵥ p)

def CausallyPrecedes (p q : P) : Prop := FutureCausal (q -ᵥ p)

@[refl] theorem causallyPrecedes_refl (p : P) : CausallyPrecedes p p := by
  simp [CausallyPrecedes]

@[trans] theorem causallyPrecedes_trans {p q r : P}
    (hpq : CausallyPrecedes p q) (hqr : CausallyPrecedes q r) : CausallyPrecedes p r := by
  have h := hqr.add hpq
  simpa [CausallyPrecedes, vsub_add_vsub_cancel] using h

theorem causallyPrecedes_antisymm {p q : P}
    (hpq : CausallyPrecedes p q) (hqp : CausallyPrecedes q p) : p = q := by
  have h : q -ᵥ p = (0 : MinkowskiModel d) :=
    eq_zero_of_futureCausal_neg hpq (by simpa [CausallyPrecedes, neg_vsub_eq_vsub_rev] using hqp)
  exact (vsub_eq_zero_iff_eq.mp h).symm

end Affine
end ProjectAInos.SmoothGeometry.Minkowski
