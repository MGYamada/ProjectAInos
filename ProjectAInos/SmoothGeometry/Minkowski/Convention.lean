/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic

/-! # Explicit Lorentz metric conventions -/

@[expose] public section

namespace ProjectAInos.SmoothGeometry

/-- The sign of a unit time vector. Neither convention is an implicit default. -/
inductive LorentzConvention
  | timePositive
  | timeNegative
  deriving DecidableEq

namespace LorentzConvention

def timeSign : LorentzConvention → ℝ
  | .timePositive => 1
  | .timeNegative => -1

def opposite : LorentzConvention → LorentzConvention
  | .timePositive => .timeNegative
  | .timeNegative => .timePositive

def negativeIndex (σ : LorentzConvention) (d : ℕ) : ℕ :=
  match σ with
  | .timePositive => d
  | .timeNegative => 1

@[simp] theorem timeSign_timePositive : timeSign .timePositive = 1 := rfl
@[simp] theorem timeSign_timeNegative : timeSign .timeNegative = -1 := rfl
@[simp] theorem opposite_opposite (σ : LorentzConvention) : σ.opposite.opposite = σ := by
  cases σ <;> rfl
@[simp] theorem timeSign_opposite (σ : LorentzConvention) :
    σ.opposite.timeSign = -σ.timeSign := by cases σ <;> simp [opposite, timeSign]
@[simp] theorem timeSign_mul_self (σ : LorentzConvention) :
    σ.timeSign * σ.timeSign = 1 := by cases σ <;> simp [timeSign]
@[simp] theorem timeSign_ne_zero (σ : LorentzConvention) : σ.timeSign ≠ 0 := by
  cases σ <;> simp [timeSign]

end LorentzConvention
end ProjectAInos.SmoothGeometry
