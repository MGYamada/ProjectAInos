module

public import ProjectAInos.Variational.SmoothAlgebra.Hom

/-!
# Real and smooth-function C-infinity rings

The real model interprets operations by evaluation. The model `C∞(ℝⁿ)` uses
pointwise substitution and retains Mathlib's existing real algebra instance.
It is free on its `n` coordinate functions, including the empty generating
family when `n = 0`. Evaluation and pullback are smooth-ring morphisms.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Variational.SmoothAlgebra

open SmoothRing

/-- The usual real algebra with its usual smooth operations. -/
instance instSmoothRingReal : SmoothRing ℝ where
  op f a := f a
  op_proj _ _ := rfl
  op_comp _ _ _ := rfl
  op_nullary _ _ := rfl
  op_addition _ := rfl
  op_multiplication _ := rfl

/-- Smooth functions with pointwise operations, in any finite dimension. -/
instance instSmoothRingOperation (m : ℕ) : SmoothRing (SmoothOperation m) where
  op := SmoothOperation.comp
  op_proj _ _ := rfl
  op_comp _ _ _ := rfl
  op_nullary _ _ := rfl
  op_addition _ := rfl
  op_multiplication _ := rfl

@[simp] theorem real_op {n : ℕ} (f : SmoothOperation n) (a : Fin n → ℝ) :
    op f a = f a := rfl

@[simp] theorem function_op {n m : ℕ} (f : SmoothOperation n)
    (g : Fin n → SmoothOperation m) : op f g = SmoothOperation.comp f g := rfl

@[simp] theorem real_exp (a : ℝ) : SmoothRing.exp a = Real.exp a := rfl

namespace SmoothOperation

variable {n m k : ℕ} {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]

/-- Interpret functions on `ℝⁿ` at a tuple of elements of any C-infinity ring. -/
def lift (a : Fin n → A) : SmoothRingHom (SmoothOperation n) A where
  toFun f := op f a
  map_op' f g := op_comp f g a

@[simp] theorem lift_apply (a : Fin n → A) (f : SmoothOperation n) :
    lift a f = op f a := rfl

@[simp] theorem lift_proj (a : Fin n → A) (i : Fin n) : lift a (proj i) = a i := op_proj i a

/-- Every morphism out of smooth functions is determined by coordinate images. -/
theorem hom_apply (h : SmoothRingHom (SmoothOperation n) A) (f : SmoothOperation n) :
    h f = op f (fun i => h (proj i)) := by
  simpa using h.map_op f proj

/-- Equality on coordinate functions suffices for equality of morphisms. -/
theorem hom_ext {h₁ h₂ : SmoothRingHom (SmoothOperation n) A}
    (h : ∀ i, h₁ (proj i) = h₂ (proj i)) : h₁ = h₂ := by
  ext f
  rw [hom_apply h₁, hom_apply h₂]
  congr 1
  funext i
  exact h i

/-- Uniqueness in the free C-infinity ring's universal property. -/
theorem lift_unique (a : Fin n → A) (h : SmoothRingHom (SmoothOperation n) A)
    (ha : ∀ i, h (proj i) = a i) : h = lift a := by
  apply hom_ext
  intro i
  rw [lift_proj, ha]

/-- `C∞(ℝⁿ)` is free on the coordinate projections, also for `n = 0`. -/
theorem existsUnique_lift (a : Fin n → A) :
    ∃! h : SmoothRingHom (SmoothOperation n) A, ∀ i, h (proj i) = a i :=
  ⟨lift a, lift_proj a, fun h ha => lift_unique a h ha⟩

/-- Evaluation at a real point preserves every smooth operation. -/
def eval (x : Fin n → ℝ) : SmoothRingHom (SmoothOperation n) ℝ := lift x

@[simp] theorem eval_apply (x : Fin n → ℝ) (f : SmoothOperation n) : eval x f = f x := rfl

/-- Pullback along a smooth map represented by its component functions. -/
def pullback (g : Fin n → SmoothOperation m) :
    SmoothRingHom (SmoothOperation n) (SmoothOperation m) := lift g

@[simp] theorem pullback_apply (g : Fin n → SmoothOperation m) (f : SmoothOperation n) :
    pullback g f = comp f g := rfl

@[simp] theorem pullback_proj (g : Fin n → SmoothOperation m) (i : Fin n) :
    pullback g (proj i) = g i := rfl

@[simp] theorem pullback_id : pullback (proj : Fin n → SmoothOperation n) =
    SmoothRingHom.id (SmoothOperation n) := rfl

/-- Pullback reverses composition of the underlying smooth maps. -/
theorem pullback_comp (g : Fin n → SmoothOperation m) (h : Fin m → SmoothOperation k) :
    (pullback h).comp (pullback g) = pullback (fun i => comp (g i) h) := rfl

/-- Evaluation after pullback is evaluation at the image point. -/
theorem eval_comp_pullback (g : Fin n → SmoothOperation m) (x : Fin m → ℝ) :
    (eval x).comp (pullback g) = eval (fun i => g i x) := rfl

/-- In dimension zero every operation is its value at the unique point. -/
theorem nullary_eq_const (f : SmoothOperation 0) : f = const 0 (f Fin.elim0) := by
  ext x
  exact congrArg f (Subsingleton.elim x Fin.elim0)

/-- One-dimensional nonlinear evaluation, beyond polynomial operations. -/
theorem eval_exp_square (t : ℝ) :
    eval ![t] (comp exponential ![proj 0 * proj 0]) = Real.exp (t * t) := rfl

/-- A two-variable operation pulled back to four variables with mixed coordinates. -/
theorem eval_four_dimensional (x : Fin 4 → ℝ) :
    eval x (pullback ![proj 0 * proj 1, proj 2 * proj 3]
      (comp exponential ![addition])) = Real.exp (x 0 * x 1 + x 2 * x 3) := rfl

end SmoothOperation
end ProjectAInos.Variational.SmoothAlgebra
