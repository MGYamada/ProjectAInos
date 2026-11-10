module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Fin.VecNotation

/-!
# Finite smooth operations

Operations are actual bundled smooth functions on real coordinate spaces, including
the zero-dimensional space. The regularity is `∞`, not the analytic regularity `ω`.
Substitution is composition with a finite tuple of smooth functions.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace ProjectAInos.Variational.SmoothAlgebra

/-- An `n`-ary smooth operation, with Mathlib's pointwise real algebra structure. -/
abbrev SmoothOperation (n : ℕ) := C^∞⟮𝓘(ℝ, Fin n → ℝ), (Fin n → ℝ); ℝ⟯

namespace SmoothOperation

variable {n m k : ℕ}

/-- Bundle a function with its ordinary smoothness certificate. -/
def ofContDiff (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) : SmoothOperation n :=
  ⟨f, hf.contMDiff⟩

@[simp] theorem ofContDiff_apply (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : Fin n → ℝ) : ofContDiff f hf x = f x := rfl

/-- A coordinate projection. There are no projections of arity zero. -/
def proj (i : Fin n) : SmoothOperation n :=
  ofContDiff (fun x => x i) (contDiff_apply ℝ (fun _ => ℝ) i)

/-- A constant operation of any arity, in particular a nullary constant. -/
def const (n : ℕ) (r : ℝ) : SmoothOperation n := ContMDiffMap.const r

/-- Substitute `n` operations of arity `m` into an operation of arity `n`. -/
def comp (f : SmoothOperation n) (g : Fin n → SmoothOperation m) : SmoothOperation m :=
  ofContDiff (fun x => f (fun i => g i x))
    (f.contMDiff.contDiff.comp (contDiff_pi.mpr fun i => (g i).contMDiff.contDiff))

@[simp] theorem proj_apply (i : Fin n) (x : Fin n → ℝ) : proj i x = x i := rfl
@[simp] theorem const_apply (r : ℝ) (x : Fin n → ℝ) : const n r x = r := rfl
@[simp] theorem comp_apply (f : SmoothOperation n) (g : Fin n → SmoothOperation m)
    (x : Fin m → ℝ) : comp f g x = f (fun i => g i x) := rfl

@[ext] theorem ext {f g : SmoothOperation n} (h : ∀ x, f x = g x) : f = g :=
  ContMDiffMap.ext h

@[simp] theorem proj_comp (i : Fin n) (g : Fin n → SmoothOperation m) :
    comp (proj i) g = g i := rfl

@[simp] theorem comp_proj (f : SmoothOperation n) : comp f proj = f := rfl

@[simp] theorem const_comp (r : ℝ) (g : Fin n → SmoothOperation m) :
    comp (const n r) g = const m r := rfl

theorem comp_assoc (f : SmoothOperation n) (g : Fin n → SmoothOperation m)
    (h : Fin m → SmoothOperation k) :
    comp (comp f g) h = comp f (fun i => comp (g i) h) := rfl

/-- Binary addition as a smooth operation. -/
def addition : SmoothOperation 2 := proj 0 + proj 1
/-- Binary multiplication as a smooth operation. -/
def multiplication : SmoothOperation 2 := proj 0 * proj 1
/-- Unary negation as a smooth operation. -/
def negation : SmoothOperation 1 := -proj 0
/-- Binary subtraction as a smooth operation. -/
def subtraction : SmoothOperation 2 := proj 0 - proj 1
/-- Unary multiplication by a real constant. -/
def scaling (r : ℝ) : SmoothOperation 1 := r • proj 0
/-- A nonpolynomial operation used to exercise the full smooth structure. -/
def exponential : SmoothOperation 1 :=
  ofContDiff (fun x => Real.exp (x 0))
    (Real.contDiff_exp.comp (contDiff_apply ℝ (fun _ => ℝ) 0))

@[simp] theorem addition_apply (x : Fin 2 → ℝ) : addition x = x 0 + x 1 := rfl
@[simp] theorem multiplication_apply (x : Fin 2 → ℝ) : multiplication x = x 0 * x 1 := rfl
@[simp] theorem negation_apply (x : Fin 1 → ℝ) : negation x = -x 0 := rfl
@[simp] theorem subtraction_apply (x : Fin 2 → ℝ) : subtraction x = x 0 - x 1 := rfl
@[simp] theorem scaling_apply (r : ℝ) (x : Fin 1 → ℝ) : scaling r x = r * x 0 := rfl
@[simp] theorem exponential_apply (x : Fin 1 → ℝ) : exponential x = Real.exp (x 0) := rfl

@[simp] theorem addition_comp (f g : SmoothOperation n) : comp addition ![f, g] = f + g := by
  ext x
  simp

@[simp] theorem multiplication_comp (f g : SmoothOperation n) :
    comp multiplication ![f, g] = f * g := by
  ext x
  simp

/-- The usual exponential identity as an equality of smooth operations. -/
theorem exponential_addition :
    comp exponential ![addition] =
      comp multiplication ![comp exponential ![proj 0], comp exponential ![proj 1]] := by
  ext x
  simp [Real.exp_add]

end SmoothOperation
end ProjectAInos.Variational.SmoothAlgebra
