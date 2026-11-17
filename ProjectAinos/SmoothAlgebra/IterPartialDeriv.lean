/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.PartialDerivative
public import Mathlib.Data.Multiset.Basic

/-!
# Iterated partial derivatives of a smooth function

The partial derivatives of a smooth function on `ℝⁿ` commute, so the iterated partial derivative
`∂^K f` is defined for a multi-index `K`, a multiset of co-ordinates
(`SmoothOperation.iterPartialDeriv`).
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SmoothAlgebra.SmoothOperation

variable {n : ℕ}

instance : LeftCommutative fun (i : Fin n) (f : SmoothOperation n) => partialDeriv i f :=
  ⟨fun i j f => partialDeriv_comm i j f⟩

/-- The iterated partial derivative `∂^K f` of a smooth function, for a multi-index `K`. -/
def iterPartialDeriv (K : Multiset (Fin n)) (f : SmoothOperation n) : SmoothOperation n :=
  Multiset.foldr (fun i g => partialDeriv i g) f K

@[simp] theorem iterPartialDeriv_zero (f : SmoothOperation n) : iterPartialDeriv 0 f = f := rfl

theorem iterPartialDeriv_cons (i : Fin n) (K : Multiset (Fin n)) (f : SmoothOperation n) :
    iterPartialDeriv (i ::ₘ K) f = partialDeriv i (iterPartialDeriv K f) :=
  Multiset.foldr_cons _ _ _ _

end ProjectAinos.SmoothAlgebra.SmoothOperation
