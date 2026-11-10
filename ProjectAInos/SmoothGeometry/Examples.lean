/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.AffineScheme

/-! # Affine spaces and the empty C∞ scheme -/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra CategoryTheory

/-- The affine C∞ space represented by smooth functions on ℝⁿ. -/
def affineSpace (n : ℕ) : Scheme := Scheme.specObj (SmoothRingCat.of (SmoothOperation n))

theorem affineSpace_isAffine (n : ℕ) : IsAffine (affineSpace n) := isAffine_spec _

/-- The real points of the free C∞-ring are exactly coordinate tuples.
This is a bijection of points; the manifold comparison is a separate stage. -/
def affineSpacePoints (n : ℕ) : RealSpectrum (SmoothOperation n) ≃ (Fin n → ℝ) where
  toFun x i := x (SmoothOperation.proj i)
  invFun x := SmoothOperation.eval x
  left_inv x := by
    apply SmoothOperation.hom_ext
    intro i
    rfl
  right_inv _ := rfl

/-- The zero-dimensional affine space has exactly one real point. -/
instance : Unique (RealSpectrum (SmoothOperation 0)) :=
  (affineSpacePoints 0).unique

/-- The empty product is the zero C∞-ring. Its spectrum supplies the empty scheme. -/
def emptyScheme : Scheme := Scheme.specObj (SmoothRingCat.of (Fin 0 → ℝ))

instance emptyScheme_isEmpty : IsEmpty emptyScheme := by
  refine ⟨fun x => ?_⟩
  change RealSpectrum (Fin 0 → ℝ) at x
  have h : (0 : Fin 0 → ℝ) = 1 := Subsingleton.elim _ _
  have heq := congrArg x.hom h
  exact zero_ne_one ((x.hom.map_zero).symm.trans (heq.trans x.hom.map_one))

theorem emptyScheme_isAffine : IsAffine emptyScheme := isAffine_spec _

/-- Coordinate pullback agrees with the map of real points of the spectrum. -/
theorem affineSpacePoints_comap {n m : ℕ} (g : Fin n → SmoothOperation m)
    (x : Fin m → ℝ) :
    affineSpacePoints n (RealSpectrum.comap (SmoothOperation.pullback g)
      ((affineSpacePoints m).symm x)) = fun i => g i x := rfl

end ProjectAInos.SmoothGeometry
