/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Tensor.CovariantDerivative
public import ProjectAinos.SmoothGeometry.Tensor.TrilinearTensoriality

/-! # Covariant differentiation of tangent-valued trilinear tensors

For a connection `∇` on the tangent bundle and a smooth section `R` of the bundle of
tangent-valued trilinear maps, the Leibniz correction

`(∇_u R)(X, Y)Z = ∇_u (R(X, Y)Z) − R(∇_u X, Y)Z − R(X, ∇_u Y)Z − R(X, Y)∇_u Z`

is tensorial in `X`, `Y` and `Z` on locally `C¹` fields, so it descends to a continuous
multilinear map on the tangent space at each point.

* `trilinearCovariantDerivative connection R x v w z u`: the value `(∇_u R)(v, w)z`; the
  direction comes last, as in `bilinearCovariantDerivative`.
* `trilinearCovariantDerivative_apply`: its value on locally `C¹` fields is the Leibniz
  correction.
-/

@[expose] public section
noncomputable section
open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.Tensor

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "TM" => TangentSpace I (M := M)

/-- The bundle of tangent-valued trilinear maps, as an iterated hom bundle. Its model carries
the norms of the hom spaces recursively; instance search does not find a norm on the threefold
space of continuous linear maps directly. -/
abbrev trilinearBundle : SmoothBundle I (M := M) :=
  SmoothBundle.hom I (SmoothBundle.tangent I)
    (SmoothBundle.hom I (SmoothBundle.tangent I)
      (SmoothBundle.hom I (SmoothBundle.tangent I) (SmoothBundle.tangent I)))

/-- Smoothness of a field of tangent-valued trilinear maps, as a section of `trilinearBundle`. -/
def IsSmoothTrilinear (R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, (trilinearBundle (I := I) (M := M)).Model)) ∞
    (fun x => TotalSpace.mk' (trilinearBundle (I := I) (M := M)).Model x (R x))

theorem IsSmoothTrilinear.mdifferentiableAt_apply
    {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x} (hR : IsSmoothTrilinear R)
    {X Y Z : ∀ x, TM x} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Z) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (fun y => R y (X y) (Y y) (Z y))) x :=
  ((((hR x).mdifferentiableAt (by simp)).clm_bundle_apply hX).clm_bundle_apply
    hY).clm_bundle_apply hZ

variable (connection : _root_.CovariantDerivative I E (TangentSpace I (M := M)))

/-- The Leibniz correction on vector fields, before descending to tangent vectors. -/
def trilinearDerivativeAux (R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    (X Y Z : ∀ x, TM x) (x : M) : TM x →L[ℝ] TM x :=
  connection.toFun (fun y => R y (X y) (Y y) (Z y)) x -
    (((R x).flip (Y x)).flip (Z x)).comp (connection.toFun X x) -
    ((R x (X x)).flip (Z x)).comp (connection.toFun Y x) -
    (R x (X x) (Y x)).comp (connection.toFun Z x)

omit [FiniteDimensional ℝ E] in
@[simp] theorem trilinearDerivativeAux_apply
    (R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x) (X Y Z : ∀ x, TM x) (x : M)
    (u : TM x) :
    trilinearDerivativeAux connection R X Y Z x u =
      connection (fun y => R y (X y) (Y y) (Z y)) x u - R x (connection X x u) (Y x) (Z x) -
        R x (X x) (connection Y x u) (Z x) - R x (X x) (Y x) (connection Z x u) := rfl

private theorem mdiff_of_one {X : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, (SmoothBundle.tangent I (M := M)).Model))
      ((1 : ℕ∞) : ℕ∞ω)
      (fun y => TotalSpace.mk' (SmoothBundle.tangent I (M := M)).Model y (X y)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x :=
  hX.mdifferentiableAt (by simp)

theorem trilinearDerivative_tensorial_left
    {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x} (hR : IsSmoothTrilinear R)
    {Y Z : ∀ x, TM x} {x : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Z) x) :
    ContMDiffTensorialAt (SmoothBundle.tangent I) 1
      (fun X => trilinearDerivativeAux connection R X Y Z x) x where
  smul {f X} hf hX := by
    have hf' : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
    have hX' := mdiff_of_one hX
    have hfun : (fun y => R y ((f • X) y) (Y y) (Z y)) =
        f • fun y => R y (X y) (Y y) (Z y) := by
      funext y
      simp
    ext u
    simp only [trilinearDerivativeAux_apply, smul_apply, hfun]
    rw [connection.isCovariantDerivativeOnUniv.leibniz
        (hR.mdifferentiableAt_apply hX' hY hZ) hf',
      connection.isCovariantDerivativeOnUniv.leibniz hX' hf']
    simp only [add_apply, smul_apply, smulRight_apply, map_add, map_smul, Pi.smul_apply']
    module
  add {X X'} hX hX' := by
    have hX₁ := mdiff_of_one hX
    have hX₂ := mdiff_of_one hX'
    have hfun : (fun y => R y ((X + X') y) (Y y) (Z y)) =
        (fun y => R y (X y) (Y y) (Z y)) + fun y => R y (X' y) (Y y) (Z y) := by
      funext y
      simp
    ext u
    simp only [trilinearDerivativeAux_apply, hfun, add_apply]
    rw [connection.isCovariantDerivativeOnUniv.add (hR.mdifferentiableAt_apply hX₁ hY hZ)
        (hR.mdifferentiableAt_apply hX₂ hY hZ),
      connection.isCovariantDerivativeOnUniv.add hX₁ hX₂]
    simp only [add_apply, map_add, Pi.add_apply]
    abel

theorem trilinearDerivative_tensorial_middle
    {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x} (hR : IsSmoothTrilinear R)
    {X Z : ∀ x, TM x}
    {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Z) x) :
    ContMDiffTensorialAt (SmoothBundle.tangent I) 1
      (fun Y => trilinearDerivativeAux connection R X Y Z x) x where
  smul {f Y} hf hY := by
    have hf' : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
    have hY' := mdiff_of_one hY
    have hfun : (fun y => R y (X y) ((f • Y) y) (Z y)) =
        f • fun y => R y (X y) (Y y) (Z y) := by
      funext y
      simp
    ext u
    simp only [trilinearDerivativeAux_apply, smul_apply, hfun]
    rw [connection.isCovariantDerivativeOnUniv.leibniz
        (hR.mdifferentiableAt_apply hX hY' hZ) hf',
      connection.isCovariantDerivativeOnUniv.leibniz hY' hf']
    simp only [add_apply, smul_apply, smulRight_apply, map_add, map_smul, Pi.smul_apply']
    module
  add {Y Y'} hY hY' := by
    have hY₁ := mdiff_of_one hY
    have hY₂ := mdiff_of_one hY'
    have hfun : (fun y => R y (X y) ((Y + Y') y) (Z y)) =
        (fun y => R y (X y) (Y y) (Z y)) + fun y => R y (X y) (Y' y) (Z y) := by
      funext y
      simp
    ext u
    simp only [trilinearDerivativeAux_apply, hfun, add_apply]
    rw [connection.isCovariantDerivativeOnUniv.add (hR.mdifferentiableAt_apply hX hY₁ hZ)
        (hR.mdifferentiableAt_apply hX hY₂ hZ),
      connection.isCovariantDerivativeOnUniv.add hY₁ hY₂]
    simp only [add_apply, map_add, Pi.add_apply]
    abel

theorem trilinearDerivative_tensorial_right
    {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x} (hR : IsSmoothTrilinear R)
    {X Y : ∀ x, TM x}
    {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x) :
    ContMDiffTensorialAt (SmoothBundle.tangent I) 1
      (fun Z => trilinearDerivativeAux connection R X Y Z x) x where
  smul {f Z} hf hZ := by
    have hf' : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
    have hZ' := mdiff_of_one hZ
    have hfun : (fun y => R y (X y) (Y y) ((f • Z) y)) =
        f • fun y => R y (X y) (Y y) (Z y) := by
      funext y
      simp
    ext u
    simp only [trilinearDerivativeAux_apply, smul_apply, hfun]
    rw [connection.isCovariantDerivativeOnUniv.leibniz
        (hR.mdifferentiableAt_apply hX hY hZ') hf',
      connection.isCovariantDerivativeOnUniv.leibniz hZ' hf']
    simp only [add_apply, smul_apply, smulRight_apply, map_add, map_smul, Pi.smul_apply']
    module
  add {Z Z'} hZ hZ' := by
    have hZ₁ := mdiff_of_one hZ
    have hZ₂ := mdiff_of_one hZ'
    have hfun : (fun y => R y (X y) (Y y) ((Z + Z') y)) =
        (fun y => R y (X y) (Y y) (Z y)) + fun y => R y (X y) (Y y) (Z' y) := by
      funext y
      simp
    ext u
    simp only [trilinearDerivativeAux_apply, hfun, add_apply]
    rw [connection.isCovariantDerivativeOnUniv.add (hR.mdifferentiableAt_apply hX hY hZ₁)
        (hR.mdifferentiableAt_apply hX hY hZ₂),
      connection.isCovariantDerivativeOnUniv.add hZ₁ hZ₂]
    simp only [add_apply, map_add, Pi.add_apply]
    abel

/-- The covariant derivative `(∇_u R)(v, w)z` of a tangent-valued trilinear tensor, linear in
the three tensor slots and in the direction `u`, which comes last. -/
def trilinearCovariantDerivative (R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    (hR : IsSmoothTrilinear R) (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x :=
  ContMDiffTensorialAt.mkHom₃ (A := SmoothBundle.tangent I) (B := SmoothBundle.tangent I)
    (C := SmoothBundle.tangent I) (n := 1)
    (fun X Y Z => trilinearDerivativeAux connection R X Y Z x) x
    (fun _ _ hY hZ => trilinearDerivative_tensorial_left connection hR
      (hY.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp)))
    (fun _ _ hX hZ => trilinearDerivative_tensorial_middle connection hR
      (hX.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp)))
    (fun _ _ hX hY => trilinearDerivative_tensorial_right connection hR
      (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp)))

/-- Evaluation on the canonical local extensions of the tensor arguments. -/
theorem trilinearCovariantDerivative_apply_eq_extend
    (R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x) (hR : IsSmoothTrilinear R)
    (x : M)
    (v w z u : TM x) :
    trilinearCovariantDerivative connection R hR x v w z u =
      trilinearDerivativeAux connection R (extend E v) (extend E w) (extend E z) x u := rfl

/-- On locally `C¹` fields the covariant derivative is the Leibniz correction. -/
theorem trilinearCovariantDerivative_apply
    {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x} (hR : IsSmoothTrilinear R)
    {X Y Z : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% Z) x) (u : TM x) :
    trilinearCovariantDerivative connection R hR x (X x) (Y x) (Z x) u =
      connection (fun y => R y (X y) (Y y) (Z y)) x u - R x (connection X x u) (Y x) (Z x) -
        R x (X x) (connection Y x u) (Z x) - R x (X x) (Y x) (connection Z x u) := by
  unfold trilinearCovariantDerivative
  rw [ContMDiffTensorialAt.mkHom₃_apply _ _ _ (by simpa using hX) (by simpa using hY)
    (by simpa using hZ), trilinearDerivativeAux_apply]

end ProjectAinos.SmoothGeometry.Tensor
