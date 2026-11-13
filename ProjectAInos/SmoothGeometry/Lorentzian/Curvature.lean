/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Regularity
public import ProjectAInos.SmoothGeometry.Tensor.Tensoriality

/-! # Curvature of the Lorentz Levi-Civita connection

We use `R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.
The field formulas make their local differentiability assumptions explicit.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- Covariant differentiation of a vector field along a vector field. -/
def covariantField (X Y : ∀ x, TM x) (x : M) : TM x := g.leviCivita Y x (X x)

theorem contMDiffAt_covariantField {n : ℕ∞} {X Y : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) n (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) (n + 1) (T% Y) x) :
    ContMDiffAt I ((I).prod I) n (T% (g.covariantField X Y)) x :=
  (g.contMDiffAt_leviCivita hY).clm_bundle_apply hX

@[simp] theorem covariantField_add_left (X Y Z : ∀ x, TM x) :
    g.covariantField (X + Y) Z = g.covariantField X Z + g.covariantField Y Z := by
  funext x
  simp [covariantField]

@[simp] theorem covariantField_smul_left (f : M → ℝ) (X Y : ∀ x, TM x) :
    g.covariantField (f • X) Y = f • g.covariantField X Y := by
  funext x
  simp [covariantField]

theorem covariantField_add_right {X Y Z : ∀ x, TM x} {x : M}
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x)
    (hZ : MDifferentiableAt I ((I).prod I) (T% Z) x) :
    g.covariantField X (Y + Z) x = g.covariantField X Y x + g.covariantField X Z x := by
  simp only [covariantField, g.leviCivita.isCovariantDerivativeOnUniv.add hY hZ, add_apply]

theorem covariantField_smul_right {f : M → ℝ} {X Y : ∀ x, TM x} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x) :
    g.covariantField X (f • Y) x =
      f x • g.covariantField X Y x + mvfderiv I f x (X x) • Y x := by
  simp only [covariantField, g.leviCivita.isCovariantDerivativeOnUniv.leibniz hY hf,
    add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]

theorem covariantField_neg_right {X Y : ∀ x, TM x} {x : M}
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x) :
    g.covariantField X (-Y) x = -g.covariantField X Y x := by
  have h := g.covariantField_smul_right (X := X) (f := fun _ => -1) mdifferentiableAt_const hY
  have hn : (fun _ : M => (-1 : ℝ)) • Y = -Y := by funext y; simp
  rw [hn] at h
  simpa [mvfderiv_const] using h

theorem covariantField_sub_right {X Y Z : ∀ x, TM x} {x : M}
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x)
    (hZ : MDifferentiableAt I ((I).prod I) (T% Z) x) :
    g.covariantField X (Y - Z) x = g.covariantField X Y x - g.covariantField X Z x := by
  rw [sub_eq_add_neg, g.covariantField_add_right hY (mdifferentiableAt_neg_section hZ),
    g.covariantField_neg_right hZ, sub_eq_add_neg]

theorem covariantField_congr_right {X Y Z : ∀ x, TM x} {x : M}
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x)
    (hZ : MDifferentiableAt I ((I).prod I) (T% Z) x)
    (h : ∀ᶠ y in 𝓝 x, Y y = Z y) :
    g.covariantField X Y x = g.covariantField X Z x :=
  congrArg (fun L => L (X x))
    (g.leviCivita.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hY hZ Filter.univ_mem h)

theorem covariantField_commutator {X Y : ∀ x, TM x} {x : M}
    (hX : MDifferentiableAt I ((I).prod I) (T% X) x)
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x) :
    g.covariantField X Y x - g.covariantField Y X x = mlieBracket I X Y x :=
  (CovariantDerivative.torsion_eq_zero_iff g.leviCivita).mp g.leviCivita_torsion hX hY

private theorem eventually_mdiff {X : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) 1 (T% X) x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I ((I).prod I) (T% X) y :=
  ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp hX).mono
    fun _ h => h.mdifferentiableAt one_ne_zero

private theorem contMDiffAt_bracket_one {X Y : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x) :
    ContMDiffAt I ((I).prod I) 1 (T% (mlieBracket I X Y)) x := by
  let : IsManifold I (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using (inferInstance : IsManifold I 2 M)
  let : IsManifold I ((2 : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  exact hX.mlieBracket_vectorField (m := 1) (n := 2) hY (by norm_num)

/-- Differentiate the torsion-free identity using only local `C²` regularity. -/
theorem covariantField_commutator_derivative {X Y Z : ∀ x, TM x} {x : M}
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    g.covariantField X (g.covariantField Y Z) x -
      g.covariantField X (g.covariantField Z Y) x =
      g.covariantField X (mlieBracket I Y Z) x := by
  have hYZ := (g.contMDiffAt_covariantField (n := 1) (hY.of_le (by norm_num))
    (hZ.of_le (by norm_num))).mdifferentiableAt one_ne_zero
  have hZY := (g.contMDiffAt_covariantField (n := 1) (hZ.of_le (by norm_num))
    (hY.of_le (by norm_num))).mdifferentiableAt one_ne_zero
  have hb := (contMDiffAt_bracket_one hY hZ).mdifferentiableAt one_ne_zero
  rw [← g.covariantField_sub_right hYZ hZY]
  apply g.covariantField_congr_right (mdifferentiableAt_sub_section hYZ hZY) hb
  filter_upwards [eventually_mdiff (hY.of_le (by norm_num)),
    eventually_mdiff (hZ.of_le (by norm_num))] with y hy hz
  exact g.covariantField_commutator hy hz

/-- The curvature expression on vector fields, with the fixed GR 5.1 sign. -/
def curvatureField (X Y Z : ∀ x, TM x) (x : M) : TM x :=
  g.covariantField X (g.covariantField Y Z) x -
    g.covariantField Y (g.covariantField X Z) x -
    g.covariantField (mlieBracket I X Y) Z x

theorem curvatureField_swap (X Y Z : ∀ x, TM x) (x : M) :
    g.curvatureField X Y Z x = -g.curvatureField Y X Z x := by
  rw [curvatureField, curvatureField, mlieBracket_swap (V := Y) (W := X)]
  simp only [covariantField, Pi.neg_apply, map_neg]
  abel

@[simp] theorem curvatureField_self (X Z : ∀ x, TM x) (x : M) :
    g.curvatureField X X Z x = 0 := by
  simp [curvatureField, covariantField]

/-- The algebraic first Bianchi identity follows from torsion-freeness and
Jacobi, with `C²` assumptions on the three local input fields. -/
theorem curvatureField_first_bianchi {X Y Z : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    g.curvatureField X Y Z x + g.curvatureField Y Z X x + g.curvatureField Z X Y x = 0 := by
  let : IsManifold I (minSmoothness ℝ 3) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using (inferInstance : IsManifold I 3 M)
  have hbXY := (contMDiffAt_bracket_one hX hY).mdifferentiableAt one_ne_zero
  have hbYZ := (contMDiffAt_bracket_one hY hZ).mdifferentiableAt one_ne_zero
  have hbZX := (contMDiffAt_bracket_one hZ hX).mdifferentiableAt one_ne_zero
  have h₁ := g.covariantField_commutator_derivative (X := X) hY hZ
  have h₂ := g.covariantField_commutator_derivative (X := Y) hZ hX
  have h₃ := g.covariantField_commutator_derivative (X := Z) hX hY
  have ht₁ := g.covariantField_commutator (hX.mdifferentiableAt (by norm_num)) hbYZ
  have ht₂ := g.covariantField_commutator (hY.mdifferentiableAt (by norm_num)) hbZX
  have ht₃ := g.covariantField_commutator (hZ.mdifferentiableAt (by norm_num)) hbXY
  have hj := leibniz_identity_mlieBracket_apply (U := X) (V := Y) (W := Z) (x := x)
    (by simpa only [minSmoothness_of_isRCLikeNormedField] using hX)
    (by simpa only [minSmoothness_of_isRCLikeNormedField] using hY)
    (by simpa only [minSmoothness_of_isRCLikeNormedField] using hZ)
  rw [mlieBracket_swap (V := mlieBracket I X Y) (W := Z),
    mlieBracket_swap (V := X) (W := Z)] at hj
  have hn : mlieBracket I Y (-mlieBracket I Z X) x = -mlieBracket I Y (mlieBracket I Z X) x := by
    simpa using mlieBracket_const_smul_right (c := (-1 : ℝ)) hbZX (V := Y)
  rw [hn] at hj
  simp only [Pi.neg_apply] at hj
  calc
    _ = (g.covariantField X (g.covariantField Y Z) x -
          g.covariantField X (g.covariantField Z Y) x - g.covariantField (mlieBracket I Y Z) X x) +
        (g.covariantField Y (g.covariantField Z X) x -
          g.covariantField Y (g.covariantField X Z) x - g.covariantField (mlieBracket I Z X) Y x) +
        (g.covariantField Z (g.covariantField X Y) x -
          g.covariantField Z (g.covariantField Y X) x - g.covariantField (mlieBracket I X Y) Z x) := by
      simp only [curvatureField]
      abel
    _ = mlieBracket I X (mlieBracket I Y Z) x +
        mlieBracket I Y (mlieBracket I Z X) x + mlieBracket I Z (mlieBracket I X Y) x := by
      rw [h₁, h₂, h₃, ht₁, ht₂, ht₃]
    _ = 0 := by rw [hj]; abel

/-- Curvature is linear over `C²` scalar germs in its first vector argument. -/
theorem curvatureField_smul_left {f : M → ℝ} {X Y Z : ∀ x, TM x} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    g.curvatureField (f • X) Y Z x = f x • g.curvatureField X Y Z x := by
  have hXZ := (g.contMDiffAt_covariantField (n := 1) (hX.of_le (by norm_num))
    (hZ.of_le (by norm_num))).mdifferentiableAt one_ne_zero
  simp only [curvatureField, covariantField_smul_left, Pi.smul_apply']
  rw [g.covariantField_smul_right (hf.mdifferentiableAt (by norm_num)) hXZ]
  simp only [covariantField, mlieBracket_smul_left (hf.mdifferentiableAt (by norm_num))
    (hX.mdifferentiableAt (by norm_num)), map_add, map_smul]
  module

theorem curvatureField_add_left {X X' Y Z : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) x)
    (hX' : ContMDiffAt I ((I).prod I) 2 (T% X') x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    g.curvatureField (X + X') Y Z x = g.curvatureField X Y Z x + g.curvatureField X' Y Z x := by
  have hXZ := (g.contMDiffAt_covariantField (n := 1) (hX.of_le (by norm_num))
    (hZ.of_le (by norm_num))).mdifferentiableAt one_ne_zero
  have hX'Z := (g.contMDiffAt_covariantField (n := 1) (hX'.of_le (by norm_num))
    (hZ.of_le (by norm_num))).mdifferentiableAt one_ne_zero
  simp only [curvatureField, covariantField_add_left, Pi.add_apply]
  rw [g.covariantField_add_right hXZ hX'Z]
  simp only [covariantField, mlieBracket_add_left (hX.mdifferentiableAt (by norm_num))
    (hX'.mdifferentiableAt (by norm_num)), map_add]
  abel

theorem curvatureField_smul_middle {f : M → ℝ} {X Y Z : ∀ x, TM x} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    g.curvatureField X (f • Y) Z x = f x • g.curvatureField X Y Z x := by
  rw [g.curvatureField_swap X (f • Y), g.curvatureField_smul_left hf hY hZ,
    g.curvatureField_swap Y X, smul_neg, neg_neg]

theorem curvatureField_add_middle {X Y Y' Z : ∀ x, TM x} {x : M}
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x)
    (hY' : ContMDiffAt I ((I).prod I) 2 (T% Y') x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    g.curvatureField X (Y + Y') Z x = g.curvatureField X Y Z x + g.curvatureField X Y' Z x := by
  rw [g.curvatureField_swap X (Y + Y'), g.curvatureField_add_left hY hY' hZ,
    g.curvatureField_swap Y X, g.curvatureField_swap Y' X]
  abel

/-- The third-slot tensoriality is a consequence of the algebraic Bianchi
identity and tensoriality in the first two slots. -/
theorem curvatureField_smul_right {f : M → ℝ} {X Y Z : ∀ x, TM x} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    g.curvatureField X Y (f • Z) x = f x • g.curvatureField X Y Z x := by
  have h := g.curvatureField_first_bianchi hX hY (hf.smul_section hZ)
  rw [g.curvatureField_smul_middle hf hZ hX, g.curvatureField_smul_left hf hZ hY] at h
  apply add_right_cancel (b := f x • g.curvatureField Y Z X x + f x • g.curvatureField Z X Y x)
  calc
    g.curvatureField X Y (f • Z) x +
        (f x • g.curvatureField Y Z X x + f x • g.curvatureField Z X Y x) = 0 := by
      simpa only [add_assoc] using h
    _ = f x • g.curvatureField X Y Z x +
        (f x • g.curvatureField Y Z X x + f x • g.curvatureField Z X Y x) := by
      rw [← smul_add, ← smul_add, ← add_assoc, g.curvatureField_first_bianchi hX hY hZ, smul_zero]

theorem curvatureField_add_right {X Y Z Z' : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x)
    (hZ' : ContMDiffAt I ((I).prod I) 2 (T% Z') x) :
    g.curvatureField X Y (Z + Z') x = g.curvatureField X Y Z x + g.curvatureField X Y Z' x := by
  have h := g.curvatureField_first_bianchi hX hY (hZ.add_section hZ')
  rw [g.curvatureField_add_middle hZ hZ' hX, g.curvatureField_add_left hZ hZ' hY] at h
  have h₁ := g.curvatureField_first_bianchi hX hY hZ
  have h₂ := g.curvatureField_first_bianchi hX hY hZ'
  apply add_right_cancel (b :=
    (g.curvatureField Y Z X x + g.curvatureField Z X Y x) +
    (g.curvatureField Y Z' X x + g.curvatureField Z' X Y x))
  calc
    _ = g.curvatureField X Y (Z + Z') x +
        (g.curvatureField Y Z X x + g.curvatureField Y Z' X x) +
        (g.curvatureField Z X Y x + g.curvatureField Z' X Y x) := by abel
    _ = 0 := h
    _ = (g.curvatureField X Y Z x + g.curvatureField Y Z X x + g.curvatureField Z X Y x) +
        (g.curvatureField X Y Z' x + g.curvatureField Y Z' X x + g.curvatureField Z' X Y x) := by
      rw [h₁, h₂, zero_add]
    _ = _ := by abel

theorem curvatureField_tensorial_left {Y Z : ∀ x, TM x} {x : M}
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    Tensor.ContMDiffTensorialAt (Tensor.SmoothBundle.tangent I) 2
      (fun X => g.curvatureField X Y Z x) x where
  smul hf hX := g.curvatureField_smul_left (by simpa using hf) (by simpa using hX) hZ
  add hX hX' := g.curvatureField_add_left (by simpa using hX) (by simpa using hX') hZ

theorem curvatureField_tensorial_middle {X Z : ∀ x, TM x} {x : M}
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    Tensor.ContMDiffTensorialAt (Tensor.SmoothBundle.tangent I) 2
      (fun Y => g.curvatureField X Y Z x) x where
  smul hf hY := g.curvatureField_smul_middle (by simpa using hf) (by simpa using hY) hZ
  add hY hY' := g.curvatureField_add_middle (by simpa using hY) (by simpa using hY') hZ

theorem curvatureField_tensorial_right {X Y : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x) :
    Tensor.ContMDiffTensorialAt (Tensor.SmoothBundle.tangent I) 2
      (fun Z => g.curvatureField X Y Z x) x where
  smul hf hZ := g.curvatureField_smul_right (by simpa using hf) hX hY (by simpa using hZ)
  add hZ hZ' := g.curvatureField_add_right hX hY (by simpa using hZ) (by simpa using hZ')

/-- Curvature depends only on the three tangent vectors, not on their `C²`
extensions to vector fields near the evaluation point. -/
theorem curvatureField_pointwise {X X' Y Y' Z Z' : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) x)
    (hX' : ContMDiffAt I ((I).prod I) 2 (T% X') x)
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x)
    (hY' : ContMDiffAt I ((I).prod I) 2 (T% Y') x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x)
    (hZ' : ContMDiffAt I ((I).prod I) 2 (T% Z') x)
    (hXX' : X x = X' x) (hYY' : Y x = Y' x) (hZZ' : Z x = Z' x) :
    g.curvatureField X Y Z x = g.curvatureField X' Y' Z' x := by
  calc
    _ = g.curvatureField X' Y Z x :=
      (g.curvatureField_tensorial_left hZ).pointwise hX hX' hXX'
    _ = g.curvatureField X' Y' Z x :=
      (g.curvatureField_tensorial_middle hZ).pointwise hY hY' hYY'
    _ = g.curvatureField X' Y' Z' x :=
      (g.curvatureField_tensorial_right hX' hY').pointwise hZ hZ' hZZ'

/-- Curvature with its first two tangent arguments fixed. -/
def curvatureLast (x : M) (u v : TM x) : TM x →L[ℝ] TM x :=
  Tensor.ContMDiffTensorialAt.mkHom
    (B := Tensor.SmoothBundle.tangent I) (n := 2)
    (fun Z => g.curvatureField (extend E u) (extend E v) Z x) x
    (g.curvatureField_tensorial_right (contMDiffAt_extend I E u) (contMDiffAt_extend I E v))

/-- Curvature with its first tangent argument fixed. -/
def curvatureMiddle (x : M) (u : TM x) : TM x →L[ℝ] TM x →L[ℝ] TM x :=
  have : T2Space (TM x) := FiberBundle.t2Space E TM x
  have : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  LinearMap.toContinuousLinearMap {
    toFun v := curvatureLast g x u v
    map_add' v w := by
      ext z
      change g.curvatureField (extend E u) (extend E (v + w)) (extend E z) x =
        g.curvatureField (extend E u) (extend E v) (extend E z) x +
        g.curvatureField (extend E u) (extend E w) (extend E z) x
      have h := (g.curvatureField_tensorial_middle (X := extend E u)
        (contMDiffAt_extend I E z)).pointwise
        (contMDiffAt_extend I E (v + w))
        ((contMDiffAt_extend I E v).add_section (contMDiffAt_extend I E w)) (by simp)
      rw [h, g.curvatureField_add_middle (contMDiffAt_extend ..) (contMDiffAt_extend ..)
        (contMDiffAt_extend ..)]
    map_smul' a v := by
      ext z
      change g.curvatureField (extend E u) (extend E (a • v)) (extend E z) x =
        a • g.curvatureField (extend E u) (extend E v) (extend E z) x
      have h := (g.curvatureField_tensorial_middle (X := extend E u)
        (contMDiffAt_extend I E z)).pointwise
        (contMDiffAt_extend I E (a • v))
        (contMDiffAt_const (c := a) |>.smul_section (contMDiffAt_extend I E v)) (by simp)
      rw [h, g.curvatureField_smul_middle contMDiffAt_const (contMDiffAt_extend ..)
        (contMDiffAt_extend ..)] }

/-- The Riemann curvature, as a continuous trilinear map on the actual tangent
space. Its application to locally `C²` vector fields is the connection commutator. -/
def curvature (x : M) : TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x :=
  have : T2Space (TM x) := FiberBundle.t2Space E TM x
  have : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  LinearMap.toContinuousLinearMap {
    toFun u := curvatureMiddle g x u
    map_add' u v := by
      ext w z
      change g.curvatureField (extend E (u + v)) (extend E w) (extend E z) x =
        g.curvatureField (extend E u) (extend E w) (extend E z) x +
        g.curvatureField (extend E v) (extend E w) (extend E z) x
      have h := (g.curvatureField_tensorial_left (Y := extend E w)
        (contMDiffAt_extend I E z)).pointwise
        (contMDiffAt_extend I E (u + v))
        ((contMDiffAt_extend I E u).add_section (contMDiffAt_extend I E v)) (by simp)
      rw [h, g.curvatureField_add_left (contMDiffAt_extend ..) (contMDiffAt_extend ..)
        (contMDiffAt_extend ..)]
    map_smul' a u := by
      ext w z
      change g.curvatureField (extend E (a • u)) (extend E w) (extend E z) x =
        a • g.curvatureField (extend E u) (extend E w) (extend E z) x
      have h := (g.curvatureField_tensorial_left (Y := extend E w)
        (contMDiffAt_extend I E z)).pointwise
        (contMDiffAt_extend I E (a • u))
        (contMDiffAt_const (c := a) |>.smul_section (contMDiffAt_extend I E u)) (by simp)
      rw [h, g.curvatureField_smul_left contMDiffAt_const (contMDiffAt_extend ..)
        (contMDiffAt_extend ..)] }

theorem curvature_apply {X Y Z : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    g.curvature x (X x) (Y x) (Z x) = g.curvatureField X Y Z x := by
  change g.curvatureField (extend E (X x)) (extend E (Y x)) (extend E (Z x)) x = _
  exact g.curvatureField_pointwise (contMDiffAt_extend ..) hX
    (contMDiffAt_extend ..) hY (contMDiffAt_extend ..) hZ (by simp) (by simp) (by simp)

/-- Evaluation on canonical local extensions; the result is independent of
these extensions by `curvature_apply`. -/
theorem curvature_apply_eq_extend (x : M) (u v w : TM x) :
    g.curvature x u v w =
      g.curvatureField (extend E u) (extend E v) (extend E w) x := rfl

theorem curvature_swap (x : M) (u v w : TM x) :
    g.curvature x u v w = -g.curvature x v u w :=
  g.curvatureField_swap (extend E u) (extend E v) (extend E w) x

@[simp] theorem curvature_self (x : M) (u w : TM x) : g.curvature x u u w = 0 :=
  g.curvatureField_self (extend E u) (extend E w) x

/-- The algebraic first Bianchi identity on arbitrary tangent vectors. -/
theorem curvature_first_bianchi (x : M) (u v w : TM x) :
    g.curvature x u v w + g.curvature x v w u + g.curvature x w u v = 0 :=
  g.curvatureField_first_bianchi (contMDiffAt_extend ..) (contMDiffAt_extend ..)
    (contMDiffAt_extend ..)

/-- Reversing the metric sign leaves the covariant derivative unchanged. -/
@[simp] theorem covariantField_opposite (X Y : ∀ x, TM x) :
    g.opposite.covariantField X Y = g.covariantField X Y := by
  funext x
  simp only [covariantField, leviCivita_opposite]

/-- The curvature convention is independent of the overall Lorentz metric sign. -/
@[simp] theorem curvatureField_opposite (X Y Z : ∀ x, TM x) :
    g.opposite.curvatureField X Y Z = g.curvatureField X Y Z := by
  funext x
  simp only [curvatureField, covariantField_opposite]

@[simp] theorem curvature_opposite (x : M) : g.opposite.curvature x = g.curvature x := by
  ext u v w
  simp only [curvature_apply_eq_extend, curvatureField_opposite]

end ProjectAInos.SmoothGeometry.LorentzMetric
