/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The Koszul construction is adapted from mathlib's
Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean
by Patrick Massot, Michael Rothgang and Heather Macbeth.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Connection

/-! # The Levi-Civita connection of a Lorentz metric

The Koszul expression is tensorial in its first and third arguments.
The inverse metric then constructs a native `CovariantDerivative` on the
actual tangent bundle, without a positive-definite metric or a global frame.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff

attribute [local fun_prop] MDifferentiable MDifferentiableAt
  MDifferentiable.add MDifferentiableAt.add
  mdifferentiableAt_fun_add_section MDifferentiableAt.fun_smul_section

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)
  {X Y Z : ∀ x : M, TangentSpace 𝓘(ℝ, MinkowskiModel d) x} {x : M}

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace I (M := M)

/-- Tensoriality of the Koszul expression in the direction field. -/
theorem tensorialAt_koszul_first
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x)
    (hZ : MDifferentiableAt I ((I).prod I) (T% Z) x) :
    TensorialAt I (MinkowskiModel d) (g.koszul · Y Z x) x where
  smul hf hX := by
    simp (disch := fun_prop) [koszul, mvfderiv_fun_mul,
      mlieBracket_smul_left, mlieBracket_smul_right,
      map_add, map_smul, g.symmetric]
    ring
  add hX₁ hX₂ := by
    simp (disch := fun_prop) [koszul, mlieBracket_add_right, mlieBracket_add_left,
      mvfderiv_fun_add, map_add]
    ring

/-- Tensoriality of the Koszul expression in its test field. -/
theorem tensorialAt_koszul_third
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x)
    (hX : MDifferentiableAt I ((I).prod I) (T% X) x) :
    TensorialAt I (MinkowskiModel d) (g.koszul X Y · x) x where
  smul hf hZ := by
    simp (disch := fun_prop) [koszul, mvfderiv_fun_mul,
      mlieBracket_smul_right, mlieBracket_smul_left,
      map_smul, map_add, g.symmetric]
    ring
  add hZ₁ hZ₂ := by
    simp (disch := fun_prop) [koszul, mlieBracket_add_right, mlieBracket_add_left,
      mvfderiv_fun_add, map_add]
    ring

/-- Raise the test covector in the tensorial Koszul expression. -/
def leviCivitaOfDifferentiableAt (hY : MDifferentiableAt I ((I).prod I) (T% Y) x) : TM x →L[ℝ] TM x :=
  (g.sharp x).toContinuousLinearMap ∘L
    TensorialAt.mkHom₂ (fun X Z => g.koszul X Y Z x) x
      (fun _Z hZ => g.tensorialAt_koszul_first hY hZ)
      (fun _X hX => g.tensorialAt_koszul_third hY hX)

theorem leviCivitaOfDifferentiableAt_pairing
    (hX : MDifferentiableAt I ((I).prod I) (T% X) x)
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x)
    (hZ : MDifferentiableAt I ((I).prod I) (T% Z) x) :
    g.form x (g.leviCivitaOfDifferentiableAt hY (X x)) (Z x) = g.koszul X Y Z x := by
  simp [leviCivitaOfDifferentiableAt, TensorialAt.mkHom₂_apply _ _ hX hZ]

open scoped Classical in
/-- The connection's action, taking zero on fields not differentiable at the point.
The connection axioms only constrain its action on differentiable sections. -/
def leviCivitaAction (Y : ∀ x : M, TM x) (x : M) : TM x →L[ℝ] TM x :=
  if hY : MDifferentiableAt I ((I).prod I) (T% Y) x then
    g.leviCivitaOfDifferentiableAt hY else 0

theorem leviCivitaAction_pairing
    (hX : MDifferentiableAt I ((I).prod I) (T% X) x)
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x)
    (hZ : MDifferentiableAt I ((I).prod I) (T% Z) x) :
    g.form x (g.leviCivitaAction Y x (X x)) (Z x) = g.koszul X Y Z x := by
  simpa [leviCivitaAction, dite_eq_left hY] using
    g.leviCivitaOfDifferentiableAt_pairing hX hY hZ

/-- The Koszul construction is additive in the differentiated field and obeys
the Leibniz rule, with the local differentiability required by mathlib. -/
theorem isCovariantDerivativeOn_leviCivitaAction :
    IsCovariantDerivativeOn (MinkowskiModel d) (g.leviCivitaAction (M := M)) where
  add {Y Y'} x hY hY' _ := by
    apply injective_eval_mdifferentiableAt_vectorField
    funext X hX
    apply g.injective_form_mdifferentiableAt
    funext Z hZ
    change g.form x (g.leviCivitaAction (Y + Y') x (X x)) (Z x) =
      g.form x (g.leviCivitaAction Y x (X x) + g.leviCivitaAction Y' x (X x)) (Z x)
    rw [g.leviCivitaAction_pairing hX (mdifferentiableAt_add_section hY hY') hZ]
    simp (disch := fun_prop) [leviCivitaAction_pairing, koszul, mvfderiv_fun_add,
      mlieBracket_add_left, mlieBracket_add_right, map_add]
    ring
  leibniz {Y f x} hY hf _ := by
    apply injective_eval_mdifferentiableAt_vectorField
    funext X hX
    apply g.injective_form_mdifferentiableAt
    funext Z hZ
    change g.form x (g.leviCivitaAction (f • Y) x (X x)) (Z x) =
      g.form x (f x • g.leviCivitaAction Y x (X x) +
        mvfderiv I f x (X x) • Y x) (Z x)
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
    rw [g.leviCivitaAction_pairing hX (hf.smul_section hY) hZ,
      g.leviCivitaAction_pairing hX hY hZ]
    simp (disch := fun_prop) [koszul, mvfderiv_fun_mul,
      mlieBracket_smul_left, mlieBracket_smul_right, map_add, map_smul, g.symmetric]
    ring

/-- The Levi-Civita connection on the actual tangent bundle of a Lorentz manifold.
Its action on fields not differentiable at the evaluation point is zero. -/
def leviCivita : CovariantDerivative I (MinkowskiModel d) TM where
  toFun := g.leviCivitaAction
  isCovariantDerivativeOnUniv := g.isCovariantDerivativeOn_leviCivitaAction

/-- The constructed connection satisfies the Koszul formula. -/
theorem leviCivita_pairing
    (hX : MDifferentiableAt I ((I).prod I) (T% X) x)
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x)
    (hZ : MDifferentiableAt I ((I).prod I) (T% Z) x) :
    g.form x (g.leviCivita Y x (X x)) (Z x) = g.koszul X Y Z x :=
  g.leviCivitaAction_pairing hX hY hZ

/-- Metric compatibility of the Koszul connection. -/
theorem leviCivita_metricCompatible : g.MetricCompatible g.leviCivita := by
  intro x v Y Z hY hZ
  have hX := mdifferentiableAt_extend I (MinkowskiModel d) v
  have e₁ := g.leviCivita_pairing hX hY hZ
  have e₂ := g.leviCivita_pairing hX hZ hY
  simp only [extend_apply_self, koszul] at e₁ e₂
  rw [g.symmetric x (Y x), e₁, e₂]
  simp only [g.symmetric, mlieBracket_swap (V := Z),
    mlieBracket_swap (V := Y) (W := extend (MinkowskiModel d) v), Pi.neg_apply, map_neg]
  ring

/-- The constructed connection is torsion-free. -/
theorem leviCivita_torsion : g.leviCivita.torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  apply g.injective_form_mdifferentiableAt
  funext Z hZ
  change g.form x (g.leviCivita Y x (X x) - g.leviCivita X x (Y x)) (Z x) =
    g.form x (mlieBracket I X Y x) (Z x)
  simp only [map_sub, sub_apply]
  rw [g.leviCivita_pairing hX hY hZ, g.leviCivita_pairing hY hX hZ]
  simp [koszul,
    mlieBracket_swap (V := Y) (W := X), mlieBracket_swap (V := Z) (W := X),
    mlieBracket_swap (V := Z) (W := Y), g.symmetric]
  ring

/-- Existence of a compatible, torsion-free connection for every smooth Lorentz metric. -/
theorem isLeviCivita_leviCivita : g.IsLeviCivita g.leviCivita :=
  ⟨g.leviCivita_metricCompatible, g.leviCivita_torsion⟩

/-- Any compatible, torsion-free connection agrees with the construction on
fields differentiable at the evaluation point. -/
theorem IsLeviCivita.eq_leviCivita
    {cov : CovariantDerivative I (MinkowskiModel d) TM} (h : g.IsLeviCivita cov)
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x) (v : TM x) :
    cov Y x v = g.leviCivita Y x v :=
  h.uniqueness g g.isLeviCivita_leviCivita hY v

/-- Reversing the Lorentz convention leaves the connection unchanged, including
its common zero extension to fields not differentiable at the point. -/
@[simp] theorem leviCivita_opposite : g.opposite.leviCivita = g.leviCivita := by
  classical
  apply CovariantDerivative.ext
  funext Y x
  by_cases hY : MDifferentiableAt I ((I).prod I) (T% Y) x
  · ext v
    exact ((g.isLeviCivita_leviCivita).opposite g).uniqueness
      g.opposite g.opposite.isLeviCivita_leviCivita hY v |>.symm
  · change g.opposite.leviCivitaAction Y x = g.leviCivitaAction Y x
    simp [leviCivitaAction, hY]

end ProjectAInos.SmoothGeometry.LorentzMetric
