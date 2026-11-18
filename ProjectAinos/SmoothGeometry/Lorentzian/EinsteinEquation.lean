/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Einstein

/-! # The Einstein equations on a Lorentz manifold

For a smooth Lorentz metric `g`, constants `κ` and `Λ` and a smooth covariant two-tensor `T`,
`g.SatisfiesEinstein κ Λ T` is the system `G + Λ g = κ T` with the Einstein tensor `G`. It is a
predicate: a Lorentz metric is not required to satisfy it.

* `SatisfiesEinstein.divergence_eq_zero`: for `κ ≠ 0` the source is conserved, `∇^a T_{ab} = 0`,
  by the contracted Bianchi identity and `∇g = 0` (Landau–Lifshitz, §95).
* `SatisfiesEinstein.contract`: the trace `(1 − n/2) R + n Λ = κ T^a{}_a` in dimension `n = d + 1`.
* `SatisfiesEinstein.ricci_eq`: away from dimension two, the trace-reversed form
  `Ric = κ (T − T^a{}_a g/(n − 2)) + 2Λ g/(n − 2)`; in four dimensions
  `Ric = κ (T − ½ T^a{}_a g) + Λ g`.
-/

@[expose] public section
noncomputable section

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

local instance (x : M) : T2Space (TM x) := FiberBundle.t2Space E TM x
local instance (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- The Einstein equations `G + Λ g = κ T` for a smooth covariant two-tensor `T`. -/
def SatisfiesEinstein (κ Λ : ℝ) (T : Tensor.SmoothBilinear («I» := I) (M := M)) : Prop :=
  ∀ x, g.einstein x + Λ • g.form x = κ • T x

variable {g} {κ Λ : ℝ} {T : Tensor.SmoothBilinear («I» := 𝓘(ℝ, MinkowskiModel d)) (M := M)}

theorem SatisfiesEinstein.apply (hT : g.SatisfiesEinstein κ Λ T) (hκ : κ ≠ 0) (x : M)
    (v w : TM x) : T x v w = κ⁻¹ * (g.einstein x v w + Λ * g.form x v w) := by
  have h := congrArg (fun B : TM x →L[ℝ] TM x →L[ℝ] ℝ => B v w) (hT x)
  simp only [add_apply, smul_apply, smul_eq_mul] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]

/-- The covariant derivative of the source is that of the Einstein tensor over `κ`. -/
theorem SatisfiesEinstein.bilinearCovariantDerivative_eq (hT : g.SatisfiesEinstein κ Λ T)
    (hκ : κ ≠ 0) (x : M) (v w u : TM x) :
    Tensor.bilinearCovariantDerivative g.leviCivita T x v w u =
      κ⁻¹ * Tensor.bilinearCovariantDerivative g.leviCivita g.einsteinBilinear x v w u := by
  have hV : MDifferentiableAt I ((I).prod I) (T% (extend E v)) x :=
    mdifferentiableAt_extend I E v
  have hW : MDifferentiableAt I ((I).prod I) (T% (extend E w)) x :=
    mdifferentiableAt_extend I E w
  have hG := g.einsteinBilinear.mdifferentiableAt_apply hV hW
  have hg := g.mdifferentiableAt_pairing hV hW
  have hΛg : MDifferentiableAt I 𝓘(ℝ)
      (fun y => Λ * g.form y (extend E v y) (extend E w y)) x :=
    mdifferentiableAt_const.mul hg
  have hsum : MDifferentiableAt I 𝓘(ℝ) (fun y => g.einsteinBilinear y (extend E v y)
      (extend E w y) + Λ * g.form y (extend E v y) (extend E w y)) x :=
    hG.add hΛg
  have hfun : (fun y => T y (extend E v y) (extend E w y)) =
      fun y => κ⁻¹ * (g.einsteinBilinear y (extend E v y) (extend E w y) +
        Λ * g.form y (extend E v y) (extend E w y)) := by
    funext y
    exact hT.apply hκ y _ _
  have hd : mvfderiv I (fun y => κ⁻¹ * (g.einsteinBilinear y (extend E v y) (extend E w y) +
      Λ * g.form y (extend E v y) (extend E w y))) x u =
      κ⁻¹ * (mvfderiv I (fun y => g.einsteinBilinear y (extend E v y) (extend E w y)) x u +
        Λ * mvfderiv I (fun y => g.form y (extend E v y) (extend E w y)) x u) := by
    rw [mvfderiv_fun_mul mdifferentiableAt_const hsum, mvfderiv_const, smul_zero, add_zero,
      mvfderiv_fun_add hG hΛg,
      mvfderiv_fun_mul mdifferentiableAt_const hg, mvfderiv_const, smul_zero, add_zero]
    simp only [smul_apply, add_apply, smul_eq_mul]
  simp only [Tensor.bilinearCovariantDerivative, TensorialAt.mkHom₂_apply_eq_extend,
    Tensor.bilinearDerivativeAux_apply]
  rw [hfun, hd, g.leviCivita_metricCompatible u hV hW, hT.apply hκ, hT.apply hκ]
  simp only [einsteinBilinear_apply, extend_apply_self]
  ring

/-- **The source of the Einstein equations is conserved**: `∇^a T_{ab} = 0`. -/
theorem SatisfiesEinstein.divergence_eq_zero (hT : g.SatisfiesEinstein κ Λ T) (hκ : κ ≠ 0)
    (x : M) : g.bilinearDivergenceCovector T x = 0 := by
  ext b
  have hflip : (Tensor.bilinearCovariantDerivative g.leviCivita T x).flip b =
      κ⁻¹ • (Tensor.bilinearCovariantDerivative g.leviCivita g.einsteinBilinear x).flip b := by
    ext a c
    simp only [flip_apply, smul_apply, smul_eq_mul, hT.bilinearCovariantDerivative_eq hκ]
  rw [bilinearDivergenceCovector_apply, hflip, g.contract_smul,
    ← bilinearDivergenceCovector_apply, einstein_divergence_eq_zero]
  simp

/-- The trace of the Einstein equations: `(1 − n/2) R + n Λ = κ T^a{}_a`. -/
theorem SatisfiesEinstein.contract (hT : g.SatisfiesEinstein κ Λ T) (x : M) :
    (1 - ((d : ℝ) + 1) / 2) * g.scalarCurvature x + ((d : ℝ) + 1) * Λ =
      κ * g.contract x (T x) := by
  have h := congrArg (g.contract x) (hT x)
  rw [g.contract_add, g.contract_smul, g.contract_smul, contract_einstein, contract_metric] at h
  rw [← h]
  ring

/-- **The trace-reversed Einstein equations.** Away from dimension two,
`Ric = κ (T − T^a{}_a g/(n − 2)) + 2Λ g/(n − 2)`. -/
theorem SatisfiesEinstein.ricci_eq (hT : g.SatisfiesEinstein κ Λ T) (hd : d ≠ 1) (x : M) :
    g.ricci x = κ • (T x - (g.contract x (T x) / ((d : ℝ) - 1)) • g.form x) +
      (2 * Λ / ((d : ℝ) - 1)) • g.form x := by
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by
    intro h'
    apply hd
    have : (d : ℝ) = 1 := by linarith
    exact_mod_cast this
  have htr := hT.contract x
  have hR : g.scalarCurvature x = 2 * (((d : ℝ) + 1) * Λ - κ * g.contract x (T x)) /
      ((d : ℝ) - 1) := by
    field_simp
    linear_combination (-2) * htr
  ext v w
  have h := congrArg (fun B : TM x →L[ℝ] TM x →L[ℝ] ℝ => B v w) (hT x)
  simp only [add_apply, smul_apply, smul_eq_mul, einstein_apply] at h
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  have hr : g.ricci x v w = κ * T x v w + g.scalarCurvature x / 2 * g.form x v w -
      Λ * g.form x v w := by linarith
  rw [hr, hR]
  field_simp
  ring

/-- In four dimensions, `Ric = κ (T − ½ T^a{}_a g) + Λ g`. -/
theorem SatisfiesEinstein.ricci_eq_four (hT : g.SatisfiesEinstein κ Λ T) (hd : d = 3) (x : M) :
    g.ricci x = κ • (T x - (g.contract x (T x) / 2) • g.form x) + Λ • g.form x := by
  have h := hT.ricci_eq (by omega) x
  have hd' : (d : ℝ) - 1 = 2 := by
    rw [hd]
    norm_num
  rw [h, hd', mul_div_cancel_left₀ Λ two_ne_zero]

end ProjectAinos.SmoothGeometry.LorentzMetric
