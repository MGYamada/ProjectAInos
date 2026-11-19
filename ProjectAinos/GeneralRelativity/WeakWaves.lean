/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Linearized
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Weak gravitational waves

Landau–Lifshitz, §107, in four dimensions with the signature `(−+++)`
(`LorentzConvention.timeNegative`), the co-ordinates `x = (x⁰, x¹, x², x³)` and `c = 1`. The
linearized Einstein operator about the Minkowski coefficients `η` is
`SmoothGeometry/Lorentzian/Linearized.lean`; `η + ε h` is an actual family of Lorentz metrics for
bounded `h` (`CoordinateMetric.linearMetricFamily`).

* `planeWave e k x = e cos(k·x)` with `k·x = Σ_a k_a x^a` (`phase`), for a constant amplitude `e`
  and a covector `k`. Its second derivatives are `∂_a ∂_b h = −k_a k_b e cos(k·x)`
  (`secondPartial_planeWave`), so `□h = −(η^{aa} k_a²) e cos(k·x)` (`flatBox_planeWave`) and
  `□h = 0` for a null covector (`IsNull`, `flatBox_planeWave_of_isNull`).
* `isHarmonicGauge_planeWave_iff`: the wave is in harmonic gauge if and only if
  `Σ_a η^{aa} k_a ē_{ab} = 0`, with `ē` the trace reverse of `e`.
* `linearizedRicci_planeWave`, `linearizedEinstein_planeWave`: for a null `k` and a harmonic
  amplitude, `δR = δG = 0`: a linearized vacuum solution. `hasDerivAt_ricci_planeWave`: for a
  symmetric amplitude this is the derivative at `ε = 0` of the native Ricci tensor of the Lorentz
  metrics `η + ε h` on the whole space-time.
* `lieOf_gaugeVector`, `linearizedRicci_planeWave_add_gauge`: the field `ξ_j = ζ_j sin(k·x)` adds
  `k ⊗ ζ + ζ ⊗ k` to the amplitude, and the linearized Ricci tensor does not change.

**Polarizations.** The symmetric matrices are the submodule `symmetricMatrices` of
`Matrix (Fin 4) (Fin 4) ℝ`, of dimension `10` (`finrank_symmetricMatrices`, through the entries
`e_{ij}` with `i ≤ j`). For a covector `k`:

* `polarizationSpace k`: the symmetric amplitudes with `Σ_a η^{aa} k_a ē_{ab} = 0`, the kernel of
  `harmonicMap k` on the symmetric matrices;
* `gaugeSpace k`: the range of `gaugeMap k : ζ ↦ k ⊗ ζ + ζ ⊗ k`, `ζ` a covector.

For `k ≠ 0`, `harmonicMap k` maps the symmetric matrices onto `ℝ⁴`, so
`finrank_polarizationSpace = 6`, and `gaugeMap k` is injective, so `finrank_gaugeSpace = 4`. For a
null `k`, `gaugeSpace_le_polarizationSpace`, and `finrank_polarizationQuotient`:
`polarizationSpace k ⧸ gaugeSpace k` has dimension `2`, the two polarizations. For the wave along
`x³`, `k = (−ν, 0, 0, ν)` (`axialCovector`), the transverse traceless amplitudes `e₊` (`e₁₁ = −e₂₂
= 1`) and `e×` (`e₁₂ = e₂₁ = 1`) are polarizations (`plusPolarization_mem`,
`crossPolarization_mem`) whose classes are a basis of the quotient (`polarizationBasis`), and the
waves `e₊ cos(ν(x³ − x⁰))` solve the linearized vacuum equations
(`linearizedRicci_plusWave`).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace Module
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.WeakWaves

open SmoothGeometry CoordinateMetric
open LorentzMetric (chartField)

/-! ### Signs -/

/-- The time sign `η₀₀ = −1`. -/
@[simp] theorem lorentzSign_zero : lorentzSign (d := 3) .timeNegative 0 = -1 := by
  simp [lorentzSign]

/-- The space sign `η₁₁ = 1`. -/
@[simp] theorem lorentzSign_one : lorentzSign (d := 3) .timeNegative 1 = 1 := by simp [lorentzSign]

/-- The space sign `η₂₂ = 1`. -/
@[simp] theorem lorentzSign_two : lorentzSign (d := 3) .timeNegative 2 = 1 := by simp [lorentzSign]

/-- The space sign `η₃₃ = 1`. -/
@[simp] theorem lorentzSign_three : lorentzSign (d := 3) .timeNegative 3 = 1 := by
  simp [lorentzSign]

/-! ### The phase and the plane wave -/

/-- The phase `k·x = Σ_a k_a x^a` of the covector `k`. -/
def phase (k : Fin 4 → ℝ) (x : MinkowskiModel 3) : ℝ := ∑ a, k a * x a

/-- The phase as a continuous linear map. -/
def phaseCLM (k : Fin 4 → ℝ) : MinkowskiModel 3 →L[ℝ] ℝ :=
  ∑ a, k a • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) a

/-- The linear map evaluates to the phase. -/
theorem phaseCLM_apply (k : Fin 4 → ℝ) (x : MinkowskiModel 3) : phaseCLM k x = phase k x := by
  simp [phaseCLM, phase]

/-- The phase is the linear map `phaseCLM k`. -/
theorem phase_eq (k : Fin 4 → ℝ) : phase k = phaseCLM k :=
  funext fun x => (phaseCLM_apply k x).symm

/-- The phase of a co-ordinate vector is a component: `k·e_b = k_b`. -/
@[simp] theorem phase_single (k : Fin 4 → ℝ) (b : Fin 4) : phase k (Pi.single b 1) = k b := by
  simp [phase, Pi.single_apply]

/-- The phase is smooth. -/
theorem contDiff_phase (k : Fin 4 → ℝ) : ContDiff ℝ ∞ (phase k) := by
  rw [phase_eq]
  exact (phaseCLM k).contDiff

/-- The derivative `∂_v cos(k·x) = −sin(k·x) (k·v)`. -/
theorem fderiv_cos_phase (k : Fin 4 → ℝ) (x v : MinkowskiModel 3) :
    fderiv ℝ (fun z => Real.cos (phase k z)) x v = -Real.sin (phase k x) * phase k v := by
  have hp : HasFDerivAt (phase k) (phaseCLM k) x := by
    rw [phase_eq]
    exact (phaseCLM k).hasFDerivAt
  have h : HasFDerivAt (fun z => Real.cos (phase k z)) (-Real.sin (phase k x) • phaseCLM k) x :=
    (Real.hasDerivAt_cos (phase k x)).comp_hasFDerivAt x hp
  rw [h.fderiv, _root_.smul_apply, smul_eq_mul, phaseCLM_apply]

/-- The derivative `∂_v sin(k·x) = cos(k·x) (k·v)`. -/
theorem fderiv_sin_phase (k : Fin 4 → ℝ) (x v : MinkowskiModel 3) :
    fderiv ℝ (fun z => Real.sin (phase k z)) x v = Real.cos (phase k x) * phase k v := by
  have hp : HasFDerivAt (phase k) (phaseCLM k) x := by
    rw [phase_eq]
    exact (phaseCLM k).hasFDerivAt
  have h : HasFDerivAt (fun z => Real.sin (phase k z)) (Real.cos (phase k x) • phaseCLM k) x :=
    (Real.hasDerivAt_sin (phase k x)).comp_hasFDerivAt x hp
  rw [h.fderiv, _root_.smul_apply, smul_eq_mul, phaseCLM_apply]

/-- `cos(k·x)` is differentiable. -/
theorem differentiable_cos_phase (k : Fin 4 → ℝ) :
    Differentiable ℝ (fun z => Real.cos (phase k z)) :=
  (Real.contDiff_cos.comp (contDiff_phase k)).differentiable (by simp)

/-- `sin(k·x)` is differentiable. -/
theorem differentiable_sin_phase (k : Fin 4 → ℝ) :
    Differentiable ℝ (fun z => Real.sin (phase k z)) :=
  (Real.contDiff_sin.comp (contDiff_phase k)).differentiable (by simp)

/-- The plane wave `h(x) = e cos(k·x)`. -/
def planeWave (e : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) (x : MinkowskiModel 3) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Real.cos (phase k x) • e

variable {e : Matrix (Fin 4) (Fin 4) ℝ} {k : Fin 4 → ℝ}

/-- The entries `h_{ij} = e_{ij} cos(k·x)` of the plane wave. -/
theorem planeWave_apply (x : MinkowskiModel 3) (i j : Fin 4) :
    planeWave e k x i j = Real.cos (phase k x) * e i j := by
  simp [planeWave]

/-- The entries of the plane wave are smooth. -/
theorem contDiffOn_planeWave (U : Set (MinkowskiModel 3)) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun z => planeWave e k z i j) U := by
  simp only [planeWave_apply]
  exact ((Real.contDiff_cos.comp (contDiff_phase k)).mul contDiff_const).contDiffOn

/-- The first derivatives `∂_v h_{ij} = −(k·v) e_{ij} sin(k·x)`. -/
theorem fderiv_planeWave (x v : MinkowskiModel 3) (i j : Fin 4) :
    fderiv ℝ (fun z => planeWave e k z i j) x v = -Real.sin (phase k x) * phase k v * e i j := by
  simp only [planeWave_apply]
  rw [fderiv_mul_const (differentiable_cos_phase k x), _root_.smul_apply, smul_eq_mul,
    fderiv_cos_phase]
  ring

/-- The second derivatives `∂_a ∂_b h_{ij} = −k_a k_b e_{ij} cos(k·x)`. -/
theorem secondPartial_planeWave (x : MinkowskiModel 3) (a b i j : Fin 4) :
    secondPartial (fun z => planeWave e k z i j) x a b =
      -(Real.cos (phase k x) * k a * k b * e i j) := by
  have e1 : (fun z => fderiv ℝ (fun w => planeWave e k w i j) z (Pi.single b 1)) =
      fun z => Real.sin (phase k z) * (-(k b * e i j)) :=
    funext fun z => by rw [fderiv_planeWave, phase_single]; ring
  rw [secondPartial, e1, fderiv_mul_const (differentiable_sin_phase k x), _root_.smul_apply,
    smul_eq_mul, fderiv_sin_phase, phase_single]
  ring

/-- `□h = −(η^{aa} k_a²) e cos(k·x)`. -/
theorem flatBox_planeWave (x : MinkowskiModel 3) (i j : Fin 4) :
    flatBox .timeNegative (fun z => planeWave e k z i j) x =
      -(∑ a, lorentzSign .timeNegative a * k a ^ 2) * (Real.cos (phase k x) * e i j) := by
  simp only [flatBox, secondPartial_planeWave, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The covector `k` is null: `η^{aa} k_a² = 0`. -/
def IsNull (k : Fin 4 → ℝ) : Prop := ∑ a, lorentzSign (d := 3) .timeNegative a * k a ^ 2 = 0

/-- For a null covector the plane wave solves the wave equation `□h = 0`. -/
theorem flatBox_planeWave_of_isNull (hk : IsNull k) (x : MinkowskiModel 3) (i j : Fin 4) :
    flatBox .timeNegative (fun z => planeWave e k z i j) x = 0 := by
  rw [flatBox_planeWave, hk]
  ring

/-! ### The harmonic gauge -/

/-- The trace reverse of the wave is the wave of the trace-reversed amplitude. -/
theorem traceReverse_planeWave (x : MinkowskiModel 3) :
    traceReverse .timeNegative (planeWave e k x) =
      Real.cos (phase k x) • traceReverse .timeNegative e :=
  traceReverse_smul _ _

/-- The divergence terms `∂_a h̄_{ab} = −k_a ē_{ab} sin(k·x)`. -/
theorem fderiv_traceReverse_planeWave (x : MinkowskiModel 3) (a b : Fin 4) :
    fderiv ℝ (fun z => traceReverse .timeNegative (planeWave e k z) a b) x (Pi.single a 1) =
      -Real.sin (phase k x) * k a * traceReverse .timeNegative e a b := by
  simp only [traceReverse_planeWave, Matrix.smul_apply, smul_eq_mul]
  rw [fderiv_mul_const (differentiable_cos_phase k x), _root_.smul_apply, smul_eq_mul,
    fderiv_cos_phase, phase_single]
  ring

/-- **The harmonic gauge for plane waves**: `∂^a h̄_{ab} = 0` everywhere if and only if
`Σ_a η^{aa} k_a ē_{ab} = 0`. -/
theorem isHarmonicGauge_planeWave_iff :
    IsHarmonicGauge .timeNegative (planeWave e k) ⊤ ↔
      ∀ b, ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b = 0 := by
  have hsum (x : MinkowskiModel 3) (b : Fin 4) :
      ∑ a, lorentzSign .timeNegative a *
          fderiv ℝ (fun z => traceReverse .timeNegative (planeWave e k z) a b) x
            (Pi.single a 1) =
        -Real.sin (phase k x) *
          ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b := by
    simp only [fderiv_traceReverse_planeWave, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  constructor
  · intro hg b
    by_cases hk : k = 0
    · simp [hk]
    · obtain ⟨m, hm⟩ := Function.ne_iff.mp hk
      simp only [Pi.zero_apply] at hm
      have hx : phase k (Pi.single m (Real.pi / 2 / k m)) = Real.pi / 2 := by
        simp only [phase, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        field_simp
      have h := hg (Pi.single m (Real.pi / 2 / k m)) (TopologicalSpace.Opens.mem_top _) b
      rw [hsum, hx, Real.sin_pi_div_two] at h
      linarith
  · intro he x _ b
    rw [hsum, he b, mul_zero]

/-- **Plane waves are linearized vacuum solutions**: for a null `k` and a harmonic amplitude,
`δR = 0`. -/
theorem linearizedRicci_planeWave (hk : IsNull k)
    (he : ∀ b, ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b = 0)
    (x : MinkowskiModel 3) (j l : Fin 4) :
    linearizedRicci .timeNegative (planeWave e k) x j l = 0 := by
  rw [linearizedRicci_of_isHarmonicGauge (U := ⊤) (fun i j => contDiffOn_planeWave _ i j)
    (isHarmonicGauge_planeWave_iff.2 he) (TopologicalSpace.Opens.mem_top x),
    flatBox_planeWave_of_isNull hk]
  ring

/-- For a null `k` and a harmonic amplitude, `δG = 0`. -/
theorem linearizedEinstein_planeWave (hk : IsNull k)
    (he : ∀ b, ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b = 0)
    (x : MinkowskiModel 3) (j l : Fin 4) :
    linearizedEinstein .timeNegative (planeWave e k) x j l = 0 := by
  simp [linearizedEinstein, linearizedScalar, linearizedRicci_planeWave hk he]

/-- The entries of a plane wave are bounded by the sum of the entries of the amplitude. -/
theorem abs_planeWave_le (x : MinkowskiModel 3) (i j : Fin 4) :
    |planeWave e k x i j| ≤ ∑ a, ∑ c, |e a c| := by
  rw [planeWave_apply, abs_mul]
  calc |Real.cos (phase k x)| * |e i j| ≤ 1 * |e i j| :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
    _ = |e i j| := one_mul _
    _ ≤ ∑ c, |e i c| := Finset.single_le_sum (f := fun c => |e i c|)
        (fun c _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ c, |e a c| := Finset.single_le_sum (f := fun a => ∑ c, |e a c|)
        (fun a _ => Finset.sum_nonneg fun c _ => abs_nonneg _) (Finset.mem_univ i)

/-- **The wave as a derivative of actual metrics.** For a symmetric amplitude, a null `k` and the
harmonic condition, the native Ricci tensor of the Lorentz metrics `η + ε e cos(k·x)` on the
whole space-time has derivative `0` at `ε = 0`. -/
theorem hasDerivAt_ricci_planeWave (hsymm : e.IsSymm) (hk : IsNull k)
    (he : ∀ b, ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b = 0)
    (x : (⊤ : Opens (MinkowskiModel 3))) (j l : Fin 4) :
    HasDerivAt (fun ε => (linearMetricFamily .timeNegative
        (fun i j => contDiffOn_planeWave (e := e) (k := k) _ i j) ε).toLorentzMetric.ricci x
        (chartField (physicalChart x) (Pi.single j 1) x)
        (chartField (physicalChart x) (Pi.single l 1) x)) 0 0 := by
  have h := hasDerivAt_ricci_linearMetricFamily (σ := .timeNegative)
    (fun i j => contDiffOn_planeWave (e := e) (k := k) _ i j)
    (fun z _ i j => by rw [planeWave_apply, planeWave_apply, hsymm.apply i j])
    (fun z _ i j => abs_planeWave_le z i j) x j l
  rwa [linearizedRicci_planeWave hk he] at h

/-! ### Gauge transformations of a plane wave -/

/-- The gauge field `ξ^j = η^{jj} ζ_j sin(k·x)`, with the covector `ξ_j = ζ_j sin(k·x)`. -/
def gaugeVector (k ζ : Fin 4 → ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 :=
  fun j => lorentzSign .timeNegative j * ζ j * Real.sin (phase k x)

/-- The gauge field is smooth. -/
theorem contDiff_gaugeVector (k ζ : Fin 4 → ℝ) : ContDiff ℝ ∞ (gaugeVector k ζ) :=
  contDiff_pi.2 fun _ => contDiff_const.mul (Real.contDiff_sin.comp (contDiff_phase k))

/-- The gauge matrices `(k ⊗ ζ + ζ ⊗ k)_{ij} = k_i ζ_j + ζ_i k_j`. -/
def gaugeMap (k : Fin 4 → ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ where
  toFun ζ := Matrix.of fun i j => k i * ζ j + ζ i * k j
  map_add' ζ ζ' := Matrix.ext fun i j => by simp; ring
  map_smul' c ζ := Matrix.ext fun i j => by simp; ring

/-- The entries of a gauge matrix. -/
theorem gaugeMap_apply (ζ : Fin 4 → ℝ) (i j : Fin 4) :
    gaugeMap k ζ i j = k i * ζ j + ζ i * k j := rfl

/-- The gauge field `ξ_j = ζ_j sin(k·x)` adds the plane wave of `k ⊗ ζ + ζ ⊗ k`:
`L_ξ η = (k ⊗ ζ + ζ ⊗ k) cos(k·x)`. -/
theorem lieOf_gaugeVector (ζ : Fin 4 → ℝ) (x : MinkowskiModel 3) :
    Matrix.of (lieOf (fun _ => Minkowski.metricMatrix .timeNegative 3) (gaugeVector k ζ) x) =
      planeWave (gaugeMap k ζ) k x := by
  refine Matrix.ext fun i j => ?_
  have hd (m c : Fin 4) : fderiv ℝ (fun z => gaugeVector k ζ z m) x (Pi.single c 1) =
      lorentzSign .timeNegative m * ζ m * (Real.cos (phase k x) * k c) := by
    simp only [gaugeVector]
    rw [fderiv_const_mul (differentiable_sin_phase k x), _root_.smul_apply, smul_eq_mul,
      fderiv_sin_phase, phase_single]
  rw [Matrix.of_apply, lieOf_metricMatrix, hd, hd, planeWave_apply, gaugeMap_apply]
  linear_combination (ζ j * (Real.cos (phase k x) * k i)) * lorentzSign_sq .timeNegative j +
    (ζ i * (Real.cos (phase k x) * k j)) * lorentzSign_sq .timeNegative i

/-- **Gauge invariance for plane waves**: adding `k ⊗ ζ + ζ ⊗ k` to the amplitude does not change
the linearized Ricci tensor. -/
theorem linearizedRicci_planeWave_add_gauge (ζ : Fin 4 → ℝ) (x : MinkowskiModel 3) (j l : Fin 4) :
    linearizedRicci .timeNegative (planeWave (e + gaugeMap k ζ) k) x j l =
      linearizedRicci .timeNegative (planeWave e k) x j l := by
  have hw : planeWave (e + gaugeMap k ζ) k = fun z => planeWave e k z +
      Matrix.of (lieOf (fun _ => Minkowski.metricMatrix .timeNegative 3) (gaugeVector k ζ) z) := by
    funext z
    rw [lieOf_gaugeVector, planeWave, planeWave, planeWave, smul_add]
  rw [hw]
  exact linearizedRicci_add_lie (U := ⊤) (fun i j => contDiffOn_planeWave _ i j)
    (contDiff_gaugeVector k ζ).contDiffOn (TopologicalSpace.Opens.mem_top x) j l

/-! ### Symmetric matrices -/

/-- The symmetric `4 × 4` matrices. -/
def symmetricMatrices : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) where
  carrier := {e | e.IsSymm}
  add_mem' ha hb := Matrix.IsSymm.add ha hb
  zero_mem' := Matrix.isSymm_zero
  smul_mem' c _ ha := Matrix.IsSymm.smul ha c

/-- Membership in the symmetric matrices. -/
theorem mem_symmetricMatrices : e ∈ symmetricMatrices ↔ e.IsSymm := Iff.rfl

/-- The pairs of indices `i ≤ j`, the free entries of a symmetric matrix. -/
abbrev UpperIndex : Type := {p : Fin 4 × Fin 4 // p.1 ≤ p.2}

/-- A symmetric matrix is given by its entries `e_{ij}` with `i ≤ j`. -/
def symmetricEquiv : symmetricMatrices ≃ₗ[ℝ] (UpperIndex → ℝ) where
  toFun e p := (e : Matrix (Fin 4) (Fin 4) ℝ) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨Matrix.of fun i j =>
      if h : i ≤ j then v ⟨(i, j), h⟩ else v ⟨(j, i), le_of_not_ge h⟩, by
    refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.of_apply]
    by_cases hij : i ≤ j
    · by_cases hji : j ≤ i
      · have := le_antisymm hij hji
        subst this
        rfl
      · rw [dite_eq_right hji, dite_eq_left hij]
    · rw [dite_eq_left (le_of_not_ge hij), dite_eq_right hij]⟩
  left_inv e := by
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    change (if h : i ≤ j then _ else _) = _
    by_cases hij : i ≤ j
    · rw [dite_eq_left hij]
    · rw [dite_eq_right hij]
      exact e.property.apply i j
  right_inv v := by
    funext p
    change (if h : p.1.1 ≤ p.1.2 then _ else _) = _
    rw [dite_eq_left p.property]

/-- **The symmetric `4 × 4` matrices have dimension `10`.** -/
theorem finrank_symmetricMatrices : finrank ℝ symmetricMatrices = 10 := by
  rw [symmetricEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
  decide

/-! ### The polarization and gauge spaces -/

/-- The harmonic condition on an amplitude, `e ↦ (Σ_a η^{aa} k_a ē_{ab})_b`. -/
def harmonicMap (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun e b := ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b
  map_add' e e' := funext fun b => by
    simp only [traceReverse_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' c e := funext fun b => by
    simp only [traceReverse_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
      Pi.smul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

/-- The components of the harmonic condition. -/
theorem harmonicMap_apply (b : Fin 4) :
    harmonicMap k e b =
      ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b := rfl

/-- The polarization amplitudes: the symmetric `e` with `Σ_a η^{aa} k_a ē_{ab} = 0`. -/
def polarizationSpace (k : Fin 4 → ℝ) : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  symmetricMatrices ⊓ LinearMap.ker (harmonicMap k)

/-- Membership in the polarization amplitudes. -/
theorem mem_polarizationSpace : e ∈ polarizationSpace k ↔ e.IsSymm ∧
    ∀ b, ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b = 0 := by
  simp only [polarizationSpace, Submodule.mem_inf, mem_symmetricMatrices, LinearMap.mem_ker,
    funext_iff, harmonicMap_apply, Pi.zero_apply]

/-- The pure-gauge amplitudes `k ⊗ ζ + ζ ⊗ k`. -/
def gaugeSpace (k : Fin 4 → ℝ) : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  LinearMap.range (gaugeMap k)

/-- **The gauge amplitudes are polarizations** for a null covector. -/
theorem gaugeSpace_le_polarizationSpace (hk : IsNull k) : gaugeSpace k ≤ polarizationSpace k := by
  rintro _ ⟨ζ, rfl⟩
  have hk' : -k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2 = 0 := by
    simpa [IsNull, Fin.sum_univ_four] using hk
  refine mem_polarizationSpace.2 ⟨Matrix.IsSymm.ext fun i j => ?_, fun b => ?_⟩
  · simp only [gaugeMap_apply]
    ring
  · fin_cases b <;>
    · simp [Fin.sum_univ_four, traceReverse_apply, flatTrace, gaugeMap_apply, metricMatrix_apply]
      linear_combination (ζ _) * hk'

/-- For `k ≠ 0` the map `ζ ↦ k ⊗ ζ + ζ ⊗ k` is injective. -/
theorem gaugeMap_injective (hk : k ≠ 0) : Function.Injective (gaugeMap k) := by
  refine (injective_iff_map_eq_zero (gaugeMap k)).2 fun ζ hζ => ?_
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hk
  simp only [Pi.zero_apply] at hm
  have hz (i j : Fin 4) : k i * ζ j + ζ i * k j = 0 := by
    have := congrFun (congrFun hζ i) j
    rwa [gaugeMap_apply] at this
  have hmm : ζ m = 0 := by
    have h := hz m m
    have : (2 * k m) * ζ m = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hm)
  funext j
  have h := hz m j
  rw [hmm, zero_mul, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hm

/-- For `k ≠ 0` the gauge amplitudes have dimension `4`. -/
theorem finrank_gaugeSpace (hk : k ≠ 0) : finrank ℝ (gaugeSpace k) = 4 := by
  rw [gaugeSpace, LinearMap.finrank_range_of_inj (gaugeMap_injective hk), Module.finrank_fin_fun]

/-- For `k ≠ 0` the harmonic condition maps the symmetric matrices onto `ℝ⁴`: the trace reverse
of `w ⊗ v + v ⊗ w − (k^a w_a) v ⊗ v`, with `k^a v_a = 1`, has the image `w`. -/
theorem exists_harmonicMap_eq (hk : k ≠ 0) (w : Fin 4 → ℝ) :
    ∃ e ∈ symmetricMatrices, harmonicMap k e = w := by
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hk
  simp only [Pi.zero_apply] at hm
  set u : Fin 4 → ℝ := fun a => lorentzSign .timeNegative a * k a
  have hum : u m ≠ 0 := by
    have hs : lorentzSign (d := 3) .timeNegative m ≠ 0 := by
      intro h0
      have := lorentzSign_sq (d := 3) .timeNegative m
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    exact mul_ne_zero hs hm
  set v : Fin 4 → ℝ := Pi.single m (u m)⁻¹
  set c : ℝ := ∑ a, u a * w a
  have hv : ∑ a, u a * v a = 1 := by
    simp only [v, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    exact mul_inv_cancel₀ hum
  set f : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun a b => w a * v b + v a * w b - c * (v a * v b)
  refine ⟨traceReverse .timeNegative f, Matrix.IsSymm.ext fun i j => ?_, funext fun b => ?_⟩
  · simp only [traceReverse_apply, f, Matrix.of_apply, metricMatrix_apply,
      flatTrace]
    by_cases hij : j = i
    · subst hij
      rfl
    · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
      ring
  · rw [harmonicMap_apply, traceReverse_traceReverse]
    have hterm (a : Fin 4) : lorentzSign .timeNegative a * k a * f a b =
        u a * w a * v b + u a * v a * w b - c * (u a * v a * v b) := by
      simp only [f, Matrix.of_apply, u]
      ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, hv]
    ring

/-- **For `k ≠ 0` the polarization amplitudes have dimension `6`.** -/
theorem finrank_polarizationSpace (hk : k ≠ 0) : finrank ℝ (polarizationSpace k) = 6 := by
  set Φ := (harmonicMap k).comp symmetricMatrices.subtype
  have hrange : LinearMap.range Φ = ⊤ := by
    refine LinearMap.range_eq_top.2 fun w => ?_
    obtain ⟨e, he, hw⟩ := exists_harmonicMap_eq hk w
    exact ⟨⟨e, he⟩, hw⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, finrank_top, Module.finrank_fin_fun, finrank_symmetricMatrices] at hsum
  have hmap : polarizationSpace k = (LinearMap.ker Φ).map symmetricMatrices.subtype := by
    ext e
    simp only [polarizationSpace, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_map,
      Φ, LinearMap.comp_apply, Submodule.subtype_apply]
    constructor
    · rintro ⟨he, hz⟩
      exact ⟨⟨e, he⟩, hz, rfl⟩
    · rintro ⟨e', hz, rfl⟩
      exact ⟨e'.property, hz⟩
  rw [hmap, Submodule.finrank_map_subtype_eq]
  omega

/-- The gauge amplitudes as a submodule of the polarization amplitudes. -/
def gaugeIn (k : Fin 4 → ℝ) : Submodule ℝ (polarizationSpace k) :=
  (gaugeSpace k).comap (polarizationSpace k).subtype

/-- **The two polarizations of a weak gravitational wave**: for a nonzero null covector `k`, the
polarization amplitudes modulo the gauge amplitudes form a space of dimension `2`. -/
theorem finrank_polarizationQuotient (hk : IsNull k) (hk0 : k ≠ 0) :
    finrank ℝ (polarizationSpace k ⧸ gaugeIn k) = 2 := by
  have hg : finrank ℝ (gaugeIn k) = 4 := by
    rw [gaugeIn, (Submodule.comapSubtypeEquivOfLe (gaugeSpace_le_polarizationSpace hk)).finrank_eq,
      finrank_gaugeSpace hk0]
  have h := Submodule.finrank_quotient_add_finrank (gaugeIn k)
  rw [hg, finrank_polarizationSpace hk0] at h
  omega

/-! ### The wave along `x³` -/

/-- The null covector `k = (−ν, 0, 0, ν)` of a wave along `x³`, with the phase `ν(x³ − x⁰)`. -/
def axialCovector (ν : ℝ) : Fin 4 → ℝ := ![-ν, 0, 0, ν]

/-- The covector `(−ν, 0, 0, ν)` is null. -/
theorem isNull_axialCovector (ν : ℝ) : IsNull (axialCovector ν) := by
  simp [IsNull, Fin.sum_univ_four, axialCovector]

/-- The covector `(−ν, 0, 0, ν)` is not zero for `ν ≠ 0`. -/
theorem axialCovector_ne_zero {ν : ℝ} (hν : ν ≠ 0) : axialCovector ν ≠ 0 := by
  intro h
  have := congrFun h 3
  simp [axialCovector] at this
  exact hν this

/-- The polarization `e₊`: `e₁₁ = −e₂₂ = 1`. -/
def plusPolarization : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 0]

/-- The polarization `e×`: `e₁₂ = e₂₁ = 1`. -/
def crossPolarization : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 0]

/-- `e₊` is a polarization of the wave along `x³`. -/
theorem plusPolarization_mem (ν : ℝ) : plusPolarization ∈ polarizationSpace (axialCovector ν) := by
  refine mem_polarizationSpace.2 ⟨Matrix.IsSymm.ext fun i j => ?_, fun b => ?_⟩
  · fin_cases i <;> fin_cases j <;> rfl
  · fin_cases b <;>
      simp [Fin.sum_univ_four, traceReverse_apply, flatTrace, metricMatrix_apply,
        plusPolarization, axialCovector]

/-- `e×` is a polarization of the wave along `x³`. -/
theorem crossPolarization_mem (ν : ℝ) :
    crossPolarization ∈ polarizationSpace (axialCovector ν) := by
  refine mem_polarizationSpace.2 ⟨Matrix.IsSymm.ext fun i j => ?_, fun b => ?_⟩
  · fin_cases i <;> fin_cases j <;> rfl
  · fin_cases b <;>
      simp [Fin.sum_univ_four, traceReverse_apply, flatTrace, metricMatrix_apply,
        crossPolarization, axialCovector]

/-- The classes of `e₊` and `e×` modulo the gauge amplitudes. -/
def polarizationClasses (ν : ℝ) : Fin 2 → polarizationSpace (axialCovector ν) ⧸
    gaugeIn (axialCovector ν) :=
  ![Submodule.Quotient.mk ⟨plusPolarization, plusPolarization_mem ν⟩,
    Submodule.Quotient.mk ⟨crossPolarization, crossPolarization_mem ν⟩]

/-- The classes of `e₊` and `e×` are linearly independent: no combination `a e₊ + b e×` is a gauge
amplitude unless `a = b = 0`, since `(k ⊗ ζ + ζ ⊗ k)_{11} = (k ⊗ ζ + ζ ⊗ k)_{12} = 0`. -/
theorem linearIndependent_polarizationClasses {ν : ℝ} :
    LinearIndependent ℝ (polarizationClasses ν) := by
  refine LinearIndependent.pair_iff.2 fun s t hst => ?_
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_eq_zero] at hst
  obtain ⟨ζ, hζ⟩ := hst
  rw [Submodule.subtype_apply, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul] at hζ
  have h11 := congrFun (congrFun hζ 1) 1
  have h12 := congrFun (congrFun hζ 1) 2
  simp [gaugeMap_apply, axialCovector, plusPolarization, crossPolarization] at h11 h12
  constructor <;> linarith

/-- **A basis of the two polarizations** of the wave along `x³`: the classes of `e₊` and `e×`. -/
def polarizationBasis {ν : ℝ} (hν : ν ≠ 0) :
    Basis (Fin 2) ℝ (polarizationSpace (axialCovector ν) ⧸ gaugeIn (axialCovector ν)) :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_polarizationClasses
    (by rw [Fintype.card_fin, finrank_polarizationQuotient (isNull_axialCovector ν)
      (axialCovector_ne_zero hν)])

/-- The plus-polarized wave `e₊ cos(ν(x³ − x⁰))` solves the linearized vacuum equations. -/
theorem linearizedRicci_plusWave (ν : ℝ) (x : MinkowskiModel 3) (j l : Fin 4) :
    linearizedRicci .timeNegative (planeWave plusPolarization (axialCovector ν)) x j l = 0 :=
  linearizedRicci_planeWave (isNull_axialCovector ν)
    (mem_polarizationSpace.1 (plusPolarization_mem ν)).2 x j l

/-- The plus-polarized wave is not zero: its entry `h₁₁` is `1` at the origin. -/
theorem planeWave_plus_apply_zero (ν : ℝ) :
    planeWave plusPolarization (axialCovector ν) 0 1 1 = 1 := by
  simp [planeWave_apply, phase, plusPolarization]

end ProjectAinos.GeneralRelativity.WeakWaves
