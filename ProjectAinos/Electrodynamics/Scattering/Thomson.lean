/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.Relativistic
public import ProjectAinos.Electrodynamics.PlaneWave
public import ProjectAinos.SmoothGeometry.ODE.FlowComplete
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Scattering by free charges

Landau–Lifshitz, *The Classical Theory of Fields*, §78, in units with `c = 1` and `div E = k⁰`, so
that the potentials carry `1/4π` and the cross section of Thomson is `σ_T = (8π/3)(e²/4πm)²`
(`thomsonCrossSection`; `(8π/3)(e²/mc²)²` in Gaussian units).

**The motion.** The scattering charge obeys the nonrelativistic equation of motion
`m ẍ = e (E + ẋ × B)` in given fields `E(t, x)`, `B(t, x)` (`IsTrajectory`, with `k = e/m`).

* `exists_trajectory`: in smooth bounded fields the motion exists for all times, because the
  field `(t, x, v) ↦ (1, v, k (E + v × B))` (`motionField`) is smooth and of linear growth
  (`flowDomain_eq_univ_of_norm_le`); `exists_trajectory_wave` for the plane wave
  `E = E₀ cos(ω (t − ⟨n, x⟩))`, `B = n × E` (`waveElectric`, `waveMagnetic`). The relativistic
  motion in proper time, `du/dτ = k F(x) u` (`IsProperTimeTrajectory`), likewise exists for all
  proper times in a smooth bounded field (`exists_properTimeTrajectory`,
  `exists_properTimeTrajectory_planeWave`).
* `norm_trajectory_sub_firstOrder_le`: **the weak-wave expansion**. In the fields `a E`, `a B` of
  the amplitude `a`, with `E` Lipschitz in the position, a charge at rest at `x₀` moves as
  `x₀ + a ξ + O(a²)` on `[0, T]`, uniformly in `|a| ≤ 1`, where `ξ̈ = k E(t, x₀)`,
  `ξ(0) = ξ̇(0) = 0` is the first-order response; the velocity is `a ξ̇ + O(a²)`. The velocity is
  of the order `a` by Grönwall's inequality, so the magnetic force and the change of the electric
  force along the path are of the order `a²`, and Grönwall's inequality for the error gives the
  constant. For the plane wave the response is explicit (`firstOrderResponse`, with a uniform
  drift from the phase at `t = 0`): `norm_trajectory_sub_firstOrderResponse_le`.

**The incident wave.** `incidentPotential ω n E₀` is the `planeWave` `A = b sin(ω (t − ⟨n, x⟩))`
with `b = −ω⁻¹ Σᵢ E₀ᵢ dxⁱ`. Its electric field is `waveElectric`
(`electricVector_incidentPotential`), and for `|n| = 1` and `⟨n, E₀⟩ = 0` its magnetic field is
`waveMagnetic` and its flux of energy along `n` is `S · n = |E|²` (`transverse_incidentPotential`,
from `transverse_planeWave`). `periodAverage ω f` is the mean over a period, with
`⟨cos²(ωt + φ)⟩ = 1/2` (`periodAverage_cos_sq`), and the averaged incident flux is
`incidentFlux = |E₀|²/2` (`incidentFlux_eq`).

**The cross section.** `crossSection e ω w S` is the averaged power of Larmor `⟨(2/3)(e²/4π)|w|²⟩`
of a charge with the acceleration `w(t)` divided by the flux `S`, and `differentialCrossSection`
the averaged angular distribution `angularPower e 0 w n` (Liénard's formula at rest,
`angularPower_zero`, whose integral over the sphere is the power of Larmor,
`integral_angularPower_zero`) divided by `S`. For the acceleration `(e/m) E(t, x₀)` of the
first-order response:

* `crossSection_eq`: **Thomson's formula** `σ = σ_T`, independent of the frequency;
* `differentialCrossSection_eq`: `dσ/dΩ = (e²/4πm)² sin²ψ`, with `ψ` the angle between the
  direction `n` of scattering and the polarization `E₀`, and
  `integral_differentialCrossSection`: its integral over the sphere of directions is `σ_T`;
* `differentialCrossSection_unpolarized`: for unpolarized light, the mean over two orthogonal
  polarizations, `dσ/dΩ = (e²/4πm)² (1 + cos²θ)/2` with the angle of scattering `θ`
  (`sin_sq_angle_add_sin_sq_angle`).

`crossSection_standardFrame` is an instance of the hypotheses (`orthonormal_standardFrame`). The
scope is the classical charge to first order in the amplitude: the reaction of the radiation (§75)
and the corrections of the order `v² ∼ a²` to the radiated power are not included.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped Topology

namespace ProjectAinos.Electrodynamics.Scattering.Thomson

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SmoothGeometry.DifferentialForm
  SpecialRelativity Radiation.Relativistic NonlinearODE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The cross product -/

/-- `|u × v| ≤ |u| |v|`. -/
theorem norm_cross_le (u v : E3) : ‖cross u v‖ ≤ ‖u‖ * ‖v‖ := by
  have h : ‖cross u v‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    rw [norm_cross_sq, mul_pow]
    nlinarith [sq_nonneg (inner ℝ u v)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- The cross product is a bounded bilinear map. -/
theorem isBoundedBilinearMap_cross : IsBoundedBilinearMap ℝ fun p : E3 × E3 => cross p.1 p.2 where
  add_left x y z := by simp [cross]
  smul_left c x y := by simp [cross]
  add_right x y z := by simp [cross]
  smul_right c x y := by simp [cross]
  bound := ⟨1, one_pos, fun x y => by rw [one_mul]; exact norm_cross_le x y⟩

/-- The cross product is smooth. -/
theorem contDiff_cross {n : WithTop ℕ∞} : ContDiff ℝ n fun p : E3 × E3 => cross p.1 p.2 :=
  isBoundedBilinearMap_cross.contDiff

/-! ### The motion of a charge in a wave -/

/-- `(x, v)` is a trajectory of a charge with the ratio `k = e/m` of charge to mass in the fields
`E(t, x)` and `B(t, x)`: `ẋ = v` and `v̇ = k (E + v × B)`, the nonrelativistic equation of motion
`m ẍ = e (E + ẋ × B)` (Landau–Lifshitz §17 for `v ≪ 1`). -/
def IsTrajectory (k : ℝ) (E B : ℝ → E3 → E3) (x v : ℝ → E3) : Prop :=
  ∀ t, HasDerivAt x (v t) t ∧ HasDerivAt v (k • (E t (x t) + cross (v t) (B t (x t)))) t

/-- The field of the equation of motion on the space of the time, the position and the velocity:
`(ṫ, ẋ, v̇) = (1, v, k (E + v × B))`. -/
def motionField (k : ℝ) (E B : ℝ → E3 → E3) (z : ℝ × E3 × E3) : ℝ × E3 × E3 :=
  (1, z.2.2, k • (E z.1 z.2.1 + cross z.2.2 (B z.1 z.2.1)))

open scoped ContDiff in
/-- The field of the equation of motion is smooth when the fields are. -/
theorem contDiff_motionField (k : ℝ) {E B : ℝ → E3 → E3}
    (hE : ContDiff ℝ ∞ fun p : ℝ × E3 => E p.1 p.2)
    (hB : ContDiff ℝ ∞ fun p : ℝ × E3 => B p.1 p.2) :
    ContDiff ℝ ∞ (motionField k E B) := by
  have hp : ContDiff ℝ ∞ fun z : ℝ × E3 × E3 => (z.1, z.2.1) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hE' : ContDiff ℝ ∞ fun z : ℝ × E3 × E3 => E z.1 z.2.1 := hE.comp hp
  have hB' : ContDiff ℝ ∞ fun z : ℝ × E3 × E3 => B z.1 z.2.1 := hB.comp hp
  have hv : ContDiff ℝ ∞ fun z : ℝ × E3 × E3 => z.2.2 := contDiff_snd.comp contDiff_snd
  have hc : ContDiff ℝ ∞ fun z : ℝ × E3 × E3 => cross z.2.2 (B z.1 z.2.1) :=
    contDiff_cross.comp (hv.prodMk hB')
  exact contDiff_const.prodMk (hv.prodMk ((hE'.add hc).const_smul k))

/-- For bounded fields the field of the equation of motion has a linear growth. -/
theorem norm_motionField_le (k : ℝ) {E B : ℝ → E3 → E3} {ME MB : ℝ}
    (hEb : ∀ t x, ‖E t x‖ ≤ ME) (hBb : ∀ t x, ‖B t x‖ ≤ MB) (z : ℝ × E3 × E3) :
    ‖motionField k E B z‖ ≤ (1 + |k| * ME) + (1 + |k| * MB) * ‖z‖ := by
  have hME : 0 ≤ ME := (norm_nonneg _).trans (hEb 0 0)
  have hMB : 0 ≤ MB := (norm_nonneg _).trans (hBb 0 0)
  have hv : ‖z.2.2‖ ≤ ‖z‖ := (norm_snd_le z.2).trans (norm_snd_le z)
  have hz := norm_nonneg z
  have hk := abs_nonneg k
  have h1 : ‖E z.1 z.2.1 + cross z.2.2 (B z.1 z.2.1)‖ ≤ ME + MB * ‖z‖ := by
    calc _ ≤ ‖E z.1 z.2.1‖ + ‖cross z.2.2 (B z.1 z.2.1)‖ := norm_add_le _ _
      _ ≤ ME + ‖z.2.2‖ * ‖B z.1 z.2.1‖ := add_le_add (hEb _ _) (norm_cross_le _ _)
      _ ≤ ME + ‖z‖ * MB := by gcongr; exact hBb _ _
      _ = ME + MB * ‖z‖ := by ring
  have h2 : ‖k • (E z.1 z.2.1 + cross z.2.2 (B z.1 z.2.1))‖ ≤ |k| * ME + |k| * MB * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |k| * _ ≤ |k| * (ME + MB * ‖z‖) := mul_le_mul_of_nonneg_left h1 hk
      _ = _ := by ring
  have h3 : 0 ≤ |k| * ME := mul_nonneg hk hME
  have h4 : 0 ≤ |k| * MB * ‖z‖ := mul_nonneg (mul_nonneg hk hMB) hz
  refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
  · simp only [motionField, norm_one]
    nlinarith
  · simp only [motionField]
    nlinarith
  · simp only [motionField]
    nlinarith

open scoped ContDiff in
/-- **The motion exists for all times** (Landau–Lifshitz §78, the motion of a charge in the field
of a wave): in smooth bounded fields `E(t, x)` and `B(t, x)` the nonrelativistic equation of motion
`ẋ = v`, `v̇ = k (E + v × B)` has a solution for all times with any initial position and
velocity. The field `(t, x, v) ↦ (1, v, k (E + v × B))` is smooth and of linear growth, so its flow
is defined everywhere (`flowDomain_eq_univ_of_norm_le`). -/
theorem exists_trajectory (k : ℝ) {E B : ℝ → E3 → E3}
    (hE : ContDiff ℝ ∞ fun p : ℝ × E3 => E p.1 p.2)
    (hB : ContDiff ℝ ∞ fun p : ℝ × E3 => B p.1 p.2) {ME MB : ℝ}
    (hEb : ∀ t x, ‖E t x‖ ≤ ME) (hBb : ∀ t x, ‖B t x‖ ≤ MB) (x₀ v₀ : E3) :
    ∃ x v : ℝ → E3, x 0 = x₀ ∧ v 0 = v₀ ∧ IsTrajectory k E B x v := by
  set X := motionField k E B with hXdef
  have hX := contDiff_motionField k hE hB
  have hdom := flowDomain_eq_univ_of_norm_le hX (norm_motionField_le k hEb hBb)
  set Φ : ℝ → ℝ × E3 × E3 := fun t => flow X (t, ((0 : ℝ), x₀, v₀)) with hΦ
  have hd : ∀ t, HasDerivAt Φ (X (Φ t)) t := fun t =>
    hasDerivAt_flow hX (by rw [hdom]; exact mem_univ _)
  have hΦ0 : Φ 0 = (0, x₀, v₀) := flow_zero X _
  have h1 : ∀ t, HasDerivAt (fun s => (Φ s).1) 1 t := fun t => by
    have h := (ContinuousLinearMap.fst ℝ ℝ (E3 × E3)).hasFDerivAt.comp_hasDerivAt t (hd t)
    have hv : (ContinuousLinearMap.fst ℝ ℝ (E3 × E3)) (X (Φ t)) = 1 := rfl
    rw [hv] at h
    exact h
  have htime : ∀ t, (Φ t).1 = t := by
    intro t
    have h := const_of_hasDerivAt_zero (g := fun s => (Φ s).1 - s) (g' := fun _ => 0)
      (fun s => by simpa using (h1 s).fun_sub (hasDerivAt_id' s)) (fun _ => rfl) t 0
    simp only [hΦ0, sub_zero] at h
    linarith
  refine ⟨fun t => (Φ t).2.1, fun t => (Φ t).2.2, by simp [hΦ0], by simp [hΦ0],
    fun t => ⟨?_, ?_⟩⟩
  · have h := ((ContinuousLinearMap.fst ℝ E3 E3).comp
      (ContinuousLinearMap.snd ℝ ℝ (E3 × E3))).hasFDerivAt.comp_hasDerivAt t (hd t)
    have hv : ((ContinuousLinearMap.fst ℝ E3 E3).comp
        (ContinuousLinearMap.snd ℝ ℝ (E3 × E3))) (X (Φ t)) = (Φ t).2.2 := rfl
    rw [hv] at h
    exact h
  · have h := ((ContinuousLinearMap.snd ℝ E3 E3).comp
      (ContinuousLinearMap.snd ℝ ℝ (E3 × E3))).hasFDerivAt.comp_hasDerivAt t (hd t)
    have hv : ((ContinuousLinearMap.snd ℝ E3 E3).comp
        (ContinuousLinearMap.snd ℝ ℝ (E3 × E3))) (X (Φ t)) =
        k • (E t (Φ t).2.1 + cross (Φ t).2.2 (B t (Φ t).2.1)) := by
      change k • (E (Φ t).1 (Φ t).2.1 + cross (Φ t).2.2 (B (Φ t).1 (Φ t).2.1)) = _
      rw [htime]
    rw [hv] at h
    exact h


/-! ### The relativistic motion in proper time -/

/-- `(x, u)` is a world line of a charge with the ratio `k = e/m` of charge to mass, parametrized
by the proper time, in the field whose mixed tensor `F^μ_ν(x)` is the linear map `F x`:
`dx/dτ = u` and `du/dτ = k F(x) u` (Landau–Lifshitz §23). -/
def IsProperTimeTrajectory (k : ℝ) (F : Spacetime → Spacetime →L[ℝ] Spacetime)
    (x u : ℝ → Spacetime) : Prop :=
  ∀ τ, HasDerivAt x (u τ) τ ∧ HasDerivAt u (k • F (x τ) (u τ)) τ

open scoped ContDiff in
/-- **The relativistic motion exists for all proper times**: in a smooth bounded field `F(x)` the
field `(x, u) ↦ (u, k F(x) u)` on `ℝ⁴ × ℝ⁴` is smooth and of linear growth, so the world line
through any event and four-velocity is defined for all proper times. -/
theorem exists_properTimeTrajectory (k : ℝ) {F : Spacetime → Spacetime →L[ℝ] Spacetime}
    (hF : ContDiff ℝ ∞ F) {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M) (x₀ u₀ : Spacetime) :
    ∃ x u : ℝ → Spacetime, x 0 = x₀ ∧ u 0 = u₀ ∧ IsProperTimeTrajectory k F x u := by
  set X : Spacetime × Spacetime → Spacetime × Spacetime := fun z => (z.2, k • F z.1 z.2)
    with hXdef
  have hX : ContDiff ℝ ∞ X :=
    contDiff_snd.prodMk (((hF.comp contDiff_fst).clm_apply contDiff_snd).const_smul k)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hb : ∀ z, ‖X z‖ ≤ 0 + (1 + |k| * M) * ‖z‖ := by
    intro z
    have h2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
    have hz := norm_nonneg z
    have hk := abs_nonneg k
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · simp only [hXdef]
      nlinarith [mul_nonneg (mul_nonneg hk hM0) hz]
    · simp only [hXdef]
      rw [norm_smul, Real.norm_eq_abs]
      calc |k| * ‖F z.1 z.2‖ ≤ |k| * (M * ‖z.2‖) :=
            mul_le_mul_of_nonneg_left
              (((F z.1).le_opNorm z.2).trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)))
              hk
        _ ≤ 0 + (1 + |k| * M) * ‖z‖ := by nlinarith [mul_nonneg hk hM0]
  have hdom := flowDomain_eq_univ_of_norm_le hX hb
  set Φ : ℝ → Spacetime × Spacetime := fun τ => flow X (τ, (x₀, u₀)) with hΦ
  have hd : ∀ τ, HasDerivAt Φ (X (Φ τ)) τ := fun τ =>
    hasDerivAt_flow hX (by rw [hdom]; exact mem_univ _)
  have hΦ0 : Φ 0 = (x₀, u₀) := flow_zero X _
  refine ⟨fun τ => (Φ τ).1, fun τ => (Φ τ).2, by simp [hΦ0], by simp [hΦ0], fun τ => ⟨?_, ?_⟩⟩
  · have h := (ContinuousLinearMap.fst ℝ Spacetime Spacetime).hasFDerivAt.comp_hasDerivAt τ (hd τ)
    have hv : (ContinuousLinearMap.fst ℝ Spacetime Spacetime) (X (Φ τ)) = (Φ τ).2 := rfl
    rw [hv] at h
    exact h
  · have h := (ContinuousLinearMap.snd ℝ Spacetime Spacetime).hasFDerivAt.comp_hasDerivAt τ (hd τ)
    have hv : (ContinuousLinearMap.snd ℝ Spacetime Spacetime) (X (Φ τ)) =
        k • F (Φ τ).1 (Φ τ).2 := rfl
    rw [hv] at h
    exact h

/-- An instance: the monochromatic plane wave `F(x) = cos(ℓ(x)) F₀` with a constant tensor `F₀` is
smooth and bounded, so the world line in it exists for all proper times. -/
theorem exists_properTimeTrajectory_planeWave (k : ℝ) (ℓ : FourCovector)
    (F₀ : Spacetime →L[ℝ] Spacetime) (x₀ u₀ : Spacetime) :
    ∃ x u : ℝ → Spacetime, x 0 = x₀ ∧ u 0 = u₀ ∧
      IsProperTimeTrajectory k (fun y => Real.cos (ℓ y) • F₀) x u :=
  exists_properTimeTrajectory (F := fun y => Real.cos (ℓ y) • F₀) k
    ((Real.contDiff_cos.comp ℓ.contDiff).smul contDiff_const)
    (M := ‖F₀‖) (fun y => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)) x₀ u₀

/-! ### The response to a weak wave -/

/-- Grönwall's inequality from the time `0` for a function with a derivative at every time: if
`f(0) = 0` and `‖f′‖ ≤ K ‖f‖ + ε` on `[0, T]`, then `‖f(t)‖ ≤ gronwallBound 0 K ε t` there. -/
theorem norm_le_gronwallBound_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {K ε T : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) (h0 : f 0 = 0)
    (hb : ∀ t ∈ Icc 0 T, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc 0 T, ‖f t‖ ≤ gronwallBound 0 K ε t := by
  intro t ht
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (a := 0) (b := T) (f := f) (f' := f')
    (δ := 0) (K := K) (ε := ε) (fun s _ => (hf s).continuousAt.continuousWithinAt)
    (fun s _ => (hf s).hasDerivWithinAt) (by simp [h0])
    (fun s hs => hb s (Ico_subset_Icc_self hs)) t ht
  simpa using h

/-- The bound of Grönwall from `0` is linear in the inhomogeneity. -/
theorem gronwallBound_zero_mul (K c ε x : ℝ) :
    gronwallBound 0 K (c * ε) x = c * gronwallBound 0 K ε x := by
  by_cases hK : K = 0
  · simp only [gronwallBound, hK, ite_true]
    ring
  · simp only [gronwallBound, hK, ite_false]
    ring

/-- The bound of Grönwall from `0` is not negative at the times `t ≥ 0`. -/
theorem gronwallBound_zero_nonneg {K ε t : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    0 ≤ gronwallBound 0 K ε t := by
  have h := gronwallBound_mono le_rfl hε hK ht
  rwa [gronwallBound_x0] at h

/-- **The weak-wave expansion** (Landau–Lifshitz §78): a charge at rest at `x₀` in the fields
`a E(t, x)`, `a B(t, x)` of the amplitude `a` moves as `x(t) = x₀ + a ξ(t) + O(a²)` on `[0, T]`,
uniformly in `|a| ≤ 1`, where `ξ` is the first-order response `ξ̈ = k E(t, x₀)` with
`ξ(0) = ξ̇(0) = 0`; the velocity is `a ξ̇ + O(a²)`. The fields are bounded and `E` is Lipschitz in
the position. The velocity is first bounded by `|a| V` (Grönwall for `v̇ = k a (E + v × B)`), so
the magnetic force `k a v × B` and the change `k a (E(t, x) − E(t, x₀))` of the electric force
along the path are of the order `a²`, and Grönwall's inequality for the error
`(x − x₀ − a ξ, v − a ξ̇)` gives the constant `C`. -/
theorem norm_trajectory_sub_firstOrder_le (k : ℝ) {E B : ℝ → E3 → E3} {ME MB L T : ℝ}
    (hEb : ∀ t x, ‖E t x‖ ≤ ME) (hBb : ∀ t x, ‖B t x‖ ≤ MB)
    (hL : ∀ t x y, ‖E t x - E t y‖ ≤ L * ‖x - y‖) (x₀ : E3) {ξ η : ℝ → E3}
    (hξ0 : ξ 0 = 0) (hη0 : η 0 = 0) (hξ : ∀ t, HasDerivAt ξ (η t) t)
    (hη : ∀ t, HasDerivAt η (k • E t x₀) t) :
    ∃ C, ∀ a : ℝ, |a| ≤ 1 → ∀ x v : ℝ → E3, x 0 = x₀ → v 0 = 0 →
      IsTrajectory k (fun t y => a • E t y) (fun t y => a • B t y) x v →
      ∀ t ∈ Icc 0 T, ‖x t - x₀ - a • ξ t‖ ≤ C * a ^ 2 ∧ ‖v t - a • η t‖ ≤ C * a ^ 2 := by
  have hME : 0 ≤ ME := (norm_nonneg _).trans (hEb 0 0)
  have hMB : 0 ≤ MB := (norm_nonneg _).trans (hBb 0 0)
  have hk := abs_nonneg k
  have hL0 := abs_nonneg L
  have hL' : ∀ t x y, ‖E t x - E t y‖ ≤ |L| * ‖x - y‖ := fun t x y =>
    (hL t x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))
  -- the first-order response is bounded on `[0, T]`
  set Ξ := gronwallBound 0 1 (|k| * ME) T with hΞdef
  have hΞ : ∀ t ∈ Icc 0 T, ‖ξ t‖ ≤ Ξ := by
    intro t ht
    have hpair : ∀ s, HasDerivAt (fun s => (ξ s, η s)) (η s, k • E s x₀) s := fun s =>
      (hξ s).prodMk (hη s)
    have hb : ∀ s ∈ Icc 0 T, ‖(η s, k • E s x₀)‖ ≤ 1 * ‖(ξ s, η s)‖ + |k| * ME := by
      intro s _
      have h1 : ‖η s‖ ≤ ‖(ξ s, η s)‖ := norm_snd_le (ξ s, η s)
      have h2 : ‖k • E s x₀‖ ≤ |k| * ME := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hEb s x₀) hk
      have h3 := norm_nonneg (ξ s, η s)
      have h4 := mul_nonneg hk hME
      refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
      · simp only
        linarith
      · simp only
        linarith
    have h := norm_le_gronwallBound_of_hasDerivAt hpair (by simp [hξ0, hη0]) hb t ht
    calc ‖ξ t‖ ≤ ‖(ξ t, η t)‖ := norm_fst_le (ξ t, η t)
      _ ≤ gronwallBound 0 1 (|k| * ME) t := h
      _ ≤ Ξ := gronwallBound_mono le_rfl (mul_nonneg hk hME) zero_le_one ht.2
  set V := gronwallBound 0 (|k| * MB) (|k| * ME) T with hVdef
  set K := 1 + |k| * |L| with hKdef
  set ε₀ := |k| * (|L| * Ξ + V * MB) with hε₀def
  refine ⟨gronwallBound 0 K ε₀ T, fun a ha x v hx0 hv0 htr t ht => ?_⟩
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hΞ0 : 0 ≤ Ξ := gronwallBound_zero_nonneg zero_le_one (mul_nonneg hk hME) hT
  have hV0 : 0 ≤ V := gronwallBound_zero_nonneg (mul_nonneg hk hMB) (mul_nonneg hk hME) hT
  have hε₀ : 0 ≤ ε₀ := mul_nonneg hk (add_nonneg (mul_nonneg hL0 hΞ0) (mul_nonneg hV0 hMB))
  have hK : 0 ≤ K := by positivity
  have ha0 := abs_nonneg a
  -- the velocity is of the order `a`
  have hvb : ∀ s ∈ Icc 0 T, ‖v s‖ ≤ |a| * V := by
    intro s hs
    have hb : ∀ s ∈ Icc 0 T, ‖k • (a • E s (x s) + cross (v s) (a • B s (x s)))‖ ≤
        (|k| * MB) * ‖v s‖ + |a| * (|k| * ME) := by
      intro s _
      have h1 : ‖a • E s (x s)‖ ≤ |a| * ME := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hEb _ _) ha0
      have h2 : ‖cross (v s) (a • B s (x s))‖ ≤ ‖v s‖ * MB := by
        refine (norm_cross_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
        have : |a| * ‖B s (x s)‖ ≤ MB := by
          calc |a| * ‖B s (x s)‖ ≤ 1 * MB :=
                mul_le_mul ha (hBb _ _) (norm_nonneg _) zero_le_one
            _ = MB := one_mul MB
        exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
      rw [norm_smul, Real.norm_eq_abs]
      calc |k| * ‖a • E s (x s) + cross (v s) (a • B s (x s))‖ ≤
            |k| * (|a| * ME + ‖v s‖ * MB) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) hk
        _ = _ := by ring
    have h := norm_le_gronwallBound_of_hasDerivAt (fun s => (htr s).2) hv0 hb s hs
    rw [gronwallBound_zero_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (gronwallBound_mono le_rfl (mul_nonneg hk hME) (mul_nonneg hk hMB) hs.2) ha0)
  -- the error
  set Y : ℝ → E3 × E3 := fun s => (x s - x₀ - a • ξ s, v s - a • η s) with hYdef
  have hY : ∀ s, HasDerivAt Y (v s - a • η s,
      k • (a • E s (x s) + cross (v s) (a • B s (x s))) - a • (k • E s x₀)) s := fun s =>
    ((((htr s).1.sub_const x₀).sub ((hξ s).const_smul a))).prodMk
      (((htr s).2).sub ((hη s).const_smul a))
  have hY0 : Y 0 = 0 := by simp [hYdef, hx0, hv0, hξ0, hη0]
  have hb : ∀ s ∈ Icc 0 T, ‖(v s - a • η s,
      k • (a • E s (x s) + cross (v s) (a • B s (x s))) - a • (k • E s x₀))‖ ≤
      K * ‖Y s‖ + a ^ 2 * ε₀ := by
    intro s hs
    have hy : ‖x s - x₀ - a • ξ s‖ ≤ ‖Y s‖ := norm_fst_le (Y s)
    have hw : ‖v s - a • η s‖ ≤ ‖Y s‖ := norm_snd_le (Y s)
    have hYn := norm_nonneg (Y s)
    have heq : k • (a • E s (x s) + cross (v s) (a • B s (x s))) - a • (k • E s x₀) =
        (k * a) • (E s (x s) - E s x₀) + k • cross (v s) (a • B s (x s)) := by
      simp only [smul_add, smul_sub, smul_smul]
      rw [mul_comm a k]
      abel
    have hx : ‖x s - x₀‖ ≤ ‖Y s‖ + |a| * Ξ := by
      have : x s - x₀ = (x s - x₀ - a • ξ s) + a • ξ s := by abel
      rw [this]
      refine (norm_add_le _ _).trans (add_le_add hy ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hΞ s hs) ha0
    have h1 : ‖(k * a) • (E s (x s) - E s x₀)‖ ≤ |k| * |L| * ‖Y s‖ + a ^ 2 * (|k| * |L| * Ξ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
      have h := hL' s (x s) x₀
      have hkaL : 0 ≤ |k| * |a| * |L| := by positivity
      calc |k| * |a| * ‖E s (x s) - E s x₀‖ ≤ |k| * |a| * (|L| * ‖x s - x₀‖) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ ≤ |k| * |a| * (|L| * (‖Y s‖ + |a| * Ξ)) := by gcongr
        _ = |k| * |a| * |L| * ‖Y s‖ + |a| ^ 2 * (|k| * |L| * Ξ) := by ring
        _ ≤ |k| * 1 * |L| * ‖Y s‖ + a ^ 2 * (|k| * |L| * Ξ) := by
          rw [sq_abs]
          gcongr
        _ = _ := by ring
    have h2 : ‖k • cross (v s) (a • B s (x s))‖ ≤ a ^ 2 * (|k| * V * MB) := by
      rw [norm_smul, Real.norm_eq_abs]
      have hc : ‖cross (v s) (a • B s (x s))‖ ≤ (|a| * V) * (|a| * MB) := by
        refine (norm_cross_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hvb s hs) (mul_le_mul_of_nonneg_left (hBb _ _) ha0) (by positivity)
          (by positivity)
      calc |k| * ‖cross (v s) (a • B s (x s))‖ ≤ |k| * ((|a| * V) * (|a| * MB)) :=
            mul_le_mul_of_nonneg_left hc hk
        _ = |a| ^ 2 * (|k| * V * MB) := by ring
        _ = _ := by rw [sq_abs]
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · simp only
      have : 0 ≤ |k| * |L| * ‖Y s‖ := by positivity
      have : 0 ≤ a ^ 2 * ε₀ := by positivity
      nlinarith
    · simp only
      rw [heq]
      refine (norm_add_le _ _).trans ?_
      have : |k| * |L| * ‖Y s‖ ≤ K * ‖Y s‖ := by
        rw [hKdef]
        nlinarith
      have : a ^ 2 * (|k| * |L| * Ξ) + a ^ 2 * (|k| * V * MB) = a ^ 2 * ε₀ := by
        rw [hε₀def]
        ring
      linarith
  have h := norm_le_gronwallBound_of_hasDerivAt hY hY0 hb t ht
  rw [gronwallBound_zero_mul] at h
  have hC : a ^ 2 * gronwallBound 0 K ε₀ t ≤ gronwallBound 0 K ε₀ T * a ^ 2 := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (gronwallBound_mono le_rfl hε₀ hK ht.2) (sq_nonneg a)
  exact ⟨(norm_fst_le (Y t)).trans (h.trans hC), (norm_snd_le (Y t)).trans (h.trans hC)⟩

/-! ### The incident plane wave -/

/-- The electric field `E(t, x) = cos(ω (t − ⟨n, x⟩)) E₀` of a linearly polarized monochromatic
plane wave of the frequency `ω` travelling in the direction `n`. -/
def waveElectric (ω : ℝ) (n E₀ : E3) (t : ℝ) (x : E3) : E3 :=
  Real.cos (ω * (t - inner ℝ n x)) • E₀

/-- The magnetic field `B = n × E` of the plane wave. -/
def waveMagnetic (ω : ℝ) (n E₀ : E3) (t : ℝ) (x : E3) : E3 :=
  cross n (waveElectric ω n E₀ t x)

/-- The electric field of the plane wave is smooth in the time and the position. -/
theorem contDiff_waveElectric (ω : ℝ) (n E₀ : E3) :
    ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E3 => waveElectric ω n E₀ p.1 p.2 := by
  unfold waveElectric
  have h : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E3 => ω * (p.1 - inner ℝ n p.2) :=
    contDiff_const.mul (contDiff_fst.sub (contDiff_const.inner ℝ contDiff_snd))
  exact (Real.contDiff_cos.comp h).smul contDiff_const

/-- The magnetic field of the plane wave is smooth in the time and the position. -/
theorem contDiff_waveMagnetic (ω : ℝ) (n E₀ : E3) :
    ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E3 => waveMagnetic ω n E₀ p.1 p.2 :=
  contDiff_cross.comp (contDiff_const.prodMk (contDiff_waveElectric ω n E₀))

/-- `|E| ≤ |E₀|`. -/
theorem norm_waveElectric_le (ω : ℝ) (n E₀ : E3) (t : ℝ) (x : E3) :
    ‖waveElectric ω n E₀ t x‖ ≤ ‖E₀‖ := by
  rw [waveElectric, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

/-- `|B| ≤ |E₀|` for a unit vector `n`. -/
theorem norm_waveMagnetic_le (ω : ℝ) {n : E3} (hn : ‖n‖ = 1) (E₀ : E3) (t : ℝ) (x : E3) :
    ‖waveMagnetic ω n E₀ t x‖ ≤ ‖E₀‖ := by
  refine (norm_cross_le _ _).trans ?_
  rw [hn, one_mul]
  exact norm_waveElectric_le ω n E₀ t x

/-- The electric field of the plane wave is Lipschitz in the position, with the constant
`|ω| ‖E₀‖`. -/
theorem norm_waveElectric_sub_le (ω : ℝ) {n : E3} (hn : ‖n‖ = 1) (E₀ : E3) (t : ℝ) (x y : E3) :
    ‖waveElectric ω n E₀ t x - waveElectric ω n E₀ t y‖ ≤ |ω| * ‖E₀‖ * ‖x - y‖ := by
  rw [waveElectric, waveElectric, ← sub_smul, norm_smul, Real.norm_eq_abs]
  have h1 := Real.abs_cos_sub_cos_le (ω * (t - inner ℝ n x)) (ω * (t - inner ℝ n y))
  have h2 : |ω * (t - inner ℝ n x) - ω * (t - inner ℝ n y)| ≤ |ω| * ‖x - y‖ := by
    have : ω * (t - inner ℝ n x) - ω * (t - inner ℝ n y) = -(ω * inner ℝ n (x - y)) := by
      rw [inner_sub_right]
      ring
    rw [this, abs_neg, abs_mul]
    gcongr
    calc |inner ℝ n (x - y)| ≤ ‖n‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
      _ = ‖x - y‖ := by rw [hn, one_mul]
  have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) (norm_nonneg E₀)
  calc _ ≤ |ω| * ‖x - y‖ * ‖E₀‖ := h3
    _ = _ := by ring

/-- The first-order response to the plane wave at `x₀`:
`ξ(t) = (k/ω²)(cos φ − cos(ω (t − ⟨n, x₀⟩)) + ω t sin φ) E₀` with `φ = ω ⟨n, x₀⟩`, the solution of
`ξ̈ = k E(t, x₀)` with `ξ(0) = ξ̇(0) = 0`. The term `ω t sin φ` is a uniform drift; the
oscillation is `−(k/ω²) E(t, x₀)`. -/
def firstOrderResponse (k ω : ℝ) (n E₀ x₀ : E3) (t : ℝ) : E3 :=
  (k / ω ^ 2 * (Real.cos (ω * inner ℝ n x₀) - Real.cos (ω * (t - inner ℝ n x₀)) +
    ω * t * Real.sin (ω * inner ℝ n x₀))) • E₀

/-- The velocity `ξ̇(t) = (k/ω)(sin(ω (t − ⟨n, x₀⟩)) + sin φ) E₀` of the first-order response. -/
def firstOrderVelocity (k ω : ℝ) (n E₀ x₀ : E3) (t : ℝ) : E3 :=
  (k / ω * (Real.sin (ω * (t - inner ℝ n x₀)) + Real.sin (ω * inner ℝ n x₀))) • E₀

/-- `ξ̇` is the derivative of `ξ`. -/
theorem hasDerivAt_firstOrderResponse (k : ℝ) {ω : ℝ} (hω : ω ≠ 0) (n E₀ x₀ : E3) (t : ℝ) :
    HasDerivAt (firstOrderResponse k ω n E₀ x₀) (firstOrderVelocity k ω n E₀ x₀ t) t := by
  set c := inner ℝ n x₀
  have h1 : HasDerivAt (fun t => ω * (t - c)) ω t := by
    simpa using ((hasDerivAt_id t).sub_const c).const_mul ω
  have h3 : HasDerivAt (fun t => ω * t * Real.sin (ω * c)) (ω * Real.sin (ω * c)) t := by
    simpa using ((hasDerivAt_id t).const_mul ω).mul_const (Real.sin (ω * c))
  have h4 := (((h1.cos).const_sub (Real.cos (ω * c))).fun_add h3).const_mul (k / ω ^ 2)
  refine (h4.smul_const E₀).congr_deriv ?_
  rw [firstOrderVelocity]
  congr 1
  field_simp
  ring

/-- `ξ̈ = k E(t, x₀)`. -/
theorem hasDerivAt_firstOrderVelocity (k : ℝ) {ω : ℝ} (hω : ω ≠ 0) (n E₀ x₀ : E3) (t : ℝ) :
    HasDerivAt (firstOrderVelocity k ω n E₀ x₀) (k • waveElectric ω n E₀ t x₀) t := by
  set c := inner ℝ n x₀
  have h1 : HasDerivAt (fun t => ω * (t - c)) ω t := by
    simpa using ((hasDerivAt_id t).sub_const c).const_mul ω
  have h4 := ((h1.sin).add_const (Real.sin (ω * c))).const_mul (k / ω)
  refine (h4.smul_const E₀).congr_deriv ?_
  rw [waveElectric, smul_smul]
  congr 1
  field_simp
  rfl

/-- `ξ(0) = 0`. -/
theorem firstOrderResponse_zero (k ω : ℝ) (n E₀ x₀ : E3) :
    firstOrderResponse k ω n E₀ x₀ 0 = 0 := by
  simp [firstOrderResponse]

/-- `ξ̇(0) = 0`. -/
theorem firstOrderVelocity_zero (k ω : ℝ) (n E₀ x₀ : E3) :
    firstOrderVelocity k ω n E₀ x₀ 0 = 0 := by
  simp [firstOrderVelocity]

/-- The motion in the plane wave of the amplitude `a` exists for all times. -/
theorem exists_trajectory_wave (k a ω : ℝ) {n : E3} (hn : ‖n‖ = 1) (E₀ x₀ v₀ : E3) :
    ∃ x v : ℝ → E3, x 0 = x₀ ∧ v 0 = v₀ ∧
      IsTrajectory k (fun t y => a • waveElectric ω n E₀ t y)
        (fun t y => a • waveMagnetic ω n E₀ t y) x v := by
  refine exists_trajectory k ((contDiff_waveElectric ω n E₀).const_smul a)
    ((contDiff_waveMagnetic ω n E₀).const_smul a) (ME := |a| * ‖E₀‖) (MB := |a| * ‖E₀‖)
    (fun t y => ?_) (fun t y => ?_) x₀ v₀
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_waveElectric_le ω n E₀ t y) (abs_nonneg a)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_waveMagnetic_le ω hn E₀ t y) (abs_nonneg a)

/-- **The weak-wave expansion in a plane wave**: a charge at rest at `x₀` in the plane wave of the
amplitude `a` moves as `x₀ + a ξ(t) + O(a²)` on `[0, T]`, with the first-order response `ξ` of
`ξ̈ = k E₀ cos(ω (t − ⟨n, x₀⟩))`. -/
theorem norm_trajectory_sub_firstOrderResponse_le (k : ℝ) {ω : ℝ} (hω : ω ≠ 0) {n : E3}
    (hn : ‖n‖ = 1) (E₀ x₀ : E3) (T : ℝ) :
    ∃ C, ∀ a : ℝ, |a| ≤ 1 → ∀ x v : ℝ → E3, x 0 = x₀ → v 0 = 0 →
      IsTrajectory k (fun t y => a • waveElectric ω n E₀ t y)
        (fun t y => a • waveMagnetic ω n E₀ t y) x v →
      ∀ t ∈ Icc 0 T, ‖x t - x₀ - a • firstOrderResponse k ω n E₀ x₀ t‖ ≤ C * a ^ 2 ∧
        ‖v t - a • firstOrderVelocity k ω n E₀ x₀ t‖ ≤ C * a ^ 2 :=
  norm_trajectory_sub_firstOrder_le k (T := T) (norm_waveElectric_le ω n E₀)
    (norm_waveMagnetic_le ω hn E₀) (norm_waveElectric_sub_le ω hn E₀) x₀
    (firstOrderResponse_zero k ω n E₀ x₀) (firstOrderVelocity_zero k ω n E₀ x₀)
    (hasDerivAt_firstOrderResponse k hω n E₀ x₀) (hasDerivAt_firstOrderVelocity k hω n E₀ x₀)

/-! ### The incident wave as a field of the library -/

/-- The amplitude `b = −ω⁻¹ Σᵢ E₀ᵢ dxⁱ` of the potential `A = b sin(ℓx)` of the incident wave. -/
def polarizationCovector (ω : ℝ) (E₀ : E3) : FourCovector :=
  -ω⁻¹ • ∑ i : Fin 3, E₀ i • (ContinuousLinearMap.proj i.succ : FourCovector)

/-- `b₀ = 0`. -/
theorem polarizationCovector_single_zero (ω : ℝ) (E₀ : E3) :
    polarizationCovector ω E₀ (Pi.single 0 1) = 0 := by
  simp [polarizationCovector, Fin.sum_univ_three]

/-- `bᵢ = −E₀ᵢ/ω`. -/
theorem polarizationCovector_single_succ (ω : ℝ) (E₀ : E3) (i : Fin 3) :
    polarizationCovector ω E₀ (Pi.single i.succ 1) = -(ω⁻¹ * E₀ i) := by
  fin_cases i <;> simp [polarizationCovector, Fin.sum_univ_three]

/-- The potential of the incident wave, the plane wave `A = b sin(ω (t − ⟨n, x⟩))` of
`planeWave`. -/
def incidentPotential (ω : ℝ) (n E₀ : E3) : Potential :=
  planeWave (wavevector ω (WithLp.ofLp n)) (polarizationCovector ω E₀) Real.sin

/-- The phase of the incident wave at the event `(t, x)` is `ω (t − ⟨n, x⟩)`. -/
theorem wavevector_vector (ω : ℝ) (n : E3) (t : ℝ) (x : E3) :
    wavevector ω (WithLp.ofLp n) (Minkowski.vector t x) = ω * (t - inner ℝ n x) := by
  rw [wavevector_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- The electric field of the incident potential is `E(t, x) = cos(ω (t − ⟨n, x⟩)) E₀`. -/
theorem electricVector_incidentPotential {ω : ℝ} (hω : ω ≠ 0) (n E₀ : E3) (t : ℝ) (x : E3) :
    electricVector (fieldTensor (incidentPotential ω n E₀) (Minkowski.vector t x)) =
      WithLp.ofLp (waveElectric ω n E₀ t x) := by
  ext i
  rw [incidentPotential, electricVector_planeWave _ _ Real.differentiableAt_sin, Real.deriv_sin,
    wavevector_vector, wavevector_single_succ, wavevector_single_zero,
    polarizationCovector_single_zero, polarizationCovector_single_succ]
  simp only [waveElectric, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **The incident wave is transverse** (`transverse_planeWave`): for a unit vector `n` and
`⟨n, E₀⟩ = 0` the magnetic field of the incident potential is `B = n × E` and the flux of energy
along `n` is `S · n = |E|²`. -/
theorem transverse_incidentPotential {ω : ℝ} (hω : ω ≠ 0) {n E₀ : E3} (hn : ‖n‖ = 1)
    (hnE : inner ℝ n E₀ = 0) (t : ℝ) (x : E3) :
    magneticVector (fieldTensor (incidentPotential ω n E₀) (Minkowski.vector t x)) =
        WithLp.ofLp (waveMagnetic ω n E₀ t x) ∧
      ∑ i, poyntingVector (fieldTensor (incidentPotential ω n E₀)) i (Minkowski.vector t x) *
        n i = ‖waveElectric ω n E₀ t x‖ ^ 2 := by
  have hn' : ∑ i, (WithLp.ofLp n) i ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hn, one_pow]
  have hnE' : n 0 * E₀ 0 + n 1 * E₀ 1 + n 2 * E₀ 2 = 0 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hnE
    linarith
  have horth : covectorInner (wavevector ω (WithLp.ofLp n)) (polarizationCovector ω E₀) = 0 := by
    rw [covectorInner_apply, wavevector_single_zero, wavevector_single_one, wavevector_single_two,
      wavevector_single_three, polarizationCovector_single_zero]
    have h1 := polarizationCovector_single_succ ω E₀ 0
    have h2 := polarizationCovector_single_succ ω E₀ 1
    have h3 := polarizationCovector_single_succ ω E₀ 2
    simp only [fin_succ_zero, fin_succ_one, fin_succ_two] at h1 h2 h3
    rw [h1, h2, h3]
    field_simp
    linear_combination hnE'
  obtain ⟨-, hB, -, -, hS, -⟩ := transverse_planeWave hω hn' horth
    (f := Real.sin) (x := Minkowski.vector t x) Real.differentiableAt_sin
  have hE := electricVector_incidentPotential hω n E₀ t x
  refine ⟨?_, ?_⟩
  · rw [← incidentPotential] at hB
    rw [hB, hE, waveMagnetic, ofLp_cross]
  · rw [← incidentPotential] at hS
    simp only [hS, hE, mul_assoc]
    rw [← Finset.mul_sum]
    have : ∑ i, n i * n i = 1 := by
      rw [← hn']
      exact Finset.sum_congr rfl fun i _ => (sq _).symm
    rw [this, mul_one, EuclideanSpace.real_norm_sq_eq]

/-! ### Averages over a period -/

/-- The average `⟨f⟩ = (ω/2π) ∫₀^{2π/ω} f(t) dt` over a period of the frequency `ω`. -/
def periodAverage (ω : ℝ) (f : ℝ → ℝ) : ℝ := ω / (2 * π) * ∫ t in (0 : ℝ)..2 * π / ω, f t

/-- The average is linear. -/
theorem periodAverage_const_mul (ω c : ℝ) (f : ℝ → ℝ) :
    periodAverage ω (fun t => c * f t) = c * periodAverage ω f := by
  simp only [periodAverage, intervalIntegral.integral_const_mul]
  ring

/-- `⟨cos²(ω t + φ)⟩ = 1/2`. -/
theorem periodAverage_cos_sq {ω : ℝ} (hω : ω ≠ 0) (φ : ℝ) :
    periodAverage ω (fun t => Real.cos (ω * t + φ) ^ 2) = 1 / 2 := by
  rw [periodAverage, intervalIntegral.integral_comp_mul_add (fun s => Real.cos s ^ 2) hω φ,
    integral_cos_sq]
  have h : ω * (2 * π / ω) + φ = φ + 2 * π := by
    field_simp
    ring
  rw [h, Real.cos_add_two_pi, Real.sin_add_two_pi, smul_eq_mul, mul_zero, zero_add]
  field_simp
  ring

/-- The averaged flux of energy of the incident wave at the point `x₀`, `⟨S · n⟩`, from the vector
of Poynting of the field of `incidentPotential`. -/
def incidentFlux (ω : ℝ) (n E₀ x₀ : E3) : ℝ :=
  periodAverage ω fun t =>
    ∑ i, poyntingVector (fieldTensor (incidentPotential ω n E₀)) i (Minkowski.vector t x₀) * n i

/-- The averaged flux of the incident wave is `⟨S · n⟩ = |E₀|²/2`. -/
theorem incidentFlux_eq {ω : ℝ} (hω : ω ≠ 0) {n E₀ : E3} (hn : ‖n‖ = 1)
    (hnE : inner ℝ n E₀ = 0) (x₀ : E3) : incidentFlux ω n E₀ x₀ = ‖E₀‖ ^ 2 / 2 := by
  have h : (fun t => ∑ i, poyntingVector (fieldTensor (incidentPotential ω n E₀)) i
      (Minkowski.vector t x₀) * n i) =
      fun t => ‖E₀‖ ^ 2 * Real.cos (ω * t + -(ω * inner ℝ n x₀)) ^ 2 := by
    funext t
    rw [(transverse_incidentPotential hω hn hnE t x₀).2, waveElectric, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have : ω * (t - inner ℝ n x₀) = ω * t + -(ω * inner ℝ n x₀) := by ring
    rw [this, mul_comm]
  rw [incidentFlux, h, periodAverage_const_mul, periodAverage_cos_sq hω]
  ring

/-! ### The cross section -/

/-- The cross section of Thomson `σ_T = (8π/3)(e²/4πm)²` in units with `c = 1` and `div E = k⁰`
(Landau–Lifshitz §78, `(8π/3)(e²/mc²)²` in Gaussian units). -/
def thomsonCrossSection (e m : ℝ) : ℝ := 8 * π / 3 * (e ^ 2 / (4 * π * m)) ^ 2

/-- The total cross section of a charge `e` whose acceleration is `w(t)`, periodic with the
frequency `ω`, in a wave of the averaged incident flux `S`: the averaged power of Larmor
`⟨(2/3)(e²/4π)|w|²⟩` (`integral_angularPower` at `v = 0`) divided by `S` (Landau–Lifshitz
§78). -/
def crossSection (e ω : ℝ) (w : ℝ → E3) (S : ℝ) : ℝ :=
  periodAverage ω (fun t => 2 / 3 * (e ^ 2 / (4 * π)) * ‖w t‖ ^ 2) / S

/-- The differential cross section in the direction `n`: the averaged power radiated per unit
solid angle, `⟨angularPower e 0 w n⟩ = ⟨e² |n × (n × w)|²/16π²⟩`, divided by the averaged incident
flux `S` (Landau–Lifshitz §78). -/
def differentialCrossSection (e ω : ℝ) (w : ℝ → E3) (S : ℝ) (n : E3) : ℝ :=
  periodAverage ω (fun t => angularPower e 0 (w t) n) / S

/-- The angular distribution of a charge at rest: `dI/dΩ = (e²/16π²)(|a|² − ⟨n, a⟩²)`. -/
theorem angularPower_zero (e : ℝ) (a : E3) {n : E3} (hn : ‖n‖ = 1) :
    angularPower e 0 a n = e ^ 2 / (16 * π ^ 2) * (‖a‖ ^ 2 - inner ℝ n a ^ 2) := by
  rw [angularPower_of_inner_eq_zero e (by simp) (inner_zero_left a) hn]
  simp

/-- The power of Larmor of a charge at rest: `∫ dI/dΩ dσ = (2/3)(e²/4π)|a|²`
(`integral_angularPower` at `v = 0`), the integrand of `crossSection`. -/
theorem integral_angularPower_zero (e : ℝ) (a : E3) :
    ∫ n : sphere (0 : E3) 1, angularPower e 0 a n ∂sphereMeasure =
      2 / 3 * (e ^ 2 / (4 * π)) * ‖a‖ ^ 2 := by
  rw [integral_angularPower e (by simp) a]
  have h : cross 0 a = 0 := by
    ext i
    simp [cross]
  simp [h]

/-- **The cross section of Thomson** (Landau–Lifshitz §78): the first-order response of a free
charge at `x₀` to the plane wave `E₀ cos(ω (t − ⟨u, x⟩))` has the acceleration
`ξ̈ = (e/m) E(t, x₀)`; its averaged power of Larmor divided by the averaged incident flux
`incidentFlux` of the field of `incidentPotential` is `σ_T = (8π/3)(e²/4πm)²`, independent of the
frequency. -/
theorem crossSection_eq (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3} (hu : ‖u‖ = 1)
    (huE : inner ℝ u E₀ = 0) (hE₀ : E₀ ≠ 0) (x₀ : E3) :
    crossSection e ω (fun t => (e / m) • waveElectric ω u E₀ t x₀) (incidentFlux ω u E₀ x₀) =
      thomsonCrossSection e m := by
  have h : (fun t => 2 / 3 * (e ^ 2 / (4 * π)) * ‖(e / m) • waveElectric ω u E₀ t x₀‖ ^ 2) =
      fun t => 2 / 3 * (e ^ 2 / (4 * π)) * (e / m) ^ 2 * ‖E₀‖ ^ 2 *
        Real.cos (ω * t + -(ω * inner ℝ u x₀)) ^ 2 := by
    funext t
    rw [waveElectric, smul_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have : ω * (t - inner ℝ u x₀) = ω * t + -(ω * inner ℝ u x₀) := by ring
    rw [this]
    ring
  have hE : ‖E₀‖ ≠ 0 := norm_ne_zero_iff.mpr hE₀
  rw [crossSection, incidentFlux_eq hω hu huE, h, periodAverage_const_mul, periodAverage_cos_sq hω,
    thomsonCrossSection]
  field_simp
  ring

/-- The differential cross section of Thomson in the direction `n`:
`dσ/dΩ = (e²/4πm)² (1 − ⟨n, E₀⟩²/|E₀|²)`. -/
theorem differentialCrossSection_eq_inner (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3}
    (hu : ‖u‖ = 1) (huE : inner ℝ u E₀ = 0) (hE₀ : E₀ ≠ 0) (x₀ : E3) {n : E3} (hn : ‖n‖ = 1) :
    differentialCrossSection e ω (fun t => (e / m) • waveElectric ω u E₀ t x₀)
        (incidentFlux ω u E₀ x₀) n =
      (e ^ 2 / (4 * π * m)) ^ 2 * (1 - inner ℝ n E₀ ^ 2 / ‖E₀‖ ^ 2) := by
  have h : (fun t => angularPower e 0 ((e / m) • waveElectric ω u E₀ t x₀) n) =
      fun t => e ^ 2 / (16 * π ^ 2) * (e / m) ^ 2 * (‖E₀‖ ^ 2 - inner ℝ n E₀ ^ 2) *
        Real.cos (ω * t + -(ω * inner ℝ u x₀)) ^ 2 := by
    funext t
    rw [angularPower_zero e _ hn, waveElectric, smul_smul, norm_smul, Real.norm_eq_abs,
      real_inner_smul_right, mul_pow, sq_abs]
    have : ω * (t - inner ℝ u x₀) = ω * t + -(ω * inner ℝ u x₀) := by ring
    rw [this]
    ring
  have hE : ‖E₀‖ ≠ 0 := norm_ne_zero_iff.mpr hE₀
  rw [differentialCrossSection, incidentFlux_eq hω hu huE, h, periodAverage_const_mul,
    periodAverage_cos_sq hω]
  field_simp
  ring

open InnerProductGeometry in
/-- **The differential cross section of Thomson** (Landau–Lifshitz §78):
`dσ/dΩ = (e²/4πm)² sin²ψ`, with `ψ` the angle between the direction `n` of scattering and the
polarization `E₀` of the incident wave. -/
theorem differentialCrossSection_eq (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3} (hu : ‖u‖ = 1)
    (huE : inner ℝ u E₀ = 0) (hE₀ : E₀ ≠ 0) (x₀ : E3) {n : E3} (hn : ‖n‖ = 1) :
    differentialCrossSection e ω (fun t => (e / m) • waveElectric ω u E₀ t x₀)
        (incidentFlux ω u E₀ x₀) n =
      (e ^ 2 / (4 * π * m)) ^ 2 * Real.sin (angle n E₀) ^ 2 := by
  rw [differentialCrossSection_eq_inner e m hω hu huE hE₀ x₀ hn, Real.sin_sq, cos_angle, hn,
    one_mul, div_pow (inner ℝ n E₀)]

/-- **The total cross section is the integral of the differential one**: over the sphere of
directions, `∫ (e²/4πm)² sin²ψ dΩ = σ_T`. -/
theorem integral_differentialCrossSection (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3}
    (hu : ‖u‖ = 1) (huE : inner ℝ u E₀ = 0) (hE₀ : E₀ ≠ 0) (x₀ : E3) :
    ∫ n : sphere (0 : E3) 1, differentialCrossSection e ω
        (fun t => (e / m) • waveElectric ω u E₀ t x₀) (incidentFlux ω u E₀ x₀) n
        ∂sphereMeasure = thomsonCrossSection e m := by
  have h : ∀ n : sphere (0 : E3) 1, differentialCrossSection e ω
      (fun t => (e / m) • waveElectric ω u E₀ t x₀) (incidentFlux ω u E₀ x₀) n =
      (e ^ 2 / (4 * π * m)) ^ 2 * (1 - inner ℝ (n : E3) E₀ ^ 2 / ‖E₀‖ ^ 2) := fun n =>
    differentialCrossSection_eq_inner e m hω hu huE hE₀ x₀ (norm_eq_of_mem_sphere n)
  have hE : ‖E₀‖ ≠ 0 := norm_ne_zero_iff.mpr hE₀
  rw [integral_congr_ae (Eventually.of_forall h), integral_const_mul,
    integral_sub (integrable_of_continuous continuous_const)
      (integrable_of_continuous (by fun_prop)), integral_const, integral_div, integral_inner_sq,
    sphereMeasure_real_univ, thomsonCrossSection, smul_eq_mul]
  field_simp
  ring

open InnerProductGeometry in
/-- For an orthonormal frame `(e₁, e₂, u)` of `ℝ³` and a unit vector `n`, the mean of `sin²ψ` over
the polarizations `e₁` and `e₂` is `(1 + cos²θ)/2`, with `θ` the angle between `n` and `u`. -/
theorem sin_sq_angle_add_sin_sq_angle {e₁ e₂ u n : E3} (h : Orthonormal ℝ ![e₁, e₂, u])
    (hn : ‖n‖ = 1) :
    (Real.sin (angle n e₁) ^ 2 + Real.sin (angle n e₂) ^ 2) / 2 =
      (1 + Real.cos (angle n u) ^ 2) / 2 := by
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range ![e₁, e₂, u]) := by
    rw [h.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)]
  have hsum := (OrthonormalBasis.mk h hspan).sum_inner_mul_inner n n
  simp only [OrthonormalBasis.coe_mk, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    real_inner_self_eq_norm_sq, hn] at hsum
  have h1 : ‖e₁‖ = 1 := by simpa using h.1 0
  have h2 : ‖e₂‖ = 1 := by simpa using h.1 1
  have h3 : ‖u‖ = 1 := by simpa using h.1 2
  rw [Real.sin_sq, Real.sin_sq, cos_angle, cos_angle, cos_angle, hn, h1, h2, h3]
  rw [real_inner_comm e₁ n, real_inner_comm e₂ n, real_inner_comm u n] at hsum ⊢
  linear_combination (-1 / 2 : ℝ) * hsum

open InnerProductGeometry in
/-- **Unpolarized incident light** (Landau–Lifshitz §78): the mean of the differential cross
sections of the two polarizations `e₁` and `e₂` of an orthonormal frame `(e₁, e₂, u)`, `u` the
direction of incidence, is `(e²/4πm)² (1 + cos²θ)/2`, with `θ` the angle of scattering. -/
theorem differentialCrossSection_unpolarized (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) {e₁ e₂ u : E3}
    (h : Orthonormal ℝ ![e₁, e₂, u]) (x₀ : E3) {n : E3} (hn : ‖n‖ = 1) :
    (differentialCrossSection e ω (fun t => (e / m) • waveElectric ω u e₁ t x₀)
        (incidentFlux ω u e₁ x₀) n +
      differentialCrossSection e ω (fun t => (e / m) • waveElectric ω u e₂ t x₀)
        (incidentFlux ω u e₂ x₀) n) / 2 =
      (e ^ 2 / (4 * π * m)) ^ 2 * ((1 + Real.cos (angle n u) ^ 2) / 2) := by
  have h1 : ‖e₁‖ = 1 := by simpa using h.1 0
  have h2 : ‖e₂‖ = 1 := by simpa using h.1 1
  have h3 : ‖u‖ = 1 := by simpa using h.1 2
  have h31 : inner ℝ u e₁ = 0 := by simpa using h.2 (show (2 : Fin 3) ≠ 0 by decide)
  have h32 : inner ℝ u e₂ = 0 := by simpa using h.2 (show (2 : Fin 3) ≠ 1 by decide)
  have hne1 : e₁ ≠ 0 := fun h0 => by simp [h0] at h1
  have hne2 : e₂ ≠ 0 := fun h0 => by simp [h0] at h2
  rw [differentialCrossSection_eq e m hω h3 h31 hne1 x₀ hn,
    differentialCrossSection_eq e m hω h3 h32 hne2 x₀ hn, ← sin_sq_angle_add_sin_sq_angle h hn]
  ring

/-- The standard frame of `ℝ³` is orthonormal. -/
theorem orthonormal_standardFrame :
    Orthonormal ℝ ![EuclideanSpace.single (0 : Fin 3) (1 : ℝ), EuclideanSpace.single 1 1,
      EuclideanSpace.single 2 1] := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal
  convert h using 1
  funext i
  fin_cases i <;> simp

/-- An instance of the hypotheses of `crossSection_eq`: the wave travelling along the third axis
and polarized along the first. -/
theorem crossSection_standardFrame (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) (x₀ : E3) :
    crossSection e ω (fun t => (e / m) • waveElectric ω (EuclideanSpace.single 2 1)
        (EuclideanSpace.single 0 1) t x₀)
      (incidentFlux ω (EuclideanSpace.single 2 1) (EuclideanSpace.single 0 1) x₀) =
      thomsonCrossSection e m :=
  crossSection_eq e m hω (by simp) (by simp [EuclideanSpace.inner_single_left]) (by simp) x₀

end ProjectAinos.Electrodynamics.Scattering.Thomson
