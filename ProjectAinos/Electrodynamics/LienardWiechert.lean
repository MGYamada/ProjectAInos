/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.RetardedTime
public import ProjectAinos.Electrodynamics.WaveEquation
public import ProjectAinos.Electrodynamics.MovingCharge
public import ProjectAinos.Electrodynamics.Electrostatics
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

/-!
# The potentials of Liénard and Wiechert

The field of a point charge `e` on a subluminal world line `w` (Landau–Lifshitz, *The Classical
Theory of Fields*, §63; units with `c = 1` and `div E = k⁰`, so that the potentials carry `1/4π`).
At an event `(t, x)` with the retarded time `τ` (`SubluminalWorldline.retardedTime`), let
`R = x − r(τ)`, `R = ‖R‖ = t − τ`, `v = ṙ(τ)`, `v̇ = r̈(τ)` and `n = R/R`.

* `lienardWiechert e w`: the potential `A = −φ dt + 𝐚 · d𝐱` (`potentialOf`) with
  `φ = e/(4π(R − R·v))` (`LienardWiechert.scalarPotential`) and `𝐚 = e v/(4π(R − R·v))`
  (`LienardWiechert.vectorPotential`), (63.4), (63.5).
* Off the world line (`SubluminalWorldline.offWorldline`) the potential is smooth
  (`contDiffAt_lienardWiechert`), satisfies the gauge of Lorenz
  (`lorenzDivergence_lienardWiechert`), and its components solve the wave equation
  (`box_lienardWiechert_zero`, `box_lienardWiechert_succ`), so that its field satisfies the
  equations of Maxwell of the vacuum (`maxwell_lienardWiechert`, `excitation_lienardWiechert`,
  by `maxwell_iff_box_of_lorenz`).
* `electricVector_lienardWiechert`: (63.8), `E` is the sum of the velocity field
  `e (1 − v²)(R − R v)/(4π(R − R·v)³)` (`LienardWiechert.velocityField`, of the order `1/R²`) and
  the acceleration field `e R × ((R − R v) × v̇)/(4π(R − R·v)³)`
  (`LienardWiechert.accelerationField`, of the order `1/R`), and
  `magneticVector_lienardWiechert`: (63.9), `B = n × E`. On the light cone of the point `r(τ)`,
  at `(τ + ρ, r(τ) + ρ n)`, the two parts are `e (1 − v²)(n − v)/(4πρ²(1 − n·v)³)` and
  `e n × ((n − v) × v̇)/(4πρ(1 − n·v)³)` (`electricVector_lienardWiechert_lightCone`,
  `magneticVector_lienardWiechert_lightCone`).
* The charge at rest has the Coulomb field `e R/(4πR³)` (`velocityField_rest`,
  `electricVector_lienardWiechert_rest`), and for the uniform motion with the velocity `V` along
  the first axis (`axisWorldline`) the potential is the boosted Coulomb potential of §38
  (`lienardWiechert_axisWorldline`, `lienardWiechert_axisWorldline_eq_movingScalar`), with
  `γ(R − R·v) = ‖x′‖` for the comoving position `x′` (`norm_comovingPosition_axisWorldline`).

The cross products are those of `crossProduct` on `Fin 3 → ℝ`, applied to vectors of
`Space 3 = EuclideanSpace ℝ (Fin 3)` through `WithLp.ofLp`; the acceleration field is defined by
`a × (b × c) = (a·c) b − (a·b) c` in `Space 3` and has the cross-product form
`accelerationField_eq_cross`.

The derivatives are computed with `LienardWiechert.HasGradAt` (a derivative `a dt + b · d𝐱` with
the time part `a` and the gradient `b ∈ Space 3`) and the rules `box_mul`, `box_comp` for the
wave operator of products and compositions, with the pairing `gradPairing` of the gradients. The
gradient of the retarded time is null (`gradPairing_tau`) and `□τ = −2/(R − R·v)` (`box_tau`);
then `□(R − R·v) = (2(1 − v²) + 4R·v̇)/(R − R·v)` (`box_denom`), and `□(1/(R − R·v)) = 0`
(`box_inv_denom`) and `□(vᵢ/(R − R·v)) = 0` (`box_vel_inv_denom`).
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

namespace LienardWiechert

/-! ### Derivatives with a time part and a gradient -/

/-- `f` has at `y` the derivative `a dt + ∇f · d𝐱` with the time derivative `a` and the
gradient `b`. -/
def HasGradAt (f : Spacetime → ℝ) (a : ℝ) (b : Space 3) (y : Spacetime) : Prop :=
  HasFDerivAt f
    (a • (time : Spacetime →L[ℝ] ℝ) + (innerSL ℝ b).comp (space : Spacetime →L[ℝ] Space 3)) y

/-- A derivative whose values are `a δ⁰ + b · 𝛅` is of the form of `HasGradAt`. -/
theorem HasGradAt.of_hasFDerivAt {f : Spacetime → ℝ} {L : Spacetime →L[ℝ] ℝ} {a : ℝ}
    {b : Space 3} {y : Spacetime} (hf : HasFDerivAt f L y)
    (hL : ∀ δ : Spacetime, L δ = a * δ 0 + inner ℝ b (space δ)) : HasGradAt f a b y := by
  have h : L = a • (time : Spacetime →L[ℝ] ℝ) +
      (innerSL ℝ b).comp (space : Spacetime →L[ℝ] Space 3) := by
    ext δ
    simp [hL]
  rw [HasGradAt, ← h]
  exact hf

/-- The derivative of `f` on a vector `δ` is `a δ⁰ + b · 𝛅`. -/
theorem HasGradAt.apply {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) (δ : Spacetime) : fderiv ℝ f y δ = a * δ 0 + inner ℝ b (space δ) := by
  rw [hf.fderiv]
  simp

/-- A function with a time derivative and a gradient is differentiable. -/
theorem HasGradAt.differentiableAt {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) : DifferentiableAt ℝ f y :=
  HasFDerivAt.differentiableAt hf

/-- The derivative `∂₀f` is the time part `a`. -/
theorem HasGradAt.partialAt_zero {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) : partialAt f 0 y = a := by
  rw [partialAt, hf.apply]
  have h0 : space (Pi.single 0 1 : Spacetime) = 0 := by
    ext j
    simp [Fin.succ_ne_zero]
  simp [h0]

/-- The derivative `∂ᵢf` is the component `bᵢ` of the gradient. -/
theorem HasGradAt.partialAt_succ {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) (i : Fin 3) : partialAt f i.succ y = b i := by
  rw [partialAt, hf.apply]
  have hs : space (Pi.single i.succ 1 : Spacetime) = EuclideanSpace.single i 1 := by
    ext j
    simp [Pi.single_apply, Fin.succ_inj]
  simp [hs, Fin.succ_ne_zero, EuclideanSpace.inner_single_right]

/-- The derivative of a sum. -/
theorem HasGradAt.add {f g : Spacetime → ℝ} {a c : ℝ} {b d : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) (hg : HasGradAt g c d y) :
    HasGradAt (fun z => f z + g z) (a + c) (b + d) y :=
  HasGradAt.of_hasFDerivAt (HasFDerivAt.add hf hg) fun δ => by
    simp [inner_add_left]
    ring

/-- The derivative of a difference. -/
theorem HasGradAt.sub {f g : Spacetime → ℝ} {a c : ℝ} {b d : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) (hg : HasGradAt g c d y) :
    HasGradAt (fun z => f z - g z) (a - c) (b - d) y :=
  HasGradAt.of_hasFDerivAt (HasFDerivAt.sub hf hg) fun δ => by
    simp [inner_sub_left]
    ring

/-- The rule of Leibniz. -/
theorem HasGradAt.mul {f g : Spacetime → ℝ} {a c : ℝ} {b d : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) (hg : HasGradAt g c d y) :
    HasGradAt (fun z => f z * g z) (f y * c + g y * a) (f y • d + g y • b) y :=
  HasGradAt.of_hasFDerivAt (HasFDerivAt.mul hf hg) fun δ => by
    simp [inner_add_left, real_inner_smul_left]
    ring

/-- The derivative of a constant multiple. -/
theorem HasGradAt.const_mul {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime}
    (k : ℝ) (hf : HasGradAt f a b y) : HasGradAt (fun z => k * f z) (k * a) (k • b) y :=
  HasGradAt.of_hasFDerivAt (HasFDerivAt.const_mul hf k) fun δ => by
    simp [real_inner_smul_left]
    ring

/-- The chain rule for a function of one variable. -/
theorem HasGradAt.comp {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime}
    {h : ℝ → ℝ} {h' : ℝ} (hh : HasDerivAt h h' (f y)) (hf : HasGradAt f a b y) :
    HasGradAt (fun z => h (f z)) (h' * a) (h' • b) y :=
  HasGradAt.of_hasFDerivAt (hh.comp_hasFDerivAt y hf) fun δ => by
    simp [real_inner_smul_left]
    ring

/-- The derivative of the negative. -/
theorem HasGradAt.neg {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) : HasGradAt (fun z => -f z) (-a) (-b) y :=
  HasGradAt.of_hasFDerivAt (HasFDerivAt.neg hf) fun δ => by
    simp [inner_neg_left]
    ring

/-- The derivative of the inverse. -/
theorem HasGradAt.inv {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) (h0 : f y ≠ 0) :
    HasGradAt (fun z => (f z)⁻¹) (-(f y ^ 2)⁻¹ * a) (-(f y ^ 2)⁻¹ • b) y :=
  hf.comp (h := fun s => s⁻¹) (hasDerivAt_inv h0)

/-- The derivative of the time `t`. -/
theorem hasGradAt_time (y : Spacetime) : HasGradAt (fun z => z 0) 1 0 y :=
  HasGradAt.of_hasFDerivAt (time : Spacetime →L[ℝ] ℝ).hasFDerivAt fun δ => by simp

/-- The derivative of the co-ordinate `xᵢ`. -/
theorem hasGradAt_coord (i : Fin 3) (y : Spacetime) :
    HasGradAt (fun z => z i.succ) 0 (EuclideanSpace.single i 1) y :=
  HasGradAt.of_hasFDerivAt (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ)
    i.succ).hasFDerivAt fun δ => by
    simp [EuclideanSpace.inner_single_left]

/-- The pairing `⟨∂f, ∂g⟩ = −∂₀f ∂₀g + Σᵢ ∂ᵢf ∂ᵢg` of the gradients in the metric of
Minkowski. -/
def gradPairing (f g : Spacetime → ℝ) (y : Spacetime) : ℝ :=
  -(partialAt f 0 y * partialAt g 0 y) + ∑ i : Fin 3, partialAt f i.succ y * partialAt g i.succ y

/-- The pairing of the gradients is `−a c + b · d`. -/
theorem HasGradAt.gradPairing {f g : Spacetime → ℝ} {a c : ℝ} {b d : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) (hg : HasGradAt g c d y) :
    LienardWiechert.gradPairing f g y = -(a * c) + inner ℝ b d := by
  simp only [LienardWiechert.gradPairing, hf.partialAt_zero, hg.partialAt_zero,
    hf.partialAt_succ, hg.partialAt_succ]
  simp [PiLp.inner_apply, mul_comm]

/-! ### The wave operator of products and compositions -/

/-- A `C²` function is differentiable near the point. -/
theorem eventually_differentiableAt {f : Spacetime → ℝ} {y : Spacetime}
    (hf : ContDiffAt ℝ 2 f y) : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ f z :=
  (hf.eventually (by simp)).mono fun _ hz => hz.differentiableAt (by simp)

/-- The derivatives of a `C²` function are differentiable at the point. -/
theorem differentiableAt_partialAt {f : Spacetime → ℝ} {y : Spacetime}
    (hf : ContDiffAt ℝ 2 f y) (μ : Fin 4) : DifferentiableAt ℝ (partialAt f μ) y :=
  (contDiffAt_partialAt (m := 1) hf (by norm_num) μ).differentiableAt one_ne_zero

/-- Functions that agree near a point have the same wave operator there. -/
theorem box_congr {f g : Spacetime → ℝ} {y : Spacetime} (h : f =ᶠ[𝓝 y] g) :
    box f y = box g y := by
  have h1 (μ : Fin 4) : partialAt f μ =ᶠ[𝓝 y] partialAt g μ :=
    h.eventuallyEq_nhds.mono fun z hz => partialAt_congr_of_eventuallyEq hz μ
  simp only [box, partialAt_congr_of_eventuallyEq (h1 _)]

/-- The wave operator of a co-ordinate vanishes. -/
theorem box_coord (μ : Fin 4) (y : Spacetime) : box (fun z => z μ) y = 0 := by
  have h (ν : Fin 4) : partialAt (fun z : Spacetime => z μ) ν =
      fun _ => (Pi.single ν 1 : Spacetime) μ := by
    funext z
    rw [partialAt, show (fun z : Spacetime => z μ) =
      ⇑(ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ) from rfl, ContinuousLinearMap.fderiv]
    rfl
  simp only [box, h, partialAt_const]
  simp

/-- The wave operator of a constant multiple. -/
theorem box_const_mul (k : ℝ) {f : Spacetime → ℝ} {y : Spacetime} (hf : ContDiffAt ℝ 2 f y) :
    box (fun z => k * f z) y = k * box f y := by
  have hev (μ : Fin 4) : partialAt (fun z => k * f z) μ =ᶠ[𝓝 y]
      fun z => k * partialAt f μ z :=
    (eventually_differentiableAt hf).mono fun z hz => partialAt_const_mul k hz μ
  have h2 (μ : Fin 4) : partialAt (partialAt (fun z => k * f z) μ) μ y =
      k * partialAt (partialAt f μ) μ y := by
    rw [partialAt_congr_of_eventuallyEq (hev μ),
      partialAt_const_mul k (differentiableAt_partialAt hf μ)]
  simp only [box, h2]
  rw [mul_add, Finset.mul_sum]
  ring

/-- The wave operator is subtractive on functions that are `C²` near the point. -/
theorem box_sub {f g : Spacetime → ℝ} {y : Spacetime} (hf : ContDiffAt ℝ 2 f y)
    (hg : ContDiffAt ℝ 2 g y) : box (fun z => f z - g z) y = box f y - box g y := by
  have h := box_add hf hg.neg
  rw [box_neg] at h
  simp only [← sub_eq_add_neg] at h
  linarith

/-- The wave operator of a finite sum. -/
theorem box_sum {ι : Type*} (s : Finset ι) {f : ι → Spacetime → ℝ} {y : Spacetime}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) y) :
    box (fun z => ∑ i ∈ s, f i z) y = ∑ i ∈ s, box (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h (μ : Fin 4) : partialAt (fun _ : Spacetime => (0 : ℝ)) μ = fun _ => 0 :=
      funext fun z => partialAt_const 0 μ z
    simp [box, h, partialAt_const]
  | insert j s hj ih =>
    have hs : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) y := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert hj]
    rw [box_add (hf j (Finset.mem_insert_self j s)) (ContDiffAt.sum fun i hi => hs i hi),
      ih hs]

/-- **The wave operator of a product**: `□(fg) = f □g + g □f + 2⟨∂f, ∂g⟩`. -/
theorem box_mul {f g : Spacetime → ℝ} {y : Spacetime} (hf : ContDiffAt ℝ 2 f y)
    (hg : ContDiffAt ℝ 2 g y) :
    box (fun z => f z * g z) y = f y * box g y + g y * box f y + 2 * gradPairing f g y := by
  have hev (μ : Fin 4) : partialAt (fun z => f z * g z) μ =ᶠ[𝓝 y]
      fun z => f z * partialAt g μ z + g z * partialAt f μ z :=
    ((eventually_differentiableAt hf).and (eventually_differentiableAt hg)).mono fun z hz =>
      partialAt_mul hz.1 hz.2 μ
  have hdf := hf.differentiableAt (by simp)
  have hdg := hg.differentiableAt (by simp)
  have h2 (μ : Fin 4) : partialAt (partialAt (fun z => f z * g z) μ) μ y =
      f y * partialAt (partialAt g μ) μ y + partialAt g μ y * partialAt f μ y +
        (g y * partialAt (partialAt f μ) μ y + partialAt f μ y * partialAt g μ y) := by
    rw [partialAt_congr_of_eventuallyEq (hev μ),
      partialAt_add (hdf.fun_mul (differentiableAt_partialAt hg μ))
        (hdg.fun_mul (differentiableAt_partialAt hf μ)),
      partialAt_mul hdf (differentiableAt_partialAt hg μ),
      partialAt_mul hdg (differentiableAt_partialAt hf μ)]
  simp only [box, gradPairing, h2, Fin.sum_univ_three]
  ring

/-- **The wave operator of a composition**: `□(h ∘ f) = h''(f) ⟨∂f, ∂f⟩ + h'(f) □f`. -/
theorem box_comp {f : Spacetime → ℝ} {y : Spacetime} {h h' : ℝ → ℝ} {h'' : ℝ}
    (hf : ContDiffAt ℝ 2 f y) (hh : ∀ᶠ s in 𝓝 (f y), HasDerivAt h (h' s) s)
    (hh' : HasDerivAt h' h'' (f y)) :
    box (fun z => h (f z)) y = h'' * gradPairing f f y + h' (f y) * box f y := by
  have hh2 : ∀ᶠ z in 𝓝 y, HasDerivAt h (h' (f z)) (f z) :=
    hf.continuousAt.tendsto.eventually hh
  have hev (μ : Fin 4) : partialAt (fun z => h (f z)) μ =ᶠ[𝓝 y]
      fun z => h' (f z) * partialAt f μ z :=
    (hh2.and (eventually_differentiableAt hf)).mono fun z hz => by
      have hd : HasFDerivAt (fun z => h (f z)) (h' (f z) • fderiv ℝ f z) z :=
        hz.1.comp_hasFDerivAt z hz.2.hasFDerivAt
      rw [partialAt, hd.fderiv]
      rfl
  have hdf := hf.differentiableAt (by simp)
  have hd' : HasFDerivAt (fun z => h' (f z)) (h'' • fderiv ℝ f y) y :=
    hh'.comp_hasFDerivAt y hdf.hasFDerivAt
  have h2 (μ : Fin 4) : partialAt (partialAt (fun z => h (f z)) μ) μ y =
      h' (f y) * partialAt (partialAt f μ) μ y + partialAt f μ y * (h'' * partialAt f μ y) := by
    rw [partialAt_congr_of_eventuallyEq (hev μ),
      partialAt_mul hd'.differentiableAt (differentiableAt_partialAt hf μ)]
    congr 2
    rw [partialAt, hd'.fderiv]
    rfl
  simp only [box, gradPairing, h2, Fin.sum_univ_three]
  ring

/-! ### The retarded quantities on space-time -/

variable (w : SubluminalWorldline)

/-- The retarded time `τ` of an event of space-time. -/
def tau (y : Spacetime) : ℝ := w.retardedTime (y 0) (space y)

/-- The separation `R = x − r(τ)` from the retarded position. -/
def sep (y : Spacetime) : Space 3 := w.retardedSeparation (y 0) (space y)

/-- The retarded velocity `v = ṙ(τ)`. -/
def vel (y : Spacetime) : Space 3 := w.retardedVelocity (y 0) (space y)

/-- The retarded acceleration `v̇ = r̈(τ)`. -/
def acc (y : Spacetime) : Space 3 := w.retardedAcceleration (y 0) (space y)

/-- The denominator `R − R·v`. -/
def denom (y : Spacetime) : ℝ := w.retardedDenominator (y 0) (space y)

/-- The factor `1 − v² + R·v̇` of the derivatives of `R − R·v`. -/
def kfac (y : Spacetime) : ℝ := 1 - ‖vel w y‖ ^ 2 + inner ℝ (sep w y) (acc w y)

/-- The distance is the time of flight, `R = t − τ`. -/
theorem norm_sep (y : Spacetime) : ‖sep w y‖ = y 0 - tau w y :=
  w.norm_retardedSeparation (y 0) (space y)

/-- `R − R·v` with `R = t − τ`. -/
theorem denom_eq (y : Spacetime) : denom w y = (y 0 - tau w y) - inner ℝ (sep w y) (vel w y) := by
  rw [denom, SubluminalWorldline.retardedDenominator, ← norm_sep]
  rfl

/-- `R − R·v > 0` off the world line. -/
theorem denom_pos {y : Spacetime} (hy : y ∈ w.offWorldline) : 0 < denom w y :=
  w.retardedDenominator_pos hy

/-- The null condition `(t − τ)² = R₁² + R₂² + R₃²`. -/
theorem sep_sq (y : Spacetime) :
    (y 0 - tau w y) ^ 2 = sep w y 0 ^ 2 + sep w y 1 ^ 2 + sep w y 2 ^ 2 := by
  rw [← norm_sep, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- The inner product of `Space 3` in components. -/
theorem inner_eq_sum (u v : Space 3) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- The square of the norm of `Space 3` in components. -/
theorem norm_sq_eq_sum (u : Space 3) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- The component `t ↦ f(t)ᵢ` of a path in space has the component of the derivative. -/
theorem hasDerivAt_component {f : ℝ → Space 3} {s : ℝ} (hf : DifferentiableAt ℝ f s)
    (i : Fin 3) : HasDerivAt (fun s => f s i) (deriv f s i) s :=
  (EuclideanSpace.proj i : Space 3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s hf.hasDerivAt

/-- A component of a smooth path in space is smooth. -/
theorem contDiff_component {f : ℝ → Space 3} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ fun s => f s i :=
  (EuclideanSpace.proj i : Space 3 →L[ℝ] ℝ).contDiff.comp hf

/-- **The derivative of the retarded time**: `∂₀τ = R/(R − R·v)`, `∇τ = −R/(R − R·v)`. -/
theorem hasGradAt_tau {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasGradAt (tau w) ((y 0 - tau w y) / denom w y) (-(denom w y)⁻¹ • sep w y) y :=
  HasGradAt.of_hasFDerivAt (w.hasFDerivAt_retardedTime_spacetime hy) fun δ => by
    simp only [_root_.smul_apply, _root_.sub_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, smul_eq_mul, time_apply, real_inner_smul_left]
    rw [w.norm_retardedSeparation]
    simp only [tau, denom, sep]
    ring

/-- The chain rule for a function of the retarded time. -/
theorem hasGradAt_comp_tau {y : Spacetime} (hy : y ∈ w.offWorldline) {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' (tau w y)) :
    HasGradAt (fun z => g (tau w z)) (g' * ((y 0 - tau w y) / denom w y))
      (g' • (-(denom w y)⁻¹ • sep w y)) y :=
  (hasGradAt_tau w hy).comp hg

/-- The derivative of a component of the separation `R = x − r(τ)`. -/
theorem hasGradAt_sep {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    HasGradAt (fun z => sep w z i) (0 - vel w y i * ((y 0 - tau w y) / denom w y))
      (EuclideanSpace.single i 1 - vel w y i • (-(denom w y)⁻¹ • sep w y)) y :=
  (hasGradAt_coord i y).sub
    (hasGradAt_comp_tau w hy (hasDerivAt_component (w.differentiable_r _) i))

/-- The derivative of the distance `R = t − τ`. -/
theorem hasGradAt_dist {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasGradAt (fun z => z 0 - tau w z) (1 - (y 0 - tau w y) / denom w y)
      (0 - -(denom w y)⁻¹ • sep w y) y :=
  (hasGradAt_time y).sub (hasGradAt_tau w hy)

/-- The derivative of a component of the retarded velocity. -/
theorem hasGradAt_vel {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    HasGradAt (fun z => vel w z i) (acc w y i * ((y 0 - tau w y) / denom w y))
      (acc w y i • (-(denom w y)⁻¹ • sep w y)) y :=
  hasGradAt_comp_tau w hy (hasDerivAt_component (w.contDiff_deriv.differentiable (by simp) _) i)

/-- The time derivative and the gradient of the retarded time as a continuous linear map. -/
def tauDeriv (y : Spacetime) : Spacetime →L[ℝ] ℝ :=
  ((y 0 - tau w y) / denom w y) • (time : Spacetime →L[ℝ] ℝ) +
    (innerSL ℝ (-(denom w y)⁻¹ • sep w y)).comp (space : Spacetime →L[ℝ] Space 3)

/-- The derivative `d𝐱 − v dτ` of the separation `R = x − r(τ)`. -/
theorem hasFDerivAt_sep {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasFDerivAt (sep w)
      ((space : Spacetime →L[ℝ] Space 3) - (tauDeriv w y).smulRight (vel w y)) y := by
  have hr : HasFDerivAt w.r ((1 : ℝ →L[ℝ] ℝ).smulRight (vel w y)) (tau w y) :=
    (w.differentiable_r _).hasDerivAt.hasFDerivAt
  have h := (space : Spacetime →L[ℝ] Space 3).hasFDerivAt.sub (hr.comp y (hasGradAt_tau w hy))
  have hfun : sep w = fun z => space z - w.r (tau w z) := rfl
  rw [hfun]
  refine h.congr_fderiv ?_
  ext δ i
  simp [tauDeriv]
  ring

/-- The derivative `v̇ dτ` of the retarded velocity. -/
theorem hasFDerivAt_vel {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasFDerivAt (vel w) ((tauDeriv w y).smulRight (acc w y)) y := by
  have hr : HasFDerivAt (deriv w.r) ((1 : ℝ →L[ℝ] ℝ).smulRight (acc w y)) (tau w y) :=
    (w.contDiff_deriv.differentiable (by simp) _).hasDerivAt.hasFDerivAt
  have h := hr.comp y (hasGradAt_tau w hy)
  have hfun : vel w = fun z => deriv w.r (tau w z) := rfl
  rw [hfun]
  refine h.congr_fderiv ?_
  ext δ i
  simp [tauDeriv]
  ring

/-- **The derivative of `R − R·v`**: `∂₀(R − R·v) = 1 − K ∂₀τ` and `∇(R − R·v) = −v − K ∇τ`
with `K = 1 − v² + R·v̇`. -/
theorem hasGradAt_denom {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasGradAt (denom w) (1 - kfac w y * ((y 0 - tau w y) / denom w y))
      (-vel w y - kfac w y • (-(denom w y)⁻¹ • sep w y)) y := by
  have hfun : denom w = fun z => (z 0 - tau w z) - inner ℝ (sep w z) (vel w z) :=
    funext (denom_eq w)
  suffices h : HasGradAt (fun z => (z 0 - tau w z) - inner ℝ (sep w z) (vel w z))
      (1 - kfac w y * ((y 0 - tau w y) / denom w y))
      (-vel w y - kfac w y • (-(denom w y)⁻¹ • sep w y)) y by rwa [← hfun] at h
  have hI := (hasFDerivAt_sep w hy).inner ℝ (hasFDerivAt_vel w hy)
  refine HasGradAt.of_hasFDerivAt (HasFDerivAt.sub (hasGradAt_dist w hy) hI) fun δ => ?_
  simp [tauDeriv, kfac, inner_sub_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm (vel w y) (space δ)]
  ring

/-! ### Smoothness off the world line -/

/-- The retarded time is smooth off the world line. -/
theorem contDiffAt_tau {y : Spacetime} (hy : y ∈ w.offWorldline) : ContDiffAt ℝ ∞ (tau w) y :=
  w.contDiffAt_retardedTime_spacetime hy

/-- A smooth function of the retarded time is smooth off the world line. -/
theorem contDiffAt_comp_tau {y : Spacetime} (hy : y ∈ w.offWorldline) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) : ContDiffAt ℝ ∞ (fun z => g (tau w z)) y :=
  hg.contDiffAt.comp y (contDiffAt_tau w hy)

/-- A co-ordinate is smooth. -/
theorem contDiffAt_coord (μ : Fin 4) (y : Spacetime) :
    ContDiffAt ℝ ∞ (fun z : Spacetime => z μ) y :=
  (ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).contDiff.contDiffAt

/-- The components of the separation are smooth off the world line. -/
theorem contDiffAt_sep {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun z => sep w z i) y :=
  (contDiffAt_coord i.succ y).sub (contDiffAt_comp_tau w hy (contDiff_component w.contDiff_r i))

/-- The components of the retarded velocity are smooth off the world line. -/
theorem contDiffAt_vel {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun z => vel w z i) y :=
  contDiffAt_comp_tau w hy (contDiff_component w.contDiff_deriv i)

/-- The distance `t − τ` is smooth off the world line. -/
theorem contDiffAt_dist {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (fun z => z 0 - tau w z) y :=
  (contDiffAt_coord 0 y).sub (contDiffAt_tau w hy)

/-- `R − R·v` is smooth off the world line. -/
theorem contDiffAt_denom {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (denom w) y := by
  have hfun : denom w = fun z => (z 0 - tau w z) - inner ℝ (sep w z) (vel w z) :=
    funext (denom_eq w)
  have hsep : ContDiffAt ℝ ∞ (sep w) y :=
    (space : Spacetime →L[ℝ] Space 3).contDiff.contDiffAt.sub
      (w.contDiff_r.contDiffAt.comp y (contDiffAt_tau w hy))
  have hvel : ContDiffAt ℝ ∞ (vel w) y := w.contDiff_deriv.contDiffAt.comp y (contDiffAt_tau w hy)
  rw [hfun]
  exact (contDiffAt_dist w hy).sub (hsep.inner ℝ hvel)

/-- `1/(R − R·v)` is smooth off the world line. -/
theorem contDiffAt_inv_denom {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (fun z => (denom w z)⁻¹) y :=
  (contDiffAt_denom w hy).inv (denom_pos w hy).ne'

/-- `2 ≤ ∞` among the orders of smoothness. -/
theorem two_le_infty : (2 : ℕ∞ω) ≤ ∞ := by simp

/-! ### The wave operator of the retarded quantities -/

/-- The gradient of the retarded time is a null covector: `⟨∂τ, ∂τ⟩ = 0`. -/
theorem gradPairing_tau {y : Spacetime} (hy : y ∈ w.offWorldline) :
    gradPairing (tau w) (tau w) y = 0 := by
  have hD := (denom_pos w hy).ne'
  rw [(hasGradAt_tau w hy).gradPairing (hasGradAt_tau w hy), real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, norm_sep]
  field_simp
  ring

/-- **The wave operator of the retarded time**: `□τ = −2/(R − R·v)`. -/
theorem box_tau {y : Spacetime} (hy : y ∈ w.offWorldline) :
    box (tau w) y = -2 / denom w y := by
  have hU := w.isOpen_offWorldline
  have hev0 : partialAt (tau w) 0 =ᶠ[𝓝 y] fun z => (z 0 - tau w z) * (denom w z)⁻¹ :=
    eventually_of_mem (hU.mem_nhds hy) fun z hz => by
      rw [(hasGradAt_tau w hz).partialAt_zero, div_eq_mul_inv]
  have hevi (i : Fin 3) : partialAt (tau w) i.succ =ᶠ[𝓝 y]
      fun z => -(sep w z i * (denom w z)⁻¹) :=
    eventually_of_mem (hU.mem_nhds hy) fun z hz => by
      rw [(hasGradAt_tau w hz).partialAt_succ]
      simp
      ring
  have hDinv := (hasGradAt_denom w hy).inv (denom_pos w hy).ne'
  have h0 := ((hasGradAt_dist w hy).mul hDinv).partialAt_zero
  have hi (i : Fin 3) := (((hasGradAt_sep w hy i).mul hDinv).neg).partialAt_succ i
  simp only [box, partialAt_congr_of_eventuallyEq hev0, partialAt_congr_of_eventuallyEq (hevi _),
    h0, hi]
  have hnull := sep_sq w y
  have hDe : denom w y = (y 0 - tau w y) -
      (sep w y 0 * vel w y 0 + sep w y 1 * vel w y 1 + sep w y 2 * vel w y 2) := by
    rw [denom_eq, inner_eq_sum]
  have hD := (denom_pos w hy).ne'
  simp [Fin.sum_univ_three]
  field_simp
  linear_combination (-2 * denom w y) * hDe - kfac w y * hnull

/-- The wave operator of a function of the retarded time: `□g(τ) = g'(τ) □τ`, since the
gradient of `τ` is null. -/
theorem box_comp_tau {y : Spacetime} (hy : y ∈ w.offWorldline) {g g' : ℝ → ℝ}
    (hg : ∀ s, HasDerivAt g (g' s) s) (hg' : Differentiable ℝ g') :
    box (fun z => g (tau w z)) y = g' (tau w y) * (-2 / denom w y) := by
  rw [box_comp ((contDiffAt_tau w hy).of_le two_le_infty) (Eventually.of_forall hg)
    (hg' _).hasDerivAt, gradPairing_tau w hy, box_tau w hy, mul_zero, zero_add]

/-- The wave operator of a component of the separation, `□Rᵢ = −vᵢ □τ`. -/
theorem box_sep {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    box (fun z => sep w z i) y = -vel w y i * (-2 / denom w y) := by
  have h := box_sub ((contDiffAt_coord i.succ y).of_le two_le_infty)
    ((contDiffAt_comp_tau w hy (contDiff_component w.contDiff_r i)).of_le two_le_infty)
  rw [box_coord, box_comp_tau w hy (fun s => hasDerivAt_component (w.differentiable_r s) i)
    ((contDiff_component w.contDiff_deriv i).differentiable (by simp))] at h
  rw [show (fun z => sep w z i) = fun z => z i.succ - w.r (tau w z) i from rfl, h]
  simp only [vel, SubluminalWorldline.retardedVelocity, tau]
  ring

/-- The wave operator of a component of the retarded velocity, `□vᵢ = v̇ᵢ □τ`. -/
theorem box_vel {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    box (fun z => vel w z i) y = acc w y i * (-2 / denom w y) :=
  box_comp_tau w hy
    (fun s => hasDerivAt_component (w.contDiff_deriv.differentiable (by simp) s) i)
    ((contDiff_component w.contDiff_deriv_deriv i).differentiable (by simp))

/-- The wave operator of the distance `R = t − τ`, `□R = −□τ`. -/
theorem box_dist {y : Spacetime} (hy : y ∈ w.offWorldline) :
    box (fun z => z 0 - tau w z) y = 2 / denom w y := by
  rw [box_sub ((contDiffAt_coord 0 y).of_le two_le_infty)
    ((contDiffAt_tau w hy).of_le two_le_infty), box_coord, box_tau w hy]
  ring

/-- The pairing `⟨∂Rᵢ, ∂vᵢ⟩ = −v̇ᵢRᵢ/(R − R·v)`. -/
theorem gradPairing_sep_vel {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    gradPairing (fun z => sep w z i) (fun z => vel w z i) y =
      -(acc w y i * sep w y i) / denom w y := by
  have hD := (denom_pos w hy).ne'
  rw [(hasGradAt_sep w hy i).gradPairing (hasGradAt_vel w hy i)]
  simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.inner_single_left, real_inner_self_eq_norm_sq, norm_sep]
  simp
  field_simp
  ring

/-- **The wave operator of `R − R·v`**: `□(R − R·v) = (2(1 − v²) + 4 R·v̇)/(R − R·v)`. -/
theorem box_denom {y : Spacetime} (hy : y ∈ w.offWorldline) :
    box (denom w) y =
      (2 * (1 - ‖vel w y‖ ^ 2) + 4 * inner ℝ (sep w y) (acc w y)) / denom w y := by
  have hfun : denom w = fun z => (z 0 - tau w z) - ∑ i : Fin 3, sep w z i * vel w z i := by
    funext z
    rw [denom_eq]
    simp [PiLp.inner_apply, mul_comm]
  have hc (i : Fin 3) : ContDiffAt ℝ 2 (fun z => sep w z i * vel w z i) y :=
    (((contDiffAt_sep w hy i).mul (contDiffAt_vel w hy i))).of_le two_le_infty
  conv_lhs => rw [hfun]
  rw [box_sub ((contDiffAt_dist w hy).of_le two_le_infty)
    (ContDiffAt.sum fun i _ => hc i), box_sum _ fun i _ => hc i, box_dist w hy]
  simp only [box_mul ((contDiffAt_sep w hy _).of_le two_le_infty)
    ((contDiffAt_vel w hy _).of_le two_le_infty), box_sep w hy, box_vel w hy,
    gradPairing_sep_vel w hy, Fin.sum_univ_three, inner_eq_sum, norm_sq_eq_sum]
  have hD := (denom_pos w hy).ne'
  field_simp
  ring

/-- The pairing `⟨∂(R − R·v), ∂(R − R·v)⟩ = 1 − v² + 2 R·v̇`. -/
theorem gradPairing_denom {y : Spacetime} (hy : y ∈ w.offWorldline) :
    gradPairing (denom w) (denom w) y = 1 - ‖vel w y‖ ^ 2 + 2 * inner ℝ (sep w y) (acc w y) := by
  have hD := (denom_pos w hy).ne'
  have hDe := denom_eq w y
  rw [(hasGradAt_denom w hy).gradPairing (hasGradAt_denom w hy)]
  rw [real_inner_comm] at hDe
  simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm (vel w y) (sep w y), kfac, norm_smul, norm_neg, Real.norm_eq_abs, mul_pow,
    sq_abs, norm_inv, norm_sep]
  field_simp
  rw [abs_of_pos (denom_pos w hy)]
  linear_combination
    (-2 * denom w y ^ 3 * (1 - ‖vel w y‖ ^ 2 + inner ℝ (sep w y) (acc w y))) * hDe

/-- **The wave operator of `1/(R − R·v)` vanishes** off the world line. -/
theorem box_inv_denom {y : Spacetime} (hy : y ∈ w.offWorldline) :
    box (fun z => (denom w z)⁻¹) y = 0 := by
  have hD := (denom_pos w hy).ne'
  have hh : ∀ᶠ s in 𝓝 (denom w y), HasDerivAt (fun s : ℝ => s⁻¹) (-(s ^ 2)⁻¹) s :=
    (eventually_ne_nhds hD).mono fun s hs => hasDerivAt_inv hs
  have hh' : HasDerivAt (fun s : ℝ => -(s ^ 2)⁻¹) (2 * (denom w y ^ 3)⁻¹) (denom w y) := by
    have h := ((hasDerivAt_pow 2 (denom w y)).inv (pow_ne_zero 2 hD)).neg
    convert h using 1
    norm_num
    field_simp
  rw [box_comp ((contDiffAt_denom w hy).of_le two_le_infty) hh hh', gradPairing_denom w hy,
    box_denom w hy]
  field_simp
  ring

/-- The pairing `⟨∂vᵢ, ∂(1/(R − R·v))⟩ = v̇ᵢ/(R − R·v)²`. -/
theorem gradPairing_vel_inv_denom {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    gradPairing (fun z => vel w z i) (fun z => (denom w z)⁻¹) y = acc w y i / denom w y ^ 2 := by
  have hD := (denom_pos w hy).ne'
  have hDe := denom_eq w y
  rw [(hasGradAt_vel w hy i).gradPairing ((hasGradAt_denom w hy).inv hD)]
  simp only [inner_sub_right, inner_neg_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_sep, kfac]
  field_simp
  linear_combination (-(acc w y i * denom w y)) * hDe

/-- **The wave operator of `vᵢ/(R − R·v)` vanishes** off the world line. -/
theorem box_vel_inv_denom {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    box (fun z => vel w z i * (denom w z)⁻¹) y = 0 := by
  have hD := (denom_pos w hy).ne'
  rw [box_mul ((contDiffAt_vel w hy i).of_le two_le_infty)
    ((contDiffAt_inv_denom w hy).of_le two_le_infty), box_inv_denom w hy, box_vel w hy,
    gradPairing_vel_inv_denom w hy]
  field_simp
  ring

/-! ### The potentials -/

/-- The scalar potential `φ = e/(4π(R − R·v))` of Liénard and Wiechert (63.5). -/
def scalarPotential (e : ℝ) (w : SubluminalWorldline) (y : Spacetime) : ℝ :=
  e / (4 * Real.pi * w.retardedDenominator (y 0) (space y))

/-- The vector potential `𝐚 = e v/(4π(R − R·v))` of Liénard and Wiechert (63.5). -/
def vectorPotential (e : ℝ) (w : SubluminalWorldline) (y : Spacetime) : Fin 3 → ℝ :=
  fun i => e * w.retardedVelocity (y 0) (space y) i /
    (4 * Real.pi * w.retardedDenominator (y 0) (space y))

/-- The scalar potential is `(e/4π) (R − R·v)⁻¹`. -/
theorem scalarPotential_eq (e : ℝ) :
    scalarPotential e w = fun z => e / (4 * Real.pi) * (denom w z)⁻¹ := by
  funext z
  simp only [scalarPotential, denom]
  ring

/-- The components of the vector potential are `(e/4π) vᵢ (R − R·v)⁻¹`. -/
theorem vectorPotential_eq (e : ℝ) (i : Fin 3) :
    (fun z => vectorPotential e w z i) =
      fun z => e / (4 * Real.pi) * (vel w z i * (denom w z)⁻¹) := by
  funext z
  simp only [vectorPotential, vel, denom]
  ring

/-- The derivative of the scalar potential off the world line. -/
theorem hasGradAt_scalarPotential (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasGradAt (scalarPotential e w)
      (e / (4 * Real.pi) * (-(denom w y ^ 2)⁻¹ * (1 - kfac w y * ((y 0 - tau w y) / denom w y))))
      ((e / (4 * Real.pi)) • (-(denom w y ^ 2)⁻¹ •
        (-vel w y - kfac w y • (-(denom w y)⁻¹ • sep w y)))) y := by
  rw [scalarPotential_eq]
  exact (((hasGradAt_denom w hy).inv (denom_pos w hy).ne').const_mul _)

/-- The derivative of a component of the vector potential off the world line. -/
theorem hasGradAt_vectorPotential (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline)
    (i : Fin 3) :
    HasGradAt (fun z => vectorPotential e w z i)
      (e / (4 * Real.pi) * (vel w y i * (-(denom w y ^ 2)⁻¹ *
        (1 - kfac w y * ((y 0 - tau w y) / denom w y))) +
          (denom w y)⁻¹ * (acc w y i * ((y 0 - tau w y) / denom w y))))
      ((e / (4 * Real.pi)) • (vel w y i • (-(denom w y ^ 2)⁻¹ •
        (-vel w y - kfac w y • (-(denom w y)⁻¹ • sep w y))) +
          (denom w y)⁻¹ • (acc w y i • (-(denom w y)⁻¹ • sep w y)))) y := by
  rw [vectorPotential_eq]
  exact (((hasGradAt_vel w hy i).mul ((hasGradAt_denom w hy).inv (denom_pos w hy).ne')).const_mul _)

/-- The scalar potential is smooth off the world line. -/
theorem contDiffAt_scalarPotential (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (scalarPotential e w) y := by
  rw [scalarPotential_eq]
  exact contDiffAt_const.mul (contDiffAt_inv_denom w hy)

/-- The components of the vector potential are smooth off the world line. -/
theorem contDiffAt_vectorPotential (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline)
    (i : Fin 3) : ContDiffAt ℝ ∞ (fun z => vectorPotential e w z i) y := by
  rw [vectorPotential_eq]
  exact contDiffAt_const.mul ((contDiffAt_vel w hy i).mul (contDiffAt_inv_denom w hy))

end LienardWiechert

open LienardWiechert

/-- **The potentials of Liénard and Wiechert** of the point charge `e` on the world line `w`
(Landau–Lifshitz (63.4), (63.5)): `A = −φ dt + 𝐚 · d𝐱` with `φ = e/(4π(R − R·v))` and
`𝐚 = e v/(4π(R − R·v))`, where `R = x − r(τ)`, `R = ‖R‖ = t − τ` and `v = ṙ(τ)` are taken at the
retarded time `τ` of the event. -/
def lienardWiechert (e : ℝ) (w : SubluminalWorldline) : Potential :=
  potentialOf (scalarPotential e w) (vectorPotential e w)

variable (w : SubluminalWorldline)

/-- The time component of the potential is `−φ`. -/
theorem potentialComponent_lienardWiechert_zero (e : ℝ) :
    potentialComponent (lienardWiechert e w) 0 = fun y => -scalarPotential e w y := by
  funext y
  rw [potentialComponent, lienardWiechert, potentialOf_apply]
  simp

/-- The spatial components of the potential are the components of `𝐚`. -/
theorem potentialComponent_lienardWiechert_succ (e : ℝ) (i : Fin 3) :
    potentialComponent (lienardWiechert e w) i.succ = fun y => vectorPotential e w y i := by
  funext y
  rw [potentialComponent, lienardWiechert, potentialOf_apply]
  simp [Pi.single_apply]

/-- The potential is smooth off the world line. -/
theorem contDiffAt_lienardWiechert (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (lienardWiechert e w) y := by
  unfold lienardWiechert potentialOf
  refine oneCovector.symm.contDiff.contDiffAt.comp y ?_
  exact ((contDiffAt_scalarPotential w e hy).neg.smul contDiffAt_const).add
    (ContDiffAt.sum fun i _ => (contDiffAt_vectorPotential w e hy i).smul contDiffAt_const)

/-- The potential is smooth on the set of the events off the world line. -/
theorem contDiffOn_lienardWiechert (e : ℝ) :
    ContDiffOn ℝ ∞ (lienardWiechert e w) w.offWorldline :=
  fun _ hy => (contDiffAt_lienardWiechert w e hy).contDiffWithinAt

/-- **The potentials of Liénard and Wiechert satisfy the gauge of Lorenz** off the world line:
`∂^μ A_μ = ∂ₜφ + div 𝐚 = 0`. -/
theorem lorenzDivergence_lienardWiechert (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    lorenzDivergence (lienardWiechert e w) y = 0 := by
  rw [lorenzDivergence, potentialComponent_lienardWiechert_zero, partialAt_neg,
    (hasGradAt_scalarPotential w e hy).partialAt_zero]
  simp only [potentialComponent_lienardWiechert_succ,
    (hasGradAt_vectorPotential w e hy _).partialAt_succ]
  have hD := (denom_pos w hy).ne'
  have hDe := denom_eq w y
  rw [inner_eq_sum] at hDe
  simp [Fin.sum_univ_three, kfac, inner_eq_sum, norm_sq_eq_sum]
  field_simp
  linear_combination (-e * (1 - (vel w y 0 ^ 2 + vel w y 1 ^ 2 + vel w y 2 ^ 2) +
    (sep w y 0 * acc w y 0 + sep w y 1 * acc w y 1 + sep w y 2 * acc w y 2))) * hDe

/-- **The time component of the potential solves the wave equation** off the world line:
`□A₀ = 0`. -/
theorem box_lienardWiechert_zero (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    box (potentialComponent (lienardWiechert e w) 0) y = 0 := by
  rw [potentialComponent_lienardWiechert_zero, box_neg, scalarPotential_eq,
    box_const_mul _ ((contDiffAt_inv_denom w hy).of_le two_le_infty), box_inv_denom w hy,
    mul_zero, neg_zero]

/-- **The spatial components of the potential solve the wave equation** off the world line:
`□aᵢ = 0`. -/
theorem box_lienardWiechert_succ (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline)
    (i : Fin 3) : box (potentialComponent (lienardWiechert e w) i.succ) y = 0 := by
  rw [potentialComponent_lienardWiechert_succ, vectorPotential_eq,
    box_const_mul _ (((contDiffAt_vel w hy i).mul (contDiffAt_inv_denom w hy)).of_le
      two_le_infty), box_vel_inv_denom w hy i, mul_zero]

/-- **The field of the potentials of Liénard and Wiechert satisfies the equations of Maxwell of
the vacuum** off the world line: `div B = 0`, `∂ₜB + curl E = 0`, `div E = 0` and
`curl B − ∂ₜE = 0`. -/
theorem maxwell_lienardWiechert (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    (divergence3 (magneticField (fieldTensor (lienardWiechert e w))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (lienardWiechert e w)) i) 0 y +
        curl (electricField (fieldTensor (lienardWiechert e w))) y i = 0) ∧
    divergence3 (electricField (fieldTensor (lienardWiechert e w))) y = 0 ∧
    ∀ i, curl (magneticField (fieldTensor (lienardWiechert e w))) y i -
        partialAt (electricField (fieldTensor (lienardWiechert e w)) i) 0 y = 0 := by
  have h := (maxwell_iff_box_of_lorenz w.isOpen_offWorldline
    ((contDiffOn_lienardWiechert w e).of_le two_le_infty)
    (fun z hz => lorenzDivergence_lienardWiechert w e hz) (fun _ => 0)).mpr
    (fun z hz => ⟨by simp [box_lienardWiechert_zero w e hz],
      fun i => by simp [box_lienardWiechert_succ w e hz i]⟩) y hy
  simpa using h

/-- Off the world line the field of the potentials of Liénard and Wiechert solves the equation
of the vacuum `d⋆F = 0`. -/
theorem excitation_lienardWiechert (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    exteriorDerivative (fun z => -star (fieldTensor (lienardWiechert e w) z)) y = 0 := by
  have h := (excitation_iff_box_of_lorenz w.isOpen_offWorldline
    ((contDiffOn_lienardWiechert w e).of_le two_le_infty)
    (fun z hz => lorenzDivergence_lienardWiechert w e hz) (fun _ => 0)).mpr
    (fun z hz => ⟨by simp [box_lienardWiechert_zero w e hz],
      fun i => by simp [box_lienardWiechert_succ w e hz i]⟩) y hy
  rwa [MovingCharge.matterCurrentForm_zero] at h

/-! ### The fields -/

namespace LienardWiechert

/-- The **velocity field** of a point charge, the first term of Landau–Lifshitz (63.8),
`e (1 − v²)(R − R v)/(4π(R − R·v)³)`; it falls off as `1/R²`. -/
def velocityField (e : ℝ) (w : SubluminalWorldline) (t : ℝ) (x : Space 3) : Space 3 :=
  (e * (1 - ‖w.retardedVelocity t x‖ ^ 2) / (4 * Real.pi * w.retardedDenominator t x ^ 3)) •
    (w.retardedSeparation t x - ‖w.retardedSeparation t x‖ • w.retardedVelocity t x)

/-- The **acceleration field** of a point charge, the second term of Landau–Lifshitz (63.8),
`e R × ((R − R v) × v̇)/(4π(R − R·v)³)`, written with `a × (b × c) = (a·c) b − (a·b) c`
(`accelerationField_eq_cross`); it falls off as `1/R`. -/
def accelerationField (e : ℝ) (w : SubluminalWorldline) (t : ℝ) (x : Space 3) : Space 3 :=
  (e / (4 * Real.pi * w.retardedDenominator t x ^ 3)) •
    (inner ℝ (w.retardedSeparation t x) (w.retardedAcceleration t x) •
        (w.retardedSeparation t x - ‖w.retardedSeparation t x‖ • w.retardedVelocity t x) -
      inner ℝ (w.retardedSeparation t x)
          (w.retardedSeparation t x - ‖w.retardedSeparation t x‖ • w.retardedVelocity t x) •
        w.retardedAcceleration t x)

/-- `∂_μ f = bᵢ` for `μ = i + 1`. -/
theorem HasGradAt.partialAt_succ' {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime}
    (hf : HasGradAt f a b y) {μ : Fin 4} (i : Fin 3) (h : μ = i.succ) : partialAt f μ y = b i :=
  h ▸ hf.partialAt_succ i

end LienardWiechert

/-- **The electric field of a point charge** (Landau–Lifshitz (63.8)) off the world line: the
sum of the velocity field `e (1 − v²)(R − R v)/(4π(R − R·v)³)` and the acceleration field
`e R × ((R − R v) × v̇)/(4π(R − R·v)³)`, at the retarded time. -/
theorem electricVector_lienardWiechert (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    electricVector (fieldTensor (lienardWiechert e w) y) =
      WithLp.ofLp (velocityField e w (y 0) (space y) + accelerationField e w (y 0) (space y)) := by
  have hA1 : ContDiffAt ℝ 1 (lienardWiechert e w) y :=
    (contDiffAt_lienardWiechert w e hy).of_le (by simp)
  funext i
  have h := (electricField_fieldTensor_eventuallyEq hA1 i).self_of_nhds
  change electricField (fieldTensor (lienardWiechert e w)) i y = _
  rw [h]
  beta_reduce
  rw [potentialComponent_lienardWiechert_zero, partialAt_neg,
    potentialComponent_lienardWiechert_succ, (hasGradAt_scalarPotential w e hy).partialAt_succ,
    (hasGradAt_vectorPotential w e hy i).partialAt_zero]
  have hD := (denom_pos w hy).ne'
  have hDe := denom_eq w y
  simp only [velocityField, accelerationField, kfac, WithLp.ofLp_add, WithLp.ofLp_smul,
    WithLp.ofLp_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, PiLp.smul_apply, PiLp.sub_apply,
    PiLp.neg_apply]
  change _ = _ * ((sep w y) i - ‖sep w y‖ * (vel w y) i) + _
  rw [show w.retardedDenominator (y 0) (space y) = denom w y from rfl,
    show w.retardedSeparation (y 0) (space y) = sep w y from rfl,
    show w.retardedVelocity (y 0) (space y) = vel w y from rfl,
    show w.retardedAcceleration (y 0) (space y) = acc w y from rfl, norm_sep]
  field_simp
  linear_combination (-(e * (y 0 - tau w y) * acc w y i)) * hDe

/-- **The magnetic field of a point charge** is `B = n × E` (Landau–Lifshitz (63.9)) off the
world line, with the direction `n = R/R` from the retarded position. -/
theorem magneticVector_lienardWiechert (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    magneticVector (fieldTensor (lienardWiechert e w) y) =
      crossProduct (WithLp.ofLp (w.retardedDirection (y 0) (space y)))
        (electricVector (fieldTensor (lienardWiechert e w) y)) := by
  have hA1 : ContDiffAt ℝ 1 (lienardWiechert e w) y :=
    (contDiffAt_lienardWiechert w e hy).of_le (by simp)
  obtain ⟨h0, h1, h2⟩ := magneticField_fieldTensor_eventuallyEq hA1
  have hp1 : potentialComponent (lienardWiechert e w) 1 = fun z => vectorPotential e w z 0 :=
    potentialComponent_lienardWiechert_succ w e 0
  have hp2 : potentialComponent (lienardWiechert e w) 2 = fun z => vectorPotential e w z 1 :=
    potentialComponent_lienardWiechert_succ w e 1
  have hp3 : potentialComponent (lienardWiechert e w) 3 = fun z => vectorPotential e w z 2 :=
    potentialComponent_lienardWiechert_succ w e 2
  have hb (j : Fin 3) {μ : Fin 4} (k : Fin 3) (h : μ = k.succ) :=
    (hasGradAt_vectorPotential w e hy j).partialAt_succ' k h
  have hD := (denom_pos w hy).ne'
  have hR : y 0 - tau w y ≠ 0 := by
    rw [← norm_sep]
    exact norm_ne_zero_iff.mpr (w.retardedSeparation_ne_zero hy)
  have hDe := denom_eq w y
  rw [electricVector_lienardWiechert w e hy]
  have key (j k : Fin 3) {μ ν : Fin 4} (hμ : μ = j.succ) (hν : ν = k.succ) :
      partialAt (fun z => vectorPotential e w z k) μ y -
          partialAt (fun z => vectorPotential e w z j) ν y =
        WithLp.ofLp (w.retardedDirection (y 0) (space y)) j *
            WithLp.ofLp (velocityField e w (y 0) (space y) +
              accelerationField e w (y 0) (space y)) k -
          WithLp.ofLp (w.retardedDirection (y 0) (space y)) k *
            WithLp.ofLp (velocityField e w (y 0) (space y) +
              accelerationField e w (y 0) (space y)) j := by
    rw [hb k j hμ, hb j k hν]
    simp only [velocityField, accelerationField, SubluminalWorldline.retardedDirection, kfac,
      smul_eq_mul, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      PiLp.smul_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.add_apply]
    rw [show w.retardedDenominator (y 0) (space y) = denom w y from rfl,
      show w.retardedSeparation (y 0) (space y) = sep w y from rfl,
      show w.retardedVelocity (y 0) (space y) = vel w y from rfl,
      show w.retardedAcceleration (y 0) (space y) = acc w y from rfl, norm_sep]
    field_simp
    linear_combination e * (y 0 - tau w y) * (sep w y k * acc w y j - sep w y j * acc w y k) * hDe
  ext k
  fin_cases k
  · change magneticField (fieldTensor (lienardWiechert e w)) 0 y = _
    rw [h0.self_of_nhds]
    beta_reduce
    rw [hp3, hp2, key 1 2 (μ := 2) (ν := 3) rfl rfl]
    simp [cross_apply]
  · change magneticField (fieldTensor (lienardWiechert e w)) 1 y = _
    rw [h1.self_of_nhds]
    beta_reduce
    rw [hp1, hp3, key 2 0 (μ := 3) (ν := 1) rfl rfl]
    simp [cross_apply]
  · change magneticField (fieldTensor (lienardWiechert e w)) 2 y = _
    rw [h2.self_of_nhds]
    beta_reduce
    rw [hp2, hp1, key 0 1 (μ := 1) (ν := 2) rfl rfl]
    simp [cross_apply]

namespace LienardWiechert

/-- The acceleration field is `e R × ((R − R v) × v̇)/(4π(R − R·v)³)`, with the cross product
`crossProduct` of `Fin 3 → ℝ`. -/
theorem accelerationField_eq_cross (e : ℝ) (t : ℝ) (x : Space 3) :
    WithLp.ofLp (accelerationField e w t x) =
      (e / (4 * Real.pi * w.retardedDenominator t x ^ 3)) •
        crossProduct (WithLp.ofLp (w.retardedSeparation t x))
          (crossProduct (WithLp.ofLp (w.retardedSeparation t x -
              ‖w.retardedSeparation t x‖ • w.retardedVelocity t x))
            (WithLp.ofLp (w.retardedAcceleration t x))) := by
  ext i
  fin_cases i <;> simp [accelerationField, cross_apply, inner_eq_sum] <;> left <;> ring

/-- An event `(τ + ρ, r(τ) + ρ n)` with `ρ > 0` on the future light cone of the point `r(τ)` of
the world line lies off the world line. -/
theorem mem_offWorldline_lightCone {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    Minkowski.vector (τ + ρ) (w.r τ + ρ • n) ∈ w.offWorldline := by
  have h : w.retardedTime (τ + ρ) (w.r τ + ρ • n) = τ := by
    have := w.retardedTime_add_norm τ (ρ • n)
    rwa [norm_smul, hn, mul_one, Real.norm_of_nonneg hρ.le] at this
  change space (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)) ≠
    w.r (Minkowski.vector (τ + ρ) (w.r τ + ρ • n) 0)
  rw [space_vector, vector_zero, ← w.retardedTime_lt_iff, h]
  linarith

/-- The retarded quantities at the event `(τ + ρ, r(τ) + ρ n)` with `ρ ≥ 0` and `‖n‖ = 1`. -/
theorem retardedTime_lightCone {τ ρ : ℝ} (hρ : 0 ≤ ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    w.retardedTime (τ + ρ) (w.r τ + ρ • n) = τ := by
  have := w.retardedTime_add_norm τ (ρ • n)
  rwa [norm_smul, hn, mul_one, Real.norm_of_nonneg hρ] at this

/-- **The velocity field on the light cone**: at the distance `ρ` in the direction `n` from the
retarded position `r(τ)`, the velocity field is `e (1 − v²)(n − v)/(4πρ²(1 − n·v)³)`. -/
theorem velocityField_lightCone (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    velocityField e w (τ + ρ) (w.r τ + ρ • n) =
      (e * (1 - ‖deriv w.r τ‖ ^ 2) /
        (4 * Real.pi * ρ ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) • (n - deriv w.r τ) := by
  have hτ := retardedTime_lightCone w (τ := τ) hρ.le hn
  have hv : inner ℝ n (deriv w.r τ) < 1 := by
    have h1 := real_inner_le_norm n (deriv w.r τ)
    rw [hn, one_mul] at h1
    linarith [w.norm_deriv_le τ, w.v₀_lt_one]
  have hv' : 1 - inner ℝ n (deriv w.r τ) ≠ 0 := by linarith
  simp only [velocityField, SubluminalWorldline.retardedDenominator,
    SubluminalWorldline.retardedSeparation, SubluminalWorldline.retardedVelocity, hτ,
    add_sub_cancel_left, norm_smul, hn, Real.norm_of_nonneg hρ.le, mul_one,
    real_inner_smul_left]
  rw [← smul_sub, smul_smul]
  congr 1
  field_simp

/-- **The acceleration field on the light cone**: at the distance `ρ` in the direction `n` from
the retarded position `r(τ)`, the acceleration field is `e n × ((n − v) × v̇)/(4πρ(1 − n·v)³)`,
written as `e ((n·v̇)(n − v) − (n·(n − v)) v̇)/(4πρ(1 − n·v)³)`; it falls off as `1/ρ`. -/
theorem accelerationField_lightCone (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3}
    (hn : ‖n‖ = 1) :
    accelerationField e w (τ + ρ) (w.r τ + ρ • n) =
      (e / (4 * Real.pi * ρ * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) •
        (inner ℝ n (deriv (deriv w.r) τ) • (n - deriv w.r τ) -
          inner ℝ n (n - deriv w.r τ) • deriv (deriv w.r) τ) := by
  have hτ := retardedTime_lightCone w (τ := τ) hρ.le hn
  have hv : inner ℝ n (deriv w.r τ) < 1 := by
    have h1 := real_inner_le_norm n (deriv w.r τ)
    rw [hn, one_mul] at h1
    linarith [w.norm_deriv_le τ, w.v₀_lt_one]
  have hv' : 1 - inner ℝ n (deriv w.r τ) ≠ 0 := by linarith
  simp only [accelerationField, SubluminalWorldline.retardedDenominator,
    SubluminalWorldline.retardedSeparation, SubluminalWorldline.retardedVelocity,
    SubluminalWorldline.retardedAcceleration, hτ, add_sub_cancel_left, norm_smul, hn,
    Real.norm_of_nonneg hρ.le, mul_one, real_inner_smul_left]
  ext i
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, inner_sub_right,
    real_inner_smul_right]
  field_simp

end LienardWiechert

/-! ### The uniform motion -/

namespace LienardWiechert

/-- The acceleration vanishes on the world line of the uniform motion. -/
theorem deriv_deriv_uniform (r₀ v : Space 3) (hv : ‖v‖ < 1) (s : ℝ) :
    deriv (deriv (SubluminalWorldline.uniform r₀ v hv).r) s = 0 := by
  have h : deriv (SubluminalWorldline.uniform r₀ v hv).r = fun _ => v :=
    funext (SubluminalWorldline.deriv_uniform r₀ v hv)
  rw [h, deriv_const]

/-- **There is no acceleration field in the uniform motion.** -/
theorem accelerationField_uniform (e : ℝ) (r₀ v : Space 3) (hv : ‖v‖ < 1) (t : ℝ)
    (x : Space 3) : accelerationField e (SubluminalWorldline.uniform r₀ v hv) t x = 0 := by
  simp [accelerationField, SubluminalWorldline.retardedAcceleration, deriv_deriv_uniform]

/-- **The velocity field of a charge at rest is the Coulomb field** `e R/(4πR³)` of
`Electrostatics.pointChargeField`. -/
theorem velocityField_rest (e : ℝ) (r₀ : Space 3) (t : ℝ) (x : Space 3) :
    velocityField e (SubluminalWorldline.rest r₀) t x =
      Electrostatics.pointChargeField e (x - r₀) := by
  have hv (s : ℝ) : deriv (SubluminalWorldline.rest r₀).r s = 0 :=
    SubluminalWorldline.deriv_uniform r₀ 0 _ s
  have hr (s : ℝ) : (SubluminalWorldline.rest r₀).r s = r₀ := by
    simp [SubluminalWorldline.rest, SubluminalWorldline.uniform]
  simp [velocityField, Electrostatics.pointChargeField, SubluminalWorldline.retardedDenominator,
    SubluminalWorldline.retardedSeparation, SubluminalWorldline.retardedVelocity, hv, hr]

end LienardWiechert

/-- **The field of a charge at rest is the Coulomb field** `E = e R/(4πR³)` off the world line. -/
theorem electricVector_lienardWiechert_rest (e : ℝ) (r₀ : Space 3) {y : Spacetime}
    (hy : y ∈ (SubluminalWorldline.rest r₀).offWorldline) :
    electricVector (fieldTensor (lienardWiechert e
        (SubluminalWorldline.rest r₀)) y) =
      WithLp.ofLp (Electrostatics.pointChargeField e (space y - r₀)) := by
  rw [electricVector_lienardWiechert _ e hy, velocityField_rest, SubluminalWorldline.rest,
    accelerationField_uniform, add_zero]

/-- The world line `t ↦ t V e₁` of the charge in uniform motion with the velocity `V` along the
first axis, which passes the origin at `t = 0`. -/
def axisWorldline (V : ℝ) (hV : |V| < 1) : SubluminalWorldline :=
  SubluminalWorldline.uniform 0 (axisVelocity V hV).val (axisVelocity V hV).property

/-- For the uniform motion `R − R·v = ‖x′‖/γ` with the comoving position `x′` of the boosted
Coulomb field. -/
theorem norm_comovingPosition_axisWorldline (V : ℝ) (hV : |V| < 1) {y : Spacetime}
    (hy : y ∈ (axisWorldline V hV).offWorldline) :
    ‖MovingCharge.comovingPosition V hV y‖ =
      (axisVelocity V hV).gamma * (axisWorldline V hV).retardedDenominator (y 0) (space y) := by
  set W := axisWorldline V hV
  set τ := W.retardedTime (y 0) (space y) with hτ
  have hr (s : ℝ) : W.r s = s • EuclideanSpace.single 0 V := by
    show 0 + s • _ = _
    rw [zero_add]
    rfl
  have hR : W.retardedSeparation (y 0) (space y) = space y - τ • EuclideanSpace.single 0 V := by
    rw [SubluminalWorldline.retardedSeparation, hr]
  have hvel : W.retardedVelocity (y 0) (space y) = EuclideanSpace.single 0 V :=
    SubluminalWorldline.deriv_uniform _ _ _ _
  have hD : W.retardedDenominator (y 0) (space y) = (y 0 - τ) - V * (y 1 - τ * V) := by
    rw [SubluminalWorldline.retardedDenominator, W.norm_retardedSeparation, ← hτ, hvel, hR,
      EuclideanSpace.inner_single_right]
    simp
  have hnull := W.norm_retardedSeparation (y 0) (space y)
  rw [hR, ← hτ] at hnull
  have hnull2 : (y 0 - τ) ^ 2 = (y 1 - τ * V) ^ 2 + y 2 ^ 2 + y 3 ^ 2 := by
    rw [← hnull, norm_sq_eq_sum]
    simp
  have hpos : 0 < W.retardedDenominator (y 0) (space y) := W.retardedDenominator_pos hy
  have hγ := axisVelocity_gamma_identity V hV
  have hγpos := (axisVelocity V hV).gamma_pos
  have hp : ‖MovingCharge.comovingPosition V hV y‖ ^ 2 =
      ((axisVelocity V hV).gamma * W.retardedDenominator (y 0) (space y)) ^ 2 := by
    rw [norm_sq_eq_sum, MovingCharge.comovingPosition_zero, MovingCharge.comovingPosition_one,
      MovingCharge.comovingPosition_two, hD]
    linear_combination (-1) * hnull2 + ((y 1 - V * τ) ^ 2 - (y 0 - τ) ^ 2) * hγ
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hp

/-- **The potentials of Liénard and Wiechert of the uniform motion are the boosted Coulomb
potential**: for the charge `e` moving with the velocity `V` along the first axis, the potential
of Liénard and Wiechert is the potential `movingCoulomb` of `MovingCharge` (Landau–Lifshitz
§38), the pullback by the boost of the potential `e/(4π|x|)` of the charge at rest; its scalar
potential is `φ = eγ/(4π√(γ²(x₁ − Vt)² + x₂² + x₃²))`. Both vanish on the world line, where
they are not defined physically. -/
theorem lienardWiechert_axisWorldline (e V : ℝ) (hV : |V| < 1) :
    lienardWiechert e (axisWorldline V hV) = MovingCharge.movingCoulomb V hV e := by
  funext y
  apply oneCovector.injective
  refine ContinuousLinearMap.ext fun v => ?_
  rw [lienardWiechert, potentialOf_apply, MovingCharge.movingCoulomb,
    MovingCharge.movingScalar_apply]
  have hvel : (axisWorldline V hV).retardedVelocity (y 0) (space y) =
      EuclideanSpace.single 0 V :=
    SubluminalWorldline.deriv_uniform _ _ _ _
  have ha (i : Fin 3) : vectorPotential e (axisWorldline V hV) y i =
      scalarPotential e (axisWorldline V hV) y * (EuclideanSpace.single 0 V : Space 3) i := by
    rw [vectorPotential, scalarPotential, hvel]
    ring
  have key : scalarPotential e (axisWorldline V hV) y = (axisVelocity V hV).gamma *
      MovingCharge.coulombPotential e (MovingCharge.comovingPosition V hV y) := by
    by_cases hy : y ∈ (axisWorldline V hV).offWorldline
    · have hD := (axisWorldline V hV).retardedDenominator_pos hy
      have hγ := (axisVelocity V hV).gamma_pos
      rw [scalarPotential, MovingCharge.coulombPotential,
        norm_comovingPosition_axisWorldline V hV hy]
      field_simp
    · have hx : space y = (axisWorldline V hV).r (y 0) := not_not.mp hy
      have hτ : (axisWorldline V hV).retardedTime (y 0) (space y) = y 0 := by
        rw [hx]
        exact (axisWorldline V hV).retardedTime_self (y 0)
      have hD : (axisWorldline V hV).retardedDenominator (y 0) (space y) = 0 := by
        rw [SubluminalWorldline.retardedDenominator, SubluminalWorldline.retardedSeparation, hτ,
          ← hx]
        simp
      have hr : (axisWorldline V hV).r (y 0) = y 0 • EuclideanSpace.single 0 V := by
        show 0 + _ • _ = _
        rw [zero_add]
        rfl
      have h1 : y 1 = y 0 * V := by
        have := congrArg (fun z : Space 3 => z 0) (hx.trans hr)
        simpa using this
      have h2 : y 2 = 0 := by
        have := congrArg (fun z : Space 3 => z 1) (hx.trans hr)
        simpa using this
      have h3 : y 3 = 0 := by
        have := congrArg (fun z : Space 3 => z 2) (hx.trans hr)
        simpa using this
      have hp : ‖MovingCharge.comovingPosition V hV y‖ = 0 := by
        have hsq : ‖MovingCharge.comovingPosition V hV y‖ ^ 2 = 0 := by
          rw [norm_sq_eq_sum, MovingCharge.comovingPosition_zero,
            MovingCharge.comovingPosition_one, MovingCharge.comovingPosition_two, h1, h2, h3]
          ring
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      rw [scalarPotential, hD, MovingCharge.coulombPotential, hp]
      simp
  simp only [Fin.sum_univ_three, ha]
  rw [key]
  simp
  ring

/-- The same statement with the potential `Electrostatics.pointChargePotential` of the point
charge: the potential of Liénard and Wiechert of the uniform motion is the boost of `e/(4π|x|)`. -/
theorem lienardWiechert_axisWorldline_eq_movingScalar (e V : ℝ) (hV : |V| < 1) :
    lienardWiechert e (axisWorldline V hV) =
      MovingCharge.movingScalar V hV (Electrostatics.pointChargePotential e) := by
  rw [lienardWiechert_axisWorldline]
  have h : Electrostatics.pointChargePotential e = MovingCharge.coulombPotential e := by
    funext p
    simp [Electrostatics.pointChargePotential, MovingCharge.coulombPotential,
      SmoothGeometry.Potential.newtonKernel, div_eq_mul_inv]
  rw [h]
  rfl

/-! ### The field on the light cones of the world line -/

/-- The scalar potential at the event `(τ + ‖y‖, r(τ) + y)` is `e/(4π(‖y‖ − y·ṙ(τ)))`. -/
theorem scalarPotential_add_norm (e τ : ℝ) (y : Space 3) :
    scalarPotential e w (Minkowski.vector (τ + ‖y‖) (w.r τ + y)) =
      e / (4 * Real.pi * (‖y‖ - inner ℝ y (deriv w.r τ))) := by
  rw [scalarPotential, vector_zero, space_vector, w.retardedDenominator_add_norm]

/-- The vector potential at the event `(τ + ‖y‖, r(τ) + y)` is `e ṙ(τ)/(4π(‖y‖ − y·ṙ(τ)))`. -/
theorem vectorPotential_add_norm (e τ : ℝ) (y : Space 3) (i : Fin 3) :
    vectorPotential e w (Minkowski.vector (τ + ‖y‖) (w.r τ + y)) i =
      e * deriv w.r τ i / (4 * Real.pi * (‖y‖ - inner ℝ y (deriv w.r τ))) := by
  rw [vectorPotential, vector_zero, space_vector, w.retardedDenominator_add_norm,
    w.retardedVelocity_add_norm]

/-- The direction from the retarded position at the event `(τ + ρ, r(τ) + ρ n)` is `n`. -/
theorem retardedDirection_lightCone {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    w.retardedDirection (τ + ρ) (w.r τ + ρ • n) = n := by
  have h := w.retardedSeparation_add_norm τ (ρ • n)
  rw [norm_smul, hn, mul_one, Real.norm_of_nonneg hρ.le] at h
  rw [SubluminalWorldline.retardedDirection, h, norm_smul, hn, mul_one,
    Real.norm_of_nonneg hρ.le, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

/-- **The electric field on the light cone** of the point `r(τ)` of the world line: at the
event `(τ + ρ, r(τ) + ρ n)` with `ρ > 0` and `‖n‖ = 1`,
`E = e (1 − v²)(n − v)/(4πρ²(1 − n·v)³) + e n × ((n − v) × v̇)/(4πρ(1 − n·v)³)` with
`v = ṙ(τ)` and `v̇ = r̈(τ)`: the velocity field falls off as `1/ρ²` and the acceleration field
as `1/ρ`. -/
theorem electricVector_lienardWiechert_lightCone (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3}
    (hn : ‖n‖ = 1) :
    electricVector (fieldTensor (lienardWiechert e w) (Minkowski.vector (τ + ρ) (w.r τ + ρ • n))) =
      WithLp.ofLp ((e * (1 - ‖deriv w.r τ‖ ^ 2) /
          (4 * Real.pi * ρ ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) • (n - deriv w.r τ) +
        (e / (4 * Real.pi * ρ * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) •
          (inner ℝ n (deriv (deriv w.r) τ) • (n - deriv w.r τ) -
            inner ℝ n (n - deriv w.r τ) • deriv (deriv w.r) τ)) := by
  rw [electricVector_lienardWiechert w e (mem_offWorldline_lightCone w hρ hn), vector_zero,
    space_vector, velocityField_lightCone w e hρ hn, accelerationField_lightCone w e hρ hn]

/-- **The magnetic field on the light cone** of the point `r(τ)` of the world line is
`B = n × E` at the event `(τ + ρ, r(τ) + ρ n)`. -/
theorem magneticVector_lienardWiechert_lightCone (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3}
    (hn : ‖n‖ = 1) :
    magneticVector (fieldTensor (lienardWiechert e w) (Minkowski.vector (τ + ρ) (w.r τ + ρ • n))) =
      crossProduct (WithLp.ofLp n) (electricVector (fieldTensor (lienardWiechert e w)
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)))) := by
  rw [magneticVector_lienardWiechert w e (mem_offWorldline_lightCone w hρ hn), vector_zero,
    space_vector, retardedDirection_lightCone w hρ hn]

end ProjectAinos.Electrodynamics
