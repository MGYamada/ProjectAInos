/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Wave.SlowSource
public import ProjectAinos.Mechanics.Basic
public import ProjectAinos.Electrodynamics.RetardedPotential
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-!
# The Lagrangian to terms of second order

Landau–Lifshitz, *The Classical Theory of Fields*, §65 (the Lagrangian of Darwin), as a
controlled approximation for prescribed slow sources and their point limit, with `c = 1` and the
units with `div E = ρ`. A source `(ρ, 𝐣)(s, x)` is made slow by `ρ_κ(t, x) = ρ(κt, x)`,
`𝐣_κ(t, x) = κ𝐣(κt, x)`, with the slowness `κ` (the ratio `v/c`). Self-fields are excluded: a
charge moves in the field of the others.

* The fields on `ℝ × ℝ³`: `electricOf` `E = −∇φ − ∂ₜ𝐚`, `magneticOf` `B = ∇ × 𝐚`,
  `lorentzDensity` `E + 𝐯 × B`; `electricOf_gauge`, `magneticOf_gauge`: gauge invariance.
* `rigidLagrangian ρ₀ φ 𝐚`: the interaction `−∫ ρ₀(x − r) φ + 𝐯 · ∫ ρ₀(x − r) 𝐚` of a rigid
  distribution; `eulerLagrange_rigidLagrangian`: **its Euler–Lagrange residual
  `∂L/∂r − d/dt ∂L/∂𝐯` is exactly the Lorentz force** `∫ ρ₀(x − r) (E + ṙ × B)` of any `C¹`
  potentials.
* `SlowSource a ρ 𝐣`: a smooth conserved source in the ball `‖x‖ ≤ a`; its retarded potentials
  `slowScalar`, `slowVector` (the components of `retardedPotential (slowSourceCurrent κ ρ 𝐣)`),
  the gauge function `darwinGauge` `χ = (κ/8π) ∫ ‖x − y‖ ∂ₛρ` (65.4) and the potentials of Darwin
  `darwinScalar` `φ' = Nρ(κt)` and `darwinVector` `𝐚' = (κ/8π) ∫ [𝐣 + (𝐣 · 𝐧)𝐧]/R` (65.6).
  `SlowSource.darwinVector_eq`: `𝐚' = κN𝐣 + ∇χ` exactly; `SlowSource.scalar_expansion`:
  `|φ − ∂ₜχ − φ'| ≤ M(R + a)⁵κ³/18`; `SlowSource.vector_expansion`:
  `|𝐚 + ∇χ − 𝐚'| ≤ M(R + a)³κ²/3`; `SlowSource.electricOf_darwinGauge`,
  `SlowSource.magneticOf_darwinGauge`: the gauge change keeps the fields;
  `SlowSource.electricField_retardedPotential_slowSourceCurrent`,
  `SlowSource.magneticField_retardedPotential_slowSourceCurrent`,
  `SlowSource.lorentzDensity_slow_eq`:
  `electricOf` and `magneticOf` of `(φ, 𝐚)` are the fields `electricField`, `magneticField` of
  `fieldTensor (retardedPotential (slowSourceCurrent κ ρ 𝐣))`.
* `SlowSource.force_eq_darwin`: **the force of the retarded field of a slow source on a rigid
  distribution is the Euler–Lagrange residual of the Lagrangian of Darwin up to `O(κ³)`**, with
  the explicit constant `(∫|ρ₀|)(M r⁵/18 + M r³/3 + 6V M r³/3)` under the bounds `SlowBounds`; no
  separation of the supports is needed for the estimate.
* The point limit: `rigidCharge`, `rigidCurrent`, `darwinPair` (the pair term of (65.7));
  `darwinInteraction_pointLimit`: the interaction Lagrangian of two smeared charges in the
  potentials of Darwin tends to `−e₁e₂/(4πR) + e₁e₂[𝐯₁ · 𝐯₂ + (𝐯₁ · 𝐧)(𝐯₂ · 𝐧)]/(8πR)`, and
  `darwinInteraction_pointLimit_pointBump` for the normalized bumps `pointBump`.
* `darwinLagrangian`: the Lagrangian (65.7) of `N` charges with the kinetic expansion
  `−m + mv²/2 + mv⁴/8` (`abs_free_sub_darwin_le`: within `|m|v⁶/4` of `−m√(1 − v²)`);
  `darwinLagrangian_pointLimit`: along prescribed slow separated trajectories it is the point limit
  of the kinetic terms and the smeared interactions; `darwinPair_comm`.
* Instances: `slowSource_example` (the charge `cos s ∂₀χ(x)` with the current
  `(sin s χ(x), 0, 0)`), `exists_slowBounds_example`, `force_eq_darwin_example`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Wave SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The fields of potentials on `ℝ × ℝ³` -/

/-- The electric field `Eᵢ = −∂ᵢφ − ∂ₜaᵢ` of the potentials `(φ, 𝐚)` on `ℝ × ℝ³`. -/
def electricOf (φ : ℝ × E3 → ℝ) (A : Fin 3 → ℝ × E3 → ℝ) (i : Fin 3) (p : ℝ × E3) : ℝ :=
  -spaceDeriv i φ p - timeDeriv (A i) p

/-- The magnetic field `𝐁 = ∇ × 𝐚` of the vector potential on `ℝ × ℝ³`. -/
def magneticOf (A : Fin 3 → ℝ × E3 → ℝ) (p : ℝ × E3) : Fin 3 → ℝ :=
  ![spaceDeriv 1 (A 2) p - spaceDeriv 2 (A 1) p, spaceDeriv 2 (A 0) p - spaceDeriv 0 (A 2) p,
    spaceDeriv 0 (A 1) p - spaceDeriv 1 (A 0) p]

/-- The density `Eᵢ + (𝐯 × 𝐁)ᵢ` of the Lorentz force on a charge moving with the velocity `𝐯`. -/
def lorentzDensity (φ : ℝ × E3 → ℝ) (A : Fin 3 → ℝ × E3 → ℝ) (v : E3) (i : Fin 3)
    (p : ℝ × E3) : ℝ :=
  electricOf φ A i p + crossProduct (WithLp.ofLp v) (magneticOf A p) i

/-- The magnetic force in components: `(𝐯 × (∇ × 𝐚))ᵢ = Σⱼ vⱼ (∂ᵢaⱼ − ∂ⱼaᵢ)`. -/
theorem crossProduct_magneticOf (A : Fin 3 → ℝ × E3 → ℝ) (v : E3) (p : ℝ × E3) (i : Fin 3) :
    crossProduct (WithLp.ofLp v) (magneticOf A p) i =
      ∑ j, v j * (spaceDeriv i (A j) p - spaceDeriv j (A i) p) := by
  rw [cross_apply]
  fin_cases i <;> simp [magneticOf, Fin.sum_univ_three] <;> ring

/-- **The electric field is gauge invariant**: the potentials `(φ − ∂ₜχ, 𝐚 + ∇χ)` have the field
of `(φ, 𝐚)` for a `C²` gauge function `χ`, since `∂ᵢ∂ₜχ = ∂ₜ∂ᵢχ`. This is the form in `(t, x)` of
`fieldTensor_gauge`, the exactness `d(dχ) = 0`. -/
theorem electricOf_gauge {φ : ℝ × E3 → ℝ} {A : Fin 3 → ℝ × E3 → ℝ} {χ : ℝ × E3 → ℝ}
    (hφ : Differentiable ℝ φ) (hA : ∀ k, Differentiable ℝ (A k)) (hχ : ContDiff ℝ 2 χ)
    (i : Fin 3) (p : ℝ × E3) :
    electricOf (fun q => φ q - timeDeriv χ q) (fun k q => A k q + spaceDeriv k χ q) i p =
      electricOf φ A i p := by
  have ht : Differentiable ℝ (timeDeriv χ) :=
    (contDiff_timeDeriv (n := 1) hχ).differentiable (by norm_num)
  have hs : ∀ k, Differentiable ℝ (spaceDeriv k χ) := fun k =>
    (contDiff_spaceDeriv (n := 1) hχ k).differentiable (by norm_num)
  simp only [electricOf]
  rw [spaceDeriv_fun_sub (hφ p) (ht p), timeDeriv_fun_add (hA i p) (hs i p),
    timeDeriv_spaceDeriv hχ.contDiffAt i]
  ring

/-- **The magnetic field is gauge invariant**: `∇ × (𝐚 + ∇χ) = ∇ × 𝐚` for a `C²` gauge function,
since `∂ᵢ∂ⱼχ = ∂ⱼ∂ᵢχ`. -/
theorem magneticOf_gauge {A : Fin 3 → ℝ × E3 → ℝ} {χ : ℝ × E3 → ℝ}
    (hA : ∀ k, Differentiable ℝ (A k)) (hχ : ContDiff ℝ 2 χ) (p : ℝ × E3) :
    magneticOf (fun k q => A k q + spaceDeriv k χ q) p = magneticOf A p := by
  have hs : ∀ k, Differentiable ℝ (spaceDeriv k χ) := fun k =>
    (contDiff_spaceDeriv (n := 1) hχ k).differentiable (by norm_num)
  have hadd : ∀ l k, spaceDeriv l (fun q => A k q + spaceDeriv k χ q) p =
      spaceDeriv l (A k) p + spaceDeriv l (spaceDeriv k χ) p := fun l k =>
    spaceDeriv_fun_add (hA k p) (hs k p) l
  have hc := spaceDeriv_spaceDeriv_comm (f := χ) (q := p) hχ.contDiffAt
  ext i
  fin_cases i <;> simp only [magneticOf, hadd] <;> simp [hc 1 2, hc 2 0, hc 0 1]

/-! ### A rigid charge distribution in given potentials -/

/-- The average `∫ ρ₀(x − r) g(t, x) dx` of a function over a rigid charge distribution `ρ₀`
centred at `r`. -/
def smear (ρ₀ : E3 → ℝ) (g : ℝ × E3 → ℝ) (t : ℝ) (r : E3) : ℝ := ∫ x, ρ₀ (x - r) * g (t, x)

/-- The average over a rigid distribution is the integral against the reflected profile. -/
theorem smear_eq_kernelIntegral (ρ₀ : E3 → ℝ) (g : ℝ × E3 → ℝ) (t : ℝ) (r : E3) :
    smear ρ₀ g t r = kernelIntegral (fun y => ρ₀ (-y)) g (t, r) := by
  rw [smear, kernelIntegral, ← integral_sub_left_eq_self (fun x => ρ₀ (x - r) * g (t, x)) volume r]
  congr 1
  funext y
  simp [smul_eq_mul]

/-- A profile of compact support gives the kernel support for every function. -/
theorem kernelSupport_reflect {ρ₀ : E3 → ℝ} (hc : HasCompactSupport ρ₀) (g : ℝ × E3 → ℝ) :
    KernelSupport (fun y => ρ₀ (-y)) g := by
  obtain ⟨b, hb⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine kernelSupport_of_kernel (b := b) (fun y hy => ?_) g
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have h := hb hmem
  rw [mem_closedBall_zero_iff, norm_neg] at h
  linarith

/-- The integrand of an average over a rigid distribution of compact support is integrable. -/
theorem integrable_smear {ρ₀ : E3 → ℝ} (hρ : Continuous ρ₀) (hc : HasCompactSupport ρ₀)
    {g : ℝ × E3 → ℝ} (hg : Continuous g) (t : ℝ) (r : E3) :
    Integrable fun x => ρ₀ (x - r) * g (t, x) :=
  ((hρ.comp (continuous_id.sub continuous_const)).mul
    (hg.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
    (hc.comp_homeomorph (Homeomorph.subRight r)).mul_right

/-- The interaction Lagrangian of a rigid charge distribution `ρ₀(x − r)` in the potentials
`(φ, 𝐚)`: `L(t, r, 𝐯) = −∫ ρ₀(x − r) φ(t, x) dx + 𝐯 · ∫ ρ₀(x − r) 𝐚(t, x) dx`, the charge and
the current `ρ₀(x − r) 𝐯` of the distribution coupled to the potentials. -/
def rigidLagrangian (ρ₀ : E3 → ℝ) (φ : ℝ × E3 → ℝ) (A : Fin 3 → ℝ × E3 → ℝ) :
    Mechanics.Lagrangian E3 :=
  fun t q => -smear ρ₀ φ t q.1 + ∑ i, q.2 i * smear ρ₀ (A i) t q.1

/-- A linear form on `ℝ × ℝ³` at `(1, 𝐰)`: `ℓ(1, 𝐰) = ℓ(1, 0) + Σₖ wₖ ℓ(0, eₖ)`. -/
theorem clm_apply_one_vec (ℓ : ℝ × E3 →L[ℝ] ℝ) (w : E3) :
    ℓ (1, w) = ℓ (1, 0) + ∑ k, w k * ℓ (0, EuclideanSpace.single k 1) := by
  have hw : ((1 : ℝ), w) = ((1 : ℝ), (0 : E3)) +
      ∑ k, w k • ((0 : ℝ), (EuclideanSpace.single k 1 : E3)) := by
    ext i
    · simp [Prod.fst_sum]
    · fin_cases i <;> simp [Fin.sum_univ_three]
  rw [hw, map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]

/-- **The Euler–Lagrange expression of a rigid distribution is the Lorentz force**: for `C¹`
potentials and a continuous profile `ρ₀` of compact support, along a path `r` differentiable at
`t`, the residual `∂L/∂r − d/dt ∂L/∂𝐯` of `rigidLagrangian ρ₀ φ 𝐚` is

  `∫ ρ₀(x − r) (Eᵢ + (ṙ × 𝐁)ᵢ)(t, x) dx`,

an exact identity: `∇(𝐯 · 𝐚) − (𝐯 · ∇)𝐚 = 𝐯 × (∇ × 𝐚)` under the integral. -/
theorem eulerLagrange_rigidLagrangian {ρ₀ : E3 → ℝ} (hρ : Continuous ρ₀)
    (hc : HasCompactSupport ρ₀) {φ : ℝ × E3 → ℝ} {A : Fin 3 → ℝ × E3 → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ k, ContDiff ℝ 1 (A k)) {r : ℝ → E3} {t : ℝ}
    (hr : DifferentiableAt ℝ r t) (i : Fin 3) :
    Mechanics.eulerLagrange (rigidLagrangian ρ₀ φ A) r t (EuclideanSpace.single i 1) =
      ∫ x, ρ₀ (x - r t) * lorentzDensity φ A (deriv r t) i (t, x) := by
  set K : E3 → ℝ := fun y => ρ₀ (-y) with hKd
  have hK : LocallyIntegrable K := (hρ.comp continuous_neg).locallyIntegrable
  have hKs : ∀ g : ℝ × E3 → ℝ, KernelSupport K g := kernelSupport_reflect hc
  set Φ := kernelIntegral K φ with hΦd
  set Ã : Fin 3 → ℝ × E3 → ℝ := fun k => kernelIntegral K (A k) with hÃd
  have hΦ : ∀ p, HasFDerivAt Φ (fderiv ℝ Φ p) p := fun p =>
    (hasFDerivAt_kernelIntegral hK hφ (hKs φ) p).differentiableAt.hasFDerivAt
  have hÃ : ∀ k p, HasFDerivAt (Ã k) (fderiv ℝ (Ã k) p) p := fun k p =>
    (hasFDerivAt_kernelIntegral hK (hA k) (hKs (A k)) p).differentiableAt.hasFDerivAt
  set ι : E3 × E3 →L[ℝ] ℝ × E3 := (0 : E3 × E3 →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ E3 E3)
  have hι : ∀ (s : ℝ) (z : E3 × E3), HasFDerivAt (fun z : E3 × E3 => (s, z.1)) ι z := fun s z =>
    (hasFDerivAt_const s z).prodMk hasFDerivAt_fst
  have hL : ∀ s, rigidLagrangian ρ₀ φ A s = fun z => -Φ (s, z.1) + ∑ k, z.2 k * Ã k (s, z.1) := by
    intro s
    funext z
    simp [rigidLagrangian, smear_eq_kernelIntegral, hΦd, hÃd, hKd]
  have hLd : ∀ (s : ℝ) (z : E3 × E3), HasFDerivAt (rigidLagrangian ρ₀ φ A s)
      (-(fderiv ℝ Φ (s, z.1)).comp ι + ∑ k, (z.2 k • (fderiv ℝ (Ã k) (s, z.1)).comp ι +
        Ã k (s, z.1) • (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).comp
          (ContinuousLinearMap.snd ℝ E3 E3))) z := by
    intro s z
    rw [hL s]
    refine ((hΦ _).comp z (hι s z)).neg.add (HasFDerivAt.fun_sum fun k _ => ?_)
    have hp : HasFDerivAt (fun z : E3 × E3 => z.2 k)
        ((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ E3 E3)) z :=
      (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).hasFDerivAt.comp z hasFDerivAt_snd
    exact hp.mul ((hÃ k _).comp z (hι s z))
  have hforce : Mechanics.force (rigidLagrangian ρ₀ φ A) r t (EuclideanSpace.single i 1) =
      -spaceDeriv i Φ (t, r t) + ∑ k, deriv r t k * spaceDeriv i (Ã k) (t, r t) := by
    rw [Mechanics.force, (hLd t _).fderiv]
    simp [ι, spaceDeriv]
  have hmom : Mechanics.momentum (rigidLagrangian ρ₀ φ A) r =
      fun s => ∑ k, Ã k (s, r s) • (EuclideanSpace.proj k : E3 →L[ℝ] ℝ) := by
    funext s
    refine ContinuousLinearMap.ext fun w => ?_
    rw [Mechanics.momentum, (hLd s _).fderiv]
    simp [ι, mul_comm, Prod.mk_zero_zero]
  have hpath : ∀ k, HasDerivAt (fun s => Ã k (s, r s)) (fderiv ℝ (Ã k) (t, r t) (1, deriv r t)) t :=
    fun k => by
      have h2 : HasDerivAt (fun s => (s, r s)) ((1 : ℝ), deriv r t) t :=
        HasDerivAt.prodMk (hasDerivAt_id' t) hr.hasDerivAt
      exact (hÃ k (t, r t)).comp_hasDerivAt t h2
  have hdmom : HasDerivAt (Mechanics.momentum (rigidLagrangian ρ₀ φ A) r)
      (∑ k, fderiv ℝ (Ã k) (t, r t) (1, deriv r t) • (EuclideanSpace.proj k : E3 →L[ℝ] ℝ)) t := by
    rw [hmom]
    exact HasDerivAt.fun_sum fun k _ =>
      (hpath k).smul_const (EuclideanSpace.proj k : E3 →L[ℝ] ℝ)
  have hmom_i : deriv (Mechanics.momentum (rigidLagrangian ρ₀ φ A) r) t
      (EuclideanSpace.single i 1) = timeDeriv (Ã i) (t, r t) +
        ∑ k, deriv r t k * spaceDeriv k (Ã i) (t, r t) := by
    rw [hdmom.deriv]
    simp [PiLp.single_apply]
    rw [clm_apply_one_vec]
    rfl
  -- the derivatives commute with the averages
  have hsd : ∀ (g : ℝ × E3 → ℝ), ContDiff ℝ 1 g → ∀ l,
      spaceDeriv l (kernelIntegral K g) = kernelIntegral K (spaceDeriv l g) := fun g hg l =>
    spaceDeriv_kernelIntegral hK hg (hKs g) l
  have htd : ∀ (g : ℝ × E3 → ℝ), ContDiff ℝ 1 g →
      timeDeriv (kernelIntegral K g) = kernelIntegral K (timeDeriv g) := fun g hg =>
    timeDeriv_kernelIntegral hK hg (hKs g)
  rw [Mechanics.eulerLagrange, sub_apply, hforce, hmom_i]
  simp only [hΦd, hÃd, hsd φ hφ, hsd _ (hA _), htd _ (hA _)]
  -- the Lorentz force as a combination of averages
  have hcont : ∀ g : ℝ × E3 → ℝ, Continuous g → Integrable fun x => ρ₀ (x - r t) * g (t, x) :=
    fun g hg => integrable_smear hρ hc hg t (r t)
  have hsφ : Continuous (spaceDeriv i φ) :=
    (contDiff_spaceDeriv (n := 0) (by simpa using hφ) i).continuous
  have hsA : ∀ k l, Continuous (spaceDeriv l (A k)) := fun k l =>
    (contDiff_spaceDeriv (n := 0) (by simpa using hA k) l).continuous
  have htA : Continuous (timeDeriv (A i)) :=
    (contDiff_timeDeriv (n := 0) (by simpa using hA i)).continuous
  have hrhs : (fun x => ρ₀ (x - r t) * lorentzDensity φ A (deriv r t) i (t, x)) = fun x =>
      -(ρ₀ (x - r t) * spaceDeriv i φ (t, x)) - ρ₀ (x - r t) * timeDeriv (A i) (t, x) +
        ∑ k, deriv r t k * (ρ₀ (x - r t) * spaceDeriv i (A k) (t, x) -
          ρ₀ (x - r t) * spaceDeriv k (A i) (t, x)) := by
    funext x
    rw [lorentzDensity, crossProduct_magneticOf, electricOf, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      ring
  have hKI : ∀ g : ℝ × E3 → ℝ, kernelIntegral K g (t, r t) = ∫ x, ρ₀ (x - r t) * g (t, x) :=
    fun g => (smear_eq_kernelIntegral ρ₀ g t (r t)).symm
  simp only [hKI]
  rw [hrhs, integral_add ?_ ?_, integral_sub ?_ ?_, integral_neg, integral_finsetSum _ ?_]
  rotate_left
  · exact fun k _ => ((hcont _ (hsA k i)).sub (hcont _ (hsA i k))).const_mul _
  · exact (hcont _ hsφ).neg
  · exact hcont _ htA
  · exact (hcont _ hsφ).neg.sub (hcont _ htA)
  · exact integrable_finsetSum _ fun k _ =>
      ((hcont _ (hsA k i)).sub (hcont _ (hsA i k))).const_mul _
  have hsum : ∑ k, ∫ x, deriv r t k * (ρ₀ (x - r t) * spaceDeriv i (A k) (t, x) -
        ρ₀ (x - r t) * spaceDeriv k (A i) (t, x)) =
      ∑ k, deriv r t k * ((∫ x, ρ₀ (x - r t) * spaceDeriv i (A k) (t, x)) -
        ∫ x, ρ₀ (x - r t) * spaceDeriv k (A i) (t, x)) :=
    Finset.sum_congr rfl fun k _ => by
      rw [integral_const_mul, integral_sub (hcont _ (hsA k i)) (hcont _ (hsA i k))]
  rw [hsum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-! ### A slow conserved source and its retarded potentials -/

/-- A **slow source**: a smooth charge density `ρ(s, x)` and current `𝐣(s, x)`, supported in the
cylinder `‖x‖ ≤ a` at all times, with the equation of continuity `∂ₛρ + div 𝐣 = 0`. Its slow
version `ρ(κt, x)`, `κ𝐣(κt, x)` (`slow`) is conserved as well (`SlowSource.continuity_slow`); the
charges move with velocities of the order `κ`. -/
structure SlowSource (a : ℝ) (ρ : ℝ × E3 → ℝ) (j : Fin 3 → ℝ × E3 → ℝ) : Prop where
  /-- The charge density is smooth. -/
  smooth_charge : ContDiff ℝ ∞ ρ
  /-- The current is smooth. -/
  smooth_current : ∀ k, ContDiff ℝ ∞ (j k)
  /-- The charge stays in the ball `‖x‖ ≤ a`. -/
  support_charge : SpatialSupport a ρ
  /-- The current stays in the ball `‖x‖ ≤ a`. -/
  support_current : ∀ k, SpatialSupport a (j k)
  /-- The equation of continuity `∂ₛρ + div 𝐣 = 0`. -/
  continuity : ∀ p, timeDeriv ρ p + ∑ k, spaceDeriv k (j k) p = 0

/-- The retarded scalar potential `φ = R(ρ_κ)` of the slow charge `ρ_κ(t, x) = ρ(κt, x)`. -/
def slowScalar (κ : ℝ) (ρ : ℝ × E3 → ℝ) : ℝ × E3 → ℝ := retardedIntegral (slow κ ρ)

/-- The retarded vector potential `𝐚 = R(𝐣_κ)` of the slow current `𝐣_κ(t, x) = κ𝐣(κt, x)`. -/
def slowVector (κ : ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (i : Fin 3) : ℝ × E3 → ℝ :=
  retardedIntegral fun p => κ * slow κ (j i) p

/-- The slow current `k = (ρ_κ, 𝐣_κ)` on space-time, through the splitting `v ↦ (v⁰, 𝐯)`. -/
def slowSourceCurrent (κ : ℝ) (ρ : ℝ × E3 → ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (v : Spacetime) :
    Spacetime :=
  Fin.cons (slow κ ρ (Wave.timeSpaceEquiv v)) fun i => κ * slow κ (j i) (Wave.timeSpaceEquiv v)

/-- The time component of the retarded potential of the slow current is `−φ`. -/
theorem potentialComponent_retardedPotential_slowSourceCurrent_zero (κ : ℝ) (ρ : ℝ × E3 → ℝ)
    (j : Fin 3 → ℝ × E3 → ℝ) :
    potentialComponent (retardedPotential (slowSourceCurrent κ ρ j)) 0 =
      fun v => -slowScalar κ ρ (Wave.timeSpaceEquiv v) := by
  rw [potentialComponent_retardedPotential_zero]
  funext v
  simp [retardedScalar, slowSourceCurrent, slowScalar]

/-- The spatial components of the retarded potential of the slow current are `aᵢ`. -/
theorem potentialComponent_retardedPotential_slowSourceCurrent_succ (κ : ℝ) (ρ : ℝ × E3 → ℝ)
    (j : Fin 3 → ℝ × E3 → ℝ) (i : Fin 3) :
    potentialComponent (retardedPotential (slowSourceCurrent κ ρ j)) i.succ =
      fun v => slowVector κ j i (Wave.timeSpaceEquiv v) := by
  rw [potentialComponent_retardedPotential_succ]
  funext v
  simp [retardedScalar, slowSourceCurrent, slowVector]

/-- The gauge function of Darwin (65.4), `χ(t, x) = (κ/8π) ∫ ‖x − y‖ ∂ₛρ(κt, y) dy`, whose time
derivative is the second-order term of the scalar potential. -/
def darwinGauge (κ : ℝ) (ρ : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  κ / (8 * π) * kernelIntegral (fun y => ‖y‖) (slow κ (timeDeriv ρ)) p

/-- The scalar potential of Darwin, the instantaneous Coulomb potential
`φ'(t, x) = ∫ ρ(κt, x − y)/(4π‖y‖) dy` (65.6). -/
def darwinScalar (κ : ℝ) (ρ : ℝ × E3 → ℝ) : ℝ × E3 → ℝ :=
  kernelIntegral Potential.newtonKernel (slow κ ρ)

/-- The kernel of Darwin, `(δᵢₖ/‖y‖ + yᵢyₖ/‖y‖³)/(8π)`, that is `(δᵢₖ + nᵢnₖ)/(8πR)`. -/
def darwinKernel (i k : Fin 3) (y : E3) : ℝ :=
  ((if i = k then 1 else 0) / ‖y‖ + y i * y k / ‖y‖ ^ 3) / (8 * π)

/-- The vector potential of Darwin (65.6),
`𝐚'(t, x) = (κ/8π) ∫ [𝐣 + (𝐣 · 𝐧)𝐧](κt, y)/‖x − y‖ dy` with `𝐧 = (x − y)/‖x − y‖`. -/
def darwinVector (κ : ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (i : Fin 3) (p : ℝ × E3) : ℝ :=
  κ * ∑ k, kernelIntegral (darwinKernel i k) (slow κ (j k)) p

/-- The kernel `δᵢₖ/‖y‖ − yᵢyₖ/‖y‖³` of the second derivatives of the distance. -/
def distanceHessian (i k : Fin 3) (y : E3) : ℝ :=
  (if i = k then 1 else 0) / ‖y‖ - y i * y k / ‖y‖ ^ 3

/-- The bound `|δᵢₖ/‖y‖ ± yᵢyₖ/‖y‖³| ≤ 2/‖y‖ = 8π/(4π‖y‖)`. -/
theorem abs_delta_div_add_le (i k : Fin 3) (y : E3) (σ : ℝ) (hσ : |σ| ≤ 1) :
    |(if i = k then 1 else 0) / ‖y‖ + σ * (y i * y k / ‖y‖ ^ 3)| ≤
      8 * π * Potential.newtonKernel y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Potential.newtonKernel]
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hi : |y i| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y i
  have hk : |y k| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y k
  have hδ : |(if i = k then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have h1 : |(if i = k then (1 : ℝ) else 0) / ‖y‖| ≤ ‖y‖⁻¹ := by
    rw [abs_div, abs_of_pos hn, div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) hδ
  have h2 : |σ * (y i * y k / ‖y‖ ^ 3)| ≤ ‖y‖⁻¹ := by
    rw [abs_mul, abs_div, abs_mul, abs_of_pos (pow_pos hn 3)]
    calc |σ| * (|y i| * |y k| / ‖y‖ ^ 3) ≤ 1 * (‖y‖ * ‖y‖ / ‖y‖ ^ 3) := by gcongr
      _ = ‖y‖⁻¹ := by field_simp
  have : 8 * π * Potential.newtonKernel y = 2 * ‖y‖⁻¹ := by
    rw [Potential.newtonKernel]
    field_simp
    ring
  rw [this]
  linarith [abs_add_le ((if i = k then (1 : ℝ) else 0) / ‖y‖) (σ * (y i * y k / ‖y‖ ^ 3))]

/-- The kernel of Darwin is bounded by the Newton kernel. -/
theorem abs_darwinKernel_le (i k : Fin 3) (y : E3) :
    |darwinKernel i k y| ≤ Potential.newtonKernel y := by
  have h := abs_delta_div_add_le i k y 1 (by simp)
  rw [darwinKernel, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * π)]
  rw [div_le_iff₀ (by positivity)]
  simpa [mul_comm] using h

/-- The kernel of the second derivatives of the distance is bounded by `8π` times the Newton
kernel. -/
theorem abs_distanceHessian_le (i k : Fin 3) (y : E3) :
    |distanceHessian i k y| ≤ 8 * π * Potential.newtonKernel y := by
  have h := abs_delta_div_add_le i k y (-1) (by simp)
  simpa [distanceHessian, sub_eq_add_neg] using h

/-- The kernel of Darwin is measurable. -/
theorem measurable_darwinKernel (i k : Fin 3) : Measurable (darwinKernel i k) := by
  unfold darwinKernel
  fun_prop

/-- The kernel of the second derivatives of the distance is measurable. -/
theorem measurable_distanceHessian (i k : Fin 3) : Measurable (distanceHessian i k) := by
  unfold distanceHessian
  fun_prop

/-- The kernel of Darwin is locally integrable. -/
theorem locallyIntegrable_darwinKernel (i k : Fin 3) : LocallyIntegrable (darwinKernel i k) :=
  Potential.locallyIntegrable_newtonKernel.mono
    (measurable_darwinKernel i k).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Potential.newtonKernel_nonneg y)]
      exact abs_darwinKernel_le i k y)

/-- The norm is a locally integrable kernel. -/
theorem locallyIntegrable_norm : LocallyIntegrable fun y : E3 => ‖y‖ :=
  continuous_norm.locallyIntegrable

namespace SlowSource

variable {a : ℝ} {ρ : ℝ × E3 → ℝ} {j : Fin 3 → ℝ × E3 → ℝ}

/-- The slow charge and current `(ρ_κ, 𝐣_κ)` satisfy the equation of continuity. -/
theorem continuity_slow (h : SlowSource a ρ j) (κ : ℝ) (p : ℝ × E3) :
    timeDeriv (slow κ ρ) p + ∑ k, spaceDeriv k (fun q => κ * slow κ (j k) q) p = 0 := by
  have hρ : Differentiable ℝ ρ := h.smooth_charge.differentiable (by simp)
  have hj : ∀ k, Differentiable ℝ (j k) := fun k =>
    (h.smooth_current k).differentiable (by simp)
  have hjs : ∀ k, Differentiable ℝ (slow κ (j k)) := fun k =>
    (contDiff_slow (h.smooth_current k) κ).differentiable (by simp)
  rw [timeDeriv_slow hρ]
  simp only [fun k => spaceDeriv_const_mul ((hjs k) p) κ k, fun k => spaceDeriv_slow (hj k) κ k]
  rw [← Finset.mul_sum, ← mul_add]
  simp [slow, h.continuity (κ * p.1, p.2)]

/-- The derivative of the equation of continuity: `∂ᵢ∂ₛρ = −Σₖ ∂ᵢ∂ₖjₖ`. -/
theorem spaceDeriv_timeDeriv (h : SlowSource a ρ j) (i : Fin 3) (q : ℝ × E3) :
    spaceDeriv i (timeDeriv ρ) q = -∑ k, spaceDeriv i (spaceDeriv k (j k)) q := by
  have ht : Differentiable ℝ (timeDeriv ρ) :=
    (contDiff_timeDeriv (n := 1) (h.smooth_charge.of_le (by simp))).differentiable (by simp)
  have hs : ∀ k, Differentiable ℝ (spaceDeriv k (j k)) := fun k =>
    (contDiff_spaceDeriv (n := 1) ((h.smooth_current k).of_le (by simp)) k).differentiable
      (by simp)
  have h0 : (fun p => timeDeriv ρ p + ∑ k, spaceDeriv k (j k) p) = fun _ => 0 :=
    funext h.continuity
  have h1 := congrArg (fun f => spaceDeriv i f q) h0
  rw [spaceDeriv_fun_add (ht q) ((Differentiable.fun_sum fun k _ => hs k) q),
    spaceDeriv_fun_sum _ (fun k _ => hs k q)] at h1
  simp only [spaceDeriv] at h1 ⊢
  rw [fderiv_fun_const, Pi.zero_apply, zero_apply] at h1
  linarith

/-- The total charge is constant: `∫ ∂ₛρ(s, z) dz = 0`. -/
theorem integral_timeDeriv (h : SlowSource a ρ j) (s : ℝ) : ∫ z, timeDeriv ρ (s, z) = 0 := by
  have hc : ∀ k, ContDiff ℝ 1 (j k) := fun k => (h.smooth_current k).of_le (by simp)
  have hint : ∀ k, Integrable fun z => spaceDeriv k (j k) (s, z) := fun k =>
    ((contDiff_spaceDeriv (n := 0) (by simpa using hc k) k).continuous.comp
      (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (((h.support_current k).spaceDeriv k).hasCompactSupport_slice s)
  have he : (fun z => timeDeriv ρ (s, z)) = fun z => -∑ k, spaceDeriv k (j k) (s, z) := by
    funext z
    linarith [h.continuity (s, z)]
  rw [he, integral_neg, integral_finsetSum _ fun k _ => hint k]
  simp [integral_spaceDeriv_eq_zero (hc _) (h.support_current _)]

end SlowSource

namespace SlowSource

variable {a : ℝ} {ρ : ℝ × E3 → ℝ} {j : Fin 3 → ℝ × E3 → ℝ}

/-- **The vector potential of Darwin is the gauge transform of the instantaneous one**
(65.4)–(65.6): for a slow source, `𝐚' = κ N𝐣(κt) + ∇χ`, that is
`(κ/8π) ∫ [𝐣 + (𝐣 · 𝐧)𝐧]/R = (κ/4π) ∫ 𝐣/R + ∇χ`. By the equation of continuity and the second
derivatives of the distance (`integral_norm_sub_mul_spaceDeriv_spaceDeriv`),
`∂ᵢχ = −(κ/8π) Σₖ ∫ (δᵢₖ − nᵢnₖ) jₖ/R`; the identity holds at every point, inside the source
as well. -/
theorem darwinVector_eq (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) (p : ℝ × E3) :
    darwinVector κ j i p = κ * kernelIntegral Potential.newtonKernel (slow κ (j i)) p +
      spaceDeriv i (darwinGauge κ ρ) p := by
  obtain ⟨t, x⟩ := p
  have hρ2 : ContDiff ℝ 2 ρ := h.smooth_charge.of_le (by simp)
  have hG : ContDiff ℝ 1 (slow κ (timeDeriv ρ)) :=
    contDiff_slow (contDiff_timeDeriv (n := 1) hρ2) κ
  have hGs : SpatialSupport a (slow κ (timeDeriv ρ)) := h.support_charge.timeDeriv.slow κ
  have hj2 : ∀ k, ContDiff ℝ 2 (j k) := fun k => (h.smooth_current k).of_le (by simp)
  have hjc : ∀ k, Continuous fun z => j k (κ * t, z) := fun k =>
    (hj2 k).continuous.comp (continuous_const.prodMk continuous_id)
  have hjcs : ∀ k, HasCompactSupport fun z => j k (κ * t, z) := fun k =>
    (h.support_current k).hasCompactSupport_slice _
  have hχ : spaceDeriv i (darwinGauge κ ρ) (t, x) =
      κ / (8 * π) * -∑ k, ∫ z, distanceHessian i k (x - z) * j k (κ * t, z) := by
    have hd : DifferentiableAt ℝ (kernelIntegral (fun y : E3 => ‖y‖) (slow κ (timeDeriv ρ)))
        (t, x) :=
      (hasFDerivAt_kernelIntegral locallyIntegrable_norm hG (hGs.kernelSupport _)
        (t, x)).differentiableAt
    rw [show darwinGauge κ ρ = fun p => κ / (8 * π) *
        kernelIntegral (fun y : E3 => ‖y‖) (slow κ (timeDeriv ρ)) p from rfl,
      spaceDeriv_const_mul hd, spaceDeriv_kernelIntegral locallyIntegrable_norm hG
        (hGs.kernelSupport _),
      spaceDeriv_slow ((contDiff_timeDeriv (n := 1) hρ2).differentiable (by norm_num)),
      kernelIntegral_eq_integral_sub]
    congr 1
    simp only [slow, h.spaceDeriv_timeDeriv i, mul_neg, Finset.mul_sum]
    rw [integral_neg, integral_finsetSum]
    · congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      exact integral_norm_sub_mul_spaceDeriv_spaceDeriv (hj2 k) (h.support_current k) _ x i k
    · intro k _
      have hc : Continuous fun z => spaceDeriv i (spaceDeriv k (j k)) (κ * t, z) :=
        (contDiff_spaceDeriv (n := 0) (contDiff_spaceDeriv (n := 1) (hj2 k) k) i).continuous.comp
          (continuous_const.prodMk continuous_id)
      exact ((continuous_norm.comp (continuous_const.sub continuous_id)).mul
        hc).integrable_of_hasCompactSupport
        ((((h.support_current k).spaceDeriv k).spaceDeriv i).hasCompactSupport_slice _).mul_left
  rw [hχ, darwinVector]
  simp only [kernelIntegral_eq_integral_sub, slow]
  have hD : ∀ k, ∫ z, darwinKernel i k (x - z) * j k (κ * t, z) =
      (if i = k then ∫ z, Potential.newtonKernel (x - z) * j k (κ * t, z) else 0) -
        (8 * π)⁻¹ * ∫ z, distanceHessian i k (x - z) * j k (κ * t, z) := by
    intro k
    have hN := integrable_kernel_sub_mul (K := Potential.newtonKernel)
      Potential.locallyIntegrable_newtonKernel.aestronglyMeasurable (C := 1)
      (fun y => by rw [one_mul, abs_of_nonneg (Potential.newtonKernel_nonneg y)])
      (hjc k) (hjcs k) x
    have hH := integrable_kernel_sub_mul (measurable_distanceHessian i k).aestronglyMeasurable
      (abs_distanceHessian_le i k) (hjc k) (hjcs k) x
    rw [← integral_const_mul]
    split_ifs with hik
    · subst hik
      rw [← integral_sub hN (hH.const_mul _)]
      congr 1
      funext z
      rcases eq_or_ne ‖x - z‖ 0 with h0 | h0
      · simp [darwinKernel, distanceHessian, Potential.newtonKernel, h0]
      · simp only [darwinKernel, distanceHessian, Potential.newtonKernel, ↓reduceIte]
        field_simp
        ring
    · rw [zero_sub, ← integral_neg]
      congr 1
      funext z
      simp only [darwinKernel, distanceHessian, hik, ↓reduceIte]
      ring
  simp only [hD, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    ← Finset.mul_sum]
  ring

/-- The gauge function of Darwin is smooth. -/
theorem contDiff_darwinGauge (h : SlowSource a ρ j) (κ : ℝ) :
    ContDiff ℝ ∞ (darwinGauge κ ρ) :=
  contDiff_const.mul (contDiff_kernelIntegral locallyIntegrable_norm
    (contDiff_slow (contDiff_infty_timeDeriv h.smooth_charge) κ)
    ((h.support_charge.timeDeriv.slow κ).kernelSupport _))

/-- The retarded scalar potential of a slow source is smooth. -/
theorem contDiff_slowScalar (h : SlowSource a ρ j) (κ : ℝ) : ContDiff ℝ ∞ (slowScalar κ ρ) :=
  contDiff_retardedIntegral (contDiff_slow h.smooth_charge κ)
    (h.support_charge.slow κ).subluminalSupport

/-- The retarded vector potential of a slow source is smooth. -/
theorem contDiff_slowVector (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (slowVector κ j i) :=
  contDiff_retardedIntegral (contDiff_const.mul (contDiff_slow (h.smooth_current i) κ))
    (((h.support_current i).slow κ).mono fun p hp => by simp [hp]).subluminalSupport

/-- The retarded potential of the slow current of a slow source is smooth. -/
theorem contDiff_retardedPotential_slowSourceCurrent (h : SlowSource a ρ j) (κ : ℝ) :
    ContDiff ℝ ∞ (retardedPotential (slowSourceCurrent κ ρ j)) := by
  have h0 : retardedScalar (fun w => slowSourceCurrent κ ρ j w 0) =
      fun v => slowScalar κ ρ (Wave.timeSpaceEquiv v) := by
    funext v
    simp [retardedScalar, slowSourceCurrent, slowScalar]
  have hi : ∀ i : Fin 3, (fun v => retardedScalar (fun w => slowSourceCurrent κ ρ j w i.succ) v) =
      fun v => slowVector κ j i (Wave.timeSpaceEquiv v) := fun i => by
    funext v
    simp [retardedScalar, slowSourceCurrent, slowVector]
  refine CavityModes.contDiff_potentialOf ?_ fun i => ?_
  · rw [h0]
    exact (h.contDiff_slowScalar κ).comp Wave.timeSpaceEquiv.contDiff
  · rw [hi i]
    exact (h.contDiff_slowVector κ i).comp Wave.timeSpaceEquiv.contDiff

/-- **The electric field of the retarded potential** of the slow current, `fieldTensor` of
`retardedPotential`, is `electricOf` of `(φ, 𝐚)` in `(t, x)`. -/
theorem electricField_retardedPotential_slowSourceCurrent (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3)
    (v : Spacetime) :
    electricField (fieldTensor (retardedPotential (slowSourceCurrent κ ρ j))) i v =
      electricOf (slowScalar κ ρ) (slowVector κ j) i (Wave.timeSpaceEquiv v) := by
  have hA : ContDiff ℝ 1 (retardedPotential (slowSourceCurrent κ ρ j)) :=
    (h.contDiff_retardedPotential_slowSourceCurrent κ).of_le (by simp)
  have hs : Differentiable ℝ (slowScalar κ ρ) := (h.contDiff_slowScalar κ).differentiable (by simp)
  have ha : Differentiable ℝ (slowVector κ j i) :=
    (h.contDiff_slowVector κ i).differentiable (by simp)
  rw [(electricField_fieldTensor_eventuallyEq hA.contDiffAt i).eq_of_nhds,
    potentialComponent_retardedPotential_slowSourceCurrent_zero,
    potentialComponent_retardedPotential_slowSourceCurrent_succ, partialAt_neg]
  have h1 := congrFun (Wave.fderiv_comp_timeSpaceEquiv_succ hs i) v
  have h2 := congrFun (Wave.fderiv_comp_timeSpaceEquiv_zero ha) v
  simp only [partialAt] at h1 h2 ⊢
  rw [h1, h2, electricOf]

/-- **The magnetic field of the retarded potential** of the slow current is `magneticOf 𝐚`. -/
theorem magneticField_retardedPotential_slowSourceCurrent (h : SlowSource a ρ j) (κ : ℝ)
    (v : Spacetime) :
    (fun i => magneticField (fieldTensor (retardedPotential (slowSourceCurrent κ ρ j))) i v) =
      magneticOf (slowVector κ j) (Wave.timeSpaceEquiv v) := by
  have hA : ContDiff ℝ 1 (retardedPotential (slowSourceCurrent κ ρ j)) :=
    (h.contDiff_retardedPotential_slowSourceCurrent κ).of_le (by simp)
  have hd : ∀ k, Differentiable ℝ (slowVector κ j k) := fun k =>
    (h.contDiff_slowVector κ k).differentiable (by simp)
  have hs : ∀ k l : Fin 3, partialAt
      (potentialComponent (retardedPotential (slowSourceCurrent κ ρ j)) k.succ) l.succ v =
        spaceDeriv l (slowVector κ j k) (Wave.timeSpaceEquiv v) := fun k l => by
    rw [potentialComponent_retardedPotential_slowSourceCurrent_succ]
    exact congrFun (Wave.fderiv_comp_timeSpaceEquiv_succ (hd k) l) v
  obtain ⟨h0, h1, h2⟩ := CavityModes.magneticField_fieldTensor_apply hA v
  have e1 : (1 : Fin 4) = (0 : Fin 3).succ := rfl
  have e2 : (2 : Fin 4) = (1 : Fin 3).succ := rfl
  have e3 : (3 : Fin 4) = (2 : Fin 3).succ := rfl
  funext i
  fin_cases i
  · rw [Fin.zero_eta, h0, e3, e2, hs, hs]
    rfl
  · rw [Fin.mk_one, h1, e3, e1, hs, hs]
    rfl
  · change magneticField (fieldTensor (retardedPotential (slowSourceCurrent κ ρ j))) 2 v =
      magneticOf (slowVector κ j) (Wave.timeSpaceEquiv v) 2
    rw [h2, e2, e1, hs, hs]
    rfl

/-- The Lorentz density of the retarded potentials is the Lorentz force density
`Eᵢ + (𝐯 × 𝐁)ᵢ` of the field of `retardedPotential (slowSourceCurrent κ ρ 𝐣)`. -/
theorem lorentzDensity_slow_eq (h : SlowSource a ρ j) (κ : ℝ) (w : E3) (i : Fin 3)
    (v : Spacetime) :
    lorentzDensity (slowScalar κ ρ) (slowVector κ j) w i (Wave.timeSpaceEquiv v) =
      electricField (fieldTensor (retardedPotential (slowSourceCurrent κ ρ j))) i v +
        crossProduct (WithLp.ofLp w)
          (fun k => magneticField (fieldTensor (retardedPotential (slowSourceCurrent κ ρ j)))
            k v) i := by
  rw [lorentzDensity, h.electricField_retardedPotential_slowSourceCurrent,
    h.magneticField_retardedPotential_slowSourceCurrent]

/-- **The gauge change of Darwin keeps the electric field** of the retarded potentials. -/
theorem electricOf_darwinGauge (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) (p : ℝ × E3) :
    electricOf (fun q => slowScalar κ ρ q - timeDeriv (darwinGauge κ ρ) q)
        (fun k q => slowVector κ j k q + spaceDeriv k (darwinGauge κ ρ) q) i p =
      electricOf (slowScalar κ ρ) (slowVector κ j) i p :=
  electricOf_gauge ((h.contDiff_slowScalar κ).differentiable (by simp))
    (fun k => (h.contDiff_slowVector κ k).differentiable (by simp))
    ((h.contDiff_darwinGauge κ).of_le (by simp)) i p

/-- **The gauge change of Darwin keeps the magnetic field** of the retarded potentials. -/
theorem magneticOf_darwinGauge (h : SlowSource a ρ j) (κ : ℝ) (p : ℝ × E3) :
    magneticOf (fun k q => slowVector κ j k q + spaceDeriv k (darwinGauge κ ρ) q) p =
      magneticOf (slowVector κ j) p :=
  magneticOf_gauge (fun k => (h.contDiff_slowVector κ k).differentiable (by simp))
    ((h.contDiff_darwinGauge κ).of_le (by simp)) p

/-- The time derivative of the gauge function of Darwin,
`∂ₜχ = (κ²/8π) ∫ ‖y‖ ∂ₛ²ρ(κt, x − y) dy`. -/
theorem timeDeriv_darwinGauge (h : SlowSource a ρ j) (κ : ℝ) (p : ℝ × E3) :
    timeDeriv (darwinGauge κ ρ) p = κ ^ 2 / (8 * π) *
      kernelIntegral (fun y => ‖y‖) (slow κ (timeDeriv (timeDeriv ρ))) p := by
  have hG : ContDiff ℝ ∞ (slow κ (timeDeriv ρ)) :=
    contDiff_slow (contDiff_infty_timeDeriv h.smooth_charge) κ
  have hGs : SpatialSupport a (slow κ (timeDeriv ρ)) := h.support_charge.timeDeriv.slow κ
  have hd : DifferentiableAt ℝ (kernelIntegral (fun y : E3 => ‖y‖) (slow κ (timeDeriv ρ))) p :=
    (hasFDerivAt_kernelIntegral locallyIntegrable_norm (hG.of_le (by simp))
      (hGs.kernelSupport _) p).differentiableAt
  rw [show darwinGauge κ ρ = fun p => κ / (8 * π) *
      kernelIntegral (fun y : E3 => ‖y‖) (slow κ (timeDeriv ρ)) p from rfl,
    timeDeriv_const_mul hd, timeDeriv_kernelIntegral locallyIntegrable_norm (hG.of_le (by simp))
      (hGs.kernelSupport _),
    timeDeriv_slow ((contDiff_infty_timeDeriv h.smooth_charge).differentiable (by simp)),
    kernelIntegral_const_mul]
  ring

/-- **The scalar potential in the gauge of Darwin** (65.6): for a slow source with
`|∂ₛ³ρ| ≤ M`, at `‖x‖ ≤ R`,

  `|φ − ∂ₜχ − Nρ(κt)| ≤ M (R + a)⁵ κ³/18`,

the first-order term `−κ (4π)⁻¹ d/ds ∫ ρ` vanishing by the conservation of the charge and the
second-order term being `∂ₜχ`. -/
theorem scalar_expansion (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ}
    (hM : ∀ p, |timeDeriv^[3] ρ p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {R : ℝ}
    (hx : ‖x‖ ≤ R) :
    |slowScalar κ ρ (t, x) - timeDeriv (darwinGauge κ ρ) (t, x) - darwinScalar κ ρ (t, x)| ≤
      M * (R + a) ^ 5 / 18 * κ ^ 3 := by
  have H := retardedIntegral_slow_expansion (n := 2) (h.smooth_charge.of_le (by simp)) ha
    h.support_charge hM hκ t hx
  have h0 : slowTerm 0 ρ (κ * t) x = darwinScalar κ ρ (t, x) := by
    simp [slowTerm, darwinScalar, kernelIntegral, slow, smul_eq_mul]
  have h1 : slowTerm 1 ρ (κ * t) x = 0 := by
    rw [slowTerm_one, h.integral_timeDeriv, mul_zero]
  have h2 : κ ^ 2 / 2 * slowTerm 2 ρ (κ * t) x = timeDeriv (darwinGauge κ ρ) (t, x) := by
    rw [slowTerm_two, h.timeDeriv_darwinGauge, kernelIntegral]
    simp only [smul_eq_mul, slow, Prod.mk_sub_mk, sub_zero]
    rw [Function.iterate_succ_apply, Function.iterate_one]
    ring
  have hsum : ∑ k ∈ Finset.range (2 + 1), (-κ) ^ k / (k.factorial : ℝ) * slowTerm k ρ (κ * t) x =
      darwinScalar κ ρ (t, x) + timeDeriv (darwinGauge κ ρ) (t, x) := by
    rw [← h0, ← h2]
    simp [Finset.sum_range_succ, h1]
  rw [hsum] at H
  have hb : M * (R + a) ^ (2 + 3) / (3 * ((2 + 1).factorial : ℝ)) * κ ^ (2 + 1) =
      M * (R + a) ^ 5 / 18 * κ ^ 3 := by
    norm_num [Nat.factorial]
  rw [slowScalar, sub_sub, add_comm (timeDeriv _ _), ← hb]
  exact H

/-- **The vector potential in the gauge of Darwin** (65.6): for a slow source with
`|∂ₛjᵢ| ≤ M`, at `‖x‖ ≤ R`,

  `|aᵢ + ∂ᵢχ − a'ᵢ| ≤ M (R + a)³ κ²/3`

with the vector potential `darwinVector` of Darwin. -/
theorem vector_expansion (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ}
    (hM : ∀ i p, |timeDeriv (j i) p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {R : ℝ}
    (hx : ‖x‖ ≤ R) (i : Fin 3) :
    |slowVector κ j i (t, x) + spaceDeriv i (darwinGauge κ ρ) (t, x) -
        darwinVector κ j i (t, x)| ≤ M * (R + a) ^ 3 / 3 * κ ^ 2 := by
  have H := retardedIntegral_slow_expansion (n := 0) ((h.smooth_current i).of_le (by simp)) ha
    (h.support_current i) (hM i) hκ t hx
  have h0 : slowTerm 0 (j i) (κ * t) x =
      kernelIntegral Potential.newtonKernel (slow κ (j i)) (t, x) := by
    simp [slowTerm, kernelIntegral, slow, smul_eq_mul]
  have hs0 : ∑ k ∈ Finset.range (0 + 1), (-κ) ^ k / (k.factorial : ℝ) *
      slowTerm k (j i) (κ * t) x = kernelIntegral Potential.newtonKernel (slow κ (j i)) (t, x) := by
    simp [h0]
  rw [hs0] at H
  rw [h.darwinVector_eq, slowVector, retardedIntegral_const_mul]
  have he : κ * retardedIntegral (slow κ (j i)) (t, x) + spaceDeriv i (darwinGauge κ ρ) (t, x) -
      (κ * kernelIntegral Potential.newtonKernel (slow κ (j i)) (t, x) +
        spaceDeriv i (darwinGauge κ ρ) (t, x)) =
      κ * (retardedIntegral (slow κ (j i)) (t, x) -
        kernelIntegral Potential.newtonKernel (slow κ (j i)) (t, x)) := by ring
  rw [he, abs_mul, abs_of_nonneg hκ]
  calc κ * |retardedIntegral (slow κ (j i)) (t, x) -
        kernelIntegral Potential.newtonKernel (slow κ (j i)) (t, x)|
      ≤ κ * (M * (R + a) ^ (0 + 3) / (3 * ((0 + 1).factorial : ℝ)) * κ ^ (0 + 1)) :=
        mul_le_mul_of_nonneg_left H hκ
    _ = M * (R + a) ^ 3 / 3 * κ ^ 2 := by norm_num; ring

end SlowSource

/-! ### The force of the retarded field and the Lagrangian of Darwin -/

/-- The Lorentz density of `C¹` potentials is continuous. -/
theorem continuous_lorentzDensity {φ : ℝ × E3 → ℝ} {A : Fin 3 → ℝ × E3 → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ k, ContDiff ℝ 1 (A k)) (v : E3) (i : Fin 3) :
    Continuous (lorentzDensity φ A v i) := by
  have h1 : ∀ g : ℝ × E3 → ℝ, ContDiff ℝ 1 g → ∀ l, Continuous (spaceDeriv l g) := fun g hg l =>
    (contDiff_spaceDeriv (n := 0) (by simpa using hg) l).continuous
  have h2 : ∀ g : ℝ × E3 → ℝ, ContDiff ℝ 1 g → Continuous (timeDeriv g) := fun g hg =>
    (contDiff_timeDeriv (n := 0) (by simpa using hg)).continuous
  have he : lorentzDensity φ A v i = fun p => -spaceDeriv i φ p - timeDeriv (A i) p +
      ∑ j, v j * (spaceDeriv i (A j) p - spaceDeriv j (A i) p) := by
    funext p
    rw [lorentzDensity, crossProduct_magneticOf, electricOf]
  rw [he]
  exact ((h1 φ hφ i).neg.sub (h2 _ (hA i))).add (continuous_finsetSum _ fun k _ =>
    continuous_const.mul ((h1 _ (hA k) i).sub (h1 _ (hA i) k)))

/-- Bounds on the time derivatives of a slow source that enter the force: `|∂ₛ³∂ᵢρ| ≤ M`,
`|∂ₛ²jᵢ| ≤ M` and `|∂ₛ∂ₗjᵢ| ≤ M`. -/
structure SlowBounds (M : ℝ) (ρ : ℝ × E3 → ℝ) (j : Fin 3 → ℝ × E3 → ℝ) : Prop where
  /-- The third time derivatives of the gradient of the charge. -/
  charge : ∀ i p, |timeDeriv^[3] (spaceDeriv i ρ) p| ≤ M
  /-- The second time derivatives of the current. -/
  current : ∀ i p, |timeDeriv (timeDeriv (j i)) p| ≤ M
  /-- The time derivatives of the spatial derivatives of the current. -/
  current_space : ∀ i l p, |timeDeriv (spaceDeriv l (j i)) p| ≤ M

namespace SlowSource

variable {a : ℝ} {ρ : ℝ × E3 → ℝ} {j : Fin 3 → ℝ × E3 → ℝ}

/-- The retarded vector potential is `κ R(𝐣_κ)` with the slow current profile. -/
theorem slowVector_eq (κ : ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (i : Fin 3) :
    slowVector κ j i = fun p => κ * retardedIntegral (slow κ (j i)) p :=
  funext fun p => retardedIntegral_const_mul κ _ p

/-- The scalar potential of Darwin is smooth. -/
theorem contDiff_darwinScalar (h : SlowSource a ρ j) (κ : ℝ) :
    ContDiff ℝ ∞ (darwinScalar κ ρ) :=
  contDiff_kernelIntegral Potential.locallyIntegrable_newtonKernel
    (contDiff_slow h.smooth_charge κ) ((h.support_charge.slow κ).kernelSupport _)

/-- The vector potential of Darwin is smooth. -/
theorem contDiff_darwinVector (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (darwinVector κ j i) :=
  contDiff_const.mul (ContDiff.sum fun k _ => contDiff_kernelIntegral
    (locallyIntegrable_darwinKernel i k) (contDiff_slow (h.smooth_current k) κ)
    (((h.support_current k).slow κ).kernelSupport _))

/-- The mixed derivative of the gauge function,
`∂ᵢ∂ₜχ = (κ²/8π) ∫ ‖y‖ ∂ᵢ∂ₛ²ρ(κt, x − y) dy`. -/
theorem spaceDeriv_timeDeriv_darwinGauge (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3)
    (p : ℝ × E3) :
    spaceDeriv i (timeDeriv (darwinGauge κ ρ)) p = κ ^ 2 / (8 * π) *
      kernelIntegral (fun y => ‖y‖) (slow κ (spaceDeriv i (timeDeriv (timeDeriv ρ)))) p := by
  have hG : ContDiff ℝ ∞ (timeDeriv (timeDeriv ρ)) :=
    contDiff_infty_timeDeriv (contDiff_infty_timeDeriv h.smooth_charge)
  have hGs : SpatialSupport a (timeDeriv (timeDeriv ρ)) :=
    h.support_charge.timeDeriv.timeDeriv
  have hd : DifferentiableAt ℝ (kernelIntegral (fun y : E3 => ‖y‖) (slow κ (timeDeriv
      (timeDeriv ρ)))) p :=
    (hasFDerivAt_kernelIntegral locallyIntegrable_norm (contDiff_slow (hG.of_le (by simp)) κ)
      ((hGs.slow κ).kernelSupport _) p).differentiableAt
  rw [show timeDeriv (darwinGauge κ ρ) = fun q => κ ^ 2 / (8 * π) *
      kernelIntegral (fun y => ‖y‖) (slow κ (timeDeriv (timeDeriv ρ))) q from
      funext (h.timeDeriv_darwinGauge κ), spaceDeriv_const_mul hd,
    spaceDeriv_kernelIntegral_slow locallyIntegrable_norm (hG.of_le (by simp)) hGs]

/-- **The gradient of the scalar potential in the gauge of Darwin**: with `|∂ₛ³∂ᵢρ| ≤ M`, at
`‖x‖ ≤ R`, `|∂ᵢφ − ∂ᵢφ' − ∂ᵢ∂ₜχ| ≤ M (R + a)⁵ κ³/18`. -/
theorem spaceDeriv_scalar_sub (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (i : Fin 3)
    (hM : ∀ p, |timeDeriv^[3] (spaceDeriv i ρ) p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3}
    {R : ℝ} (hx : ‖x‖ ≤ R) :
    |spaceDeriv i (slowScalar κ ρ) (t, x) - spaceDeriv i (darwinScalar κ ρ) (t, x) -
        spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x)| ≤ M * (R + a) ^ 5 / 18 * κ ^ 3 := by
  have hρ : ContDiff ℝ ∞ ρ := h.smooth_charge
  have hg : ContDiff ℝ ∞ (spaceDeriv i ρ) := contDiff_infty_spaceDeriv hρ i
  have hgs : SpatialSupport a (spaceDeriv i ρ) := h.support_charge.spaceDeriv i
  have H := retardedIntegral_slow_expansion (n := 2) (hg.of_le (by simp)) ha hgs hM hκ t hx
  have h0 : slowTerm 0 (spaceDeriv i ρ) (κ * t) x =
      kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv i ρ)) (t, x) := by
    simp [slowTerm, kernelIntegral, slow, smul_eq_mul]
  have h1 : slowTerm 1 (spaceDeriv i ρ) (κ * t) x = 0 := by
    rw [slowTerm_one]
    have he : (fun z => timeDeriv (spaceDeriv i ρ) (κ * t, z)) =
        fun z => spaceDeriv i (timeDeriv ρ) (κ * t, z) :=
      funext fun z => timeDeriv_spaceDeriv (hρ.of_le (by simp)).contDiffAt i
    rw [he, integral_spaceDeriv_eq_zero (contDiff_timeDeriv (n := 1) (hρ.of_le (by simp)))
      h.support_charge.timeDeriv, mul_zero]
  have h2 : κ ^ 2 / 2 * slowTerm 2 (spaceDeriv i ρ) (κ * t) x =
      spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x) := by
    rw [slowTerm_two, h.spaceDeriv_timeDeriv_darwinGauge, kernelIntegral,
      iterate_timeDeriv_spaceDeriv (N := 3) (hρ.of_le (by simp)) i (by norm_num)]
    simp only [smul_eq_mul, slow, Prod.mk_sub_mk, sub_zero]
    rw [Function.iterate_succ_apply, Function.iterate_one]
    ring
  have hsum : ∑ k ∈ Finset.range (2 + 1), (-κ) ^ k / (k.factorial : ℝ) *
      slowTerm k (spaceDeriv i ρ) (κ * t) x =
      kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv i ρ)) (t, x) +
        spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x) := by
    rw [← h0, ← h2]
    simp [Finset.sum_range_succ, h1]
  rw [hsum] at H
  have hb : M * (R + a) ^ (2 + 3) / (3 * ((2 + 1).factorial : ℝ)) * κ ^ (2 + 1) =
      M * (R + a) ^ 5 / 18 * κ ^ 3 := by
    norm_num [Nat.factorial]
  rw [slowScalar, spaceDeriv_retardedIntegral_slow (hρ.of_le (by simp)) h.support_charge,
    darwinScalar, spaceDeriv_kernelIntegral_slow Potential.locallyIntegrable_newtonKernel
      (hρ.of_le (by simp)) h.support_charge, sub_sub, ← hb]
  exact H

/-- **The time derivative of the vector potential in the gauge of Darwin**: with
`|∂ₛ²jᵢ| ≤ M`, at `‖x‖ ≤ R`, `|∂ₜaᵢ − ∂ₜa'ᵢ + ∂ᵢ∂ₜχ| ≤ M (R + a)³ κ³/3`. -/
theorem timeDeriv_vector_sub (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (i : Fin 3)
    (hM : ∀ p, |timeDeriv (timeDeriv (j i)) p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3}
    {R : ℝ} (hx : ‖x‖ ≤ R) :
    |timeDeriv (slowVector κ j i) (t, x) - timeDeriv (darwinVector κ j i) (t, x) +
        spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x)| ≤ M * (R + a) ^ 3 / 3 * κ ^ 3 := by
  have hj : ContDiff ℝ ∞ (j i) := h.smooth_current i
  have hjs : SpatialSupport a (j i) := h.support_current i
  have hχ : ContDiff ℝ ∞ (darwinGauge κ ρ) := h.contDiff_darwinGauge κ
  have hR : Differentiable ℝ (retardedIntegral (slow κ (j i))) :=
    (contDiff_retardedIntegral (contDiff_slow hj κ) (hjs.slow κ).subluminalSupport).differentiable
      (by simp)
  have hN : Differentiable ℝ (kernelIntegral Potential.newtonKernel (slow κ (j i))) :=
    (contDiff_kernelIntegral Potential.locallyIntegrable_newtonKernel (contDiff_slow hj κ)
      ((hjs.slow κ).kernelSupport _)).differentiable (by simp)
  have hχi : Differentiable ℝ (spaceDeriv i (darwinGauge κ ρ)) :=
    (contDiff_infty_spaceDeriv hχ i).differentiable (by simp)
  have e1 : timeDeriv (slowVector κ j i) (t, x) =
      κ * (κ * retardedIntegral (slow κ (timeDeriv (j i))) (t, x)) := by
    rw [slowVector_eq, timeDeriv_const_mul (hR _),
      timeDeriv_retardedIntegral_slow (hj.of_le (by simp)) hjs]
  have e2 : timeDeriv (darwinVector κ j i) (t, x) =
      κ * (κ * kernelIntegral Potential.newtonKernel (slow κ (timeDeriv (j i))) (t, x)) +
        spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x) := by
    rw [show darwinVector κ j i = fun p => κ * kernelIntegral Potential.newtonKernel
        (slow κ (j i)) p + spaceDeriv i (darwinGauge κ ρ) p from funext (h.darwinVector_eq κ i),
      timeDeriv_fun_add ((hN _).const_mul κ) (hχi _), timeDeriv_const_mul (hN _),
      timeDeriv_kernelIntegral_slow Potential.locallyIntegrable_newtonKernel (hj.of_le (by simp))
        hjs, timeDeriv_spaceDeriv (hχ.of_le (by simp)).contDiffAt i]
  rw [e1, e2]
  have hB := abs_retardedIntegral_slow_sub_newton_le (contDiff_infty_timeDeriv hj |>.of_le
    (by simp)) ha hjs.timeDeriv hM hκ t hx
  have he : κ * (κ * retardedIntegral (slow κ (timeDeriv (j i))) (t, x)) -
      (κ * (κ * kernelIntegral Potential.newtonKernel (slow κ (timeDeriv (j i))) (t, x)) +
        spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x)) +
      spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x) =
      κ ^ 2 * (retardedIntegral (slow κ (timeDeriv (j i))) (t, x) -
        kernelIntegral Potential.newtonKernel (slow κ (timeDeriv (j i))) (t, x)) := by ring
  rw [he, abs_mul, abs_of_nonneg (by positivity)]
  calc κ ^ 2 * |retardedIntegral (slow κ (timeDeriv (j i))) (t, x) -
        kernelIntegral Potential.newtonKernel (slow κ (timeDeriv (j i))) (t, x)|
      ≤ κ ^ 2 * (M * (R + a) ^ 3 / 3 * κ) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = M * (R + a) ^ 3 / 3 * κ ^ 3 := by ring

/-- **The spatial derivatives of the vector potential in the gauge of Darwin**: with
`|∂ₛ∂ₗjₖ| ≤ M`, at `‖x‖ ≤ R`, `|∂ₗaₖ − ∂ₗa'ₖ + ∂ₗ∂ₖχ| ≤ M (R + a)³ κ²/3`. -/
theorem spaceDeriv_vector_sub (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (k l : Fin 3)
    (hM : ∀ p, |timeDeriv (spaceDeriv l (j k)) p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3}
    {R : ℝ} (hx : ‖x‖ ≤ R) :
    |spaceDeriv l (slowVector κ j k) (t, x) - spaceDeriv l (darwinVector κ j k) (t, x) +
        spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x)| ≤ M * (R + a) ^ 3 / 3 * κ ^ 2 := by
  have hj : ContDiff ℝ ∞ (j k) := h.smooth_current k
  have hjs : SpatialSupport a (j k) := h.support_current k
  have hχ : ContDiff ℝ ∞ (darwinGauge κ ρ) := h.contDiff_darwinGauge κ
  have hR : Differentiable ℝ (retardedIntegral (slow κ (j k))) :=
    (contDiff_retardedIntegral (contDiff_slow hj κ) (hjs.slow κ).subluminalSupport).differentiable
      (by simp)
  have hN : Differentiable ℝ (kernelIntegral Potential.newtonKernel (slow κ (j k))) :=
    (contDiff_kernelIntegral Potential.locallyIntegrable_newtonKernel (contDiff_slow hj κ)
      ((hjs.slow κ).kernelSupport _)).differentiable (by simp)
  have hχk : Differentiable ℝ (spaceDeriv k (darwinGauge κ ρ)) :=
    (contDiff_infty_spaceDeriv hχ k).differentiable (by simp)
  have e1 : spaceDeriv l (slowVector κ j k) (t, x) =
      κ * retardedIntegral (slow κ (spaceDeriv l (j k))) (t, x) := by
    rw [slowVector_eq, spaceDeriv_const_mul (hR _),
      spaceDeriv_retardedIntegral_slow (hj.of_le (by simp)) hjs]
  have e2 : spaceDeriv l (darwinVector κ j k) (t, x) =
      κ * kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv l (j k))) (t, x) +
        spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x) := by
    rw [show darwinVector κ j k = fun p => κ * kernelIntegral Potential.newtonKernel
        (slow κ (j k)) p + spaceDeriv k (darwinGauge κ ρ) p from funext (h.darwinVector_eq κ k),
      spaceDeriv_fun_add ((hN _).const_mul κ) (hχk _), spaceDeriv_const_mul (hN _),
      spaceDeriv_kernelIntegral_slow Potential.locallyIntegrable_newtonKernel
        (hj.of_le (by simp)) hjs]
  rw [e1, e2]
  have hB := abs_retardedIntegral_slow_sub_newton_le ((contDiff_infty_spaceDeriv hj l).of_le
    (by simp)) ha (hjs.spaceDeriv l) hM hκ t hx
  have he : κ * retardedIntegral (slow κ (spaceDeriv l (j k))) (t, x) -
      (κ * kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv l (j k))) (t, x) +
        spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x)) +
      spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x) =
      κ * (retardedIntegral (slow κ (spaceDeriv l (j k))) (t, x) -
        kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv l (j k))) (t, x)) := by ring
  rw [he, abs_mul, abs_of_nonneg hκ]
  calc κ * |retardedIntegral (slow κ (spaceDeriv l (j k))) (t, x) -
        kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv l (j k))) (t, x)|
      ≤ κ * (M * (R + a) ^ 3 / 3 * κ) := mul_le_mul_of_nonneg_left hB hκ
    _ = M * (R + a) ^ 3 / 3 * κ ^ 2 := by ring

end SlowSource

namespace SlowSource

variable {a : ℝ} {ρ : ℝ × E3 → ℝ} {j : Fin 3 → ℝ × E3 → ℝ}

/-- The difference of the Lorentz densities of the retarded potentials and of the potentials of
Darwin, at a point `‖x‖ ≤ R` and a velocity `‖𝐯‖ ≤ Vκ`, is at most
`(M r⁵/18 + M r³/3 + 6V M r³/3) κ³` with `r = R + a`. -/
theorem abs_lorentzDensity_sub_le (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ}
    (hM : SlowBounds M ρ j) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {R : ℝ} (hx : ‖x‖ ≤ R)
    {v : E3} {V : ℝ} (hv : ‖v‖ ≤ V * κ) (i : Fin 3) :
    |lorentzDensity (slowScalar κ ρ) (slowVector κ j) v i (t, x) -
        lorentzDensity (darwinScalar κ ρ) (darwinVector κ j) v i (t, x)| ≤
      (M * (R + a) ^ 5 / 18 + M * (R + a) ^ 3 / 3 + 6 * V * (M * (R + a) ^ 3 / 3)) * κ ^ 3 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM.current i (t, x))
  set e1 := spaceDeriv i (slowScalar κ ρ) (t, x) - spaceDeriv i (darwinScalar κ ρ) (t, x) -
    spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x) with he1
  set e2 := timeDeriv (slowVector κ j i) (t, x) - timeDeriv (darwinVector κ j i) (t, x) +
    spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x) with he2
  set m : Fin 3 → Fin 3 → ℝ := fun l k => spaceDeriv l (slowVector κ j k) (t, x) -
    spaceDeriv l (darwinVector κ j k) (t, x) + spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x)
    with hm
  have hsym : ∀ l k, spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x) =
      spaceDeriv k (spaceDeriv l (darwinGauge κ ρ)) (t, x) := fun l k =>
    spaceDeriv_spaceDeriv_comm ((h.contDiff_darwinGauge κ).of_le (by simp)).contDiffAt l k
  have hid : lorentzDensity (slowScalar κ ρ) (slowVector κ j) v i (t, x) -
      lorentzDensity (darwinScalar κ ρ) (darwinVector κ j) v i (t, x) =
      -e1 - e2 + ∑ k, v k * (m i k - m k i) := by
    rw [lorentzDensity, lorentzDensity, crossProduct_magneticOf, crossProduct_magneticOf,
      electricOf, electricOf]
    have hk : ∀ k, v k * (m i k - m k i) =
        v k * (spaceDeriv i (slowVector κ j k) (t, x) - spaceDeriv k (slowVector κ j i) (t, x)) -
        v k * (spaceDeriv i (darwinVector κ j k) (t, x) -
          spaceDeriv k (darwinVector κ j i) (t, x)) := fun k => by
      simp only [hm]
      rw [hsym i k]
      ring
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib, he1, he2]
    ring
  have hb1 := h.spaceDeriv_scalar_sub ha i (hM.charge i) hκ t hx
  have hb2 := h.timeDeriv_vector_sub ha i (hM.current i) hκ t hx
  have hbm : ∀ l k, |m l k| ≤ M * (R + a) ^ 3 / 3 * κ ^ 2 := fun l k =>
    h.spaceDeriv_vector_sub ha k l (hM.current_space k l) hκ t hx
  have hvk : ∀ k, |v k| ≤ V * κ := fun k =>
    (by simpa using PiLp.norm_apply_le v k : |v k| ≤ ‖v‖).trans hv
  have hsum : |∑ k, v k * (m i k - m k i)| ≤ 6 * V * (M * (R + a) ^ 3 / 3) * κ ^ 3 := by
    have hC : 0 ≤ M * (R + a) ^ 3 / 3 * κ ^ 2 := by
      have : 0 ≤ R + a := by linarith [norm_nonneg x]
      positivity
    calc |∑ k, v k * (m i k - m k i)| ≤ ∑ k, |v k * (m i k - m k i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 3, V * κ * (2 * (M * (R + a) ^ 3 / 3 * κ ^ 2)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          refine mul_le_mul (hvk k) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hvk k))
          linarith [abs_sub (m i k) (m k i), hbm i k, hbm k i]
      _ = 6 * V * (M * (R + a) ^ 3 / 3) * κ ^ 3 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  rw [hid]
  calc |-e1 - e2 + ∑ k, v k * (m i k - m k i)| ≤ |e1| + |e2| + |∑ k, v k * (m i k - m k i)| := by
        have := abs_add_le (-e1 - e2) (∑ k, v k * (m i k - m k i))
        have := abs_sub (-e1) e2
        rw [abs_neg] at this
        linarith
    _ ≤ M * (R + a) ^ 5 / 18 * κ ^ 3 + M * (R + a) ^ 3 / 3 * κ ^ 3 +
        6 * V * (M * (R + a) ^ 3 / 3) * κ ^ 3 := by gcongr
    _ = _ := by ring

/-- **The force of the retarded field and the Lagrangian of Darwin** (Landau–Lifshitz §65): a
rigid distribution `ρ₀(x − r(t))`, with `ρ₀` continuous and zero outside `‖z‖ ≤ b`, moves in the
retarded field of a slow source with `‖r(t)‖ ≤ R` and `‖ṙ(t)‖ ≤ Vκ`. The Lorentz force
`∫ ρ₀(x − r) (E + ṙ × B)` of the retarded field and the Euler–Lagrange residual of the
interaction Lagrangian of Darwin `rigidLagrangian ρ₀ φ' 𝐚'` (65.6) differ by at most

  `(∫|ρ₀|) (M r⁵/18 + M r³/3 + 6V M r³/3) κ³`,  `r = R + b + a`,

uniformly in the position. The Euler–Lagrange residual is exactly the Lorentz force of the
potentials of Darwin (`eulerLagrange_rigidLagrangian`), and these have the fields of the
retarded potentials up to `O(κ³)` in `E` and `O(κ²)` in `B`. -/
theorem force_eq_darwin (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (hM : SlowBounds M ρ j)
    {ρ₀ : E3 → ℝ} (hρ₀ : Continuous ρ₀) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → ρ₀ z = 0)
    {κ : ℝ} (hκ : 0 ≤ κ) {r : ℝ → E3} {t : ℝ} (hr : DifferentiableAt ℝ r t) {R V : ℝ}
    (hrR : ‖r t‖ ≤ R) (hV : ‖deriv r t‖ ≤ V * κ) (i : Fin 3) :
    |(∫ x, ρ₀ (x - r t) * lorentzDensity (slowScalar κ ρ) (slowVector κ j) (deriv r t) i (t, x)) -
        Mechanics.eulerLagrange (rigidLagrangian ρ₀ (darwinScalar κ ρ) (darwinVector κ j)) r t
          (EuclideanSpace.single i 1)| ≤
      (∫ z, |ρ₀ z|) * ((M * (R + b + a) ^ 5 / 18 + M * (R + b + a) ^ 3 / 3 +
        6 * V * (M * (R + b + a) ^ 3 / 3)) * κ ^ 3) := by
  have hc : HasCompactSupport ρ₀ :=
    HasCompactSupport.intro (isCompact_closedBall 0 b) fun z hz => hb z (by simpa using hz)
  have hφD : ContDiff ℝ 1 (darwinScalar κ ρ) := (h.contDiff_darwinScalar κ).of_le (by simp)
  have haD : ∀ k, ContDiff ℝ 1 (darwinVector κ j k) := fun k =>
    (h.contDiff_darwinVector κ k).of_le (by simp)
  have hφR : ContDiff ℝ 1 (slowScalar κ ρ) := (h.contDiff_slowScalar κ).of_le (by simp)
  have haR : ∀ k, ContDiff ℝ 1 (slowVector κ j k) := fun k =>
    (h.contDiff_slowVector κ k).of_le (by simp)
  rw [eulerLagrange_rigidLagrangian hρ₀ hc hφD haD hr i,
    ← integral_sub (integrable_smear hρ₀ hc (continuous_lorentzDensity hφR haR _ i) t (r t))
      (integrable_smear hρ₀ hc (continuous_lorentzDensity hφD haD _ i) t (r t))]
  set C := (M * (R + b + a) ^ 5 / 18 + M * (R + b + a) ^ 3 / 3 +
    6 * V * (M * (R + b + a) ^ 3 / 3)) * κ ^ 3 with hC
  have hint : Integrable fun x => |ρ₀ (x - r t)| * C :=
    (((hρ₀.comp (continuous_id.sub continuous_const)).abs).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.subRight (r t))).abs).mul_const C
  have hpt : ∀ x, ‖ρ₀ (x - r t) * lorentzDensity (slowScalar κ ρ) (slowVector κ j)
      (deriv r t) i (t, x) - ρ₀ (x - r t) * lorentzDensity (darwinScalar κ ρ) (darwinVector κ j)
        (deriv r t) i (t, x)‖ ≤ |ρ₀ (x - r t)| * C := by
    intro x
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hx : ‖x - r t‖ ≤ b
    · have hxR : ‖x‖ ≤ R + b := by
        have := norm_le_norm_add_norm_sub' x (r t)
        linarith
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [hC]
      exact h.abs_lorentzDensity_sub_le ha hM hκ t hxR hV i
    · simp [hb _ (not_le.mp hx)]
  rw [← Real.norm_eq_abs]
  calc ‖∫ x, (ρ₀ (x - r t) * lorentzDensity (slowScalar κ ρ) (slowVector κ j) (deriv r t) i
        (t, x) - ρ₀ (x - r t) * lorentzDensity (darwinScalar κ ρ) (darwinVector κ j)
          (deriv r t) i (t, x))‖
      ≤ ∫ x, |ρ₀ (x - r t)| * C := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = (∫ z, |ρ₀ z|) * C := by
        rw [integral_mul_const, integral_sub_right_eq_self (fun z => |ρ₀ z|) (r t)]

end SlowSource

/-! ### An instance: an oscillating dipole layer -/

/-- The derivative `∂₀χ` of the bump `χ = spaceBump` along the first axis. -/
def bumpSlope (x : E3) : ℝ := fderiv ℝ spaceBump x (EuclideanSpace.single 0 1)

/-- The charge `ρ(s, x) = cos s · ∂₀χ(x)` of the instance. -/
def exampleCharge : ℝ × E3 → ℝ := fun p => Real.cos p.1 * bumpSlope p.2

/-- The current `𝐣(s, x) = (sin s · χ(x), 0, 0)` of the instance. -/
def exampleCurrent : Fin 3 → ℝ × E3 → ℝ :=
  ![fun p => Real.sin p.1 * spaceBump p.2, fun _ => 0, fun _ => 0]

/-- The bump is smooth. -/
theorem contDiff_spaceBump : ContDiff ℝ ∞ (spaceBump : E3 → ℝ) := spaceBump.contDiff

/-- The slope of the bump is smooth. -/
theorem contDiff_bumpSlope : ContDiff ℝ ∞ bumpSlope :=
  (contDiff_spaceBump.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- The bump vanishes outside the ball of radius `2`. -/
theorem spaceBump_eq_zero {x : E3} (hx : 2 < ‖x‖) : spaceBump x = 0 :=
  image_eq_zero_of_notMem_tsupport (by
    rw [spaceBump.tsupport_eq]
    simpa [spaceBump] using hx)

/-- The derivative of the bump vanishes outside the ball of radius `2`. -/
theorem fderiv_spaceBump_eq_zero {x : E3} (hx : 2 < ‖x‖) : fderiv ℝ spaceBump x = 0 :=
  fderiv_of_notMem_tsupport ℝ (by
    rw [spaceBump.tsupport_eq]
    simpa [spaceBump] using hx)

/-- **An instance of a slow source**: the oscillating charge `cos s · ∂₀χ(x)` with the current
`(sin s · χ(x), 0, 0)` is smooth, stays in the ball of radius `2` and is conserved. -/
theorem slowSource_example : SlowSource 2 exampleCharge exampleCurrent := by
  have hcos : ContDiff ℝ ∞ fun p : ℝ × E3 => Real.cos p.1 := Real.contDiff_cos.comp contDiff_fst
  have hsin : ContDiff ℝ ∞ fun p : ℝ × E3 => Real.sin p.1 := Real.contDiff_sin.comp contDiff_fst
  refine ⟨hcos.mul (contDiff_bumpSlope.comp contDiff_snd), fun k => ?_, fun p hp => ?_,
    fun k p hp => ?_, fun p => ?_⟩
  · fin_cases k
    · exact hsin.mul (contDiff_spaceBump.comp contDiff_snd)
    · exact contDiff_const
    · exact contDiff_const
  · simp [exampleCharge, bumpSlope, fderiv_spaceBump_eq_zero hp]
  · fin_cases k <;> simp [exampleCurrent, spaceBump_eq_zero hp]
  · have h1 : timeDeriv exampleCharge = fun p => -Real.sin p.1 * bumpSlope p.2 :=
      timeDeriv_mul_slice (fun s => Real.hasDerivAt_cos s)
        (contDiff_bumpSlope.differentiable (by simp))
    have h2 : spaceDeriv 0 (exampleCurrent 0) =
        fun p => Real.sin p.1 * fderiv ℝ spaceBump p.2 (EuclideanSpace.single 0 1) :=
      spaceDeriv_mul_slice Real.differentiable_sin (contDiff_spaceBump.differentiable (by simp)) 0
    have h3 : ∀ k : Fin 3, k ≠ 0 → exampleCurrent k = fun _ => 0 := by
      intro k hk
      fin_cases k
      · exact absurd rfl hk
      · rfl
      · rfl
    rw [Fin.sum_univ_three, h1, h2, h3 1 (by decide), h3 2 (by decide), spaceDeriv_zero,
      spaceDeriv_zero]
    simp [bumpSlope]

/-- **The instance has bounded derivatives**: some `M` bounds `∂ₛ³∂ᵢρ`, `∂ₛ²jᵢ` and `∂ₛ∂ₗjᵢ`. -/
theorem exists_slowBounds_example : ∃ M, SlowBounds M exampleCharge exampleCurrent := by
  obtain ⟨C₁, hC₁⟩ :=
    (contDiff_bumpSlope.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (HasCompactSupport.fderiv (𝕜 := ℝ) (HasCompactSupport.intro (isCompact_closedBall (0 : E3) 2)
      fun x hx => by simp [bumpSlope, fderiv_spaceBump_eq_zero (by simpa using hx)]))
  obtain ⟨C₂, hC₂⟩ :=
    (contDiff_spaceBump.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (spaceBump.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hslope : ∀ i x, |fderiv ℝ bumpSlope x (EuclideanSpace.single i 1)| ≤ C₁ := fun i x => by
    have := (fderiv ℝ bumpSlope x).le_opNorm (EuclideanSpace.single i 1)
    rw [PiLp.norm_single, norm_one, mul_one] at this
    exact (Real.norm_eq_abs _ ▸ this).trans (hC₁ x)
  have hbump : ∀ l x, |fderiv ℝ spaceBump x (EuclideanSpace.single l 1)| ≤ C₂ := fun l x => by
    have := (fderiv ℝ spaceBump x).le_opNorm (EuclideanSpace.single l 1)
    rw [PiLp.norm_single, norm_one, mul_one] at this
    exact (Real.norm_eq_abs _ ▸ this).trans (hC₂ x)
  have hC₁0 : 0 ≤ C₁ := (abs_nonneg _).trans (hslope 0 0)
  have hC₂0 : 0 ≤ C₂ := (abs_nonneg _).trans (hbump 0 0)
  have hsl : Differentiable ℝ bumpSlope := contDiff_bumpSlope.differentiable (by simp)
  have hbd : Differentiable ℝ (spaceBump : E3 → ℝ) := contDiff_spaceBump.differentiable (by simp)
  have hbd' : ∀ l, Differentiable ℝ fun x : E3 =>
      fderiv ℝ spaceBump x (EuclideanSpace.single l 1) :=
    fun l => ((contDiff_spaceBump.fderiv_right (m := ∞) le_rfl).clm_apply
      contDiff_const).differentiable (by simp)
  have hzero : ∀ k : Fin 3, k ≠ 0 → exampleCurrent k = fun _ => 0 := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · rfl
    · rfl
  refine ⟨C₁ + C₂ + 1, fun i p => ?_, fun i p => ?_, fun i l p => ?_⟩
  · have h0 : spaceDeriv i exampleCharge = fun p => Real.cos p.1 *
        fderiv ℝ bumpSlope p.2 (EuclideanSpace.single i 1) :=
      spaceDeriv_mul_slice Real.differentiable_cos hsl i
    have hsd : Differentiable ℝ fun x => fderiv ℝ bumpSlope x (EuclideanSpace.single i 1) :=
      ((contDiff_bumpSlope.fderiv_right (m := ∞) le_rfl).clm_apply
        contDiff_const).differentiable (by simp)
    set G : E3 → ℝ := fun x => fderiv ℝ bumpSlope x (EuclideanSpace.single i 1) with hG
    have h1 : timeDeriv (fun p : ℝ × E3 => Real.cos p.1 * G p.2) =
        fun p => -Real.sin p.1 * G p.2 :=
      timeDeriv_mul_slice (fun s => Real.hasDerivAt_cos s) hsd
    have h2 : timeDeriv (fun p : ℝ × E3 => -Real.sin p.1 * G p.2) =
        fun p => -Real.cos p.1 * G p.2 :=
      timeDeriv_mul_slice (c := fun s => -Real.sin s) (fun s => (Real.hasDerivAt_sin s).fun_neg)
        hsd
    have h3 : timeDeriv (fun p : ℝ × E3 => -Real.cos p.1 * G p.2) =
        fun p => Real.sin p.1 * G p.2 := by
      rw [timeDeriv_mul_slice (c := fun s => -Real.cos s) (fun s => (Real.hasDerivAt_cos s).fun_neg)
        hsd]
      simp
    rw [h0, Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_one, h1,
      h2, h3, abs_mul]
    calc |Real.sin p.1| * |fderiv ℝ bumpSlope p.2 (EuclideanSpace.single i 1)| ≤ 1 * C₁ :=
          mul_le_mul (Real.abs_sin_le_one _) (hslope i p.2) (abs_nonneg _) zero_le_one
      _ ≤ C₁ + C₂ + 1 := by linarith
  · by_cases hi : i = 0
    · subst hi
      have h1 := timeDeriv_mul_slice (fun s => Real.hasDerivAt_sin s) hbd
      have h2 := timeDeriv_mul_slice (fun s => Real.hasDerivAt_cos s) hbd
      change |timeDeriv (timeDeriv fun p : ℝ × E3 => Real.sin p.1 * spaceBump p.2) p| ≤ _
      rw [h1, h2, abs_mul, abs_neg]
      calc |Real.sin p.1| * |spaceBump p.2| ≤ 1 * 1 :=
            mul_le_mul (Real.abs_sin_le_one _) (by
              rw [abs_of_nonneg spaceBump.nonneg]
              exact spaceBump.le_one) (abs_nonneg _) zero_le_one
        _ ≤ C₁ + C₂ + 1 := by linarith
    · rw [hzero i hi, timeDeriv_zero, timeDeriv_zero]
      simp only [abs_zero]
      linarith
  · by_cases hi : i = 0
    · subst hi
      have h0 : spaceDeriv l (exampleCurrent 0) = fun p => Real.sin p.1 *
          fderiv ℝ spaceBump p.2 (EuclideanSpace.single l 1) :=
        spaceDeriv_mul_slice Real.differentiable_sin hbd l
      rw [h0, timeDeriv_mul_slice (fun s => Real.hasDerivAt_sin s) (hbd' l), abs_mul]
      calc |Real.cos p.1| * |fderiv ℝ spaceBump p.2 (EuclideanSpace.single l 1)| ≤ 1 * C₂ :=
            mul_le_mul (Real.abs_cos_le_one _) (hbump l p.2) (abs_nonneg _) zero_le_one
        _ ≤ C₁ + C₂ + 1 := by linarith
    · rw [hzero i hi, spaceDeriv_zero, timeDeriv_zero]
      simp only [abs_zero]
      linarith

/-! ### The point limit -/

/-- A rigid charge `e η(x − R(s))` carried along the path `R`. -/
def rigidCharge (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) : ℝ × E3 → ℝ := fun p => e * η (p.2 - R p.1)

/-- The current `e Ṙ(s) η(x − R(s))` of a rigid charge. -/
def rigidCurrent (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (k : Fin 3) : ℝ × E3 → ℝ :=
  fun p => e * deriv R p.1 k * η (p.2 - R p.1)

/-- The interaction of two point charges in the Lagrangian of Darwin (65.7), in the units with
`div E = ρ`: `−e₁e₂/(4πR) + e₁e₂ [𝐯₁ · 𝐯₂ + (𝐯₁ · 𝐧)(𝐯₂ · 𝐧)]/(8πR)` with `R = ‖r₂ − r₁‖`
and `𝐧 = (r₂ − r₁)/R`. -/
def darwinPair (e₁ e₂ : ℝ) (r₁ r₂ v₁ v₂ : E3) : ℝ :=
  -(e₁ * e₂) / (4 * π * ‖r₂ - r₁‖) +
    e₁ * e₂ * (inner ℝ v₁ v₂ + inner ℝ v₁ (‖r₂ - r₁‖⁻¹ • (r₂ - r₁)) *
      inner ℝ v₂ (‖r₂ - r₁‖⁻¹ • (r₂ - r₁))) / (8 * π * ‖r₂ - r₁‖)

/-- The kernel of Darwin contracted with two velocities:
`Σᵢₖ wᵢ vₖ (δᵢₖ + nᵢnₖ)/(8πR) = [𝐯 · 𝐰 + (𝐯 · 𝐧)(𝐰 · 𝐧)]/(8πR)`. -/
theorem sum_darwinKernel (v w z : E3) :
    ∑ i, w i * ∑ k, v k * darwinKernel i k z =
      (inner ℝ v w + inner ℝ v (‖z‖⁻¹ • z) * inner ℝ w (‖z‖⁻¹ • z)) / (8 * π * ‖z‖) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [darwinKernel]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp only [darwinKernel, inner_smul_right, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three, star_trivial]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  field_simp
  ring

/-- The kernel of Darwin is continuous away from the origin. -/
theorem continuousAt_darwinKernel (i k : Fin 3) {z : E3} (hz : z ≠ 0) :
    ContinuousAt (darwinKernel i k) z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hc : ∀ l : Fin 3, Continuous fun y : E3 => y l := fun l =>
    (EuclideanSpace.proj l : E3 →L[ℝ] ℝ).continuous
  unfold darwinKernel
  exact ((continuousAt_const.div continuous_norm.continuousAt hn).add
    ((((hc i).mul (hc k)).continuousAt).div (continuous_norm.continuousAt.pow 3)
      (pow_ne_zero 3 hn))).div_const _

/-- The Newton kernel is continuous away from the origin. -/
theorem continuousAt_newtonKernel {z : E3} (hz : z ≠ 0) : ContinuousAt Potential.newtonKernel z :=
  (Potential.contDiffAt_newtonKernel hz (n := 0)).continuousAt

/-- A kernel continuous away from the origin is continuous on a ball about `z₀ ≠ 0` of radius
`‖z₀‖/2`. -/
theorem continuousOn_closedBall_of_continuousAt {K : E3 → ℝ}
    (hK : ∀ z : E3, z ≠ 0 → ContinuousAt K z) {z₀ : E3} (hz₀ : z₀ ≠ 0) :
    ContinuousOn K (closedBall z₀ (‖z₀‖ / 2)) := fun z hz => by
  refine (hK z fun h => ?_).continuousWithinAt
  subst h
  rw [mem_closedBall, dist_zero_left] at hz
  have := norm_pos_iff.mpr hz₀
  linarith

/-- The smeared kernel `x ↦ ∫ K(y) η(x − y − r) dy` of a locally integrable kernel against a
continuous profile vanishing outside a ball is continuous. -/
theorem continuous_kernel_average {K : E3 → ℝ} (hK : LocallyIntegrable K) {η : E3 → ℝ}
    (hη : Continuous η) {ε : ℝ} (hηs : ∀ z : E3, ε < ‖z‖ → η z = 0) (r : E3) :
    Continuous fun x => ∫ y, K y * η (x - y - r) := by
  set F : ℝ × E3 → ℝ := fun p => η (p.2 - r) with hF
  have hFs : SpatialSupport (ε + ‖r‖) F := fun p hp => hηs _ (by
    have := norm_sub_norm_le p.2 r
    linarith)
  have hc := (continuous_kernelIntegral hK (hη.comp (continuous_snd.sub continuous_const))
    (hFs.kernelSupport K)).comp (continuous_const.prodMk continuous_id : Continuous fun x : E3 =>
      ((0 : ℝ), x))
  refine hc.congr fun x => ?_
  simp [kernelIntegral, smul_eq_mul, sub_right_comm]

/-- **The point limit of the interaction of Darwin** (65.7): for rigid charges `e₁ η_ε(x − R₁(s))`
and `e₂ η_ε(x − r₂)` with even weights `η_ε` of mass one supported in the balls of radius `ε`,
the interaction Lagrangian `rigidLagrangian` of the second charge, with the velocity `𝐯₂`, in
the potentials of Darwin of the first converges as `ε → 0⁺` to

  `−e₁e₂/(4πR) + e₁e₂ [𝐯₁ · 𝐯₂ + (𝐯₁ · 𝐧)(𝐯₂ · 𝐧)]/(8πR)`  (`darwinPair`),

with `r₁ = R₁(κt)`, `𝐯₁ = κṘ₁(κt)`, `R = ‖r₂ − r₁‖ > 0`. Newton's theorem is not needed: the
interaction is a double average of the kernels, which are continuous near `r₂ − r₁`. -/
theorem darwinInteraction_pointLimit {η : ℝ → E3 → ℝ} (hηc : ∀ ε, Continuous (η ε))
    (hη0 : ∀ ε z, 0 ≤ η ε z) (hη1 : ∀ ε, 0 < ε → ∫ z, η ε z = 1)
    (hηs : ∀ ε, 0 < ε → ∀ z : E3, ε < ‖z‖ → η ε z = 0) (hηe : ∀ ε z, η ε (-z) = η ε z)
    (e₁ e₂ κ : ℝ) (R₁ : ℝ → E3) (t : ℝ) (r₂ v₂ : E3) (hR : r₂ ≠ R₁ (κ * t)) :
    Tendsto (fun ε => rigidLagrangian (fun z => e₂ * η ε z)
        (darwinScalar κ (rigidCharge e₁ (η ε) R₁)) (darwinVector κ (rigidCurrent e₁ (η ε) R₁))
        t (r₂, v₂)) (𝓝[>] 0)
      (𝓝 (darwinPair e₁ e₂ (R₁ (κ * t)) r₂ (κ • deriv R₁ (κ * t)) v₂)) := by
  set r₁ := R₁ (κ * t) with hr₁
  set v₁ : E3 := κ • deriv R₁ (κ * t) with hv₁
  have hz₀ : r₂ - r₁ ≠ 0 := sub_ne_zero.mpr hR
  have hδ : 0 < ‖r₂ - r₁‖ / 2 := by have := norm_pos_iff.mpr hz₀; positivity
  set A : ℝ → (E3 → ℝ) → ℝ := fun ε K => ∫ x, η ε (x - r₂) * ∫ y, K y * η ε (x - y - r₁)
    with hA
  have hlim : ∀ K : E3 → ℝ, LocallyIntegrable K → (∀ z : E3, z ≠ 0 → ContinuousAt K z) →
      Tendsto (fun ε => A ε K) (𝓝[>] 0) (𝓝 (K (r₂ - r₁))) := fun K hK hKc =>
    tendsto_integral_weight_mul_average hηc hη0 hη1 hηs hηe hδ
      (continuousOn_closedBall_of_continuousAt hKc hz₀)
      (fun ε hε => continuous_kernel_average hK (hηc ε) (hηs ε hε) r₁)
  have hinner : ∀ ε (K : E3 → ℝ) (c : ℝ) (x : E3),
      (∫ y, K y * (c * η ε (x - y - r₁))) = c * ∫ y, K y * η ε (x - y - r₁) :=
    fun ε K c x => by
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
  have hscalar : ∀ ε, smear (fun z => e₂ * η ε z)
      (darwinScalar κ (rigidCharge e₁ (η ε) R₁)) t r₂ = e₁ * e₂ * A ε Potential.newtonKernel := by
    intro ε
    have hpt : ∀ x : E3, darwinScalar κ (rigidCharge e₁ (η ε) R₁) (t, x) =
        e₁ * ∫ y, Potential.newtonKernel y * η ε (x - y - r₁) := fun x => by
      rw [← hinner]
      simp [darwinScalar, kernelIntegral, slow, rigidCharge, smul_eq_mul, hr₁]
    simp only [smear, hpt, hA]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hvector : ∀ ε, 0 < ε → ∀ i, smear (fun z => e₂ * η ε z)
      (darwinVector κ (rigidCurrent e₁ (η ε) R₁) i) t r₂ =
      e₁ * e₂ * ∑ k, v₁ k * A ε (darwinKernel i k) := by
    intro ε hε i
    have hpt : ∀ x : E3, darwinVector κ (rigidCurrent e₁ (η ε) R₁) i (t, x) =
        e₁ * ∑ k, v₁ k * ∫ y, darwinKernel i k y * η ε (x - y - r₁) := fun x => by
      simp only [darwinVector, kernelIntegral, slow, rigidCurrent, smul_eq_mul, Prod.mk_sub_mk,
        sub_zero, ← hr₁]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hinner, hv₁, PiLp.smul_apply, smul_eq_mul]
      ring
    have hηcs : HasCompactSupport fun x => η ε (x - r₂) :=
      (HasCompactSupport.intro (isCompact_closedBall 0 ε) fun z hz =>
        hηs ε hε z (by simpa using hz)).comp_homeomorph (Homeomorph.subRight r₂)
    have hint : ∀ k, Integrable fun x =>
        η ε (x - r₂) * ∫ y, darwinKernel i k y * η ε (x - y - r₁) := fun k =>
      (((hηc ε).comp (continuous_id.sub continuous_const)).mul
        (continuous_kernel_average (locallyIntegrable_darwinKernel i k) (hηc ε) (hηs ε hε)
          r₁)).integrable_of_hasCompactSupport hηcs.mul_right
    simp only [smear, hpt, hA]
    have he : (fun x => e₂ * η ε (x - r₂) *
        (e₁ * ∑ k, v₁ k * ∫ y, darwinKernel i k y * η ε (x - y - r₁))) =
        fun x => e₁ * e₂ * ∑ k, v₁ k * (η ε (x - r₂) *
          ∫ y, darwinKernel i k y * η ε (x - y - r₁)) := by
      funext x
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [he, integral_const_mul, integral_finsetSum _ fun k _ => (hint k).const_mul _]
    simp only [integral_const_mul]
  have hL : ∀ ε, 0 < ε → rigidLagrangian (fun z => e₂ * η ε z)
      (darwinScalar κ (rigidCharge e₁ (η ε) R₁)) (darwinVector κ (rigidCurrent e₁ (η ε) R₁))
      t (r₂, v₂) = -(e₁ * e₂ * A ε Potential.newtonKernel) +
        ∑ i, v₂ i * (e₁ * e₂ * ∑ k, v₁ k * A ε (darwinKernel i k)) := fun ε hε => by
    simp only [rigidLagrangian, hscalar, hvector ε hε]
  have hT := ((hlim Potential.newtonKernel Potential.locallyIntegrable_newtonKernel
    fun z hz => continuousAt_newtonKernel hz).const_mul (e₁ * e₂)).neg.add
    (tendsto_finsetSum Finset.univ fun i _ => ((tendsto_finsetSum Finset.univ fun k _ =>
      (hlim (darwinKernel i k) (locallyIntegrable_darwinKernel i k)
        fun z hz => continuousAt_darwinKernel i k hz).const_mul (v₁ k)).const_mul
          (e₁ * e₂)).const_mul (v₂ i))
  have hval : -(e₁ * e₂ * Potential.newtonKernel (r₂ - r₁)) +
      ∑ i, v₂ i * (e₁ * e₂ * ∑ k, v₁ k * darwinKernel i k (r₂ - r₁)) =
      darwinPair e₁ e₂ r₁ r₂ v₁ v₂ := by
    have hs := sum_darwinKernel v₁ v₂ (r₂ - r₁)
    have hs' : ∑ i, v₂ i * (e₁ * e₂ * ∑ k, v₁ k * darwinKernel i k (r₂ - r₁)) =
        e₁ * e₂ * ∑ i, v₂ i * ∑ k, v₁ k * darwinKernel i k (r₂ - r₁) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hs', hs, darwinPair, Potential.newtonKernel]
    ring
  rw [← hval]
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [hL ε hε]

/-- A family of weights for the point limit: the normalized smooth bump of radius `ε`
(and `0` for `ε ≤ 0`). -/
def pointBump (ε : ℝ) : E3 → ℝ :=
  if h : 0 < ε then (⟨ε / 2, ε, by positivity, by linarith⟩ : ContDiffBump (0 : E3)).normed volume
  else 0

/-- **The point limit for the normalized bumps**: `darwinInteraction_pointLimit` holds for the
family `pointBump`, which is continuous, nonnegative, even, of mass one and supported in the ball
of radius `ε`. -/
theorem darwinInteraction_pointLimit_pointBump (e₁ e₂ κ : ℝ) (R₁ : ℝ → E3) (t : ℝ)
    (r₂ v₂ : E3) (hR : r₂ ≠ R₁ (κ * t)) :
    Tendsto (fun ε => rigidLagrangian (fun z => e₂ * pointBump ε z)
        (darwinScalar κ (rigidCharge e₁ (pointBump ε) R₁))
        (darwinVector κ (rigidCurrent e₁ (pointBump ε) R₁)) t (r₂, v₂)) (𝓝[>] 0)
      (𝓝 (darwinPair e₁ e₂ (R₁ (κ * t)) r₂ (κ • deriv R₁ (κ * t)) v₂)) := by
  refine darwinInteraction_pointLimit (fun ε => ?_) (fun ε z => ?_) (fun ε hε => ?_)
    (fun ε hε z hz => ?_) (fun ε z => ?_) e₁ e₂ κ R₁ t r₂ v₂ hR
  · unfold pointBump
    split_ifs
    · exact ContDiffBump.continuous_normed _
    · exact continuous_const
  · unfold pointBump
    split_ifs
    · exact ContDiffBump.nonneg_normed _ z
    · exact le_rfl
  · simp only [pointBump, hε, ↓reduceDIte]
    exact ContDiffBump.integral_normed _
  · simp only [pointBump, hε, ↓reduceDIte]
    refine Function.notMem_support.mp fun hmem => ?_
    rw [ContDiffBump.support_normed_eq, mem_ball_zero_iff] at hmem
    exact absurd hz (not_lt.mpr hmem.le)
  · unfold pointBump
    split_ifs
    · exact ContDiffBump.normed_neg _ z
    · rfl

/-! ### The Lagrangian of `N` charges -/

/-- The interaction of Darwin is symmetric in the two charges. -/
theorem darwinPair_comm (e₁ e₂ : ℝ) (r₁ r₂ v₁ v₂ : E3) :
    darwinPair e₁ e₂ r₁ r₂ v₁ v₂ = darwinPair e₂ e₁ r₂ r₁ v₂ v₁ := by
  have h : r₁ - r₂ = -(r₂ - r₁) := (neg_sub r₂ r₁).symm
  simp only [darwinPair, h, norm_neg, smul_neg, inner_neg_right, real_inner_comm v₁ v₂]
  ring

/-- **The Lagrangian of Darwin** (65.7) of `N` point charges with the masses `m` and the charges
`e`, to the second order in `v/c`: the expansion `−m + mv²/2 + mv⁴/8` of the free Lagrangian
`−m√(1 − v²)` (`abs_sqrt_one_sub_sub_le`) and the interactions `darwinPair` of the pairs. -/
def darwinLagrangian {N : ℕ} (m e : Fin N → ℝ) : Mechanics.Lagrangian (Fin N → E3) :=
  fun _ q => ∑ a, (-m a + m a * ‖q.2 a‖ ^ 2 / 2 + m a * ‖q.2 a‖ ^ 4 / 8) +
    ∑ a, ∑ b, if a < b then darwinPair (e a) (e b) (q.1 a) (q.1 b) (q.2 a) (q.2 b) else 0

/-- **The kinetic expansion**: `|√(1 − s) − (1 − s/2 − s²/8)| ≤ s³/4` for `0 ≤ s ≤ 1/2`, so the
free Lagrangian `−m√(1 − v²)` is `−m + mv²/2 + mv⁴/8` up to `|m| v⁶/4`. -/
theorem abs_sqrt_one_sub_sub_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    |√(1 - s) - (1 - s / 2 - s ^ 2 / 8)| ≤ s ^ 3 / 4 := by
  set y := √(1 - s) with hy
  set P := 1 - s / 2 - s ^ 2 / 8 with hP
  have hy2 : y ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hyP : 1 ≤ y + P := by
    have : 1 / 2 ≤ y ^ 2 := by rw [hy2]; linarith
    have h1 : 1 / 2 ≤ y := by nlinarith
    nlinarith
  have hdiff : y - P = -(s ^ 3 / 8 + s ^ 4 / 64) / (y + P) := by
    rw [eq_div_iff (by linarith)]
    nlinarith [hy2]
  rw [hdiff, abs_div, abs_neg, abs_of_nonneg (by positivity), abs_of_pos (by linarith)]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_nonneg hs0 3, pow_nonneg hs0 4]

/-- **The free Lagrangian to the fourth order**: `|−m√(1 − v²) − (−m + mv²/2 + mv⁴/8)| ≤
|m| v⁶/4` for `v² ≤ 1/2`. -/
theorem abs_free_sub_darwin_le (m : ℝ) {v : E3} (hv : ‖v‖ ^ 2 ≤ 1 / 2) :
    |-m * √(1 - ‖v‖ ^ 2) - (-m + m * ‖v‖ ^ 2 / 2 + m * ‖v‖ ^ 4 / 8)| ≤ |m| * ‖v‖ ^ 6 / 4 := by
  have h := abs_sqrt_one_sub_sub_le (sq_nonneg ‖v‖) hv
  have he : -m * √(1 - ‖v‖ ^ 2) - (-m + m * ‖v‖ ^ 2 / 2 + m * ‖v‖ ^ 4 / 8) =
      -m * (√(1 - ‖v‖ ^ 2) - (1 - ‖v‖ ^ 2 / 2 - (‖v‖ ^ 2) ^ 2 / 8)) := by ring
  rw [he, abs_mul, abs_neg]
  calc |m| * |√(1 - ‖v‖ ^ 2) - (1 - ‖v‖ ^ 2 / 2 - (‖v‖ ^ 2) ^ 2 / 8)| ≤
        |m| * ((‖v‖ ^ 2) ^ 3 / 4) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |m| * ‖v‖ ^ 6 / 4 := by ring

/-- **The Lagrangian of Darwin is the point limit** (Landau–Lifshitz §65): for prescribed slow
trajectories `r_a(t) = R_a(κt)` with the velocities `κṘ_a(κt)`, separated at the time `t`, the
Lagrangian (65.7) is the kinetic expansion plus the limit `ε → 0⁺` of the interaction
Lagrangians `rigidLagrangian` of the smeared charges `e_b η_ε(x − r_b)` in the potentials of
Darwin of the smeared charges `e_a`, `a < b` (`darwinInteraction_pointLimit_pointBump`). -/
theorem darwinLagrangian_pointLimit {N : ℕ} (m e : Fin N → ℝ) (κ : ℝ) (R : Fin N → ℝ → E3)
    (t : ℝ) (hsep : ∀ a b, a ≠ b → R a (κ * t) ≠ R b (κ * t)) :
    Tendsto (fun ε => ∑ a, (-m a + m a * ‖κ • deriv (R a) (κ * t)‖ ^ 2 / 2 +
        m a * ‖κ • deriv (R a) (κ * t)‖ ^ 4 / 8) +
      ∑ a, ∑ b, if a < b then rigidLagrangian (fun z => e b * pointBump ε z)
        (darwinScalar κ (rigidCharge (e a) (pointBump ε) (R a)))
        (darwinVector κ (rigidCurrent (e a) (pointBump ε) (R a))) t
        (R b (κ * t), κ • deriv (R b) (κ * t)) else 0) (𝓝[>] 0)
      (𝓝 (darwinLagrangian m e t
        (fun a => R a (κ * t), fun a => κ • deriv (R a) (κ * t)))) := by
  refine tendsto_const_nhds.add (tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_)
  by_cases hab : a < b
  · simp only [hab, ↓reduceIte]
    exact darwinInteraction_pointLimit_pointBump (e a) (e b) κ (R a) t _ _
      (hsep b a (ne_of_gt hab))
  · simp only [hab, ↓reduceIte]
    exact tendsto_const_nhds

/-! ### An application of the force of Darwin -/

/-- **The force of Darwin for the instance**: a bump at rest at `5e₀`, in the retarded field of
the oscillating source `slowSource_example`, feels the force of the Lagrangian of Darwin up to
`C κ³` with a constant `C` independent of the slowness and of the time. -/
theorem force_eq_darwin_example (i : Fin 3) :
    ∃ C, ∀ κ, 0 ≤ κ → ∀ t, |(∫ x, spaceBump (x - (5 : ℝ) • EuclideanSpace.single 0 1) *
        lorentzDensity (slowScalar κ exampleCharge) (slowVector κ exampleCurrent)
          (deriv (fun _ : ℝ => (5 : ℝ) • (EuclideanSpace.single 0 1 : E3)) t) i (t, x)) -
      Mechanics.eulerLagrange (rigidLagrangian spaceBump (darwinScalar κ exampleCharge)
        (darwinVector κ exampleCurrent)) (fun _ => (5 : ℝ) • EuclideanSpace.single 0 1) t
          (EuclideanSpace.single i 1)| ≤ C * κ ^ 3 := by
  obtain ⟨M, hM⟩ := exists_slowBounds_example
  refine ⟨(∫ z, |spaceBump z|) * (M * (5 + 2 + 2) ^ 5 / 18 + M * (5 + 2 + 2) ^ 3 / 3 +
    6 * 0 * (M * (5 + 2 + 2) ^ 3 / 3)), fun κ hκ t => ?_⟩
  have hr5 : ‖(5 : ℝ) • (EuclideanSpace.single 0 1 : E3)‖ ≤ 5 := by
    rw [norm_smul, PiLp.norm_single]
    norm_num
  have h := slowSource_example.force_eq_darwin (by norm_num) hM spaceBump.continuous
    (b := 2) (fun z hz => spaceBump_eq_zero hz) hκ (t := t) (differentiableAt_const _) hr5
    (V := 0) (by simp) i
  rw [mul_assoc]
  exact h

end ProjectAinos.Electrodynamics
