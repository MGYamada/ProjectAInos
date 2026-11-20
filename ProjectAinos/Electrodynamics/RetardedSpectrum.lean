/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.RetardedPotential
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Tactic

/-!
# The spectral resolution of the retarded potentials

Landau–Lifshitz, *The Classical Theory of Fields*, §64. The Fourier transform in time has
Mathlib's normalization `ĝ(ν, x) = ∫ e^{−2πiνt} g(t, x) dt` (`timeFourier` on `ℝ × ℝ³`, and
`spacetimeFourier` on `Spacetime` through the splitting `Wave.timeSpaceEquiv`), in the frequency
`ν = ω/2π`; the Fourier component `g_ω = ∫ g e^{iωt} dt` of Landau–Lifshitz is `ĝ(−ω/2π, x)`, so
the phase `e^{−2πiν‖y‖}` below is their `e^{ikR}`. The units have `c = 1` and `div E = k⁰`, and the
sources have compact support in space-time.

* `fourier_retardedIntegral`: **the spectral resolution of the retarded integral**,
  `Â(ν, x) = ∫ e^{−2πiν‖y‖} f̂(ν, x − y)/(4π‖y‖) dy` for a continuous source `f`, by Fubini's
  theorem (`integrable_fourier_retarded`) and the translation `t ↦ t + ‖y‖` of the time.
* `helmholtz_fourier_retardedIntegral`: **the Helmholtz equation** `(Δ + (2πν)²) Â = −f̂` for a
  `C²` source, with Mathlib's Laplacian `Δ` of functions `ℝ³ → ℂ`. It follows from the wave
  equation `□A = ∂ₜ²A − ΔA = f` (`Wave.wave_retardedIntegral`) by `helmholtz_timeFourier`: the
  time derivative becomes `(∂ₜu)^ = 2πiν û` (`timeFourier_timeDeriv`, from `Real.fourier_deriv`),
  and the derivatives in space commute with the transform (`hasFDerivAt_timeFourier`,
  `fderiv_timeFourier_apply`, `laplacian_timeFourier`).
* `TimeBoundedSupport a g`: the support lies in `|t| ≤ a + ‖x‖`, so that `g` has compact support
  in time at every point of space, locally uniformly. The retarded integral of a source of compact
  support has one (`exists_timeBoundedSupport_retardedIntegral`): by Huygens' principle in three
  dimensions the source is seen at `x` only during a bounded interval of time.
* `fourier_retardedPotential` and `helmholtz_fourier_retardedPotential`: the components
  `A₀ = −φ` and `aᵢ` of the retarded potential `retardedPotential k` have
  `Â₀ = −∫ e^{−2πiν‖y‖} k̂⁰(ν, x − y)/(4π‖y‖) dy`, `âᵢ = ∫ e^{−2πiν‖y‖} k̂ⁱ(ν, x − y)/(4π‖y‖) dy`,
  `(Δ + (2πν)²) Â₀ = k̂⁰` and `(Δ + (2πν)²) âᵢ = −k̂ⁱ`, that is `(Δ + (2πν)²) Â_μ = −k̂_μ` with the
  index lowered by `η = diag(−1, 1, 1, 1)`, as `box A_μ = −k_μ` (`box_retardedPotential`).
* An instance: the circulating current `circulatingCurrent`, a nonzero smooth conserved current of
  compact support (`fourier_retardedPotential_circulatingCurrent`,
  `helmholtz_fourier_retardedPotential_circulatingCurrent`).

The far-zone radiation amplitude of a point charge needs the field of Liénard and Wiechert and is
not treated here; nor is the inverse transform.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff FourierTransform Laplacian

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The Fourier transform in time -/

section TimeFourier

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The **Fourier transform in time** `ĝ(ν, x) = ∫ e^{−2πiνt} g(t, x) dt` of a function on
`ℝ × ℝ³`, at the frequency `ν` and the point `x` of space. -/
def timeFourier (g : ℝ × E3 → G) (ν : ℝ) (x : E3) : G := 𝓕 (fun t : ℝ => g (t, x)) ν

/-- The Fourier transform in time is `∫ e^{−2πiνt} g(t, x) dt`. -/
theorem timeFourier_eq (g : ℝ × E3 → G) (ν : ℝ) (x : E3) :
    timeFourier g ν x = ∫ t : ℝ, (𝐞 (-(t * ν)) : ℂ) • g (t, x) := by
  rw [timeFourier, Real.fourier_real_eq]
  rfl

/-- The character `t ↦ e^{−2πiνt}` is continuous. -/
theorem continuous_fourierChar_mul (ν : ℝ) : Continuous fun t : ℝ => (𝐞 (-(t * ν)) : ℂ) := by
  change Continuous fun t : ℝ => Complex.exp (↑(2 * π * -(t * ν)) * Complex.I)
  fun_prop

end TimeFourier

/-! ### Supports bounded in time -/

section TimeBounded

variable {H : Type*} [NormedAddCommGroup H]

/-- A function on `ℝ × ℝ³` has **support bounded in time** with the constant `a` if its support
lies in `|t| ≤ a + ‖x‖`: at every point of space it vanishes for large `|t|`, uniformly on bounded
sets of space. -/
def TimeBoundedSupport (a : ℝ) (g : ℝ × E3 → H) : Prop :=
  tsupport g ⊆ {p | |p.1| ≤ a + ‖p.2‖}

/-- A function supported in the support of a function with support bounded in time has support
bounded in time. -/
theorem TimeBoundedSupport.mono {H' : Type*} [NormedAddCommGroup H'] {a : ℝ} {g : ℝ × E3 → H}
    {g' : ℝ × E3 → H'} (hg : TimeBoundedSupport a g) (h : tsupport g' ⊆ tsupport g) :
    TimeBoundedSupport a g' :=
  h.trans hg

/-- A function with support bounded in time vanishes at `(t, x)` for `|t| > a + ‖x‖`. -/
theorem TimeBoundedSupport.eq_zero {a : ℝ} {g : ℝ × E3 → H} (hg : TimeBoundedSupport a g)
    {t : ℝ} {x : E3} (ht : a + ‖x‖ < |t|) : g (t, x) = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => absurd (hg h) (by simpa using ht)

/-- A function of compact support has support bounded in time. -/
theorem exists_timeBoundedSupport_of_hasCompactSupport {g : ℝ × E3 → H}
    (hg : HasCompactSupport g) : ∃ a, TimeBoundedSupport a g := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun p hp => ?_⟩
  have h := hR hp
  rw [mem_closedBall_zero_iff] at h
  have h1 : |p.1| ≤ ‖p‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_fst_le p
  simp only [mem_ofPred_eq]
  linarith [norm_nonneg p.2]

/-- At a point of space, a function with support bounded in time has compact support in time. -/
theorem TimeBoundedSupport.hasCompactSupport_slice {a : ℝ} {g : ℝ × E3 → H}
    (hg : TimeBoundedSupport a g) (x : E3) : HasCompactSupport fun t : ℝ => g (t, x) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (a + ‖x‖)) fun t ht =>
    hg.eq_zero (by simpa using ht)

/-- At a point of space, a continuous function with support bounded in time is integrable in
time. -/
theorem TimeBoundedSupport.integrable_slice {a : ℝ} {g : ℝ × E3 → H}
    (hg : TimeBoundedSupport a g) (hc : Continuous g) (x : E3) :
    Integrable fun t : ℝ => g (t, x) :=
  (hc.comp (by fun_prop)).integrable_of_hasCompactSupport (hg.hasCompactSupport_slice x)

/-- The derivative of a function with support bounded in time has support bounded in time. -/
theorem TimeBoundedSupport.fderiv {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {a : ℝ} {g : ℝ × E3 → H'} (hg : TimeBoundedSupport a g) :
    TimeBoundedSupport a (fderiv ℝ g) :=
  hg.mono (tsupport_fderiv_subset ℝ)

end TimeBounded

/-! ### Derivatives in space of the Fourier transform in time -/

section Derivative

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The integrand `e^{−2πiνt} g(t, x)` of the Fourier transform in time of a continuous function
with support bounded in time is integrable. -/
theorem TimeBoundedSupport.integrable_fourier {a : ℝ} {g : ℝ × E3 → G}
    (hg : TimeBoundedSupport a g) (hc : Continuous g) (ν : ℝ) (x : E3) :
    Integrable fun t : ℝ => (𝐞 (-(t * ν)) : ℂ) • g (t, x) :=
  ((continuous_fourierChar_mul ν).smul (hc.comp (by fun_prop))).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall 0 (a + ‖x‖)) fun t ht => by
      change (𝐞 (-(t * ν)) : ℂ) • g (t, x) = 0
      rw [hg.eq_zero (by simpa using ht), smul_zero])

/-- The restriction `L ↦ L ∘ inr` of a linear map on `ℝ × ℝ³` to space. -/
def restrictSpace : (ℝ × E3 →L[ℝ] G) →L[ℝ] (E3 →L[ℝ] G) :=
  (ContinuousLinearMap.compL ℝ E3 (ℝ × E3) G).flip (ContinuousLinearMap.inr ℝ ℝ E3)

/-- The restriction to space is the composition with `inr`. -/
@[simp] theorem restrictSpace_apply (L : ℝ × E3 →L[ℝ] G) :
    restrictSpace L = L.comp (ContinuousLinearMap.inr ℝ ℝ E3) := rfl

/-- **The derivative in space of the Fourier transform in time** is the Fourier transform in time
of the derivative restricted to space, for a `C¹` function with support bounded in time. -/
theorem hasFDerivAt_timeFourier [CompleteSpace G] {g : ℝ × E3 → G} (hg : ContDiff ℝ 1 g)
    {a : ℝ} (hs : TimeBoundedSupport a g) (ν : ℝ) (x₀ : E3) :
    HasFDerivAt (timeFourier g ν) (restrictSpace (timeFourier (fderiv ℝ g) ν x₀)) x₀ := by
  have hc' : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have he := continuous_fourierChar_mul ν
  set M := a + ‖x₀‖ + 1
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) M).prod
    (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn hc'.continuousOn
  set F' : E3 → ℝ → E3 →L[ℝ] G := fun x t =>
    restrictSpace ((𝐞 (-(t * ν)) : ℂ) • fderiv ℝ g (t, x))
  have hbound : ∀ t : ℝ, ∀ x ∈ ball x₀ 1, ‖F' x t‖ ≤
      (closedBall (0 : ℝ) M).indicator (fun _ => ‖(restrictSpace : (ℝ × E3 →L[ℝ] G) →L[ℝ] _)‖ * C)
        t := by
    intro t x hx
    by_cases ht : t ∈ closedBall (0 : ℝ) M
    · rw [indicator_of_mem ht]
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [norm_smul, Circle.norm_coe, one_mul]
      exact hC _ ⟨ht, ball_subset_closedBall hx⟩
    · rw [indicator_of_notMem ht]
      have hx' : ‖x‖ < ‖x₀‖ + 1 := by
        have := norm_sub_norm_le x x₀
        rw [mem_ball, dist_eq_norm] at hx
        linarith
      have ht' : a + ‖x‖ < |t| := by
        rw [mem_closedBall_zero_iff, not_le, Real.norm_eq_abs] at ht
        linarith
      simp [F', hs.fderiv.eq_zero ht']
  have hdiff : ∀ t : ℝ, ∀ x ∈ ball x₀ 1,
      HasFDerivAt (fun x => (𝐞 (-(t * ν)) : ℂ) • g (t, x)) (F' x t) x := by
    intro t x _
    have h := ((hg.differentiable (by norm_num) (t, x)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right t x)).const_smul (𝐞 (-(t * ν)) : ℂ)
    have hF : F' x t =
        (𝐞 (-(t * ν)) : ℂ) • (fderiv ℝ g (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3) := by
      simp only [F', restrictSpace_apply, ContinuousLinearMap.smul_comp]
    rw [hF]
    exact h
  have hint' : Integrable fun t : ℝ => (𝐞 (-(t * ν)) : ℂ) • fderiv ℝ g (t, x₀) :=
    hs.fderiv.integrable_fourier hc' ν x₀
  have H := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (ball_mem_nhds x₀ one_pos)
    (F := fun x t => (𝐞 (-(t * ν)) : ℂ) • g (t, x)) (F' := F')
    (Eventually.of_forall fun x => (hs.integrable_fourier hg.continuous ν x).aestronglyMeasurable)
    (hs.integrable_fourier hg.continuous ν x₀)
    (restrictSpace.continuous.comp (he.smul (hc'.comp (by fun_prop)))).aestronglyMeasurable
    (Eventually.of_forall fun t x hx => hbound t x hx)
    ((integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
      measurableSet_closedBall)
    (Eventually.of_forall fun t x hx => hdiff t x hx)
  have h1 : (fun x => ∫ t : ℝ, (𝐞 (-(t * ν)) : ℂ) • g (t, x)) = timeFourier g ν :=
    funext fun x => (timeFourier_eq g ν x).symm
  have h2 : ∫ t : ℝ, F' x₀ t = restrictSpace (timeFourier (fderiv ℝ g) ν x₀) := by
    rw [timeFourier_eq]
    exact restrictSpace.integral_comp_comm hint'
  rw [h1, h2] at H
  exact H

/-- The derivative in space of the Fourier transform in time. -/
theorem fderiv_timeFourier [CompleteSpace G] {g : ℝ × E3 → G} (hg : ContDiff ℝ 1 g) {a : ℝ}
    (hs : TimeBoundedSupport a g) (ν : ℝ) :
    fderiv ℝ (timeFourier g ν) = fun x => restrictSpace (timeFourier (fderiv ℝ g) ν x) :=
  funext fun x => (hasFDerivAt_timeFourier hg hs ν x).fderiv

/-- The Fourier transform in time commutes with the evaluation of linear maps. -/
theorem timeFourier_apply_clm [CompleteSpace G] {L : ℝ × E3 → ℝ × E3 →L[ℝ] G}
    (hc : Continuous L) {a : ℝ} (hs : TimeBoundedSupport a L) (ν : ℝ) (x : E3)
    (v : ℝ × E3) : timeFourier L ν x v = timeFourier (fun p => L p v) ν x :=
  Real.fourier_continuousLinearMap_apply (hs.integrable_slice hc x)

/-- **The directional derivative in space of the Fourier transform in time**:
`∂ᵥĝ(ν, x) = (∂ᵥg)^(ν, x)` for a `C¹` function with support bounded in time. -/
theorem fderiv_timeFourier_apply [CompleteSpace G] {g : ℝ × E3 → G} (hg : ContDiff ℝ 1 g)
    {a : ℝ} (hs : TimeBoundedSupport a g) (ν : ℝ) (x v : E3) :
    fderiv ℝ (timeFourier g ν) x v = timeFourier (fun p => fderiv ℝ g p (0, v)) ν x := by
  rw [fderiv_timeFourier hg hs]
  change restrictSpace (timeFourier (fderiv ℝ g) ν x) v = _
  rw [restrictSpace_apply, ContinuousLinearMap.comp_apply,
    timeFourier_apply_clm (hg.continuous_fderiv (by norm_num)) hs.fderiv]
  rfl

/-- The second derivative in space of the Fourier transform in time is the Fourier transform in
time of the second derivative, for a `C²` function with support bounded in time. -/
theorem fderiv_fderiv_timeFourier_apply [CompleteSpace G] {g : ℝ × E3 → G}
    (hg : ContDiff ℝ 2 g) {a : ℝ} (hs : TimeBoundedSupport a g) (ν : ℝ) (x v w : E3) :
    fderiv ℝ (fderiv ℝ (timeFourier g ν)) x v w =
      timeFourier (fun p => fderiv ℝ (fderiv ℝ g) p (0, v) (0, w)) ν x := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hg' : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hc'' : Continuous (fderiv ℝ (fderiv ℝ g)) := hg'.continuous_fderiv (by norm_num)
  have h := restrictSpace.hasFDerivAt.comp x (hasFDerivAt_timeFourier hg' hs.fderiv ν x)
  rw [fderiv_timeFourier hg1 hs, show (fun x => restrictSpace (timeFourier (fderiv ℝ g) ν x)) =
    restrictSpace ∘ timeFourier (fderiv ℝ g) ν from rfl, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, restrictSpace_apply, ContinuousLinearMap.inr_apply]
  rw [timeFourier_apply_clm hc'' hs.fderiv.fderiv, timeFourier_apply_clm (hc''.clm_apply
    continuous_const) (hs.fderiv.fderiv.mono (tsupport_comp_subset
      (g := fun L : ℝ × E3 →L[ℝ] ℝ × E3 →L[ℝ] G => L (0, v)) (by simp) _))]

/-- **The Laplacian of the Fourier transform in time** is the Fourier transform in time of the
Laplacian in space, for a `C²` function with support bounded in time. -/
theorem laplacian_timeFourier [CompleteSpace G] {g : ℝ × E3 → G} (hg : ContDiff ℝ 2 g) {a : ℝ}
    (hs : TimeBoundedSupport a g) (ν : ℝ) (x : E3) :
    Δ (timeFourier g ν) x = ∑ i, timeFourier (fun p => fderiv ℝ (fderiv ℝ g) p
      (0, EuclideanSpace.single i 1) (0, EuclideanSpace.single i 1)) ν x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact fderiv_fderiv_timeFourier_apply hg hs ν x _ _

end Derivative

/-! ### Real functions -/

section Real

/-- The complex function of a real function with support bounded in time has support bounded in
time. -/
theorem TimeBoundedSupport.ofReal {a : ℝ} {u : ℝ × E3 → ℝ} (hs : TimeBoundedSupport a u) :
    TimeBoundedSupport a fun p => (u p : ℂ) :=
  hs.mono (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero u)

/-- The second derivative of the complex function of a `C²` real function is the complex number
of its second derivative. -/
theorem fderiv_fderiv_ofReal {u : ℝ × E3 → ℝ} (hu : ContDiff ℝ 2 u) (p v w : ℝ × E3) :
    fderiv ℝ (fderiv ℝ fun q => (u q : ℂ)) p v w = (fderiv ℝ (fderiv ℝ u) p v w : ℂ) := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hd' : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set L := ContinuousLinearMap.compL ℝ (ℝ × E3) ℝ ℂ Complex.ofRealCLM
  have h1 : fderiv ℝ (fun q => (u q : ℂ)) = fun q => L (fderiv ℝ u q) := by
    funext q
    exact (Complex.ofRealCLM.hasFDerivAt.comp q (hd q).hasFDerivAt).fderiv
  rw [h1, show (fun q => L (fderiv ℝ u q)) = L ∘ fderiv ℝ u from rfl,
    (L.hasFDerivAt.comp p (hd' p).hasFDerivAt).fderiv]
  rfl

/-- **The Fourier transform of the time derivative**: `(∂ₜu)^(ν, x) = 2πiν û(ν, x)` for a `C¹`
real function with support bounded in time. -/
theorem timeFourier_timeDeriv {u : ℝ × E3 → ℝ} (hu : ContDiff ℝ 1 u) {a : ℝ}
    (hs : TimeBoundedSupport a u) (ν : ℝ) (x : E3) :
    timeFourier (fun p => (Wave.timeDeriv u p : ℂ)) ν x =
      2 * π * Complex.I * ν * timeFourier (fun p => (u p : ℂ)) ν x := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (u (t, x) : ℂ)) (Wave.timeDeriv u (t, x) : ℂ) t := by
    intro t
    have h := (hu.differentiable (by norm_num) (t, x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))
    exact h.ofReal_comp
  have hderiv : deriv (fun t : ℝ => (u (t, x) : ℂ)) = fun t => (Wave.timeDeriv u (t, x) : ℂ) :=
    funext fun t => (hd t).deriv
  have ht : TimeBoundedSupport a (Wave.timeDeriv u) := hs.mono (Wave.tsupport_timeDeriv_subset u)
  have hct : Continuous (Wave.timeDeriv u) :=
    (Wave.contDiff_timeDeriv (n := 0) (by simpa using hu)).continuous
  have h := Real.fourier_deriv (f := fun t : ℝ => (u (t, x) : ℂ))
    (hs.ofReal.integrable_slice (by fun_prop) x) (fun t => (hd t).differentiableAt)
    (by rw [hderiv]; exact ht.ofReal.integrable_slice (by fun_prop) x)
  rw [hderiv] at h
  have h' := congrFun h ν
  simp only [smul_eq_mul] at h'
  exact h'

/-- The Fourier transform in time of a difference minus a finite sum, for continuous functions
with support bounded in time. -/
theorem timeFourier_sub_sum {a : ℝ} {T : ℝ × E3 → ℂ} {S : Fin 3 → ℝ × E3 → ℂ}
    (hT : Continuous T) (hTs : TimeBoundedSupport a T) (hS : ∀ i, Continuous (S i))
    (hSs : ∀ i, TimeBoundedSupport a (S i)) (ν : ℝ) (x : E3) :
    timeFourier (fun p => T p - ∑ i, S i p) ν x =
      timeFourier T ν x - ∑ i, timeFourier (S i) ν x := by
  simp only [timeFourier_eq, smul_sub, Finset.smul_sum]
  rw [integral_sub (hTs.integrable_fourier hT ν x)
      (integrable_finsetSum _ fun i _ => (hSs i).integrable_fourier (hS i) ν x),
    integral_finsetSum _ fun i _ => (hSs i).integrable_fourier (hS i) ν x]

/-- **The Helmholtz equation**: a `C²` real solution `u` of the wave equation
`□u = ∂ₜ²u − Δu = f` with support bounded in time has the Fourier transform in time with
`(Δ + (2πν)²) û(ν, ·) = −f̂(ν, ·)`. -/
theorem helmholtz_timeFourier {u f : ℝ × E3 → ℝ} (hu : ContDiff ℝ 2 u) {a : ℝ}
    (hs : TimeBoundedSupport a u) (hwave : ∀ p, Wave.waveOperator u p = f p) (ν : ℝ) (x : E3) :
    Δ (timeFourier (fun p => (u p : ℂ)) ν) x +
        (2 * π * ν) ^ 2 * timeFourier (fun p => (u p : ℂ)) ν x =
      -timeFourier (fun p => (f p : ℂ)) ν x := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have ht1 : ContDiff ℝ 1 (Wave.timeDeriv u) := Wave.contDiff_timeDeriv (n := 1) hu
  have hts : TimeBoundedSupport a (Wave.timeDeriv u) := hs.mono (Wave.tsupport_timeDeriv_subset u)
  have htts : TimeBoundedSupport a (Wave.timeDeriv (Wave.timeDeriv u)) :=
    hts.mono (Wave.tsupport_timeDeriv_subset _)
  have hssu : ∀ i, TimeBoundedSupport a (Wave.spaceDeriv i (Wave.spaceDeriv i u)) := fun i =>
    (hs.mono (Wave.tsupport_spaceDeriv_subset i u)).mono (Wave.tsupport_spaceDeriv_subset i _)
  have hctt : Continuous (Wave.timeDeriv (Wave.timeDeriv u)) :=
    (Wave.contDiff_timeDeriv (n := 0) ht1).continuous
  have hcss : ∀ i, Continuous (Wave.spaceDeriv i (Wave.spaceDeriv i u)) := fun i =>
    (Wave.contDiff_spaceDeriv (n := 0) (Wave.contDiff_spaceDeriv (n := 1) hu i) i).continuous
  -- the Laplacian
  have hΔ : Δ (timeFourier (fun p => (u p : ℂ)) ν) x =
      ∑ i, timeFourier (fun p => (Wave.spaceDeriv i (Wave.spaceDeriv i u) p : ℂ)) ν x := by
    have hcu : ContDiff ℝ 2 fun p => (u p : ℂ) := Complex.ofRealCLM.contDiff.comp hu
    rw [laplacian_timeFourier hcu hs.ofReal]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    funext p
    rw [fderiv_fderiv_ofReal hu, ← Wave.fderiv_fderiv_apply_eq hu.contDiffAt]
    rfl
  -- the second time derivative
  have hT : timeFourier (fun p => (Wave.timeDeriv (Wave.timeDeriv u) p : ℂ)) ν x =
      (2 * π * Complex.I * ν) ^ 2 * timeFourier (fun p => (u p : ℂ)) ν x := by
    rw [timeFourier_timeDeriv ht1 hts, timeFourier_timeDeriv hu1 hs]
    ring
  -- the source
  have hf : (fun p => (f p : ℂ)) = fun p => (Wave.timeDeriv (Wave.timeDeriv u) p : ℂ) -
      ∑ i, (Wave.spaceDeriv i (Wave.spaceDeriv i u) p : ℂ) := by
    funext p
    rw [← hwave p, Wave.waveOperator]
    push_cast
    rfl
  have hF := timeFourier_sub_sum (by fun_prop) htts.ofReal (fun i => by fun_prop)
    (fun i => (hssu i).ofReal) ν x
  rw [← hf] at hF
  rw [hΔ, hF, hT]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination ((2 * π * ν) ^ 2 * timeFourier (fun p => (u p : ℂ)) ν x) * hI

end Real

/-! ### The retarded integral -/

/-- **The support of the retarded integral is bounded in time** for a source of compact support:
in the ball `‖p‖ ≤ R` of space-time it is supported in `|t| ≤ 2R + ‖x‖`, the source being seen
at `x` only between the times `−R` and `‖x‖ + 2R` (Huygens' principle in three dimensions). -/
theorem exists_timeBoundedSupport_retardedIntegral {f : ℝ × E3 → ℝ} (hf : HasCompactSupport f) :
    ∃ a, TimeBoundedSupport a (Wave.retardedIntegral f) := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨2 * R, closure_minimal (fun p hp => ?_) (isClosed_le (by fun_prop) (by fun_prop))⟩
  by_contra hlt
  apply hp
  have hz : ∀ y : E3, f (p - (‖y‖, y)) = 0 := by
    intro y
    by_contra hne
    have h := hR (subset_tsupport f hne)
    rw [mem_closedBall_zero_iff] at h
    have h1 : |p.1 - ‖y‖| ≤ R := by
      have := (norm_fst_le (p - (‖y‖, y))).trans h
      simpa using this
    have h2 : ‖p.2 - y‖ ≤ R := by
      have := (norm_snd_le (p - (‖y‖, y))).trans h
      simpa using this
    have h3 := norm_sub_norm_le y p.2
    rw [norm_sub_rev y p.2] at h3
    have hR0 : 0 ≤ R := (norm_nonneg _).trans h
    apply hlt
    simp only [mem_ofPred_eq]
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [norm_nonneg p.2, norm_nonneg y]
  simp [Wave.retardedIntegral, hz]

/-- The integrand `e^{−2πiνt} f(t − ‖y‖, x − y)/(4π‖y‖)` of the Fourier transform in time of the
retarded integral is integrable on `ℝ × ℝ³`, for a continuous source of compact support. -/
theorem integrable_fourier_retarded {f : ℝ × E3 → ℝ} (hc : Continuous f)
    (hf : HasCompactSupport f) (ν : ℝ) (x : E3) :
    Integrable (fun q : ℝ × E3 => (𝐞 (-(q.1 * ν)) : ℂ) *
      (((4 * π * ‖q.2‖)⁻¹ * f (q.1 - ‖q.2‖, x - q.2) : ℝ) : ℂ)) (volume.prod volume) := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hf
  set M₁ := ‖x‖ + R
  set M₂ := R + M₁
  have hb := Integrable.mul_prod (μ := volume) (ν := volume)
    ((integrableOn_const (C := (1 : ℝ)) measure_closedBall_lt_top.ne).integrable_indicator
      (measurableSet_closedBall (x := (0 : ℝ)) (ε := M₂)))
    (Wave.integrable_indicator_newtonKernel C M₁)
  refine hb.mono' ?_ (Eventually.of_forall fun q => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    refine ((continuous_fourierChar_mul ν).comp continuous_fst).measurable.mul
      (Complex.measurable_ofReal.comp ?_)
    exact (measurable_const.mul measurable_snd.norm).inv.mul (hc.comp (by fun_prop)).measurable
  · have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, norm_mul,
      Real.norm_of_nonneg (by positivity)]
    by_cases hne : f (q.1 - ‖q.2‖, x - q.2) = 0
    · rw [hne, norm_zero, mul_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
        (indicator_nonneg (fun y _ => mul_nonneg hC0 (Potential.newtonKernel_nonneg y)) _)
    have h := hR (subset_tsupport f hne)
    rw [mem_closedBall_zero_iff] at h
    have h1 : |q.1 - ‖q.2‖| ≤ R := by
      have := (norm_fst_le (q.1 - ‖q.2‖, x - q.2)).trans h
      simpa using this
    have h2 : ‖x - q.2‖ ≤ R := (norm_snd_le (q.1 - ‖q.2‖, x - q.2)).trans h
    have h3 := norm_sub_norm_le q.2 x
    rw [norm_sub_rev q.2 x] at h3
    have hy : ‖q.2‖ ≤ M₁ := by linarith
    have ht : |q.1| ≤ M₂ := by
      rw [abs_le] at h1 ⊢
      constructor <;> linarith [norm_nonneg q.2]
    rw [indicator_of_mem (by simpa using ht), indicator_of_mem (by simpa using hy), one_mul,
      Potential.newtonKernel, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (by positivity)

/-- **The spectral resolution of the retarded integral**: for a continuous source `f` of compact
support in space-time, the Fourier transform in time of the retarded integral is
`Â(ν, x) = ∫ e^{−2πiν‖y‖} f̂(ν, x − y)/(4π‖y‖) dy`, the retarded integral of the Fourier
components with the phase `e^{−2πiν‖y‖}` of the delay `‖y‖`. -/
theorem fourier_retardedIntegral {f : ℝ × E3 → ℝ} (hc : Continuous f) (hf : HasCompactSupport f)
    (ν : ℝ) (x : E3) :
    timeFourier (fun p => ((Wave.retardedIntegral f p : ℝ) : ℂ)) ν x =
      ∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
        timeFourier (fun p => (f p : ℂ)) ν (x - y) / (4 * π * ‖y‖) := by
  set H : ℝ → E3 → ℂ := fun t y => (𝐞 (-(t * ν)) : ℂ) *
    (((4 * π * ‖y‖)⁻¹ * f (t - ‖y‖, x - y) : ℝ) : ℂ) with hH
  have h1 : timeFourier (fun p => ((Wave.retardedIntegral f p : ℝ) : ℂ)) ν x =
      ∫ t, ∫ y, H t y := by
    rw [timeFourier_eq]
    congr 1
    funext t
    rw [smul_eq_mul, Wave.retardedIntegral_apply, ← integral_complex_ofReal,
      ← integral_const_mul]
    congr 1
    funext y
    simp only [hH, div_eq_inv_mul]
  have h2 : ∀ y : E3, ∫ t, H t y = Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
      timeFourier (fun p => (f p : ℂ)) ν (x - y) / (4 * π * ‖y‖) := by
    intro y
    have he : (𝐞 (-(‖y‖ * ν)) : ℂ) = Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) := by
      rw [Real.fourierChar_apply]
      congr 1
      push_cast
      ring
    have hs : ∀ s : ℝ, H (s + ‖y‖) y = Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) /
        (4 * π * ‖y‖) * ((𝐞 (-(s * ν)) : ℂ) • (f (s, x - y) : ℂ)) := by
      intro s
      simp only [hH, add_sub_cancel_right, smul_eq_mul]
      rw [show -((s + ‖y‖) * ν) = -(s * ν) + -(‖y‖ * ν) by ring, AddChar.map_add_eq_mul,
        Circle.coe_mul, he]
      push_cast
      ring
    rw [← integral_add_right_eq_self (fun t => H t y) ‖y‖, funext hs, integral_const_mul,
      timeFourier_eq]
    ring
  rw [h1, integral_integral_swap (integrable_fourier_retarded hc hf ν x)]
  exact congrArg _ (funext h2)

/-- **The Helmholtz equation for the retarded integral**: for a `C²` source `f` of compact
support in space-time, the Fourier transform in time `Â` of the retarded integral satisfies
`(Δ + (2πν)²) Â(ν, ·) = −f̂(ν, ·)`. -/
theorem helmholtz_fourier_retardedIntegral {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 2 f)
    (hf : HasCompactSupport f) (ν : ℝ) (x : E3) :
    Δ (timeFourier (fun p => ((Wave.retardedIntegral f p : ℝ) : ℂ)) ν) x +
        (2 * π * ν) ^ 2 * timeFourier (fun p => ((Wave.retardedIntegral f p : ℝ) : ℂ)) ν x =
      -timeFourier (fun p => (f p : ℂ)) ν x := by
  obtain ⟨R, hs⟩ := Wave.exists_subluminalSupport_of_hasCompactSupport hf
  obtain ⟨a, ha⟩ := exists_timeBoundedSupport_retardedIntegral hf
  have hu : ContDiff ℝ 2 (Wave.retardedIntegral f) := by
    have h := Wave.contDiff_retardedIntegral (n := 2) (by exact_mod_cast hc) hs
    exact_mod_cast h
  exact helmholtz_timeFourier hu ha (Wave.wave_retardedIntegral hc hs) ν x

/-! ### The retarded potentials -/

/-- The **Fourier transform in time** `ĥ(ν, x) = ∫ e^{−2πiνt} h(t, x) dt` of a function on
space-time, at the point `x` of space, through the splitting `Wave.timeSpaceEquiv`. -/
def spacetimeFourier (h : Spacetime → ℝ) (ν : ℝ) (x : E3) : ℂ :=
  timeFourier (fun p => (h (Wave.timeSpaceEquiv.symm p) : ℂ)) ν x

/-- The Fourier transform in time on space-time is `∫ e^{−2πiνt} h(t, x) dt`. -/
theorem spacetimeFourier_eq (h : Spacetime → ℝ) (ν : ℝ) (x : E3) :
    spacetimeFourier h ν x = ∫ t : ℝ, (𝐞 (-(t * ν)) : ℂ) * h (Minkowski.vector t x) := by
  simp only [spacetimeFourier, timeFourier_eq, smul_eq_mul, Wave.timeSpaceEquiv_symm_apply]

/-- The Fourier transform in time of `−h` is `−ĥ`. -/
theorem spacetimeFourier_neg (h : Spacetime → ℝ) (ν : ℝ) :
    spacetimeFourier (fun v => -h v) ν = -spacetimeFourier h ν := by
  funext x
  simp only [spacetimeFourier_eq, Pi.neg_apply, Complex.ofReal_neg, mul_neg, integral_neg]

/-- The retarded integral on space-time, written in `(t, x)`, is the retarded integral of the
source written in `(t, x)`. -/
theorem retardedScalar_symm (g : Spacetime → ℝ) (p : ℝ × E3) :
    retardedScalar g (Wave.timeSpaceEquiv.symm p) =
      Wave.retardedIntegral (fun q => g (Wave.timeSpaceEquiv.symm q)) p := by
  rw [retardedScalar, ContinuousLinearEquiv.apply_symm_apply]

/-- **The spectral resolution of the retarded integral on space-time**: for a continuous source
`g` of compact support, `(Rg)^(ν, x) = ∫ e^{−2πiν‖y‖} ĝ(ν, x − y)/(4π‖y‖) dy`. -/
theorem fourier_retardedScalar {g : Spacetime → ℝ} (hc : Continuous g) (hg : HasCompactSupport g)
    (ν : ℝ) (x : E3) :
    spacetimeFourier (retardedScalar g) ν x =
      ∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
        spacetimeFourier g ν (x - y) / (4 * π * ‖y‖) := by
  simp only [spacetimeFourier, retardedScalar_symm]
  exact fourier_retardedIntegral (hc.comp Wave.timeSpaceEquiv.symm.continuous)
    (hg.comp_homeomorph Wave.timeSpaceEquiv.symm.toHomeomorph) ν x

/-- **The Helmholtz equation on space-time**: for a `C²` source `g` of compact support,
`(Δ + (2πν)²) (Rg)^(ν, ·) = −ĝ(ν, ·)`. -/
theorem helmholtz_fourier_retardedScalar {g : Spacetime → ℝ} (hc : ContDiff ℝ 2 g)
    (hg : HasCompactSupport g) (ν : ℝ) (x : E3) :
    Δ (spacetimeFourier (retardedScalar g) ν) x +
        (2 * π * ν) ^ 2 * spacetimeFourier (retardedScalar g) ν x =
      -spacetimeFourier g ν x := by
  have h : spacetimeFourier (retardedScalar g) ν = timeFourier (fun p =>
      ((Wave.retardedIntegral (fun q => g (Wave.timeSpaceEquiv.symm q)) p : ℝ) : ℂ)) ν := by
    funext y
    simp only [spacetimeFourier, retardedScalar_symm]
  rw [h]
  exact helmholtz_fourier_retardedIntegral (hc.comp Wave.timeSpaceEquiv.symm.contDiff)
    (hg.comp_homeomorph Wave.timeSpaceEquiv.symm.toHomeomorph) ν x

/-- A component of a function of compact support has compact support. -/
theorem hasCompactSupport_spacetimeComponent {k : Spacetime → Spacetime} (hk : HasCompactSupport k)
    (μ : Fin 4) : HasCompactSupport fun w => k w μ :=
  hk.comp_left (g := fun v : Spacetime => v μ) rfl

/-- **The spectral resolution of the retarded potentials**: for a
continuous current `k` of compact support, the Fourier components of `A₀ = −φ` and of `aᵢ` are
`Â₀(ν, x) = −∫ e^{−2πiν‖y‖} k̂⁰(ν, x − y)/(4π‖y‖) dy` and
`âᵢ(ν, x) = ∫ e^{−2πiν‖y‖} k̂ⁱ(ν, x − y)/(4π‖y‖) dy`. -/
theorem fourier_retardedPotential {k : Spacetime → Spacetime} (hc : Continuous k)
    (hk : HasCompactSupport k) (ν : ℝ) (x : E3) :
    spacetimeFourier (potentialComponent (retardedPotential k) 0) ν x =
        -∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
          spacetimeFourier (fun w => k w 0) ν (x - y) / (4 * π * ‖y‖) ∧
      ∀ i : Fin 3, spacetimeFourier (potentialComponent (retardedPotential k) i.succ) ν x =
        ∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
          spacetimeFourier (fun w => k w i.succ) ν (x - y) / (4 * π * ‖y‖) := by
  have hcμ : ∀ μ : Fin 4, Continuous fun w => k w μ := fun μ => (continuous_apply μ).comp hc
  refine ⟨?_, fun i => ?_⟩
  · rw [potentialComponent_retardedPotential_zero, spacetimeFourier_neg, Pi.neg_apply,
      fourier_retardedScalar (hcμ 0) (hasCompactSupport_spacetimeComponent hk 0)]
  · rw [potentialComponent_retardedPotential_succ,
      fourier_retardedScalar (hcμ i.succ) (hasCompactSupport_spacetimeComponent hk i.succ)]

/-- **The Helmholtz equations of the retarded potentials**: for a
`C²` current `k` of compact support, `(Δ + (2πν)²) Â₀ = k̂⁰` and `(Δ + (2πν)²) âᵢ = −k̂ⁱ`, that is
`(Δ + (2πν)²) Â_μ = −k̂_μ` with the index lowered by `η = diag(−1, 1, 1, 1)`. -/
theorem helmholtz_fourier_retardedPotential {k : Spacetime → Spacetime} (hc : ContDiff ℝ 2 k)
    (hk : HasCompactSupport k) (ν : ℝ) (x : E3) :
    Δ (spacetimeFourier (potentialComponent (retardedPotential k) 0) ν) x +
        (2 * π * ν) ^ 2 * spacetimeFourier (potentialComponent (retardedPotential k) 0) ν x =
      spacetimeFourier (fun w => k w 0) ν x ∧
    ∀ i : Fin 3, Δ (spacetimeFourier (potentialComponent (retardedPotential k) i.succ) ν) x +
        (2 * π * ν) ^ 2 * spacetimeFourier (potentialComponent (retardedPotential k) i.succ) ν x =
      -spacetimeFourier (fun w => k w i.succ) ν x := by
  have hcμ : ∀ μ : Fin 4, ContDiff ℝ 2 fun w => k w μ := fun μ =>
    (ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).contDiff.comp hc
  refine ⟨?_, fun i => ?_⟩
  · have h := helmholtz_fourier_retardedScalar (hcμ 0)
      (hasCompactSupport_spacetimeComponent hk 0) ν x
    rw [potentialComponent_retardedPotential_zero, spacetimeFourier_neg,
      InnerProductSpace.laplacian_neg, Pi.neg_apply, Pi.neg_apply]
    linear_combination -h
  · rw [potentialComponent_retardedPotential_succ]
    exact helmholtz_fourier_retardedScalar (hcμ i.succ)
      (hasCompactSupport_spacetimeComponent hk i.succ) ν x

/-! ### An instance -/

/-- **An instance of the spectral resolution**: the retarded potential of the circulating
current, a nonzero smooth conserved current of compact support (`circulatingCurrent_ne_zero`),
has the Fourier components of `fourier_retardedPotential`. -/
theorem fourier_retardedPotential_circulatingCurrent (ν : ℝ) (x : E3) :
    spacetimeFourier (potentialComponent (retardedPotential circulatingCurrent) 0) ν x =
        -∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
          spacetimeFourier (fun w => circulatingCurrent w 0) ν (x - y) / (4 * π * ‖y‖) ∧
      ∀ i : Fin 3,
        spacetimeFourier (potentialComponent (retardedPotential circulatingCurrent) i.succ) ν x =
          ∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
            spacetimeFourier (fun w => circulatingCurrent w i.succ) ν (x - y) / (4 * π * ‖y‖) :=
  fourier_retardedPotential contDiff_circulatingCurrent.continuous
    hasCompactSupport_circulatingCurrent ν x

/-- **An instance of the Helmholtz equations**: the Fourier components of the retarded potential
of the circulating current satisfy `(Δ + (2πν)²) Â_μ = −k̂_μ`. -/
theorem helmholtz_fourier_retardedPotential_circulatingCurrent (ν : ℝ) (x : E3) :
    Δ (spacetimeFourier (potentialComponent (retardedPotential circulatingCurrent) 0) ν) x +
        (2 * π * ν) ^ 2 *
          spacetimeFourier (potentialComponent (retardedPotential circulatingCurrent) 0) ν x =
      spacetimeFourier (fun w => circulatingCurrent w 0) ν x ∧
    ∀ i : Fin 3,
      Δ (spacetimeFourier (potentialComponent (retardedPotential circulatingCurrent) i.succ) ν) x +
          (2 * π * ν) ^ 2 * spacetimeFourier
            (potentialComponent (retardedPotential circulatingCurrent) i.succ) ν x =
        -spacetimeFourier (fun w => circulatingCurrent w i.succ) ν x :=
  helmholtz_fourier_retardedPotential (contDiff_circulatingCurrent.of_le (by simp))
    hasCompactSupport_circulatingCurrent ν x

end ProjectAinos.Electrodynamics
