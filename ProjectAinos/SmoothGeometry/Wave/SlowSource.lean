/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Wave.RetardedIntegral
public import ProjectAinos.SmoothGeometry.Potential.NewtonPotential
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Slow sources

Sources on `ℝ × ℝ³` supported in a fixed cylinder `‖x‖ ≤ a` at all times (`SpatialSupport`),
their slow rescaling `f_κ(t, x) = f(κt, x)` (`slow`) with the slowness `κ` (the ratio `v/c` of
Landau–Lifshitz, *The Classical Theory of Fields*, §65), and the expansion of their retarded
integral in `κ`.

* `abs_sub_taylor_le`, `abs_sub_taylor_sub_le`: Taylor's formula with a bounded remainder for a
  chain of derivatives `g₀, …, gₙ`.
* `retardedIntegral_slow_expansion`: **the slow expansion**
  `R(f_κ)(t, x) = Σ_{k ≤ n} ((−κ)ᵏ/k!) (4π)⁻¹ ∫ ‖y‖ᵏ⁻¹ ∂ₜᵏf(κt, x − y) dy` up to
  `M (ρ + a)ⁿ⁺³ κⁿ⁺¹/(3 (n + 1)!)` for `|∂ₜⁿ⁺¹f| ≤ M` and `‖x‖ ≤ ρ`; the terms are `slowTerm`
  (`slowTerm_zero`: the Newton potential, `slowTerm_one`, `slowTerm_two`), and
  `abs_retardedIntegral_slow_sub_newton_le` is the leading order. The derivatives of a slow
  retarded integral are the slow retarded integrals of the derivatives
  (`timeDeriv_retardedIntegral_slow`, `spaceDeriv_retardedIntegral_slow`), so the expansion applies
  to the fields.
* `kernelIntegral K F (t, x) = ∫ K(y) F(t, x − y) dy` against a locally integrable kernel, with a
  bounded support of the integrand (`KernelSupport`): continuity, derivatives under the integral
  and smoothness (`hasFDerivAt_kernelIntegral`, `contDiff_kernelIntegral`,
  `timeDeriv_kernelIntegral`, `spaceDeriv_kernelIntegral`, `timeDeriv_kernelIntegral_slow`,
  `spaceDeriv_kernelIntegral_slow`); `kernelIntegral_eq_integral_sub` writes it over the source
  points and `integrable_kernel_sub_mul` integrates kernels bounded by the Newton kernel.
* `integral_norm_sub_mul_fderiv_fderiv`: **the second derivatives of the distance** in the sense
  of distributions, `∫ ‖x − z‖ ∂ᵥ∂_w F = ∫ (⟨v, w⟩/‖x − z‖ − ⟨v, x − z⟩⟨w, x − z⟩/‖x − z‖³) F`,
  with no point term, from the regularized distance `√(‖x − z‖² + δ²)`
  (`integral_regularDistance_mul_fderiv_fderiv`) as `δ → 0⁺`; in space-time form
  `integral_norm_sub_mul_spaceDeriv_spaceDeriv`.
* Averages over small balls: `abs_integral_weight_mul_sub_le`,
  `abs_integral_weight_mul_average_sub_le`, and `tendsto_integral_weight_mul_average`, the point
  limit `∫ η_ε(x − r₂) ∫ K(y) η_ε(x − y − r₁) dy dx → K(r₂ − r₁)` of two smeared points.
* The calculus of `timeDeriv` and `spaceDeriv`: linearity (`timeDeriv_fun_add`, …), symmetry
  (`spaceDeriv_spaceDeriv_comm`, `iterate_timeDeriv_spaceDeriv`), slices
  (`hasDerivAt_timeSlice_of_differentiableAt`, `spaceDeriv_eq_fderiv_slice`,
  `integral_spaceDeriv_eq_zero`) and products `c(s) G(x)` (`timeDeriv_mul_slice`,
  `spaceDeriv_mul_slice`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff Nat

namespace ProjectAinos.SmoothGeometry.Wave

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Taylor's formula with a bounded derivative -/

/-- **Taylor's formula with a bounded remainder**: if `g₀, …, gₙ` are successive derivatives,
`g₀(h) = Σ_{k < n} hᵏ/k! gₖ(0)` up to `M hⁿ/n!` for `0 ≤ h`, where `|gₙ| ≤ M` on `[0, h]`. -/
theorem abs_sub_taylor_le {g : ℕ → ℝ → ℝ} {M : ℝ} (n : ℕ)
    (hg : ∀ k < n, ∀ s, HasDerivAt (g k) (g (k + 1) s) s) {h : ℝ} (hh : 0 ≤ h)
    (hM : ∀ s ∈ Icc 0 h, |g n s| ≤ M) :
    |g 0 h - ∑ k ∈ Finset.range n, h ^ k / k ! * g k 0| ≤ M * h ^ n / n ! := by
  induction n generalizing g h with
  | zero => simpa using hM h ⟨hh, le_rfl⟩
  | succ n ih =>
    set Φ : ℝ → ℝ := fun u => g 0 u - ∑ k ∈ Finset.range (n + 1), u ^ k / k ! * g k 0 with hΦd
    set Φ' : ℝ → ℝ := fun u => g 1 u - ∑ k ∈ Finset.range n, u ^ k / k ! * g (k + 1) 0
    have hΦ : ∀ u, HasDerivAt Φ (Φ' u) u := by
      intro u
      have h0 := hg 0 (by omega) u
      have he : (fun u : ℝ => ∑ k ∈ Finset.range (n + 1), u ^ k / k ! * g k 0) =
          fun u => ∑ k ∈ Finset.range n, u ^ (k + 1) / (k + 1)! * g (k + 1) 0 + g 0 0 := by
        funext u
        rw [Finset.sum_range_succ']
        simp
      have hs : HasDerivAt (fun u : ℝ => ∑ k ∈ Finset.range (n + 1), u ^ k / k ! * g k 0)
          (∑ k ∈ Finset.range n, u ^ k / k ! * g (k + 1) 0) u := by
        rw [he]
        refine (HasDerivAt.fun_sum fun k _ => ?_).add_const _
        have hk := ((hasDerivAt_pow (k + 1) u).div_const ((k + 1)! : ℝ)).mul_const (g (k + 1) 0)
        convert hk using 1
        rw [Nat.factorial_succ]
        push_cast
        field_simp
      exact h0.sub hs
    have hb : ∀ u ∈ Ico 0 h, ‖Φ' u‖ ≤ M * u ^ n / n ! := fun u hu =>
      ih (g := fun k => g (k + 1)) (fun k hk s => hg (k + 1) (by omega) s) hu.1
        (fun s hs => hM s ⟨hs.1, hs.2.trans hu.2.le⟩)
    have hB : ∀ u, HasDerivAt (fun u : ℝ => M * u ^ (n + 1) / (n + 1)!) (M * u ^ n / n !) u := by
      intro u
      have hk := ((hasDerivAt_pow (n + 1) u).const_mul M).div_const ((n + 1)! : ℝ)
      convert hk using 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    have h0 : ‖Φ 0‖ ≤ M * 0 ^ (n + 1) / (n + 1)! := by
      simp [hΦd, Finset.sum_range_succ']
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := Φ) (a := 0) (b := h)
      (fun u _ => (hΦ u).continuousAt.continuousWithinAt) (fun u _ => (hΦ u).hasDerivWithinAt)
      h0 hB hb ⟨hh, le_rfl⟩
    simpa [hΦd] using this

/-- **Taylor's formula backwards in time**: if `g₀, …, gₙ` are successive derivatives and
`|gₙ| ≤ M`, then `g₀(s₀ − h) = Σ_{k < n} (−h)ᵏ/k! gₖ(s₀)` up to `M hⁿ/n!` for `0 ≤ h`. -/
theorem abs_sub_taylor_sub_le {g : ℕ → ℝ → ℝ} {M : ℝ} (n : ℕ)
    (hg : ∀ k < n, ∀ s, HasDerivAt (g k) (g (k + 1) s) s) (s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hM : ∀ s, |g n s| ≤ M) :
    |g 0 (s₀ - h) - ∑ k ∈ Finset.range n, (-h) ^ k / k ! * g k s₀| ≤ M * h ^ n / n ! := by
  have H := abs_sub_taylor_le (g := fun k u => (-1) ^ k * g k (s₀ - u)) (M := M) n
    (fun k hk u => by
      have h1 := (hg k hk (s₀ - u)).comp u ((hasDerivAt_id u).const_sub s₀)
      convert h1.const_mul ((-1 : ℝ) ^ k) using 1
      simp only [Function.comp_def]
      ring) hh (fun s _ => by simpa [abs_mul] using hM (s₀ - s))
  convert H using 3
  · simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow]
    simp only [sub_zero]
    ring

/-! ### Time derivatives -/

/-- Along the axis of the time, a function has its time derivative as its derivative. -/
theorem hasDerivAt_timeSlice_of_differentiableAt {F : ℝ × E3 → ℝ} {s : ℝ} {z : E3}
    (hF : DifferentiableAt ℝ F (s, z)) :
    HasDerivAt (fun s' => F (s', z)) (timeDeriv F (s, z)) s :=
  hF.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id' s).prodMk (hasDerivAt_const s z))

/-- The iterated time derivatives `∂ₜᵏf` of a `Cᴺ` function are `Cᵐ` for `m + k ≤ N`. -/
theorem contDiff_iterate_timeDeriv {N : ℕ} {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ N f) {m k : ℕ}
    (hk : m + k ≤ N) : ContDiff ℝ m (timeDeriv^[k] f) := by
  induction k generalizing f N with
  | zero => exact hf.of_le (by exact_mod_cast (by omega : m ≤ N))
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    refine ih (N := N') (contDiff_timeDeriv (n := N') ?_) (by omega)
    exact_mod_cast hf

/-! ### Linearity and symmetry of the partial derivatives -/

/-- The time derivative of a sum. -/
theorem timeDeriv_fun_add {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) :
    timeDeriv (fun q => f q + g q) p = timeDeriv f p + timeDeriv g p := by
  simp [timeDeriv, fderiv_fun_add hf hg]

/-- The time derivative of a difference. -/
theorem timeDeriv_fun_sub {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) :
    timeDeriv (fun q => f q - g q) p = timeDeriv f p - timeDeriv g p := by
  simp [timeDeriv, fderiv_fun_sub hf hg]

/-- The time derivative of a constant multiple. -/
theorem timeDeriv_const_mul {f : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (c : ℝ) : timeDeriv (fun q => c * f q) p = c * timeDeriv f p := by
  simp [timeDeriv, fderiv_const_mul hf c]

/-- A spatial derivative of a sum. -/
theorem spaceDeriv_fun_add {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    spaceDeriv i (fun q => f q + g q) p = spaceDeriv i f p + spaceDeriv i g p := by
  simp [spaceDeriv, fderiv_fun_add hf hg]

/-- A spatial derivative of a difference. -/
theorem spaceDeriv_fun_sub {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    spaceDeriv i (fun q => f q - g q) p = spaceDeriv i f p - spaceDeriv i g p := by
  simp [spaceDeriv, fderiv_fun_sub hf hg]

/-- A spatial derivative of a constant multiple. -/
theorem spaceDeriv_const_mul {f : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (c : ℝ) (i : Fin 3) : spaceDeriv i (fun q => c * f q) p = c * spaceDeriv i f p := by
  simp [spaceDeriv, fderiv_const_mul hf c]

/-- A spatial derivative of a finite sum. -/
theorem spaceDeriv_fun_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ × E3 → ℝ} {p : ℝ × E3}
    (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) p) (i : Fin 3) :
    spaceDeriv i (fun q => ∑ k ∈ s, f k q) p = ∑ k ∈ s, spaceDeriv i (f k) p := by
  simp [spaceDeriv, fderiv_fun_sum hf]

/-- The time derivative of a finite sum. -/
theorem timeDeriv_fun_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ × E3 → ℝ} {p : ℝ × E3}
    (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) p) :
    timeDeriv (fun q => ∑ k ∈ s, f k q) p = ∑ k ∈ s, timeDeriv (f k) p := by
  simp [timeDeriv, fderiv_fun_sum hf]

/-- The spatial derivatives of a `C²` function commute: `∂ᵢ∂ⱼf = ∂ⱼ∂ᵢf`. -/
theorem spaceDeriv_spaceDeriv_comm {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hf : ContDiffAt ℝ 2 f q)
    (i j : Fin 3) : spaceDeriv i (spaceDeriv j f) q = spaceDeriv j (spaceDeriv i f) q := by
  have hs := hf.isSymmSndFDerivAt (by simp)
  change fderiv ℝ (fun p => fderiv ℝ f p (0, EuclideanSpace.single j 1)) q
      (0, EuclideanSpace.single i 1) =
    fderiv ℝ (fun p => fderiv ℝ f p (0, EuclideanSpace.single i 1)) q
      (0, EuclideanSpace.single j 1)
  rw [fderiv_fderiv_apply_eq hf, fderiv_fderiv_apply_eq hf]
  exact hs _ _

/-! ### Products of a function of the time and a function of space -/

/-- The time derivative of a product `c(s) G(x)`: `∂ₛ(c G) = c' G`. -/
theorem timeDeriv_mul_slice {c c' : ℝ → ℝ} (hc : ∀ s, HasDerivAt c (c' s) s) {G : E3 → ℝ}
    (hG : Differentiable ℝ G) :
    timeDeriv (fun p : ℝ × E3 => c p.1 * G p.2) = fun p => c' p.1 * G p.2 := by
  funext p
  have h1 : HasFDerivAt (fun p : ℝ × E3 => c p.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (c' p.1)).comp (ContinuousLinearMap.fst ℝ ℝ E3)) p :=
    (hc p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : ℝ × E3 => G p.2)
      ((fderiv ℝ G p.2).comp (ContinuousLinearMap.snd ℝ ℝ E3)) p :=
    (hG p.2).hasFDerivAt.comp p hasFDerivAt_snd
  rw [timeDeriv, (h1.fun_mul h2).fderiv]
  simp [mul_comm]

/-- A spatial derivative of a product `c(s) G(x)`: `∂ᵢ(c G) = c ∂ᵢG`. -/
theorem spaceDeriv_mul_slice {c : ℝ → ℝ} (hc : Differentiable ℝ c) {G : E3 → ℝ}
    (hG : Differentiable ℝ G) (i : Fin 3) :
    spaceDeriv i (fun p : ℝ × E3 => c p.1 * G p.2) =
      fun p => c p.1 * fderiv ℝ G p.2 (EuclideanSpace.single i 1) := by
  funext p
  have h1 : HasFDerivAt (fun p : ℝ × E3 => c p.1)
      ((fderiv ℝ c p.1).comp (ContinuousLinearMap.fst ℝ ℝ E3)) p :=
    (hc p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : ℝ × E3 => G p.2)
      ((fderiv ℝ G p.2).comp (ContinuousLinearMap.snd ℝ ℝ E3)) p :=
    (hG p.2).hasFDerivAt.comp p hasFDerivAt_snd
  rw [spaceDeriv, (h1.fun_mul h2).fderiv]
  simp

/-- The derivatives of the zero function vanish. -/
theorem timeDeriv_zero : timeDeriv (fun _ : ℝ × E3 => (0 : ℝ)) = fun _ => 0 := by
  funext p
  simp [timeDeriv]

/-- The spatial derivatives of the zero function vanish. -/
theorem spaceDeriv_zero (i : Fin 3) : spaceDeriv i (fun _ : ℝ × E3 => (0 : ℝ)) = fun _ => 0 := by
  funext p
  simp [spaceDeriv]

/-! ### Sources in a fixed ball -/

section Support

variable {G : Type*} [NormedAddCommGroup G]

/-- A function on `ℝ × ℝ³` is **supported in the cylinder** `‖x‖ ≤ a` if it vanishes for
`‖x‖ > a` at all times. -/
def SpatialSupport (a : ℝ) (f : ℝ × E3 → G) : Prop := ∀ p : ℝ × E3, a < ‖p.2‖ → f p = 0

/-- A function supported in the cylinder vanishes near the points outside it. -/
theorem SpatialSupport.eventuallyEq_zero {a : ℝ} {f : ℝ × E3 → G} (hf : SpatialSupport a f)
    {p : ℝ × E3} (hp : a < ‖p.2‖) : f =ᶠ[𝓝 p] fun _ => 0 :=
  eventually_of_mem ((isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
    hp) fun q hq => hf q hq

/-- The closed support of a function supported in the cylinder lies in the cylinder. -/
theorem SpatialSupport.tsupport_subset {a : ℝ} {f : ℝ × E3 → G} (hf : SpatialSupport a f) :
    tsupport f ⊆ {p | ‖p.2‖ ≤ a} :=
  closure_minimal (fun p hp => not_lt.mp fun h => hp (hf p h))
    (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)

/-- A function supported in the cylinder `‖x‖ ≤ a` has subluminal support with the speed `0`. -/
theorem SpatialSupport.subluminalSupport {a : ℝ} {f : ℝ × E3 → G} (hf : SpatialSupport a f) :
    SubluminalSupport a 0 f :=
  ⟨le_rfl, zero_lt_one, fun p hp => by simpa using hf.tsupport_subset hp⟩

/-- A function that vanishes where another one does is supported in its cylinder. -/
theorem SpatialSupport.mono {G' : Type*} [NormedAddCommGroup G'] {a : ℝ} {f : ℝ × E3 → G}
    {g : ℝ × E3 → G'} (hf : SpatialSupport a f) (hg : ∀ p, f p = 0 → g p = 0) :
    SpatialSupport a g :=
  fun p hp => hg p (hf p hp)

/-- The **slow rescaling** `f_κ(t, x) = f(κt, x)` of a source, with the slowness parameter `κ`
(the ratio `v/c` of Landau–Lifshitz). -/
def slow (κ : ℝ) (f : ℝ × E3 → G) (p : ℝ × E3) : G := f (κ * p.1, p.2)

/-- The linear map `(t, x) ↦ (κt, x)`. -/
def slowMap (κ : ℝ) : ℝ × E3 →L[ℝ] ℝ × E3 :=
  (κ • ContinuousLinearMap.fst ℝ ℝ E3).prod (ContinuousLinearMap.snd ℝ ℝ E3)

omit [NormedAddCommGroup G] in
/-- The slow rescaling is the composition with `(t, x) ↦ (κt, x)`. -/
theorem slow_eq_comp (κ : ℝ) (f : ℝ × E3 → G) : slow κ f = f ∘ slowMap κ := by
  funext p
  simp [slow, slowMap]

/-- The slow rescaling keeps the cylinder of the support. -/
theorem SpatialSupport.slow {a : ℝ} {f : ℝ × E3 → G} (hf : SpatialSupport a f) (κ : ℝ) :
    SpatialSupport a (slow κ f) := fun _ hp => hf _ hp

variable [NormedSpace ℝ G]

/-- The derivative of a function supported in the cylinder is supported in the cylinder. -/
theorem SpatialSupport.fderiv {a : ℝ} {f : ℝ × E3 → G} (hf : SpatialSupport a f) :
    SpatialSupport a (fderiv ℝ f) := fun p hp => by
  rw [(hf.eventuallyEq_zero hp).fderiv_eq]
  simp

/-- The slow rescaling of a `Cⁿ` function is `Cⁿ`. -/
theorem contDiff_slow {n : ℕ∞ω} {f : ℝ × E3 → G} (hf : ContDiff ℝ n f) (κ : ℝ) :
    ContDiff ℝ n (slow κ f) := by
  rw [slow_eq_comp]
  exact hf.comp (slowMap κ).contDiff

/-- The derivative of the slow rescaling: `D(f_κ)(p) v = Df(κt, x)(κv⁰, 𝐯)`. -/
theorem fderiv_slow {f : ℝ × E3 → G} (hf : Differentiable ℝ f) (κ : ℝ) (p v : ℝ × E3) :
    _root_.fderiv ℝ (slow κ f) p v = _root_.fderiv ℝ f (κ * p.1, p.2) (κ * v.1, v.2) := by
  rw [slow_eq_comp, fderiv_comp p (hf _) (slowMap κ).differentiableAt, (slowMap κ).fderiv]
  simp [slowMap]

end Support

/-- The time derivatives of a function supported in the cylinder are supported in it. -/
theorem SpatialSupport.timeDeriv {a : ℝ} {f : ℝ × E3 → ℝ} (hf : SpatialSupport a f) :
    SpatialSupport a (timeDeriv f) := fun p hp => by
  simp [Wave.timeDeriv, hf.fderiv p hp]

/-- The spatial derivatives of a function supported in the cylinder are supported in it. -/
theorem SpatialSupport.spaceDeriv {a : ℝ} {f : ℝ × E3 → ℝ} (hf : SpatialSupport a f)
    (i : Fin 3) : SpatialSupport a (spaceDeriv i f) := fun p hp => by
  simp [Wave.spaceDeriv, hf.fderiv p hp]

/-- The iterated time derivatives of a function supported in the cylinder are supported in it. -/
theorem SpatialSupport.iterate_timeDeriv {a : ℝ} {f : ℝ × E3 → ℝ} (hf : SpatialSupport a f)
    (k : ℕ) : SpatialSupport a (Wave.timeDeriv^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.timeDeriv

/-- The time derivative of the slow rescaling: `∂ₜ(f_κ) = κ (∂ₜf)_κ`. -/
theorem timeDeriv_slow {f : ℝ × E3 → ℝ} (hf : Differentiable ℝ f) (κ : ℝ) :
    timeDeriv (slow κ f) = fun p => κ * slow κ (timeDeriv f) p := by
  funext p
  rw [Wave.timeDeriv, fderiv_slow hf]
  have : ((κ * (1 : ℝ), (0 : E3)) : ℝ × E3) = κ • ((1 : ℝ), (0 : E3)) := by simp
  rw [this, map_smul, smul_eq_mul]
  rfl

/-- The spatial derivatives of the slow rescaling: `∂ᵢ(f_κ) = (∂ᵢf)_κ`. -/
theorem spaceDeriv_slow {f : ℝ × E3 → ℝ} (hf : Differentiable ℝ f) (κ : ℝ) (i : Fin 3) :
    spaceDeriv i (slow κ f) = slow κ (spaceDeriv i f) := by
  funext p
  rw [Wave.spaceDeriv, fderiv_slow hf]
  simp only [mul_zero]
  rfl

/-- The retarded integral is linear in a constant factor. -/
theorem retardedIntegral_const_mul (c : ℝ) (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    retardedIntegral (fun q => c * f q) p = c * retardedIntegral f p := by
  simp only [retardedIntegral, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext y
  ring

/-- **The time derivative of a slow retarded integral**:
`∂ₜ R(f_κ) = κ R((∂ₜf)_κ)` for a `C¹` function supported in a cylinder. -/
theorem timeDeriv_retardedIntegral_slow {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) {a : ℝ}
    (hs : SpatialSupport a f) (κ : ℝ) :
    timeDeriv (retardedIntegral (slow κ f)) =
      fun p => κ * retardedIntegral (slow κ (timeDeriv f)) p := by
  rw [timeDeriv_retardedIntegral (contDiff_slow hf κ) (hs.slow κ).subluminalSupport,
    timeDeriv_slow (hf.differentiable (by norm_num))]
  funext p
  exact retardedIntegral_const_mul κ _ p

/-- **The spatial derivatives of a slow retarded integral**: `∂ᵢ R(f_κ) = R((∂ᵢf)_κ)` for a `C¹`
function supported in a cylinder. -/
theorem spaceDeriv_retardedIntegral_slow {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) {a : ℝ}
    (hs : SpatialSupport a f) (κ : ℝ) (i : Fin 3) :
    spaceDeriv i (retardedIntegral (slow κ f)) = retardedIntegral (slow κ (spaceDeriv i f)) := by
  rw [spaceDeriv_retardedIntegral (contDiff_slow hf κ) (hs.slow κ).subluminalSupport,
    spaceDeriv_slow (hf.differentiable (by norm_num))]

/-! ### The slow expansion of the retarded integral -/

/-- The `k`-th term of the slow expansion, `(4π)⁻¹ ∫ ‖y‖ᵏ⁻¹ ∂ₜᵏf(s, x − y) dy`, written with the
Newton kernel `1/(4π‖y‖)`; the term `k = 0` is the Newton potential of `f(s, ·)`
(`slowTerm_zero`). -/
def slowTerm (k : ℕ) (f : ℝ × E3 → ℝ) (s : ℝ) (x : E3) : ℝ :=
  ∫ y, Potential.newtonKernel y * (‖y‖ ^ k * timeDeriv^[k] f (s, x - y))

/-- The term `k = 0` of the slow expansion is the Newton potential. -/
theorem slowTerm_zero (f : ℝ × E3 → ℝ) (s : ℝ) (x : E3) :
    slowTerm 0 f s x = Potential.newtonPotential (fun z => f (s, z)) x := by
  simp [slowTerm, Potential.newtonPotential_apply]

/-- The product of the Newton kernel with a continuous function that vanishes outside a ball is
integrable. -/
theorem integrable_newtonKernel_mul_of_vanish {g : E3 → ℝ} (hg : Continuous g) {r : ℝ}
    (hr : ∀ y : E3, r < ‖y‖ → g y = 0) :
    Integrable fun y => Potential.newtonKernel y * g y := by
  have h := Potential.locallyIntegrable_newtonKernel.integrable_smul_right_of_hasCompactSupport hg
    (HasCompactSupport.intro (isCompact_closedBall 0 r) fun y hy => hr y (by simpa using hy))
  simpa [smul_eq_mul] using h

/-- **The slow expansion of the retarded integral** (Landau–Lifshitz §65): for a `Cⁿ⁺¹` source
supported in the cylinder `‖x‖ ≤ a` with `|∂ₜⁿ⁺¹f| ≤ M`, the retarded integral of the slow source
`f_κ(t, x) = f(κt, x)` is, for `κ ≥ 0` and `‖x‖ ≤ ρ`,

  `R(f_κ)(t, x) = Σ_{k ≤ n} ((−κ)ᵏ/k!) (4π)⁻¹ ∫ ‖y‖ᵏ⁻¹ ∂ₜᵏf(κt, x − y) dy`

up to `M (ρ + a)ⁿ⁺³ κⁿ⁺¹/(3 (n + 1)!)`: Taylor's formula in the time at the retarded time
`κ(t − ‖y‖)`, integrated over the ball `‖y‖ ≤ ρ + a` of volume `4π(ρ + a)³/3`. -/
theorem retardedIntegral_slow_expansion {f : ℝ × E3 → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    {a M : ℝ} (ha : 0 ≤ a) (hs : SpatialSupport a f) (hM : ∀ p, |timeDeriv^[n + 1] f p| ≤ M)
    {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {ρ : ℝ} (hx : ‖x‖ ≤ ρ) :
    |retardedIntegral (slow κ f) (t, x) -
        ∑ k ∈ Finset.range (n + 1), (-κ) ^ k / k ! * slowTerm k f (κ * t) x| ≤
      M * (ρ + a) ^ (n + 3) / (3 * (n + 1)!) * κ ^ (n + 1) := by
  have hf' : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞ω) f := by exact_mod_cast hf
  set r := ρ + a with hr_def
  have hr : 0 ≤ r := by have := norm_nonneg x; linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hcont : ∀ k ≤ n + 1, Continuous (timeDeriv^[k] f) := fun k hk =>
    (contDiff_iterate_timeDeriv hf' (m := 0) (k := k) (by omega)).continuous
  have hdiff : ∀ k < n + 1, Differentiable ℝ (timeDeriv^[k] f) := fun k hk =>
    (contDiff_iterate_timeDeriv hf' (m := 1) (k := k) (by omega)).differentiable (by norm_num)
  have hvan : ∀ y : E3, r < ‖y‖ → ∀ (k : ℕ) (s : ℝ), timeDeriv^[k] f (s, x - y) = 0 := by
    intro y hy k s
    refine hs.iterate_timeDeriv k _ ?_
    have := norm_sub_norm_le y x
    rw [norm_sub_rev] at this
    show a < ‖x - y‖
    linarith
  set T : E3 → ℝ := fun y => ∑ k ∈ Finset.range (n + 1),
    (-(κ * ‖y‖)) ^ k / k ! * timeDeriv^[k] f (κ * t, x - y) with hT
  have htaylor : ∀ y : E3, |f (κ * t - κ * ‖y‖, x - y) - T y| ≤
      M * (κ * ‖y‖) ^ (n + 1) / (n + 1)! := fun y => by
    have H := abs_sub_taylor_sub_le (g := fun k s => timeDeriv^[k] f (s, x - y)) (h := κ * ‖y‖)
      (n + 1)
      (fun k hk s => by
        have h1 := hasDerivAt_timeSlice_of_differentiableAt ((hdiff k hk) (s, x - y))
        rwa [← Function.iterate_succ_apply' timeDeriv k f] at h1)
      (κ * t) (by positivity) (fun s => hM _)
    simpa using H
  have hcT : Continuous T := by
    refine continuous_finsetSum _ fun k hk => ?_
    exact ((continuous_const.mul continuous_norm).neg.pow k |>.div_const _).mul
      ((hcont k (by simp at hk; omega)).comp (by fun_prop))
  have hTvan : ∀ y : E3, r < ‖y‖ → T y = 0 := fun y hy => by
    simp [hT, hvan y hy]
  have hR : retardedIntegral (slow κ f) (t, x) =
      ∫ y, Potential.newtonKernel y * f (κ * t - κ * ‖y‖, x - y) := by
    simp only [retardedIntegral, slow, Potential.newtonKernel, smul_eq_mul, Prod.mk_sub_mk,
      mul_sub]
  have hS : ∑ k ∈ Finset.range (n + 1), (-κ) ^ k / k ! * slowTerm k f (κ * t) x =
      ∫ y, Potential.newtonKernel y * T y := by
    simp only [slowTerm, hT, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    · intro k hk
      have h := integrable_newtonKernel_mul_of_vanish (g := fun y => (-(κ * ‖y‖)) ^ k / k ! *
        timeDeriv^[k] f (κ * t, x - y))
        (((continuous_const.mul continuous_norm).neg.pow k |>.div_const _).mul
          ((hcont k (by simp at hk; omega)).comp (by fun_prop)))
        (r := r) (fun y hy => by simp [hvan y hy])
      exact h
  have hf0 : Continuous fun y : E3 => f (κ * t - κ * ‖y‖, x - y) :=
    hf.continuous.comp (by fun_prop)
  have hfvan : ∀ y : E3, r < ‖y‖ → f (κ * t - κ * ‖y‖, x - y) = 0 := fun y hy =>
    hvan y hy 0 _
  rw [hR, hS, ← integral_sub (integrable_newtonKernel_mul_of_vanish hf0 hfvan)
    (integrable_newtonKernel_mul_of_vanish hcT hTvan)]
  set c : ℝ := M * κ ^ (n + 1) * r ^ n / (4 * π * (n + 1)!) with hc
  have hpt : ∀ y : E3, ‖Potential.newtonKernel y * f (κ * t - κ * ‖y‖, x - y) -
      Potential.newtonKernel y * T y‖ ≤ (closedBall (0 : E3) r).indicator (fun _ => c) y := by
    intro y
    by_cases hy : ‖y‖ ≤ r
    · rw [indicator_of_mem (by simpa using hy), ← mul_sub, norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (Potential.newtonKernel_nonneg y)]
      rcases eq_or_ne y 0 with rfl | hy0
      · simp only [Potential.newtonKernel, norm_zero, mul_zero, inv_zero, zero_mul, hc]
        positivity
      · have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy0
        calc Potential.newtonKernel y * |f (κ * t - κ * ‖y‖, x - y) - T y|
            ≤ Potential.newtonKernel y * (M * (κ * ‖y‖) ^ (n + 1) / (n + 1)!) :=
              mul_le_mul_of_nonneg_left (htaylor y) (Potential.newtonKernel_nonneg y)
          _ = M * κ ^ (n + 1) * ‖y‖ ^ n / (4 * π * (n + 1)!) := by
              rw [Potential.newtonKernel]
              field_simp
              ring
          _ ≤ c := by
              rw [hc]
              gcongr
    · rw [indicator_of_notMem (by simpa using hy)]
      have hy' : r < ‖y‖ := not_le.mp hy
      simp [hfvan y hy', hTvan y hy']
  have hint : Integrable ((closedBall (0 : E3) r).indicator fun _ => c) :=
    (integrableOn_const (C := c) measure_closedBall_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  calc |∫ y, (Potential.newtonKernel y * f (κ * t - κ * ‖y‖, x - y) -
        Potential.newtonKernel y * T y)|
      ≤ ∫ y, (closedBall (0 : E3) r).indicator (fun _ => c) y := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = M * (ρ + a) ^ (n + 3) / (3 * (n + 1)!) * κ ^ (n + 1) := by
        rw [integral_indicator_const _ measurableSet_closedBall, Measure.real,
          EuclideanSpace.volume_closedBall_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity), smul_eq_mul, hc,
          ← hr_def]
        field_simp
        ring

/-! ### Integrals against a kernel in space -/

section KernelIntegral

variable {G : Type*} [NormedAddCommGroup G]

/-- The integrand `K(y) F(p − (0, y))` vanishes, for the points `p` near any point, outside a
ball of `y`: either the kernel or the function provides the bounded support. -/
def KernelSupport (K : E3 → ℝ) (F : ℝ × E3 → G) : Prop :=
  ∀ p₀ : ℝ × E3, ∃ L, ∀ p ∈ ball p₀ 1, ∀ y : E3, L < ‖y‖ → K y = 0 ∨ p - (0, y) ∉ tsupport F

/-- The kernel support passes to a function with a smaller support. -/
theorem KernelSupport.mono {G' : Type*} [NormedAddCommGroup G'] {K : E3 → ℝ} {F : ℝ × E3 → G}
    {F' : ℝ × E3 → G'} (h : KernelSupport K F) (hF : tsupport F' ⊆ tsupport F) :
    KernelSupport K F' := fun p₀ => by
  obtain ⟨L, hL⟩ := h p₀
  exact ⟨L, fun p hp y hy => (hL p hp y hy).imp id fun h' h'' => h' (hF h'')⟩

/-- A function supported in a cylinder has the kernel support for every kernel. -/
theorem SpatialSupport.kernelSupport {a : ℝ} {F : ℝ × E3 → G} (hF : SpatialSupport a F)
    (K : E3 → ℝ) : KernelSupport K F := fun p₀ => by
  refine ⟨a + ‖p₀.2‖ + 1, fun p hp y hy => Or.inr fun hmem => ?_⟩
  have h1 : ‖p.2 - y‖ ≤ a := by simpa using hF.tsupport_subset hmem
  have h2 : ‖p.2 - p₀.2‖ < 1 := by
    rw [← dist_eq_norm]
    exact lt_of_le_of_lt (le_max_right _ _) (mem_ball.mp hp)
  have h3 := norm_sub_norm_le y p.2
  have h4 := norm_sub_norm_le p.2 p₀.2
  rw [norm_sub_rev y] at h3
  linarith

/-- A kernel that vanishes outside a ball gives the kernel support for every function. -/
theorem kernelSupport_of_kernel {K : E3 → ℝ} {b : ℝ} (hK : ∀ y : E3, b < ‖y‖ → K y = 0)
    (F : ℝ × E3 → G) : KernelSupport K F :=
  fun _ => ⟨b, fun _ _ y hy => Or.inl (hK y hy)⟩

/-- The integrand vanishes outside the ball of the kernel support. -/
theorem KernelSupport.smul_eq_zero {K : E3 → ℝ} {F : ℝ × E3 → G} {L : ℝ} {p₀ : ℝ × E3}
    (hL : ∀ p ∈ ball p₀ 1, ∀ y : E3, L < ‖y‖ → K y = 0 ∨ p - (0, y) ∉ tsupport F)
    [Module ℝ G] {p : ℝ × E3} (hp : p ∈ ball p₀ 1) {y : E3} (hy : L < ‖y‖) :
    K y • F (p - (0, y)) = 0 := by
  rcases hL p hp y hy with h | h
  · simp [h]
  · simp [image_eq_zero_of_notMem_tsupport h]

variable [NormedSpace ℝ G]

/-- The derivative of a function has the kernel support of the function. -/
theorem KernelSupport.fderiv {K : E3 → ℝ} {F : ℝ × E3 → G} (h : KernelSupport K F) :
    KernelSupport K (_root_.fderiv ℝ F) :=
  h.mono (tsupport_fderiv_subset ℝ)

/-- The **integral against a kernel in space**, `∫ K(y) F(t, x − y) dy` at `p = (t, x)`. -/
def kernelIntegral (K : E3 → ℝ) (F : ℝ × E3 → G) (p : ℝ × E3) : G :=
  ∫ y, K y • F (p - (0, y))

/-- The integrand of the integral against a locally integrable kernel is integrable. -/
theorem KernelSupport.integrable {K : E3 → ℝ} {F : ℝ × E3 → G} (hs : KernelSupport K F)
    (hK : LocallyIntegrable K) (hF : Continuous F) (p : ℝ × E3) :
    Integrable fun y => K y • F (p - (0, y)) := by
  obtain ⟨L, hL⟩ := hs p
  have hon : IntegrableOn (fun y => K y • F (p - (0, y))) (closedBall (0 : E3) L) :=
    (hK.integrableOn_isCompact (isCompact_closedBall 0 L)).smul_continuousOn
      (hF.comp (by fun_prop)).continuousOn (isCompact_closedBall 0 L)
  refine hon.integrable_of_forall_notMem_eq_zero fun y hy => ?_
  exact KernelSupport.smul_eq_zero hL (mem_ball_self one_pos) (by simpa using hy)

/-- A local bound for the integrand: near `p₀` it is at most `C |K(y)|` on a ball of `y` and
vanishes outside. -/
theorem KernelSupport.exists_bound {K : E3 → ℝ} {F : ℝ × E3 → G} (hs : KernelSupport K F)
    (hF : Continuous F) (p₀ : ℝ × E3) :
    ∃ C L, ∀ p ∈ ball p₀ 1, ∀ y : E3,
      ‖K y • F (p - (0, y))‖ ≤ (closedBall (0 : E3) L).indicator (fun y => C * ‖K y‖) y := by
  obtain ⟨L, hL⟩ := hs p₀
  have hKc : IsCompact ((fun q : (ℝ × E3) × E3 => q.1 - ((0 : ℝ), q.2)) ''
      (closedBall p₀ 1 ×ˢ closedBall (0 : E3) L)) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (by fun_prop)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨C, L, fun p hp y => ?_⟩
  by_cases hy : ‖y‖ ≤ L
  · rw [indicator_of_mem (by simpa using hy), norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _ ⟨(p, y), ⟨ball_subset_closedBall hp,
      by simpa using hy⟩, rfl⟩) (norm_nonneg _)
  · rw [indicator_of_notMem (by simpa using hy), KernelSupport.smul_eq_zero hL hp
      (not_le.mp hy), norm_zero]

/-- The local bound is integrable. -/
theorem integrable_indicator_mul_norm {K : E3 → ℝ} (hK : LocallyIntegrable K) (C L : ℝ) :
    Integrable ((closedBall (0 : E3) L).indicator fun y => C * ‖K y‖) :=
  IntegrableOn.integrable_indicator
    ((hK.integrableOn_isCompact (isCompact_closedBall 0 L)).norm.const_mul C)
    measurableSet_closedBall

/-- The integral against a locally integrable kernel of a continuous function is continuous. -/
theorem continuous_kernelIntegral {K : E3 → ℝ} {F : ℝ × E3 → G} (hK : LocallyIntegrable K)
    (hc : Continuous F) (hs : KernelSupport K F) : Continuous (kernelIntegral K F) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨C, L, hC⟩ := hs.exists_bound hc p₀
  refine continuousAt_of_dominated (Eventually.of_forall fun p =>
    (hs.integrable hK hc p).aestronglyMeasurable) ?_ (integrable_indicator_mul_norm hK C L) ?_
  · filter_upwards [ball_mem_nhds p₀ one_pos] with p hp
    exact Eventually.of_forall (hC p hp)
  · exact Eventually.of_forall fun y => (continuous_const.smul (hc.comp (by fun_prop))).continuousAt

/-- **The derivative of an integral against a kernel** is the integral of the derivative, for a
`C¹` function. -/
theorem hasFDerivAt_kernelIntegral [CompleteSpace G] {K : E3 → ℝ} {F : ℝ × E3 → G}
    (hK : LocallyIntegrable K) (hc : ContDiff ℝ 1 F) (hs : KernelSupport K F) (p₀ : ℝ × E3) :
    HasFDerivAt (kernelIntegral K F) (kernelIntegral K (_root_.fderiv ℝ F) p₀) p₀ := by
  have hc' : Continuous (_root_.fderiv ℝ F) := hc.continuous_fderiv (by norm_num)
  obtain ⟨C, L, hC⟩ := hs.fderiv.exists_bound hc' p₀
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds p₀ one_pos)
    (Eventually.of_forall fun p => (hs.integrable hK hc.continuous p).aestronglyMeasurable)
    (hs.integrable hK hc.continuous p₀) (hs.fderiv.integrable hK hc' p₀).aestronglyMeasurable
    (Eventually.of_forall fun y p hp => hC p hp y) (integrable_indicator_mul_norm hK C L)
    (Eventually.of_forall fun y p _ => ?_)
  exact ((hasFDerivAt_comp_sub ((0 : ℝ), y)).mpr
    ((hc.differentiable (by norm_num)) (p - (0, y))).hasFDerivAt).const_smul (K y)

/-- The derivative of an integral against a kernel of a `C¹` function. -/
theorem fderiv_kernelIntegral [CompleteSpace G] {K : E3 → ℝ} {F : ℝ × E3 → G}
    (hK : LocallyIntegrable K) (hc : ContDiff ℝ 1 F) (hs : KernelSupport K F) :
    _root_.fderiv ℝ (kernelIntegral K F) = kernelIntegral K (_root_.fderiv ℝ F) :=
  funext fun p => (hasFDerivAt_kernelIntegral hK hc hs p).fderiv

/-- The integral against a kernel commutes with the evaluation of linear maps. -/
theorem kernelIntegral_apply_clm [CompleteSpace G] {K : E3 → ℝ} {F : ℝ × E3 → ℝ × E3 →L[ℝ] G}
    (hK : LocallyIntegrable K) (hc : Continuous F) (hs : KernelSupport K F) (p v : ℝ × E3) :
    kernelIntegral K F p v = kernelIntegral K (fun q => F q v) p := by
  rw [kernelIntegral, ContinuousLinearMap.integral_apply (hs.integrable hK hc p)]
  rfl

/-- **Smoothness of an integral against a kernel**: for a `Cⁿ` function it is `Cⁿ`. -/
theorem contDiff_kernelIntegral_nat [CompleteSpace G] {K : E3 → ℝ} (hK : LocallyIntegrable K)
    (n : ℕ) {F : ℝ × E3 → G} (hc : ContDiff ℝ n F) (hs : KernelSupport K F) :
    ContDiff ℝ n (kernelIntegral K F) := by
  induction n generalizing G with
  | zero => exact contDiff_zero.mpr (continuous_kernelIntegral hK (contDiff_zero.mp hc) hs)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one] at hc ⊢
    rw [contDiff_succ_iff_hasFDerivAt]
    exact ⟨kernelIntegral K (_root_.fderiv ℝ F), ih (hc.fderiv_right le_rfl) hs.fderiv,
      hasFDerivAt_kernelIntegral hK (hc.of_le (by simp)) hs⟩

/-- **Smoothness of an integral against a kernel**, for `n ≤ ∞`. -/
theorem contDiff_kernelIntegral [CompleteSpace G] {K : E3 → ℝ} (hK : LocallyIntegrable K)
    {n : ℕ∞} {F : ℝ × E3 → G} (hc : ContDiff ℝ n F) (hs : KernelSupport K F) :
    ContDiff ℝ n (kernelIntegral K F) := by
  induction n with
  | top =>
    exact contDiff_infty.mpr fun m =>
      contDiff_kernelIntegral_nat hK m (hc.of_le (by exact_mod_cast le_top)) hs
  | coe m => exact contDiff_kernelIntegral_nat hK m hc hs

end KernelIntegral

/-- The time derivative commutes with an integral against a kernel. -/
theorem timeDeriv_kernelIntegral {K : E3 → ℝ} {F : ℝ × E3 → ℝ} (hK : LocallyIntegrable K)
    (hc : ContDiff ℝ 1 F) (hs : KernelSupport K F) :
    timeDeriv (kernelIntegral K F) = kernelIntegral K (timeDeriv F) := by
  funext p
  rw [timeDeriv, fderiv_kernelIntegral hK hc hs,
    kernelIntegral_apply_clm hK (hc.continuous_fderiv (by norm_num)) hs.fderiv]
  rfl

/-- The spatial derivatives commute with an integral against a kernel. -/
theorem spaceDeriv_kernelIntegral {K : E3 → ℝ} {F : ℝ × E3 → ℝ} (hK : LocallyIntegrable K)
    (hc : ContDiff ℝ 1 F) (hs : KernelSupport K F) (i : Fin 3) :
    spaceDeriv i (kernelIntegral K F) = kernelIntegral K (spaceDeriv i F) := by
  funext p
  rw [spaceDeriv, fderiv_kernelIntegral hK hc hs,
    kernelIntegral_apply_clm hK (hc.continuous_fderiv (by norm_num)) hs.fderiv]
  rfl

/-- The kernel support passes to the time derivative. -/
theorem KernelSupport.timeDeriv {K : E3 → ℝ} {F : ℝ × E3 → ℝ} (h : KernelSupport K F) :
    KernelSupport K (Wave.timeDeriv F) :=
  h.mono (tsupport_timeDeriv_subset F)

/-- The kernel support passes to the spatial derivatives. -/
theorem KernelSupport.spaceDeriv {K : E3 → ℝ} {F : ℝ × E3 → ℝ} (h : KernelSupport K F)
    (i : Fin 3) : KernelSupport K (Wave.spaceDeriv i F) :=
  h.mono (tsupport_spaceDeriv_subset i F)

/-- The integral against a kernel at `(t, x)` as an integral over the source points,
`∫ K(x − z) F(t, z) dz`. -/
theorem kernelIntegral_eq_integral_sub (K : E3 → ℝ) (F : ℝ × E3 → ℝ) (t : ℝ) (x : E3) :
    kernelIntegral K F (t, x) = ∫ z, K (x - z) * F (t, z) := by
  rw [kernelIntegral, ← integral_sub_left_eq_self (fun z => K (x - z) * F (t, z)) volume x]
  congr 1
  funext y
  simp [smul_eq_mul]

/-- The integral against a kernel is linear in a constant factor. -/
theorem kernelIntegral_const_mul (K : E3 → ℝ) (c : ℝ) (F : ℝ × E3 → ℝ) (p : ℝ × E3) :
    kernelIntegral K (fun q => c * F q) p = c * kernelIntegral K F p := by
  simp only [kernelIntegral, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext y
  ring

/-- The time derivative of a smooth function is smooth. -/
theorem contDiff_infty_timeDeriv {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (timeDeriv f) :=
  contDiff_infty.mpr fun n => contDiff_timeDeriv (n := n) (hf.of_le (by simp))

/-- The spatial derivatives of a smooth function are smooth. -/
theorem contDiff_infty_spaceDeriv {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (spaceDeriv i f) :=
  contDiff_infty.mpr fun n => contDiff_spaceDeriv (n := n) (hf.of_le (by simp)) i

/-- A kernel bounded by a multiple of the Newton kernel, against a continuous function of compact
support, is integrable over the source points. -/
theorem integrable_kernel_sub_mul {K : E3 → ℝ} (hK : AEStronglyMeasurable K) {C : ℝ}
    (hKC : ∀ y, |K y| ≤ C * Potential.newtonKernel y) {g : E3 → ℝ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (x : E3) : Integrable fun z => K (x - z) * g z := by
  have hb := ((Potential.integrable_newtonKernel_mul (ρ := fun z => |g z|) hcg.abs hg.abs
    x).comp_sub_left x).const_mul C
  refine hb.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (hK.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).mul
      hg.aestronglyMeasurable
  · simp only [sub_sub_cancel, norm_mul, Real.norm_eq_abs]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hKC _) (abs_nonneg _)

/-- The term of the slow expansion as an integral against the kernel `‖y‖ᵏ/(4π‖y‖)`. -/
theorem slowTerm_eq_kernelIntegral (k : ℕ) (f : ℝ × E3 → ℝ) (s : ℝ) (x : E3) :
    slowTerm k f s x =
      kernelIntegral (fun y => Potential.newtonKernel y * ‖y‖ ^ k) (timeDeriv^[k] f) (s, x) := by
  simp only [slowTerm, kernelIntegral, smul_eq_mul, Prod.mk_sub_mk, sub_zero, mul_assoc]

/-! ### The second derivatives of the distance -/

/-- The derivative of the regularized distance `K(z) = √(‖x − z‖² + δ²)` along `u` is
`−⟨x − z, u⟩/K(z)`. -/
theorem hasFDerivAt_regularDistance (x : E3) {δ : ℝ} (hδ : δ ≠ 0) (z : E3) :
    HasFDerivAt (fun z' : E3 => √(‖x - z'‖ ^ 2 + δ ^ 2))
      ((1 / (2 * √(‖x - z‖ ^ 2 + δ ^ 2))) •
        ((2 • innerSL ℝ (x - z)).comp (-ContinuousLinearMap.id ℝ E3))) z := by
  have hq : 0 < ‖x - z‖ ^ 2 + δ ^ 2 := by positivity
  exact (((hasStrictFDerivAt_norm_sq (x - z)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_sub x)).add_const (δ ^ 2)).sqrt hq.ne'

/-- **Integration by parts against the regularized distance**: for `δ ≠ 0` and
`K(z) = √(‖x − z‖² + δ²)`, `∫ K ∂ᵥ∂_w F = ∫ (⟨v, w⟩/K − ⟨v, x − z⟩⟨w, x − z⟩/K³) F` for a `C²`
function `F` of compact support. -/
theorem integral_regularDistance_mul_fderiv_fderiv {F : E3 → ℝ} (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) (x v w : E3) {δ : ℝ} (hδ : δ ≠ 0) :
    ∫ z, √(‖x - z‖ ^ 2 + δ ^ 2) * fderiv ℝ (fun z' => fderiv ℝ F z' w) z v =
      ∫ z, (inner ℝ v w / √(‖x - z‖ ^ 2 + δ ^ 2) -
        inner ℝ v (x - z) * inner ℝ w (x - z) / √(‖x - z‖ ^ 2 + δ ^ 2) ^ 3) * F z := by
  set K : E3 → ℝ := fun z => √(‖x - z‖ ^ 2 + δ ^ 2) with hK
  have hKpos : ∀ z, 0 < K z := fun z => Real.sqrt_pos.mpr (by positivity)
  have hKd := hasFDerivAt_regularDistance x hδ
  have hKcont : Continuous K := by
    rw [hK]
    fun_prop
  have hKv : ∀ z, fderiv ℝ K z v = -(inner ℝ v (x - z) / K z) := fun z => by
    have := (hKpos z).ne'
    rw [(hKd z).fderiv]
    simp only [hK] at this ⊢
    simp only [smul_apply, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, innerSL_apply_apply, inner_neg_right,
      real_inner_comm v (x - z), nsmul_eq_mul, Nat.cast_ofNat]
    field_simp
  set g : E3 → ℝ := fun z => inner ℝ v (x - z) * (K z)⁻¹ with hg
  have hgd : ∀ z, HasFDerivAt g (inner ℝ v (x - z) • ((-(K z ^ 2)⁻¹) • fderiv ℝ K z) +
      (K z)⁻¹ • ((innerSL ℝ v).comp (-ContinuousLinearMap.id ℝ E3))) z := fun z => by
    have h1 := (innerSL ℝ v).hasFDerivAt.comp z ((hasFDerivAt_id z).const_sub x)
    have h2 := (hasDerivAt_inv (hKpos z).ne').comp_hasFDerivAt z
      ((hKd z).differentiableAt.hasFDerivAt)
    exact h1.mul h2
  have hgw : ∀ z, fderiv ℝ g z w =
      -(inner ℝ v w / K z) + inner ℝ v (x - z) * inner ℝ w (x - z) / K z ^ 3 := fun z => by
    have := (hKpos z).ne'
    rw [(hgd z).fderiv, (hKd z).fderiv]
    simp only [hK] at this ⊢
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, innerSL_apply_apply, inner_neg_right,
      real_inner_comm (x - z) w, nsmul_eq_mul, Nat.cast_ofNat]
    field_simp
    ring
  have hgcont : Continuous g := by
    rw [hg]
    exact (continuous_const.inner (continuous_const.sub continuous_id)).mul
      (hKcont.inv₀ fun z => (hKpos z).ne')
  have hKvc : Continuous fun z => fderiv ℝ K z v := by
    simp only [hKv]
    exact ((continuous_const.inner (continuous_const.sub continuous_id)).div hKcont
      fun z => (hKpos z).ne').neg
  have hgwc : Continuous fun z => fderiv ℝ g z w := by
    simp only [hgw]
    exact (continuous_const.div hKcont fun z => (hKpos z).ne').neg.add
      (((continuous_const.inner (continuous_const.sub continuous_id)).mul
        (continuous_const.inner (continuous_const.sub continuous_id))).div (hKcont.pow 3)
        fun z => pow_ne_zero 3 (hKpos z).ne')
  set Fw : E3 → ℝ := fun z => fderiv ℝ F z w with hFw
  have hFw1 : ContDiff ℝ 1 Fw := (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hcFw : HasCompactSupport Fw := hc.fderiv_apply (𝕜 := ℝ) w
  have hcFwv : HasCompactSupport fun z => fderiv ℝ Fw z v := hcFw.fderiv_apply (𝕜 := ℝ) v
  have hFwvc : Continuous fun z => fderiv ℝ Fw z v :=
    (hFw1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have step1 : ∫ z, K z * fderiv ℝ Fw z v = -∫ z, fderiv ℝ K z v * Fw z := by
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
      (fun z _ => (hKd z).differentiableAt) (fun z _ => (hFw1.differentiable (by norm_num)) z)
    · exact (hKvc.mul hFw1.continuous).integrable_of_hasCompactSupport hcFw.mul_left
    · exact (hKcont.mul hFwvc).integrable_of_hasCompactSupport hcFwv.mul_left
    · exact (hKcont.mul hFw1.continuous).integrable_of_hasCompactSupport hcFw.mul_left
  have step2 : ∫ z, g z * fderiv ℝ F z w = -∫ z, fderiv ℝ g z w * F z := by
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
      (fun z _ => (hgd z).differentiableAt) (fun z _ => (hF.differentiable (by norm_num)) z)
    · exact (hgwc.mul hF.continuous).integrable_of_hasCompactSupport hc.mul_left
    · exact (hgcont.mul hFw1.continuous).integrable_of_hasCompactSupport hcFw.mul_left
    · exact (hgcont.mul hF.continuous).integrable_of_hasCompactSupport hc.mul_left
  change ∫ z, K z * fderiv ℝ Fw z v = _
  rw [step1]
  have e1 : (fun z => fderiv ℝ K z v * Fw z) = fun z => -(g z * fderiv ℝ F z w) := by
    funext z
    rw [hKv, hg, hFw]
    simp only [div_eq_mul_inv]
    ring
  rw [e1, integral_neg, neg_neg, step2, ← integral_neg]
  congr 1
  funext z
  rw [hgw]
  ring

/-- **The second derivatives of the distance**, in the sense of distributions: for a `C²`
function `F` of compact support,

  `∫ ‖x − z‖ ∂ᵥ∂_w F(z) dz = ∫ (⟨v, w⟩/‖x − z‖ − ⟨v, x − z⟩⟨w, x − z⟩/‖x − z‖³) F(z) dz`.

There is no point term at `z = x`, since the first derivatives of the distance are bounded. The
proof lets `δ → 0⁺` in `integral_regularDistance_mul_fderiv_fderiv`, with the bounds
`K ≤ ‖x − z‖ + 1` and `|⟨v, w⟩/K − ⟨v, x − z⟩⟨w, x − z⟩/K³| ≤ 2‖v‖‖w‖/‖x − z‖`. -/
theorem integral_norm_sub_mul_fderiv_fderiv {F : E3 → ℝ} (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) (x v w : E3) :
    ∫ z, ‖x - z‖ * fderiv ℝ (fun z' => fderiv ℝ F z' w) z v =
      ∫ z, (inner ℝ v w / ‖x - z‖ -
        inner ℝ v (x - z) * inner ℝ w (x - z) / ‖x - z‖ ^ 3) * F z := by
  set D : E3 → ℝ := fun z => fderiv ℝ (fun z' => fderiv ℝ F z' w) z v with hD
  have hFw1 : ContDiff ℝ 1 fun z => fderiv ℝ F z w :=
    (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDc : Continuous D := (hFw1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcD : HasCompactSupport D := (hc.fderiv_apply (𝕜 := ℝ) w).fderiv_apply (𝕜 := ℝ) v
  have hKlim : ∀ z : E3, Tendsto (fun δ : ℝ => √(‖x - z‖ ^ 2 + δ ^ 2)) (𝓝[>] 0)
      (𝓝 ‖x - z‖) := fun z => by
    have hcont : Continuous fun δ : ℝ => √(‖x - z‖ ^ 2 + δ ^ 2) := by fun_prop
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hKge : ∀ (δ : ℝ) (z : E3), ‖x - z‖ ≤ √(‖x - z‖ ^ 2 + δ ^ 2) := fun δ z => by
    calc ‖x - z‖ = √(‖x - z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
  have hL : Tendsto (fun δ : ℝ => ∫ z, √(‖x - z‖ ^ 2 + δ ^ 2) * D z) (𝓝[>] 0)
      (𝓝 (∫ z, ‖x - z‖ * D z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => (‖x - z‖ + 1) * |D z|)
      ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun δ =>
        ((by fun_prop : Continuous fun z : E3 => √(‖x - z‖ ^ 2 + δ ^ 2)).mul
          hDc).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
      refine Eventually.of_forall fun z => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      refine mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩)
        (abs_nonneg _)
      nlinarith [hδ.1, hδ.2, norm_nonneg (x - z)]
    · exact (((continuous_norm.comp (continuous_const.sub continuous_id)).add
        continuous_const).mul hDc.abs).integrable_of_hasCompactSupport hcD.abs.mul_left
    · exact Eventually.of_forall fun z => (hKlim z).mul_const _
  have h0 : ∀ᵐ z : E3, z ≠ x := by
    rw [ae_iff]
    simp
  have hbint : Integrable fun z : E3 => 2 * ‖v‖ * ‖w‖ * (‖x - z‖⁻¹ * |F z|) := by
    have h := ((Potential.integrable_newtonKernel_mul (ρ := fun z => |F z|) hc.abs hF.continuous.abs
      x).comp_sub_left x).const_mul (2 * ‖v‖ * ‖w‖ * (4 * π))
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp only [sub_sub_cancel, Potential.newtonKernel, mul_inv]
    have hπ : (4 * π) ≠ 0 := by positivity
    field_simp
  have hR : Tendsto (fun δ : ℝ => ∫ z, (inner ℝ v w / √(‖x - z‖ ^ 2 + δ ^ 2) -
      inner ℝ v (x - z) * inner ℝ w (x - z) / √(‖x - z‖ ^ 2 + δ ^ 2) ^ 3) * F z) (𝓝[>] 0)
      (𝓝 (∫ z, (inner ℝ v w / ‖x - z‖ -
        inner ℝ v (x - z) * inner ℝ w (x - z) / ‖x - z‖ ^ 3) * F z)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => 2 * ‖v‖ * ‖w‖ * (‖x - z‖⁻¹ * |F z|)) ?_ ?_ hbint ?_
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      have hK : Continuous fun z : E3 => √(‖x - z‖ ^ 2 + δ ^ 2) := by fun_prop
      have hKp : ∀ z : E3, √(‖x - z‖ ^ 2 + δ ^ 2) ≠ 0 := fun z =>
        (Real.sqrt_pos.mpr (by positivity)).ne'
      exact (((continuous_const.div hK hKp).sub
        (((continuous_const.inner (continuous_const.sub continuous_id)).mul
          (continuous_const.inner (continuous_const.sub continuous_id))).div (hK.pow 3)
          fun z => pow_ne_zero 3 (hKp z))).mul hF.continuous).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      filter_upwards [h0] with z hz
      set n := ‖x - z‖ with hn
      set K := √(‖x - z‖ ^ 2 + δ ^ 2) with hKd
      have hnp : 0 < n := norm_pos_iff.mpr (sub_ne_zero.mpr hz.symm)
      have hnK : n ≤ K := hKge δ z
      have hKp : 0 < K := hnp.trans_le hnK
      have hvw := abs_real_inner_le_norm v w
      have hvu := abs_real_inner_le_norm v (x - z)
      have hwu := abs_real_inner_le_norm w (x - z)
      have h1 : |inner ℝ v w / K| ≤ ‖v‖ * ‖w‖ * n⁻¹ := by
        rw [abs_div, abs_of_pos hKp, div_eq_mul_inv]
        exact mul_le_mul hvw (inv_anti₀ hnp hnK) (by positivity) (by positivity)
      have h2 : |inner ℝ v (x - z) * inner ℝ w (x - z) / K ^ 3| ≤ ‖v‖ * ‖w‖ * n⁻¹ := by
        rw [abs_div, abs_mul, abs_of_pos (pow_pos hKp 3)]
        calc |inner ℝ v (x - z)| * |inner ℝ w (x - z)| / K ^ 3
            ≤ (‖v‖ * n) * (‖w‖ * n) / n ^ 3 := by
              gcongr
          _ = ‖v‖ * ‖w‖ * n⁻¹ := by
              field_simp
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |inner ℝ v w / K - inner ℝ v (x - z) * inner ℝ w (x - z) / K ^ 3| * |F z|
          ≤ (‖v‖ * ‖w‖ * n⁻¹ + ‖v‖ * ‖w‖ * n⁻¹) * |F z| :=
            mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
        _ = 2 * ‖v‖ * ‖w‖ * (n⁻¹ * |F z|) := by ring
    · filter_upwards [h0] with z hz
      have hn : ‖x - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz.symm)
      exact ((tendsto_const_nhds.div (hKlim z) hn).sub (tendsto_const_nhds.div
        ((hKlim z).pow 3) (pow_ne_zero 3 hn))).mul_const (F z)
  have heq : (fun δ : ℝ => ∫ z, √(‖x - z‖ ^ 2 + δ ^ 2) * D z) =ᶠ[𝓝[>] 0]
      fun δ : ℝ => ∫ z, (inner ℝ v w / √(‖x - z‖ ^ 2 + δ ^ 2) -
        inner ℝ v (x - z) * inner ℝ w (x - z) / √(‖x - z‖ ^ 2 + δ ^ 2) ^ 3) * F z := by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact integral_regularDistance_mul_fderiv_fderiv hF hc x v w hδ.ne'
  exact tendsto_nhds_unique (hL.congr' heq) hR

/-! ### Spatial slices -/

/-- A spatial derivative is the derivative of the spatial slice `z ↦ g(s, z)`. -/
theorem spaceDeriv_eq_fderiv_slice {g : ℝ × E3 → ℝ} {s : ℝ} {z : E3}
    (hg : DifferentiableAt ℝ g (s, z)) (i : Fin 3) :
    spaceDeriv i g (s, z) = fderiv ℝ (fun z' => g (s, z')) z (EuclideanSpace.single i 1) := by
  have h : HasFDerivAt (fun z' => g (s, z'))
      ((fderiv ℝ g (s, z)).comp ((0 : E3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E3))) z :=
    hg.hasFDerivAt.comp z ((hasFDerivAt_const s z).prodMk (hasFDerivAt_id z))
  rw [h.fderiv]
  rfl

/-- The spatial slice of a `Cⁿ` function supported in a cylinder is `Cⁿ` with compact support. -/
theorem SpatialSupport.hasCompactSupport_slice {a : ℝ} {g : ℝ × E3 → ℝ}
    (hs : SpatialSupport a g) (s : ℝ) : HasCompactSupport fun z : E3 => g (s, z) :=
  HasCompactSupport.intro (isCompact_closedBall 0 a) fun z hz => hs (s, z) (by simpa using hz)

/-- **The integral of a spatial derivative vanishes**, `∫ ∂ᵢg(s, z) dz = 0`, for a `C¹` function
supported in a cylinder. -/
theorem integral_spaceDeriv_eq_zero {g : ℝ × E3 → ℝ} (hg : ContDiff ℝ 1 g) {a : ℝ}
    (hs : SpatialSupport a g) (s : ℝ) (i : Fin 3) : ∫ z, spaceDeriv i g (s, z) = 0 := by
  simp_rw [fun z => spaceDeriv_eq_fderiv_slice ((hg.differentiable (by norm_num)) (s, z)) i]
  exact integral_fderiv_eq_zero (hg.comp (contDiff_const.prodMk contDiff_id))
    (hs.hasCompactSupport_slice s) _

/-- **The second derivatives of the distance in space-time form**: for a `C²` function supported
in a cylinder, `∫ ‖x − z‖ ∂ᵢ∂ₖg(s, z) dz = ∫ (δᵢₖ/‖x − z‖ − (x − z)ᵢ(x − z)ₖ/‖x − z‖³) g(s, z) dz`.
-/
theorem integral_norm_sub_mul_spaceDeriv_spaceDeriv {g : ℝ × E3 → ℝ} (hg : ContDiff ℝ 2 g)
    {a : ℝ} (hs : SpatialSupport a g) (s : ℝ) (x : E3) (i k : Fin 3) :
    ∫ z, ‖x - z‖ * spaceDeriv i (spaceDeriv k g) (s, z) =
      ∫ z, ((if i = k then 1 else 0) / ‖x - z‖ - (x - z) i * (x - z) k / ‖x - z‖ ^ 3) *
        g (s, z) := by
  set F : E3 → ℝ := fun z => g (s, z) with hFd
  have hF : ContDiff ℝ 2 F := hg.comp (contDiff_const.prodMk contDiff_id)
  have h1 : ∀ z', spaceDeriv k g (s, z') = fderiv ℝ F z' (EuclideanSpace.single k 1) :=
    fun z' => spaceDeriv_eq_fderiv_slice ((hg.differentiable (by norm_num)) _) k
  have h2 : ∀ z, spaceDeriv i (spaceDeriv k g) (s, z) = fderiv ℝ
      (fun z' => fderiv ℝ F z' (EuclideanSpace.single k 1)) z (EuclideanSpace.single i 1) :=
    fun z => by
      rw [spaceDeriv_eq_fderiv_slice
        (((contDiff_spaceDeriv (n := 1) hg k).differentiable (by norm_num)) _) i]
      congr 2
      funext z'
      exact h1 z'
  simp_rw [h2]
  rw [integral_norm_sub_mul_fderiv_fderiv hF (hs.hasCompactSupport_slice s) x _ _]
  congr 1
  funext z
  simp [EuclideanSpace.inner_single_left, PiLp.single_apply, hFd]

/-- The time derivatives commute with a spatial derivative: `∂ₜᵏ∂ᵢf = ∂ᵢ∂ₜᵏf` for a `Cᴺ`
function with `k + 1 ≤ N`. -/
theorem iterate_timeDeriv_spaceDeriv {N : ℕ} {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ N f) (i : Fin 3)
    {k : ℕ} (hk : k + 1 ≤ N) : timeDeriv^[k] (spaceDeriv i f) = spaceDeriv i (timeDeriv^[k] f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
    funext p
    exact timeDeriv_spaceDeriv
      ((contDiff_iterate_timeDeriv hf (m := 2) (k := k) (by omega)).contDiffAt) i

/-- The kernel `‖y‖²/(4π‖y‖) = ‖y‖/(4π)` of the second term of the slow expansion. -/
theorem newtonKernel_mul_norm_sq (y : E3) :
    Potential.newtonKernel y * ‖y‖ ^ 2 = (4 * π)⁻¹ * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    rw [Potential.newtonKernel]
    field_simp

/-- The second term of the slow expansion is `(4π)⁻¹ ∫ ‖y‖ ∂ₜ²f(s, x − y) dy`. -/
theorem slowTerm_two (f : ℝ × E3 → ℝ) (s : ℝ) (x : E3) :
    slowTerm 2 f s x = (4 * π)⁻¹ * ∫ y, ‖y‖ * timeDeriv^[2] f (s, x - y) := by
  rw [slowTerm, ← integral_const_mul]
  congr 1
  funext y
  rw [← mul_assoc, newtonKernel_mul_norm_sq, mul_assoc]

/-- The first term of the slow expansion is `(4π)⁻¹ ∫ ∂ₜf(s, z) dz`, independent of the point. -/
theorem slowTerm_one (f : ℝ × E3 → ℝ) (s : ℝ) (x : E3) :
    slowTerm 1 f s x = (4 * π)⁻¹ * ∫ z, timeDeriv f (s, z) := by
  have h0 : ∀ᵐ y : E3, y ≠ 0 := by
    rw [ae_iff]
    simp
  have hae : (fun y : E3 => Potential.newtonKernel y * (‖y‖ ^ 1 * timeDeriv^[1] f (s, x - y)))
      =ᵐ[volume] fun y => (4 * π)⁻¹ * timeDeriv f (s, x - y) := by
    filter_upwards [h0] with y hy
    have : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    simp only [Potential.newtonKernel, pow_one, Function.iterate_one]
    field_simp
  rw [slowTerm, integral_congr_ae hae, integral_const_mul,
    integral_sub_left_eq_self (fun z => timeDeriv f (s, z)) volume x]

/-! ### Averages over a small ball -/

/-- **An average is close to the value**: for a nonnegative weight `η` of total mass one that
vanishes outside the ball of radius `ε`, and a function `g` continuous on the ball of radius `ε`
about `z₀` with `|g − c| ≤ θ` there, `|∫ η(x − z₀) g(x) dx − c| ≤ θ`. -/
theorem abs_integral_weight_mul_sub_le {η : E3 → ℝ} (hηc : Continuous η) (hη0 : ∀ z, 0 ≤ η z)
    (hη1 : ∫ z, η z = 1) {ε : ℝ} (hηs : ∀ z : E3, ε < ‖z‖ → η z = 0) {g : E3 → ℝ} {z₀ : E3}
    (hg : ContinuousOn g (closedBall z₀ ε)) {c θ : ℝ}
    (hgc : ∀ x ∈ closedBall z₀ ε, |g x - c| ≤ θ) :
    |(∫ x, η (x - z₀) * g x) - c| ≤ θ := by
  have hvan : ∀ x ∉ closedBall z₀ ε, η (x - z₀) = 0 := fun x hx =>
    hηs _ (by rw [mem_closedBall, dist_eq_norm] at hx; linarith)
  have hint : Integrable fun x => η (x - z₀) * (g x - c) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall z₀ ε) ?_ ?_
    · exact ((hηc.comp (continuous_id.sub continuous_const)).continuousOn.mul
        (hg.sub continuousOn_const)).integrableOn_compact (isCompact_closedBall _ _)
    · intro x hx
      simp [hvan x hx]
  have hint2 : Integrable fun x => η (x - z₀) * g x := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall z₀ ε) ?_ ?_
    · exact ((hηc.comp (continuous_id.sub continuous_const)).continuousOn.mul
        hg).integrableOn_compact (isCompact_closedBall _ _)
    · intro x hx
      simp [hvan x hx]
  have hηint : Integrable fun x => η (x - z₀) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall z₀ ε) ?_ ?_
    · exact (hηc.comp (continuous_id.sub continuous_const)).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)
    · exact fun x hx => hvan x hx
  have hmass : ∫ x, η (x - z₀) = 1 := by
    rw [integral_sub_right_eq_self (fun z => η z) z₀, hη1]
  have hsplit : (∫ x, η (x - z₀) * g x) - c = ∫ x, η (x - z₀) * (g x - c) := by
    have : ∫ x, η (x - z₀) * (g x - c) =
        (∫ x, η (x - z₀) * g x) - ∫ x, η (x - z₀) * c := by
      calc ∫ x, η (x - z₀) * (g x - c) = ∫ x, (η (x - z₀) * g x - η (x - z₀) * c) := by
            congr 1
            funext x
            ring
        _ = _ := integral_sub hint2 (hηint.mul_const c)
    rw [this, integral_mul_const, hmass, one_mul]
  rw [hsplit, ← Real.norm_eq_abs]
  have hbd : ∀ x, ‖η (x - z₀) * (g x - c)‖ ≤ η (x - z₀) * θ := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hη0 _)]
    by_cases hx : x ∈ closedBall z₀ ε
    · exact mul_le_mul_of_nonneg_left (hgc x hx) (hη0 _)
    · simp [hvan x hx]
  calc ‖∫ x, η (x - z₀) * (g x - c)‖ ≤ ∫ x, η (x - z₀) * θ :=
        norm_integral_le_of_norm_le (hηint.mul_const θ) (Eventually.of_forall hbd)
    _ = θ := by rw [integral_mul_const, hmass, one_mul]

/-- **A double average is close to the value**: for an even weight `η` as in
`abs_integral_weight_mul_sub_le` and a kernel `K` with `|K − K(r₂ − r₁)| ≤ θ` on the ball of
radius `2ε` about `r₂ − r₁`, the interaction `∫ η(x − r₂) ∫ K(y) η(x − y − r₁) dy dx` of the two
smeared points differs from `K(r₂ − r₁)` by at most `θ`. -/
theorem abs_integral_weight_mul_average_sub_le {η : E3 → ℝ} (hηc : Continuous η)
    (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∫ z, η z = 1) {ε : ℝ}
    (hηs : ∀ z : E3, ε < ‖z‖ → η z = 0) (hηe : ∀ z, η (-z) = η z) {K : E3 → ℝ} {r₁ r₂ : E3}
    (hK : ContinuousOn K (closedBall (r₂ - r₁) (2 * ε))) {θ : ℝ}
    (hKθ : ∀ z ∈ closedBall (r₂ - r₁) (2 * ε), |K z - K (r₂ - r₁)| ≤ θ)
    (hA : ContinuousOn (fun x => ∫ y, K y * η (x - y - r₁)) (closedBall r₂ ε)) :
    |(∫ x, η (x - r₂) * ∫ y, K y * η (x - y - r₁)) - K (r₂ - r₁)| ≤ θ := by
  refine abs_integral_weight_mul_sub_le hηc hη0 hη1 hηs hA fun x hx => ?_
  have hsub : closedBall (x - r₁) ε ⊆ closedBall (r₂ - r₁) (2 * ε) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz hx ⊢
    calc ‖z - (r₂ - r₁)‖ = ‖(z - (x - r₁)) + (x - r₂)‖ := by congr 1; abel
      _ ≤ ‖z - (x - r₁)‖ + ‖x - r₂‖ := norm_add_le _ _
      _ ≤ 2 * ε := by linarith
  have h := abs_integral_weight_mul_sub_le hηc hη0 hη1 hηs (hK.mono hsub)
    (fun z hz => hKθ z (hsub hz))
  have he : (∫ y, K y * η (x - y - r₁)) = ∫ y, η (y - (x - r₁)) * K y := by
    congr 1
    funext y
    rw [mul_comm, ← hηe (y - (x - r₁))]
    congr 2
    abel
  rw [he]
  exact h

/-- **The point limit of the interaction of two smeared points**: for a family of even weights
`η_ε` of mass one supported in the balls of radius `ε`, and a kernel `K` continuous on a ball
about `r₂ − r₁`,

  `∫ η_ε(x − r₂) ∫ K(y) η_ε(x − y − r₁) dy dx → K(r₂ − r₁)`  as `ε → 0⁺`. -/
theorem tendsto_integral_weight_mul_average {η : ℝ → E3 → ℝ} (hηc : ∀ ε, Continuous (η ε))
    (hη0 : ∀ ε z, 0 ≤ η ε z) (hη1 : ∀ ε, 0 < ε → ∫ z, η ε z = 1)
    (hηs : ∀ ε, 0 < ε → ∀ z : E3, ε < ‖z‖ → η ε z = 0) (hηe : ∀ ε z, η ε (-z) = η ε z)
    {K : E3 → ℝ} {r₁ r₂ : E3} {δ : ℝ} (hδ : 0 < δ) (hK : ContinuousOn K (closedBall (r₂ - r₁) δ))
    (hA : ∀ ε, 0 < ε → Continuous fun x => ∫ y, K y * η ε (x - y - r₁)) :
    Tendsto (fun ε => ∫ x, η ε (x - r₂) * ∫ y, K y * η ε (x - y - r₁)) (𝓝[>] 0)
      (𝓝 (K (r₂ - r₁))) := by
  rw [Metric.tendsto_nhds]
  intro θ hθ
  have hKa : ContinuousAt K (r₂ - r₁) := hK.continuousAt (closedBall_mem_nhds _ hδ)
  obtain ⟨ρ, hρ, hKρ⟩ := Metric.continuousAt_iff.mp hKa (θ / 2) (by positivity)
  have hmin : 0 < min δ ρ / 4 := by positivity
  filter_upwards [Ioo_mem_nhdsGT hmin] with ε hε
  have h2ε : 2 * ε < min δ ρ := by linarith [hε.2]
  have hball : closedBall (r₂ - r₁) (2 * ε) ⊆ closedBall (r₂ - r₁) δ :=
    closedBall_subset_closedBall (by linarith [min_le_left δ ρ])
  have h := abs_integral_weight_mul_average_sub_le (hηc ε) (hη0 ε) (hη1 ε hε.1)
    (hηs ε hε.1) (hηe ε) (hK.mono hball) (θ := θ / 2)
    (fun z hz => by
      have hz' : dist z (r₂ - r₁) < ρ := by
        rw [mem_closedBall] at hz
        linarith [min_le_right δ ρ]
      exact (hKρ hz').le)
    (hA ε hε.1).continuousOn
  rw [Real.dist_eq]
  linarith

/-! ### Slow integrals against a kernel -/

/-- The spatial derivatives of a slow integral against a kernel:
`∂ᵢ ∫ K(y) f(κt, x − y) dy = ∫ K(y) ∂ᵢf(κt, x − y) dy`. -/
theorem spaceDeriv_kernelIntegral_slow {K : E3 → ℝ} (hK : LocallyIntegrable K)
    {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) {a : ℝ} (hs : SpatialSupport a f) (κ : ℝ)
    (i : Fin 3) :
    spaceDeriv i (kernelIntegral K (slow κ f)) = kernelIntegral K (slow κ (spaceDeriv i f)) := by
  rw [spaceDeriv_kernelIntegral hK (contDiff_slow hf κ) ((hs.slow κ).kernelSupport K),
    spaceDeriv_slow (hf.differentiable (by norm_num))]

/-- The time derivative of a slow integral against a kernel:
`∂ₜ ∫ K(y) f(κt, x − y) dy = κ ∫ K(y) ∂ₛf(κt, x − y) dy`. -/
theorem timeDeriv_kernelIntegral_slow {K : E3 → ℝ} (hK : LocallyIntegrable K)
    {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) {a : ℝ} (hs : SpatialSupport a f) (κ : ℝ) :
    timeDeriv (kernelIntegral K (slow κ f)) =
      fun p => κ * kernelIntegral K (slow κ (timeDeriv f)) p := by
  rw [timeDeriv_kernelIntegral hK (contDiff_slow hf κ) ((hs.slow κ).kernelSupport K),
    timeDeriv_slow (hf.differentiable (by norm_num))]
  funext p
  exact kernelIntegral_const_mul K κ _ p

/-- **The leading slow term**: for a `C¹` source supported in the cylinder `‖x‖ ≤ a` with
`|∂ₜf| ≤ M`, the retarded integral of the slow source is its instantaneous Newton potential up to
`M (ρ + a)³ κ/3` at `‖x‖ ≤ ρ`. -/
theorem abs_retardedIntegral_slow_sub_newton_le {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f)
    {a M : ℝ} (ha : 0 ≤ a) (hs : SpatialSupport a f) (hM : ∀ p, |timeDeriv f p| ≤ M)
    {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {ρ : ℝ} (hx : ‖x‖ ≤ ρ) :
    |retardedIntegral (slow κ f) (t, x) - kernelIntegral Potential.newtonKernel (slow κ f) (t, x)|
      ≤ M * (ρ + a) ^ 3 / 3 * κ := by
  have H := retardedIntegral_slow_expansion (n := 0) (by simpa using hf) ha hs hM hκ t hx
  have hs0 : ∑ k ∈ Finset.range (0 + 1), (-κ) ^ k / k ! * slowTerm k f (κ * t) x =
      kernelIntegral Potential.newtonKernel (slow κ f) (t, x) := by
    simp [slowTerm, kernelIntegral, slow, smul_eq_mul]
  rw [hs0] at H
  convert H using 1
  norm_num

end ProjectAinos.SmoothGeometry.Wave
