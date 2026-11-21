/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Wave.SlowSource
import ProjectAinos.Electrodynamics.DarwinLagrangian
import ProjectAinos.Electrodynamics.DarwinPointCharge

/-! Public consumers of the Lagrangian to terms of second order (Landau–Lifshitz §65): the slow
expansion of the retarded integral with an explicit remainder, the Darwin gauge and potentials of
a slow conserved source, the Euler–Lagrange expression of a rigid charge in given potentials as
the Lorentz force, the force of the retarded field of a slow source on a rigid charge to order
`κ²`, the point limit of the smeared interaction, the Darwin Lagrangian (65.7), and for point
charges the Liénard–Wiechert field to second order and the force as the Euler–Lagrange expression
of (65.7) to order `κ²`. Default elaborator options are intentional: these checks must not rely
on the implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section


section SlowSource

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff Nat

namespace ProjectAinos.SmoothGeometry.Wave

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {g : ℕ → ℝ → ℝ} {M : ℝ} (n : ℕ) (hg : ∀ k < n, ∀ s, HasDerivAt (g k) (g (k + 1) s) s)
    {h : ℝ} (hh : 0 ≤ h) (hM : ∀ s ∈ Icc 0 h, |g n s| ≤ M) :
    |g 0 h - ∑ k ∈ Finset.range n, h ^ k / k ! * g k 0| ≤ M * h ^ n / n ! :=
  abs_sub_taylor_le n hg hh hM

example {g : ℕ → ℝ → ℝ} {M : ℝ} (n : ℕ) (hg : ∀ k < n, ∀ s, HasDerivAt (g k) (g (k + 1) s) s)
    (s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (hM : ∀ s, |g n s| ≤ M) :
    |g 0 (s₀ - h) - ∑ k ∈ Finset.range n, (-h) ^ k / k ! * g k s₀| ≤ M * h ^ n / n ! :=
  abs_sub_taylor_sub_le n hg s₀ hh hM

example {F : ℝ × E3 → ℝ} {s : ℝ} {z : E3} (hF : DifferentiableAt ℝ F (s, z)) :
    HasDerivAt (fun s' => F (s', z)) (timeDeriv F (s, z)) s :=
  hasDerivAt_timeSlice_of_differentiableAt hF

example {N : ℕ} {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ N f) {m k : ℕ} (hk : m + k ≤ N) :
    ContDiff ℝ m (timeDeriv^[k] f) :=
  contDiff_iterate_timeDeriv hf hk

example {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) :
    timeDeriv (fun q => f q + g q) p = timeDeriv f p + timeDeriv g p :=
  timeDeriv_fun_add hf hg

example {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) :
    timeDeriv (fun q => f q - g q) p = timeDeriv f p - timeDeriv g p :=
  timeDeriv_fun_sub hf hg

example {f : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p) (c : ℝ) :
    timeDeriv (fun q => c * f q) p = c * timeDeriv f p :=
  timeDeriv_const_mul hf c

example {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    spaceDeriv i (fun q => f q + g q) p = spaceDeriv i f p + spaceDeriv i g p :=
  spaceDeriv_fun_add hf hg i

example {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    spaceDeriv i (fun q => f q - g q) p = spaceDeriv i f p - spaceDeriv i g p :=
  spaceDeriv_fun_sub hf hg i

example {f : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 3) :
    spaceDeriv i (fun q => c * f q) p = c * spaceDeriv i f p :=
  spaceDeriv_const_mul hf c i

example {ι : Type*} (s : Finset ι) {f : ι → ℝ × E3 → ℝ} {p : ℝ × E3}
    (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) p) (i : Fin 3) :
    spaceDeriv i (fun q => ∑ k ∈ s, f k q) p = ∑ k ∈ s, spaceDeriv i (f k) p :=
  spaceDeriv_fun_sum s hf i

example {ι : Type*} (s : Finset ι) {f : ι → ℝ × E3 → ℝ} {p : ℝ × E3}
    (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) p) :
    timeDeriv (fun q => ∑ k ∈ s, f k q) p = ∑ k ∈ s, timeDeriv (f k) p :=
  timeDeriv_fun_sum s hf

example {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hf : ContDiffAt ℝ 2 f q) (i j : Fin 3) :
    spaceDeriv i (spaceDeriv j f) q = spaceDeriv j (spaceDeriv i f) q :=
  spaceDeriv_spaceDeriv_comm hf i j

example {c c' : ℝ → ℝ} (hc : ∀ s, HasDerivAt c (c' s) s) {G : E3 → ℝ} (hG : Differentiable ℝ G) :
    timeDeriv (fun p : ℝ × E3 => c p.1 * G p.2) = fun p => c' p.1 * G p.2 :=
  timeDeriv_mul_slice hc hG

example {c : ℝ → ℝ} (hc : Differentiable ℝ c) {G : E3 → ℝ} (hG : Differentiable ℝ G) (i : Fin 3) :
    spaceDeriv i (fun p : ℝ × E3 => c p.1 * G p.2) =
      fun p => c p.1 * fderiv ℝ G p.2 (EuclideanSpace.single i 1) :=
  spaceDeriv_mul_slice hc hG i

example :
    timeDeriv (fun _ : ℝ × E3 => (0 : ℝ)) = fun _ => 0 :=
  timeDeriv_zero

example (i : Fin 3) :
    spaceDeriv i (fun _ : ℝ × E3 => (0 : ℝ)) = fun _ => 0 :=
  spaceDeriv_zero i

section Support

variable {G : Type*} [NormedAddCommGroup G]

example (a : ℝ) (f : ℝ × E3 → G) :
    Prop :=
  SpatialSupport a f

example {a : ℝ} {f : ℝ × E3 → G} (hf : SpatialSupport a f) {p : ℝ × E3} (hp : a < ‖p.2‖) :
    f =ᶠ[𝓝 p] fun _ => 0 :=
  SpatialSupport.eventuallyEq_zero hf hp

example {a : ℝ} {f : ℝ × E3 → G} (hf : SpatialSupport a f) :
    tsupport f ⊆ {p | ‖p.2‖ ≤ a} :=
  SpatialSupport.tsupport_subset hf

example {a : ℝ} {f : ℝ × E3 → G} (hf : SpatialSupport a f) :
    SubluminalSupport a 0 f :=
  SpatialSupport.subluminalSupport hf

example {G' : Type*} [NormedAddCommGroup G'] {a : ℝ} {f : ℝ × E3 → G} {g : ℝ × E3 → G'}
    (hf : SpatialSupport a f) (hg : ∀ p, f p = 0 → g p = 0) :
    SpatialSupport a g :=
  SpatialSupport.mono hf hg

example (κ : ℝ) (f : ℝ × E3 → G) (p : ℝ × E3) :
    G :=
  slow κ f p

example (κ : ℝ) :
    ℝ × E3 →L[ℝ] ℝ × E3 :=
  slowMap κ

example (κ : ℝ) (f : ℝ × E3 → G) :
    slow κ f = f ∘ slowMap κ :=
  slow_eq_comp κ f

example {a : ℝ} {f : ℝ × E3 → G} (hf : SpatialSupport a f) (κ : ℝ) :
    SpatialSupport a (slow κ f) :=
  SpatialSupport.slow hf κ

variable [NormedSpace ℝ G]

example {a : ℝ} {f : ℝ × E3 → G} (hf : SpatialSupport a f) :
    SpatialSupport a (fderiv ℝ f) :=
  SpatialSupport.fderiv hf

example {n : ℕ∞ω} {f : ℝ × E3 → G} (hf : ContDiff ℝ n f) (κ : ℝ) :
    ContDiff ℝ n (slow κ f) :=
  contDiff_slow hf κ

example {f : ℝ × E3 → G} (hf : Differentiable ℝ f) (κ : ℝ) (p v : ℝ × E3) :
    _root_.fderiv ℝ (slow κ f) p v = _root_.fderiv ℝ f (κ * p.1, p.2) (κ * v.1, v.2) :=
  fderiv_slow hf κ p v

end Support

example {a : ℝ} {f : ℝ × E3 → ℝ} (hf : SpatialSupport a f) :
    SpatialSupport a (timeDeriv f) :=
  SpatialSupport.timeDeriv hf

example {a : ℝ} {f : ℝ × E3 → ℝ} (hf : SpatialSupport a f) (i : Fin 3) :
    SpatialSupport a (spaceDeriv i f) :=
  SpatialSupport.spaceDeriv hf i

example {a : ℝ} {f : ℝ × E3 → ℝ} (hf : SpatialSupport a f) (k : ℕ) :
    SpatialSupport a (Wave.timeDeriv^[k] f) :=
  SpatialSupport.iterate_timeDeriv hf k

example {f : ℝ × E3 → ℝ} (hf : Differentiable ℝ f) (κ : ℝ) :
    timeDeriv (slow κ f) = fun p => κ * slow κ (timeDeriv f) p :=
  timeDeriv_slow hf κ

example {f : ℝ × E3 → ℝ} (hf : Differentiable ℝ f) (κ : ℝ) (i : Fin 3) :
    spaceDeriv i (slow κ f) = slow κ (spaceDeriv i f) :=
  spaceDeriv_slow hf κ i

example (c : ℝ) (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    retardedIntegral (fun q => c * f q) p = c * retardedIntegral f p :=
  retardedIntegral_const_mul c f p

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) {a : ℝ} (hs : SpatialSupport a f) (κ : ℝ) :
    timeDeriv (retardedIntegral (slow κ f)) =
      fun p => κ * retardedIntegral (slow κ (timeDeriv f)) p :=
  timeDeriv_retardedIntegral_slow hf hs κ

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) {a : ℝ} (hs : SpatialSupport a f) (κ : ℝ)
    (i : Fin 3) :
    spaceDeriv i (retardedIntegral (slow κ f)) = retardedIntegral (slow κ (spaceDeriv i f)) :=
  spaceDeriv_retardedIntegral_slow hf hs κ i

example (k : ℕ) (f : ℝ × E3 → ℝ) (s : ℝ) (x : E3) :
    ℝ :=
  slowTerm k f s x

example (f : ℝ × E3 → ℝ) (s : ℝ) (x : E3) :
    slowTerm 0 f s x = Potential.newtonPotential (fun z => f (s, z)) x :=
  slowTerm_zero f s x

example {g : E3 → ℝ} (hg : Continuous g) {r : ℝ} (hr : ∀ y : E3, r < ‖y‖ → g y = 0) :
    Integrable fun y => Potential.newtonKernel y * g y :=
  integrable_newtonKernel_mul_of_vanish hg hr

example {f : ℝ × E3 → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f) {a M : ℝ} (ha : 0 ≤ a)
    (hs : SpatialSupport a f) (hM : ∀ p, |timeDeriv^[n + 1] f p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ)
    {x : E3} {ρ : ℝ} (hx : ‖x‖ ≤ ρ) :
    |retardedIntegral (slow κ f) (t, x) -
        ∑ k ∈ Finset.range (n + 1), (-κ) ^ k / k ! * slowTerm k f (κ * t) x| ≤
      M * (ρ + a) ^ (n + 3) / (3 * (n + 1)!) * κ ^ (n + 1) :=
  retardedIntegral_slow_expansion hf ha hs hM hκ t hx

section KernelIntegral

variable {G : Type*} [NormedAddCommGroup G]

example (K : E3 → ℝ) (F : ℝ × E3 → G) :
    Prop :=
  KernelSupport K F

example {G' : Type*} [NormedAddCommGroup G'] {K : E3 → ℝ} {F : ℝ × E3 → G} {F' : ℝ × E3 → G'}
    (h : KernelSupport K F) (hF : tsupport F' ⊆ tsupport F) :
    KernelSupport K F' :=
  KernelSupport.mono h hF

example {a : ℝ} {F : ℝ × E3 → G} (hF : SpatialSupport a F) (K : E3 → ℝ) :
    KernelSupport K F :=
  SpatialSupport.kernelSupport hF K

example {K : E3 → ℝ} {b : ℝ} (hK : ∀ y : E3, b < ‖y‖ → K y = 0) (F : ℝ × E3 → G) :
    KernelSupport K F :=
  kernelSupport_of_kernel hK F

example {K : E3 → ℝ} {F : ℝ × E3 → G} {L : ℝ} {p₀ : ℝ × E3}
    (hL : ∀ p ∈ ball p₀ 1, ∀ y : E3, L < ‖y‖ → K y = 0 ∨ p - (0, y) ∉ tsupport F) [Module ℝ G]
    {p : ℝ × E3} (hp : p ∈ ball p₀ 1) {y : E3} (hy : L < ‖y‖) :
    K y • F (p - (0, y)) = 0 :=
  KernelSupport.smul_eq_zero hL hp hy

variable [NormedSpace ℝ G]

example {K : E3 → ℝ} {F : ℝ × E3 → G} (h : KernelSupport K F) :
    KernelSupport K (_root_.fderiv ℝ F) :=
  KernelSupport.fderiv h

example (K : E3 → ℝ) (F : ℝ × E3 → G) (p : ℝ × E3) :
    G :=
  kernelIntegral K F p

example {K : E3 → ℝ} {F : ℝ × E3 → G} (hs : KernelSupport K F) (hK : LocallyIntegrable K)
    (hF : Continuous F) (p : ℝ × E3) :
    Integrable fun y => K y • F (p - (0, y)) :=
  KernelSupport.integrable hs hK hF p

example {K : E3 → ℝ} {F : ℝ × E3 → G} (hs : KernelSupport K F) (hF : Continuous F) (p₀ : ℝ × E3) :
    ∃ C L, ∀ p ∈ ball p₀ 1, ∀ y : E3,
      ‖K y • F (p - (0, y))‖ ≤ (closedBall (0 : E3) L).indicator (fun y => C * ‖K y‖) y :=
  KernelSupport.exists_bound hs hF p₀

example {K : E3 → ℝ} (hK : LocallyIntegrable K) (C L : ℝ) :
    Integrable ((closedBall (0 : E3) L).indicator fun y => C * ‖K y‖) :=
  integrable_indicator_mul_norm hK C L

example {K : E3 → ℝ} {F : ℝ × E3 → G} (hK : LocallyIntegrable K) (hc : Continuous F)
    (hs : KernelSupport K F) :
    Continuous (kernelIntegral K F) :=
  continuous_kernelIntegral hK hc hs

example [CompleteSpace G] {K : E3 → ℝ} {F : ℝ × E3 → G} (hK : LocallyIntegrable K)
    (hc : ContDiff ℝ 1 F) (hs : KernelSupport K F) (p₀ : ℝ × E3) :
    HasFDerivAt (kernelIntegral K F) (kernelIntegral K (_root_.fderiv ℝ F) p₀) p₀ :=
  hasFDerivAt_kernelIntegral hK hc hs p₀

example [CompleteSpace G] {K : E3 → ℝ} {F : ℝ × E3 → G} (hK : LocallyIntegrable K)
    (hc : ContDiff ℝ 1 F) (hs : KernelSupport K F) :
    _root_.fderiv ℝ (kernelIntegral K F) = kernelIntegral K (_root_.fderiv ℝ F) :=
  fderiv_kernelIntegral hK hc hs

example [CompleteSpace G] {K : E3 → ℝ} {F : ℝ × E3 → ℝ × E3 →L[ℝ] G} (hK : LocallyIntegrable K)
    (hc : Continuous F) (hs : KernelSupport K F) (p v : ℝ × E3) :
    kernelIntegral K F p v = kernelIntegral K (fun q => F q v) p :=
  kernelIntegral_apply_clm hK hc hs p v

example [CompleteSpace G] {K : E3 → ℝ} (hK : LocallyIntegrable K) (n : ℕ) {F : ℝ × E3 → G}
    (hc : ContDiff ℝ n F) (hs : KernelSupport K F) :
    ContDiff ℝ n (kernelIntegral K F) :=
  contDiff_kernelIntegral_nat hK n hc hs

example [CompleteSpace G] {K : E3 → ℝ} (hK : LocallyIntegrable K) {n : ℕ∞} {F : ℝ × E3 → G}
    (hc : ContDiff ℝ n F) (hs : KernelSupport K F) :
    ContDiff ℝ n (kernelIntegral K F) :=
  contDiff_kernelIntegral hK hc hs

end KernelIntegral

example {K : E3 → ℝ} {F : ℝ × E3 → ℝ} (hK : LocallyIntegrable K) (hc : ContDiff ℝ 1 F)
    (hs : KernelSupport K F) :
    timeDeriv (kernelIntegral K F) = kernelIntegral K (timeDeriv F) :=
  timeDeriv_kernelIntegral hK hc hs

example {K : E3 → ℝ} {F : ℝ × E3 → ℝ} (hK : LocallyIntegrable K) (hc : ContDiff ℝ 1 F)
    (hs : KernelSupport K F) (i : Fin 3) :
    spaceDeriv i (kernelIntegral K F) = kernelIntegral K (spaceDeriv i F) :=
  spaceDeriv_kernelIntegral hK hc hs i

example {K : E3 → ℝ} {F : ℝ × E3 → ℝ} (h : KernelSupport K F) :
    KernelSupport K (Wave.timeDeriv F) :=
  KernelSupport.timeDeriv h

example {K : E3 → ℝ} {F : ℝ × E3 → ℝ} (h : KernelSupport K F) (i : Fin 3) :
    KernelSupport K (Wave.spaceDeriv i F) :=
  KernelSupport.spaceDeriv h i

example (K : E3 → ℝ) (F : ℝ × E3 → ℝ) (t : ℝ) (x : E3) :
    kernelIntegral K F (t, x) = ∫ z, K (x - z) * F (t, z) :=
  kernelIntegral_eq_integral_sub K F t x

example (K : E3 → ℝ) (c : ℝ) (F : ℝ × E3 → ℝ) (p : ℝ × E3) :
    kernelIntegral K (fun q => c * F q) p = c * kernelIntegral K F p :=
  kernelIntegral_const_mul K c F p

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (timeDeriv f) :=
  contDiff_infty_timeDeriv hf

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (spaceDeriv i f) :=
  contDiff_infty_spaceDeriv hf i

example {K : E3 → ℝ} (hK : AEStronglyMeasurable K) {C : ℝ}
    (hKC : ∀ y, |K y| ≤ C * Potential.newtonKernel y) {g : E3 → ℝ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (x : E3) :
    Integrable fun z => K (x - z) * g z :=
  integrable_kernel_sub_mul hK hKC hg hcg x

example (k : ℕ) (f : ℝ × E3 → ℝ) (s : ℝ) (x : E3) :
    slowTerm k f s x =
      kernelIntegral (fun y => Potential.newtonKernel y * ‖y‖ ^ k) (timeDeriv^[k] f) (s, x) :=
  slowTerm_eq_kernelIntegral k f s x

example (x : E3) {δ : ℝ} (hδ : δ ≠ 0) (z : E3) :
    HasFDerivAt (fun z' : E3 => √(‖x - z'‖ ^ 2 + δ ^ 2))
      ((1 / (2 * √(‖x - z‖ ^ 2 + δ ^ 2))) •
        ((2 • innerSL ℝ (x - z)).comp (-ContinuousLinearMap.id ℝ E3))) z :=
  hasFDerivAt_regularDistance x hδ z

example {F : E3 → ℝ} (hF : ContDiff ℝ 2 F) (hc : HasCompactSupport F) (x v w : E3) {δ : ℝ}
    (hδ : δ ≠ 0) :
    ∫ z, √(‖x - z‖ ^ 2 + δ ^ 2) * fderiv ℝ (fun z' => fderiv ℝ F z' w) z v =
      ∫ z, (inner ℝ v w / √(‖x - z‖ ^ 2 + δ ^ 2) -
        inner ℝ v (x - z) * inner ℝ w (x - z) / √(‖x - z‖ ^ 2 + δ ^ 2) ^ 3) * F z :=
  integral_regularDistance_mul_fderiv_fderiv hF hc x v w hδ

example {F : E3 → ℝ} (hF : ContDiff ℝ 2 F) (hc : HasCompactSupport F) (x v w : E3) :
    ∫ z, ‖x - z‖ * fderiv ℝ (fun z' => fderiv ℝ F z' w) z v =
      ∫ z, (inner ℝ v w / ‖x - z‖ -
        inner ℝ v (x - z) * inner ℝ w (x - z) / ‖x - z‖ ^ 3) * F z :=
  integral_norm_sub_mul_fderiv_fderiv hF hc x v w

example {g : ℝ × E3 → ℝ} {s : ℝ} {z : E3} (hg : DifferentiableAt ℝ g (s, z)) (i : Fin 3) :
    spaceDeriv i g (s, z) = fderiv ℝ (fun z' => g (s, z')) z (EuclideanSpace.single i 1) :=
  spaceDeriv_eq_fderiv_slice hg i

example {a : ℝ} {g : ℝ × E3 → ℝ} (hs : SpatialSupport a g) (s : ℝ) :
    HasCompactSupport fun z : E3 => g (s, z) :=
  SpatialSupport.hasCompactSupport_slice hs s

example {g : ℝ × E3 → ℝ} (hg : ContDiff ℝ 1 g) {a : ℝ} (hs : SpatialSupport a g) (s : ℝ)
    (i : Fin 3) :
    ∫ z, spaceDeriv i g (s, z) = 0 :=
  integral_spaceDeriv_eq_zero hg hs s i

example {g : ℝ × E3 → ℝ} (hg : ContDiff ℝ 2 g) {a : ℝ} (hs : SpatialSupport a g) (s : ℝ) (x : E3)
    (i k : Fin 3) :
    ∫ z, ‖x - z‖ * spaceDeriv i (spaceDeriv k g) (s, z) =
      ∫ z, ((if i = k then 1 else 0) / ‖x - z‖ - (x - z) i * (x - z) k / ‖x - z‖ ^ 3) *
        g (s, z) :=
  integral_norm_sub_mul_spaceDeriv_spaceDeriv hg hs s x i k

example {N : ℕ} {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ N f) (i : Fin 3) {k : ℕ} (hk : k + 1 ≤ N) :
    timeDeriv^[k] (spaceDeriv i f) = spaceDeriv i (timeDeriv^[k] f) :=
  iterate_timeDeriv_spaceDeriv hf i hk

example (y : E3) :
    Potential.newtonKernel y * ‖y‖ ^ 2 = (4 * π)⁻¹ * ‖y‖ :=
  newtonKernel_mul_norm_sq y

example (f : ℝ × E3 → ℝ) (s : ℝ) (x : E3) :
    slowTerm 2 f s x = (4 * π)⁻¹ * ∫ y, ‖y‖ * timeDeriv^[2] f (s, x - y) :=
  slowTerm_two f s x

example (f : ℝ × E3 → ℝ) (s : ℝ) (x : E3) :
    slowTerm 1 f s x = (4 * π)⁻¹ * ∫ z, timeDeriv f (s, z) :=
  slowTerm_one f s x

example {η : E3 → ℝ} (hηc : Continuous η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∫ z, η z = 1) {ε : ℝ}
    (hηs : ∀ z : E3, ε < ‖z‖ → η z = 0) {g : E3 → ℝ} {z₀ : E3}
    (hg : ContinuousOn g (closedBall z₀ ε)) {c θ : ℝ} (hgc : ∀ x ∈ closedBall z₀ ε, |g x - c| ≤ θ) :
    |(∫ x, η (x - z₀) * g x) - c| ≤ θ :=
  abs_integral_weight_mul_sub_le hηc hη0 hη1 hηs hg hgc

example {η : E3 → ℝ} (hηc : Continuous η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∫ z, η z = 1) {ε : ℝ}
    (hηs : ∀ z : E3, ε < ‖z‖ → η z = 0) (hηe : ∀ z, η (-z) = η z) {K : E3 → ℝ} {r₁ r₂ : E3}
    (hK : ContinuousOn K (closedBall (r₂ - r₁) (2 * ε))) {θ : ℝ}
    (hKθ : ∀ z ∈ closedBall (r₂ - r₁) (2 * ε), |K z - K (r₂ - r₁)| ≤ θ)
    (hA : ContinuousOn (fun x => ∫ y, K y * η (x - y - r₁)) (closedBall r₂ ε)) :
    |(∫ x, η (x - r₂) * ∫ y, K y * η (x - y - r₁)) - K (r₂ - r₁)| ≤ θ :=
  abs_integral_weight_mul_average_sub_le hηc hη0 hη1 hηs hηe hK hKθ hA

example {η : ℝ → E3 → ℝ} (hηc : ∀ ε, Continuous (η ε)) (hη0 : ∀ ε z, 0 ≤ η ε z)
    (hη1 : ∀ ε, 0 < ε → ∫ z, η ε z = 1) (hηs : ∀ ε, 0 < ε → ∀ z : E3, ε < ‖z‖ → η ε z = 0)
    (hηe : ∀ ε z, η ε (-z) = η ε z) {K : E3 → ℝ} {r₁ r₂ : E3} {δ : ℝ} (hδ : 0 < δ)
    (hK : ContinuousOn K (closedBall (r₂ - r₁) δ))
    (hA : ∀ ε, 0 < ε → Continuous fun x => ∫ y, K y * η ε (x - y - r₁)) :
    Tendsto (fun ε => ∫ x, η ε (x - r₂) * ∫ y, K y * η ε (x - y - r₁)) (𝓝[>] 0)
      (𝓝 (K (r₂ - r₁))) :=
  tendsto_integral_weight_mul_average hηc hη0 hη1 hηs hηe hδ hK hA

example {K : E3 → ℝ} (hK : LocallyIntegrable K) {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) {a : ℝ}
    (hs : SpatialSupport a f) (κ : ℝ) (i : Fin 3) :
    spaceDeriv i (kernelIntegral K (slow κ f)) = kernelIntegral K (slow κ (spaceDeriv i f)) :=
  spaceDeriv_kernelIntegral_slow hK hf hs κ i

example {K : E3 → ℝ} (hK : LocallyIntegrable K) {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) {a : ℝ}
    (hs : SpatialSupport a f) (κ : ℝ) :
    timeDeriv (kernelIntegral K (slow κ f)) =
      fun p => κ * kernelIntegral K (slow κ (timeDeriv f)) p :=
  timeDeriv_kernelIntegral_slow hK hf hs κ

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) {a M : ℝ} (ha : 0 ≤ a) (hs : SpatialSupport a f)
    (hM : ∀ p, |timeDeriv f p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {ρ : ℝ} (hx : ‖x‖ ≤ ρ) :
    |retardedIntegral (slow κ f) (t, x) - kernelIntegral Potential.newtonKernel (slow κ f) (t, x)|
      ≤ M * (ρ + a) ^ 3 / 3 * κ :=
  abs_retardedIntegral_slow_sub_newton_le hf ha hs hM hκ t hx

end ProjectAinos.SmoothGeometry.Wave

end SlowSource

section Darwin

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Wave SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (φ : ℝ × E3 → ℝ) (A : Fin 3 → ℝ × E3 → ℝ) (i : Fin 3) (p : ℝ × E3) :
    ℝ :=
  electricOf φ A i p

example (A : Fin 3 → ℝ × E3 → ℝ) (p : ℝ × E3) :
    Fin 3 → ℝ :=
  magneticOf A p

example (φ : ℝ × E3 → ℝ) (A : Fin 3 → ℝ × E3 → ℝ) (v : E3) (i : Fin 3) (p : ℝ × E3) :
    ℝ :=
  lorentzDensity φ A v i p

example (A : Fin 3 → ℝ × E3 → ℝ) (v : E3) (p : ℝ × E3) (i : Fin 3) :
    crossProduct (WithLp.ofLp v) (magneticOf A p) i =
      ∑ j, v j * (spaceDeriv i (A j) p - spaceDeriv j (A i) p) :=
  crossProduct_magneticOf A v p i

example {φ : ℝ × E3 → ℝ} {A : Fin 3 → ℝ × E3 → ℝ} {χ : ℝ × E3 → ℝ} (hφ : Differentiable ℝ φ)
    (hA : ∀ k, Differentiable ℝ (A k)) (hχ : ContDiff ℝ 2 χ) (i : Fin 3) (p : ℝ × E3) :
    electricOf (fun q => φ q - timeDeriv χ q) (fun k q => A k q + spaceDeriv k χ q) i p =
      electricOf φ A i p :=
  electricOf_gauge hφ hA hχ i p

example {A : Fin 3 → ℝ × E3 → ℝ} {χ : ℝ × E3 → ℝ} (hA : ∀ k, Differentiable ℝ (A k))
    (hχ : ContDiff ℝ 2 χ) (p : ℝ × E3) :
    magneticOf (fun k q => A k q + spaceDeriv k χ q) p = magneticOf A p :=
  magneticOf_gauge hA hχ p

example (ρ₀ : E3 → ℝ) (g : ℝ × E3 → ℝ) (t : ℝ) (r : E3) :
    ℝ :=
  smear ρ₀ g t r

example (ρ₀ : E3 → ℝ) (g : ℝ × E3 → ℝ) (t : ℝ) (r : E3) :
    smear ρ₀ g t r = kernelIntegral (fun y => ρ₀ (-y)) g (t, r) :=
  smear_eq_kernelIntegral ρ₀ g t r

example {ρ₀ : E3 → ℝ} (hc : HasCompactSupport ρ₀) (g : ℝ × E3 → ℝ) :
    KernelSupport (fun y => ρ₀ (-y)) g :=
  kernelSupport_reflect hc g

example {ρ₀ : E3 → ℝ} (hρ : Continuous ρ₀) (hc : HasCompactSupport ρ₀) {g : ℝ × E3 → ℝ}
    (hg : Continuous g) (t : ℝ) (r : E3) :
    Integrable fun x => ρ₀ (x - r) * g (t, x) :=
  integrable_smear hρ hc hg t r

example (ρ₀ : E3 → ℝ) (φ : ℝ × E3 → ℝ) (A : Fin 3 → ℝ × E3 → ℝ) :
    Mechanics.Lagrangian E3 :=
  rigidLagrangian ρ₀ φ A

example (ℓ : ℝ × E3 →L[ℝ] ℝ) (w : E3) :
    ℓ (1, w) = ℓ (1, 0) + ∑ k, w k * ℓ (0, EuclideanSpace.single k 1) :=
  clm_apply_one_vec ℓ w

example {ρ₀ : E3 → ℝ} (hρ : Continuous ρ₀) (hc : HasCompactSupport ρ₀) {φ : ℝ × E3 → ℝ}
    {A : Fin 3 → ℝ × E3 → ℝ} (hφ : ContDiff ℝ 1 φ) (hA : ∀ k, ContDiff ℝ 1 (A k)) {r : ℝ → E3}
    {t : ℝ} (hr : DifferentiableAt ℝ r t) (i : Fin 3) :
    Mechanics.eulerLagrange (rigidLagrangian ρ₀ φ A) r t (EuclideanSpace.single i 1) =
      ∫ x, ρ₀ (x - r t) * lorentzDensity φ A (deriv r t) i (t, x) :=
  eulerLagrange_rigidLagrangian hρ hc hφ hA hr i

example (κ : ℝ) (ρ : ℝ × E3 → ℝ) :
    ℝ × E3 → ℝ :=
  slowScalar κ ρ

example (κ : ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (i : Fin 3) :
    ℝ × E3 → ℝ :=
  slowVector κ j i

example (κ : ℝ) (ρ : ℝ × E3 → ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (v : Spacetime) :
    Spacetime :=
  slowSourceCurrent κ ρ j v

example (κ : ℝ) (ρ : ℝ × E3 → ℝ) (j : Fin 3 → ℝ × E3 → ℝ) :
    potentialComponent (retardedPotential (slowSourceCurrent κ ρ j)) 0 =
      fun v => -slowScalar κ ρ (Wave.timeSpaceEquiv v) :=
  potentialComponent_retardedPotential_slowSourceCurrent_zero κ ρ j

example (κ : ℝ) (ρ : ℝ × E3 → ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (i : Fin 3) :
    potentialComponent (retardedPotential (slowSourceCurrent κ ρ j)) i.succ =
      fun v => slowVector κ j i (Wave.timeSpaceEquiv v) :=
  potentialComponent_retardedPotential_slowSourceCurrent_succ κ ρ j i

example (κ : ℝ) (ρ : ℝ × E3 → ℝ) (p : ℝ × E3) :
    ℝ :=
  darwinGauge κ ρ p

example (κ : ℝ) (ρ : ℝ × E3 → ℝ) :
    ℝ × E3 → ℝ :=
  darwinScalar κ ρ

example (i k : Fin 3) (y : E3) :
    ℝ :=
  darwinKernel i k y

example (κ : ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (i : Fin 3) (p : ℝ × E3) :
    ℝ :=
  darwinVector κ j i p

example (i k : Fin 3) (y : E3) :
    ℝ :=
  distanceHessian i k y

example (i k : Fin 3) (y : E3) (σ : ℝ) (hσ : |σ| ≤ 1) :
    |(if i = k then 1 else 0) / ‖y‖ + σ * (y i * y k / ‖y‖ ^ 3)| ≤
      8 * π * Potential.newtonKernel y :=
  abs_delta_div_add_le i k y σ hσ

example (i k : Fin 3) (y : E3) :
    |darwinKernel i k y| ≤ Potential.newtonKernel y :=
  abs_darwinKernel_le i k y

example (i k : Fin 3) (y : E3) :
    |distanceHessian i k y| ≤ 8 * π * Potential.newtonKernel y :=
  abs_distanceHessian_le i k y

example (i k : Fin 3) :
    Measurable (darwinKernel i k) :=
  measurable_darwinKernel i k

example (i k : Fin 3) :
    Measurable (distanceHessian i k) :=
  measurable_distanceHessian i k

example (i k : Fin 3) :
    LocallyIntegrable (darwinKernel i k) :=
  locallyIntegrable_darwinKernel i k

example :
    LocallyIntegrable fun y : E3 => ‖y‖ :=
  locallyIntegrable_norm

namespace SlowSource

variable {a : ℝ} {ρ : ℝ × E3 → ℝ} {j : Fin 3 → ℝ × E3 → ℝ}

example (h : SlowSource a ρ j) (κ : ℝ) (p : ℝ × E3) :
    timeDeriv (slow κ ρ) p + ∑ k, spaceDeriv k (fun q => κ * slow κ (j k) q) p = 0 :=
  continuity_slow h κ p

example (h : SlowSource a ρ j) (i : Fin 3) (q : ℝ × E3) :
    spaceDeriv i (timeDeriv ρ) q = -∑ k, spaceDeriv i (spaceDeriv k (j k)) q :=
  spaceDeriv_timeDeriv h i q

example (h : SlowSource a ρ j) (s : ℝ) :
    ∫ z, timeDeriv ρ (s, z) = 0 :=
  integral_timeDeriv h s

end SlowSource

namespace SlowSource

variable {a : ℝ} {ρ : ℝ × E3 → ℝ} {j : Fin 3 → ℝ × E3 → ℝ}

example (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) (p : ℝ × E3) :
    darwinVector κ j i p = κ * kernelIntegral Potential.newtonKernel (slow κ (j i)) p +
      spaceDeriv i (darwinGauge κ ρ) p :=
  darwinVector_eq h κ i p

example (h : SlowSource a ρ j) (κ : ℝ) :
    ContDiff ℝ ∞ (darwinGauge κ ρ) :=
  contDiff_darwinGauge h κ

example (h : SlowSource a ρ j) (κ : ℝ) :
    ContDiff ℝ ∞ (slowScalar κ ρ) :=
  contDiff_slowScalar h κ

example (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (slowVector κ j i) :=
  contDiff_slowVector h κ i

example (h : SlowSource a ρ j) (κ : ℝ) :
    ContDiff ℝ ∞ (retardedPotential (slowSourceCurrent κ ρ j)) :=
  contDiff_retardedPotential_slowSourceCurrent h κ

example (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) (v : Spacetime) :
    electricField (fieldTensor (retardedPotential (slowSourceCurrent κ ρ j))) i v =
      electricOf (slowScalar κ ρ) (slowVector κ j) i (Wave.timeSpaceEquiv v) :=
  electricField_retardedPotential_slowSourceCurrent h κ i v

example (h : SlowSource a ρ j) (κ : ℝ) (v : Spacetime) :
    (fun i => magneticField (fieldTensor (retardedPotential (slowSourceCurrent κ ρ j))) i v) =
      magneticOf (slowVector κ j) (Wave.timeSpaceEquiv v) :=
  magneticField_retardedPotential_slowSourceCurrent h κ v

example (h : SlowSource a ρ j) (κ : ℝ) (w : E3) (i : Fin 3) (v : Spacetime) :
    lorentzDensity (slowScalar κ ρ) (slowVector κ j) w i (Wave.timeSpaceEquiv v) =
      electricField (fieldTensor (retardedPotential (slowSourceCurrent κ ρ j))) i v +
        crossProduct (WithLp.ofLp w)
          (fun k => magneticField (fieldTensor (retardedPotential (slowSourceCurrent κ ρ j)))
            k v) i :=
  lorentzDensity_slow_eq h κ w i v

example (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) (p : ℝ × E3) :
    electricOf (fun q => slowScalar κ ρ q - timeDeriv (darwinGauge κ ρ) q)
        (fun k q => slowVector κ j k q + spaceDeriv k (darwinGauge κ ρ) q) i p =
      electricOf (slowScalar κ ρ) (slowVector κ j) i p :=
  electricOf_darwinGauge h κ i p

example (h : SlowSource a ρ j) (κ : ℝ) (p : ℝ × E3) :
    magneticOf (fun k q => slowVector κ j k q + spaceDeriv k (darwinGauge κ ρ) q) p =
      magneticOf (slowVector κ j) p :=
  magneticOf_darwinGauge h κ p

example (h : SlowSource a ρ j) (κ : ℝ) (p : ℝ × E3) :
    timeDeriv (darwinGauge κ ρ) p = κ ^ 2 / (8 * π) *
      kernelIntegral (fun y => ‖y‖) (slow κ (timeDeriv (timeDeriv ρ))) p :=
  timeDeriv_darwinGauge h κ p

example (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (hM : ∀ p, |timeDeriv^[3] ρ p| ≤ M) {κ : ℝ}
    (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {R : ℝ} (hx : ‖x‖ ≤ R) :
    |slowScalar κ ρ (t, x) - timeDeriv (darwinGauge κ ρ) (t, x) - darwinScalar κ ρ (t, x)| ≤
      M * (R + a) ^ 5 / 18 * κ ^ 3 :=
  scalar_expansion h ha hM hκ t hx

example (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (hM : ∀ i p, |timeDeriv (j i) p| ≤ M) {κ : ℝ}
    (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {R : ℝ} (hx : ‖x‖ ≤ R) (i : Fin 3) :
    |slowVector κ j i (t, x) + spaceDeriv i (darwinGauge κ ρ) (t, x) -
        darwinVector κ j i (t, x)| ≤ M * (R + a) ^ 3 / 3 * κ ^ 2 :=
  vector_expansion h ha hM hκ t hx i

end SlowSource

example {φ : ℝ × E3 → ℝ} {A : Fin 3 → ℝ × E3 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hA : ∀ k, ContDiff ℝ 1 (A k)) (v : E3) (i : Fin 3) :
    Continuous (lorentzDensity φ A v i) :=
  continuous_lorentzDensity hφ hA v i

namespace SlowSource

variable {a : ℝ} {ρ : ℝ × E3 → ℝ} {j : Fin 3 → ℝ × E3 → ℝ}

example (κ : ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (i : Fin 3) :
    slowVector κ j i = fun p => κ * retardedIntegral (slow κ (j i)) p :=
  slowVector_eq κ j i

example (h : SlowSource a ρ j) (κ : ℝ) :
    ContDiff ℝ ∞ (darwinScalar κ ρ) :=
  contDiff_darwinScalar h κ

example (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (darwinVector κ j i) :=
  contDiff_darwinVector h κ i

example (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) (p : ℝ × E3) :
    spaceDeriv i (timeDeriv (darwinGauge κ ρ)) p = κ ^ 2 / (8 * π) *
      kernelIntegral (fun y => ‖y‖) (slow κ (spaceDeriv i (timeDeriv (timeDeriv ρ)))) p :=
  spaceDeriv_timeDeriv_darwinGauge h κ i p

example (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (i : Fin 3)
    (hM : ∀ p, |timeDeriv^[3] (spaceDeriv i ρ) p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3}
    {R : ℝ} (hx : ‖x‖ ≤ R) :
    |spaceDeriv i (slowScalar κ ρ) (t, x) - spaceDeriv i (darwinScalar κ ρ) (t, x) -
        spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x)| ≤ M * (R + a) ^ 5 / 18 * κ ^ 3 :=
  spaceDeriv_scalar_sub h ha i hM hκ t hx

example (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (i : Fin 3)
    (hM : ∀ p, |timeDeriv (timeDeriv (j i)) p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {R : ℝ}
    (hx : ‖x‖ ≤ R) :
    |timeDeriv (slowVector κ j i) (t, x) - timeDeriv (darwinVector κ j i) (t, x) +
        spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x)| ≤ M * (R + a) ^ 3 / 3 * κ ^ 3 :=
  timeDeriv_vector_sub h ha i hM hκ t hx

example (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (k l : Fin 3)
    (hM : ∀ p, |timeDeriv (spaceDeriv l (j k)) p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3}
    {R : ℝ} (hx : ‖x‖ ≤ R) :
    |spaceDeriv l (slowVector κ j k) (t, x) - spaceDeriv l (darwinVector κ j k) (t, x) +
        spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x)| ≤ M * (R + a) ^ 3 / 3 * κ ^ 2 :=
  spaceDeriv_vector_sub h ha k l hM hκ t hx

end SlowSource

namespace SlowSource

variable {a : ℝ} {ρ : ℝ × E3 → ℝ} {j : Fin 3 → ℝ × E3 → ℝ}

example (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (hM : SlowBounds M ρ j) {κ : ℝ} (hκ : 0 ≤ κ)
    (t : ℝ) {x : E3} {R : ℝ} (hx : ‖x‖ ≤ R) {v : E3} {V : ℝ} (hv : ‖v‖ ≤ V * κ) (i : Fin 3) :
    |lorentzDensity (slowScalar κ ρ) (slowVector κ j) v i (t, x) -
        lorentzDensity (darwinScalar κ ρ) (darwinVector κ j) v i (t, x)| ≤
      (M * (R + a) ^ 5 / 18 + M * (R + a) ^ 3 / 3 + 6 * V * (M * (R + a) ^ 3 / 3)) * κ ^ 3 :=
  abs_lorentzDensity_sub_le h ha hM hκ t hx hv i

example (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (hM : SlowBounds M ρ j) {ρ₀ : E3 → ℝ}
    (hρ₀ : Continuous ρ₀) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → ρ₀ z = 0) {κ : ℝ} (hκ : 0 ≤ κ)
    {r : ℝ → E3} {t : ℝ} (hr : DifferentiableAt ℝ r t) {R V : ℝ} (hrR : ‖r t‖ ≤ R)
    (hV : ‖deriv r t‖ ≤ V * κ) (i : Fin 3) :
    |(∫ x, ρ₀ (x - r t) * lorentzDensity (slowScalar κ ρ) (slowVector κ j) (deriv r t) i (t, x)) -
        Mechanics.eulerLagrange (rigidLagrangian ρ₀ (darwinScalar κ ρ) (darwinVector κ j)) r t
          (EuclideanSpace.single i 1)| ≤
      (∫ z, |ρ₀ z|) * ((M * (R + b + a) ^ 5 / 18 + M * (R + b + a) ^ 3 / 3 +
        6 * V * (M * (R + b + a) ^ 3 / 3)) * κ ^ 3) :=
  force_eq_darwin h ha hM hρ₀ hb hκ hr hrR hV i

end SlowSource

example (x : E3) :
    ℝ :=
  bumpSlope x

example :
    ℝ × E3 → ℝ :=
  exampleCharge

example :
    Fin 3 → ℝ × E3 → ℝ :=
  exampleCurrent

example :
    ContDiff ℝ ∞ (spaceBump : E3 → ℝ) :=
  contDiff_spaceBump

example :
    ContDiff ℝ ∞ bumpSlope :=
  contDiff_bumpSlope

example {x : E3} (hx : 2 < ‖x‖) :
    spaceBump x = 0 :=
  spaceBump_eq_zero hx

example {x : E3} (hx : 2 < ‖x‖) :
    fderiv ℝ spaceBump x = 0 :=
  fderiv_spaceBump_eq_zero hx

example :
    SlowSource 2 exampleCharge exampleCurrent :=
  slowSource_example

example :
    ∃ M, SlowBounds M exampleCharge exampleCurrent :=
  exists_slowBounds_example

example (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) :
    ℝ × E3 → ℝ :=
  rigidCharge e η R

example (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (k : Fin 3) :
    ℝ × E3 → ℝ :=
  rigidCurrent e η R k

example (e₁ e₂ : ℝ) (r₁ r₂ v₁ v₂ : E3) :
    ℝ :=
  darwinPair e₁ e₂ r₁ r₂ v₁ v₂

example (v w z : E3) :
    ∑ i, w i * ∑ k, v k * darwinKernel i k z =
      (inner ℝ v w + inner ℝ v (‖z‖⁻¹ • z) * inner ℝ w (‖z‖⁻¹ • z)) / (8 * π * ‖z‖) :=
  sum_darwinKernel v w z

example (i k : Fin 3) {z : E3} (hz : z ≠ 0) :
    ContinuousAt (darwinKernel i k) z :=
  continuousAt_darwinKernel i k hz

example {z : E3} (hz : z ≠ 0) :
    ContinuousAt Potential.newtonKernel z :=
  continuousAt_newtonKernel hz

example {K : E3 → ℝ} (hK : ∀ z : E3, z ≠ 0 → ContinuousAt K z) {z₀ : E3} (hz₀ : z₀ ≠ 0) :
    ContinuousOn K (closedBall z₀ (‖z₀‖ / 2)) :=
  continuousOn_closedBall_of_continuousAt hK hz₀

example {K : E3 → ℝ} (hK : LocallyIntegrable K) {η : E3 → ℝ} (hη : Continuous η) {ε : ℝ}
    (hηs : ∀ z : E3, ε < ‖z‖ → η z = 0) (r : E3) :
    Continuous fun x => ∫ y, K y * η (x - y - r) :=
  continuous_kernel_average hK hη hηs r

example {η : ℝ → E3 → ℝ} (hηc : ∀ ε, Continuous (η ε)) (hη0 : ∀ ε z, 0 ≤ η ε z)
    (hη1 : ∀ ε, 0 < ε → ∫ z, η ε z = 1) (hηs : ∀ ε, 0 < ε → ∀ z : E3, ε < ‖z‖ → η ε z = 0)
    (hηe : ∀ ε z, η ε (-z) = η ε z) (e₁ e₂ κ : ℝ) (R₁ : ℝ → E3) (t : ℝ) (r₂ v₂ : E3)
    (hR : r₂ ≠ R₁ (κ * t)) :
    Tendsto (fun ε => rigidLagrangian (fun z => e₂ * η ε z)
        (darwinScalar κ (rigidCharge e₁ (η ε) R₁)) (darwinVector κ (rigidCurrent e₁ (η ε) R₁))
        t (r₂, v₂)) (𝓝[>] 0)
      (𝓝 (darwinPair e₁ e₂ (R₁ (κ * t)) r₂ (κ • deriv R₁ (κ * t)) v₂)) :=
  darwinInteraction_pointLimit hηc hη0 hη1 hηs hηe e₁ e₂ κ R₁ t r₂ v₂ hR

example (ε : ℝ) :
    E3 → ℝ :=
  pointBump ε

example (e₁ e₂ κ : ℝ) (R₁ : ℝ → E3) (t : ℝ) (r₂ v₂ : E3) (hR : r₂ ≠ R₁ (κ * t)) :
    Tendsto (fun ε => rigidLagrangian (fun z => e₂ * pointBump ε z)
        (darwinScalar κ (rigidCharge e₁ (pointBump ε) R₁))
        (darwinVector κ (rigidCurrent e₁ (pointBump ε) R₁)) t (r₂, v₂)) (𝓝[>] 0)
      (𝓝 (darwinPair e₁ e₂ (R₁ (κ * t)) r₂ (κ • deriv R₁ (κ * t)) v₂)) :=
  darwinInteraction_pointLimit_pointBump e₁ e₂ κ R₁ t r₂ v₂ hR

example (e₁ e₂ : ℝ) (r₁ r₂ v₁ v₂ : E3) :
    darwinPair e₁ e₂ r₁ r₂ v₁ v₂ = darwinPair e₂ e₁ r₂ r₁ v₂ v₁ :=
  darwinPair_comm e₁ e₂ r₁ r₂ v₁ v₂

example {N : ℕ} (m e : Fin N → ℝ) :
    Mechanics.Lagrangian (Fin N → E3) :=
  darwinLagrangian m e

example {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    |√(1 - s) - (1 - s / 2 - s ^ 2 / 8)| ≤ s ^ 3 / 4 :=
  abs_sqrt_one_sub_sub_le hs0 hs

example (m : ℝ) {v : E3} (hv : ‖v‖ ^ 2 ≤ 1 / 2) :
    |-m * √(1 - ‖v‖ ^ 2) - (-m + m * ‖v‖ ^ 2 / 2 + m * ‖v‖ ^ 4 / 8)| ≤ |m| * ‖v‖ ^ 6 / 4 :=
  abs_free_sub_darwin_le m hv

example {N : ℕ} (m e : Fin N → ℝ) (κ : ℝ) (R : Fin N → ℝ → E3) (t : ℝ)
    (hsep : ∀ a b, a ≠ b → R a (κ * t) ≠ R b (κ * t)) :
    Tendsto (fun ε => ∑ a, (-m a + m a * ‖κ • deriv (R a) (κ * t)‖ ^ 2 / 2 +
        m a * ‖κ • deriv (R a) (κ * t)‖ ^ 4 / 8) +
      ∑ a, ∑ b, if a < b then rigidLagrangian (fun z => e b * pointBump ε z)
        (darwinScalar κ (rigidCharge (e a) (pointBump ε) (R a)))
        (darwinVector κ (rigidCurrent (e a) (pointBump ε) (R a))) t
        (R b (κ * t), κ • deriv (R b) (κ * t)) else 0) (𝓝[>] 0)
      (𝓝 (darwinLagrangian m e t
        (fun a => R a (κ * t), fun a => κ • deriv (R a) (κ * t)))) :=
  darwinLagrangian_pointLimit m e κ R t hsep

example (i : Fin 3) :
    ∃ C, ∀ κ, 0 ≤ κ → ∀ t, |(∫ x, spaceBump (x - (5 : ℝ) • EuclideanSpace.single 0 1) *
        lorentzDensity (slowScalar κ exampleCharge) (slowVector κ exampleCurrent)
          (deriv (fun _ : ℝ => (5 : ℝ) • (EuclideanSpace.single 0 1 : E3)) t) i (t, x)) -
      Mechanics.eulerLagrange (rigidLagrangian spaceBump (darwinScalar κ exampleCharge)
        (darwinVector κ exampleCurrent)) (fun _ => (5 : ℝ) • EuclideanSpace.single 0 1) t
          (EuclideanSpace.single i 1)| ≤ C * κ ^ 3 :=
  force_eq_darwin_example i

end ProjectAinos.Electrodynamics

end Darwin

section DarwinPointCharge

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Wave SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {R₁ : ℝ → E3} (hR : Differentiable ℝ R₁) (κ t : ℝ) :
    deriv (fun t => R₁ (κ * t)) t = κ • deriv R₁ (κ * t) :=
  deriv_slowPath hR κ t

example (R₁ : ℝ → E3) (hR : ContDiff ℝ ∞ R₁) {V₁ : ℝ} (hV : ∀ s, ‖deriv R₁ s‖ ≤ V₁) {κ : ℝ}
    (hκ : 0 ≤ κ) (hκV : κ * V₁ < 1) :
    SubluminalWorldline :=
  slowWorldline R₁ hR hV hκ hκV

example (K : E3 → ℝ) (e : ℝ) (φ : ℝ × E3 → ℝ) (A : Fin 3 → ℝ × E3 → ℝ) (g : ℝ → ℝ) :
    Mechanics.Lagrangian E3 :=
  pointLagrangian K e φ A g

example {K : E3 → ℝ} (hK : ContDiff ℝ 2 K) (e : ℝ) {φ : ℝ × E3 → ℝ} {A : Fin 3 → ℝ × E3 → ℝ}
    (g : ℝ → ℝ) {r : ℝ → E3} {t : ℝ} (hφ : ∀ᶠ p in 𝓝 (t, r t), DifferentiableAt ℝ φ p)
    (hA : ∀ k, ∀ᶠ p in 𝓝 (t, r t), DifferentiableAt ℝ (A k) p)
    (hr : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ r s) (hr' : DifferentiableAt ℝ (deriv r) t) (i : Fin 3) :
    Mechanics.eulerLagrange (pointLagrangian K e φ A g) r t (EuclideanSpace.single i 1) =
      -deriv (fun s => fderiv ℝ K (deriv r s) (EuclideanSpace.single i 1)) t +
        e * lorentzDensity φ A (deriv r t) i (t, r t) :=
  eulerLagrange_pointLagrangian hK e g hφ hA hr hr' i

example {N : ℕ} {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (L : Mechanics.Lagrangian (Fin N → Q)) (q : ℝ → Fin N → Q) (a : Fin N) {t : ℝ}
    (hL : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (L s) (q s, deriv q s))
    (hq : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ q s)
    (hM : DifferentiableAt ℝ (Mechanics.momentum L q) t) (w : Q) :
    Mechanics.eulerLagrange L q t (Pi.single a w) =
      Mechanics.eulerLagrange
        (fun s z => L s (Function.update (q s) a z.1, Function.update (deriv q s) a z.2))
        (fun s => q s a) t w :=
  eulerLagrange_update L q a hL hq hM w

example (e : ℝ) (c : ℝ → E3) (p : ℝ × E3) :
    ℝ :=
  pointScalar e c p

example (e : ℝ) (c : ℝ → E3) (i : Fin 3) (p : ℝ × E3) :
    ℝ :=
  pointVector e c i p

example (i k : Fin 3) {z : E3} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (darwinKernel i k) z :=
  contDiffAt_darwinKernel i k hz

example (e : ℝ) {c : ℝ → E3} (hc : ContDiff ℝ ∞ c) {p : ℝ × E3} (hp : p.2 ≠ c p.1) :
    ContDiffAt ℝ ∞ (pointScalar e c) p :=
  contDiffAt_pointScalar e hc hp

example (e : ℝ) {c : ℝ → E3} (hc : ContDiff ℝ ∞ c) (i : Fin 3) {p : ℝ × E3} (hp : p.2 ≠ c p.1) :
    ContDiffAt ℝ ∞ (pointVector e c i) p :=
  contDiffAt_pointVector e hc i hp

example {F : ℝ × E3 → ℝ} {c : ℝ → E3} (hc : Continuous c)
    (hF : ∀ p : ℝ × E3, p.2 ≠ c p.1 → ContDiffAt ℝ ∞ F p) {p : ℝ × E3} (hp : p.2 ≠ c p.1) :
    ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ F q :=
  eventually_differentiableAt_point hc hF hp

example (e₁ e₂ : ℝ) (c : ℝ → E3) (s : ℝ) (r u : E3) :
    darwinPair e₁ e₂ r (c s) u (deriv c s) =
      -e₁ * pointScalar e₂ c (s, r) + e₁ * ∑ k, u k * pointVector e₂ c k (s, r) :=
  darwinPair_eq_point e₁ e₂ c s r u

example (m : ℝ) (v : E3) :
    ℝ :=
  darwinKinetic m v

example (m : ℝ) :
    ContDiff ℝ ∞ (darwinKinetic m) :=
  contDiff_darwinKinetic m

example (m : ℝ) (v : E3) (i : Fin 3) :
    fderiv ℝ (darwinKinetic m) v (EuclideanSpace.single i 1) = m * (1 + ‖v‖ ^ 2 / 2) * v i :=
  fderiv_darwinKinetic m v i

example {N : ℕ} (m e : Fin N → ℝ) (s : ℝ) {z : (Fin N → E3) × (Fin N → E3)}
    (hz : ∀ b c, b ≠ c → z.1 b ≠ z.1 c) :
    ContDiffAt ℝ ∞ (darwinLagrangian m e s) z :=
  contDiffAt_darwinLagrangian m e s hz

example {N : ℕ} (m e : Fin N → ℝ) (Q : Fin N → ℝ → E3) (a : Fin N) (s : ℝ) :
    ℝ :=
  darwinRest m e Q a s

example {N : ℕ} (m e : Fin N → ℝ) (Q : Fin N → ℝ → E3) (a : Fin N) (s : ℝ) (z : E3 × E3) :
    darwinLagrangian m e s (Function.update (fun b => Q b s) a z.1,
        Function.update (fun b => deriv (Q b) s) a z.2) =
      pointLagrangian (darwinKinetic (m a)) (e a)
        (fun p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointScalar (e b) (Q b) p)
        (fun k p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointVector (e b) (Q b) k p)
        (darwinRest m e Q a) s z :=
  darwinLagrangian_update m e Q a s z

example {N : ℕ} (m e : Fin N → ℝ) {Q : Fin N → ℝ → E3} (hQ : ∀ b, ContDiff ℝ ∞ (Q b)) {t : ℝ}
    (hsep : ∀ b c, b ≠ c → Q b t ≠ Q c t) (a : Fin N) (i : Fin 3) :
    Mechanics.eulerLagrange (darwinLagrangian m e) (fun s b => Q b s) t
        (Pi.single a (EuclideanSpace.single i 1)) =
      -deriv (fun s => m a * (1 + ‖deriv (Q a) s‖ ^ 2 / 2) * deriv (Q a) s i) t +
        e a * lorentzDensity (fun p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointScalar (e b) (Q b) p)
          (fun k p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointVector (e b) (Q b) k p)
          (deriv (Q a) t) i (t, Q a t) :=
  eulerLagrange_darwinLagrangian m e hQ hsep a i

example (κ : ℝ) :
    Fin 2 → ℝ → E3 :=
  examplePaths κ

example (m e : Fin 2 → ℝ) (κ : ℝ) (i : Fin 3) :
    Mechanics.eulerLagrange (darwinLagrangian m e) (fun s b => examplePaths κ b s) 0
        (Pi.single 0 (EuclideanSpace.single i 1)) =
      -deriv (fun s => m 0 * (1 + ‖deriv (examplePaths κ 0) s‖ ^ 2 / 2) *
          deriv (examplePaths κ 0) s i) 0 +
        e 0 * lorentzDensity
          (fun p => ∑ b ∈ ({0}ᶜ : Finset (Fin 2)), pointScalar (e b) (examplePaths κ b) p)
          (fun k p => ∑ b ∈ ({0}ᶜ : Finset (Fin 2)), pointVector (e b) (examplePaths κ b) k p)
          (deriv (examplePaths κ 0) 0) i (0, examplePaths κ 0 0) :=
  eulerLagrange_darwinLagrangian_example m e κ i

section Jet

variable {P : Type*}

example (S : Set P) (ε q q₀ q₁ q₂ : P → ℝ) :
    Prop :=
  Jet S ε q q₀ q₁ q₂

variable {S : Set P} {ε : P → ℝ}

example {q q₀ q₁ q₂ q₃ : P → ℝ}
    (h : ∀ p ∈ S, q p = q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p + ε p ^ 3 * q₃ p)
    (hb : ∃ C, ∀ p ∈ S, |q₀ p| ≤ C ∧ |q₁ p| ≤ C ∧ |q₂ p| ≤ C ∧ |q₃ p| ≤ C) :
    Jet S ε q q₀ q₁ q₂ :=
  Jet.of_eq h hb

example {q : P → ℝ} (hb : ∃ C, ∀ p ∈ S, |q p| ≤ C) :
    Jet S ε q q (fun _ => 0) (fun _ => 0) :=
  Jet.const hb

example :
    Jet S ε ε (fun _ => 0) (fun _ => 1) (fun _ => 0) :=
  Jet.eps

example {q q₀ q₁ q₂ r r₀ r₁ r₂ : P → ℝ} (hq : Jet S ε q q₀ q₁ q₂) (hr : Jet S ε r r₀ r₁ r₂) :
    Jet S ε (fun p => q p + r p) (fun p => q₀ p + r₀ p) (fun p => q₁ p + r₁ p)
      (fun p => q₂ p + r₂ p) :=
  Jet.add hq hr

example {q q₀ q₁ q₂ : P → ℝ} (c : ℝ) (hq : Jet S ε q q₀ q₁ q₂) :
    Jet S ε (fun p => c * q p) (fun p => c * q₀ p) (fun p => c * q₁ p) (fun p => c * q₂ p) :=
  Jet.const_mul c hq

example {q q₀ q₁ q₂ r r₀ r₁ r₂ : P → ℝ} (hq : Jet S ε q q₀ q₁ q₂) (hr : Jet S ε r r₀ r₁ r₂) :
    Jet S ε (fun p => q p - r p) (fun p => q₀ p - r₀ p) (fun p => q₁ p - r₁ p)
      (fun p => q₂ p - r₂ p) :=
  Jet.sub hq hr

example {a b c e C : ℝ} (he : |e| ≤ 1) (ha : |a| ≤ C) (hb : |b| ≤ C) (hc : |c| ≤ C) :
    |a + e * b + e ^ 2 * c| ≤ 3 * C :=
  abs_poly2_le he ha hb hc

example (hε : ∀ p ∈ S, |ε p| ≤ 1) {q q₀ q₁ q₂ r r₀ r₁ r₂ : P → ℝ} (hq : Jet S ε q q₀ q₁ q₂)
    (hr : Jet S ε r r₀ r₁ r₂) :
    Jet S ε (fun p => q p * r p) (fun p => q₀ p * r₀ p) (fun p => q₀ p * r₁ p + q₁ p * r₀ p)
      (fun p => q₀ p * r₂ p + q₁ p * r₁ p + q₂ p * r₀ p) :=
  Jet.mul hε hq hr

example {q q' q₀ q₁ q₂ : P → ℝ} {K : ℝ} (h : ∀ p ∈ S, |q p - q' p| ≤ K * |ε p| ^ 3)
    (hq : Jet S ε q' q₀ q₁ q₂) :
    Jet S ε q q₀ q₁ q₂ :=
  Jet.of_close h hq

example {q q₀ q₁ q₂ q' a b c : P → ℝ} (hq : Jet S ε q q₀ q₁ q₂) (h : ∀ p ∈ S, q' p = q p)
    (ha : ∀ p ∈ S, a p = q₀ p) (hb : ∀ p ∈ S, b p = q₁ p) (hc : ∀ p ∈ S, c p = q₂ p) :
    Jet S ε q' a b c :=
  Jet.congr hq h ha hb hc

example {ι : Type*} (s : Finset ι) {q q₀ q₁ q₂ : ι → P → ℝ}
    (hq : ∀ k ∈ s, Jet S ε (q k) (q₀ k) (q₁ k) (q₂ k)) :
    Jet S ε (fun p => ∑ k ∈ s, q k p) (fun p => ∑ k ∈ s, q₀ k p) (fun p => ∑ k ∈ s, q₁ k p)
      (fun p => ∑ k ∈ s, q₂ k p) :=
  Jet.sum s hq

example {q : P → ℝ} (hq : Jet S ε q (fun _ => 0) (fun _ => 0) (fun _ => 0)) :
    ∃ C, ∀ p ∈ S, |q p| ≤ C * |ε p| ^ 3 :=
  Jet.bound_three hq

example (hε : ∀ p ∈ S, |ε p| ≤ 1) {q q₂ : P → ℝ} (hq : Jet S ε q (fun _ => 0) (fun _ => 0) q₂) :
    ∃ C, ∀ p ∈ S, |q p| ≤ C * |ε p| ^ 2 :=
  Jet.bound_two hε hq

example (hε : ∀ p ∈ S, |ε p| ≤ 1) {q q₁ q₂ : P → ℝ} (hq : Jet S ε q (fun _ => 0) q₁ q₂) :
    ∃ C, ∀ p ∈ S, |q p| ≤ C * |ε p| :=
  Jet.abs_le_of_zero hε hq

example (hε : ∀ p ∈ S, |ε p| ≤ 1) {q q₀ q₁ q₂ : P → ℝ} (hq : Jet S ε q q₀ q₁ q₂) {c : ℝ}
    (hc : 0 < c) (hqc : ∀ p ∈ S, c ≤ |q p| ∧ c ≤ |q₀ p|) :
    Jet S ε (fun p => (q p)⁻¹) (fun p => (q₀ p)⁻¹) (fun p => -(q₁ p / q₀ p ^ 2))
      (fun p => q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2) :=
  Jet.inv hε hq hc hqc

example {z c : ℝ} (hc : 0 < c) (hz : 0 ≤ 1 + z) (hy : c ≤ √(1 + z)) :
    |(√(1 + z))⁻¹ - (1 - z / 2 + 3 * z ^ 2 / 8)| ≤
      (3 * (1 + z) + 9 * √(1 + z) + 8) / (8 * c) * |z| ^ 3 :=
  abs_inv_sqrt_sub_le hc hz hy

example (hε : ∀ p ∈ S, |ε p| ≤ 1) {z z₁ z₂ : P → ℝ} (hz : Jet S ε z (fun _ => 0) z₁ z₂) {c : ℝ}
    (hc : 0 < c) (hzc : ∀ p ∈ S, 0 ≤ 1 + z p ∧ c ≤ √(1 + z p)) :
    Jet S ε (fun p => (√(1 + z p))⁻¹) (fun _ => 1) (fun p => -(z₁ p / 2))
      (fun p => -(z₂ p / 2) + 3 * z₁ p ^ 2 / 8) :=
  Jet.invSqrt hε hz hc hzc

end Jet

namespace SlowData

example (d : SlowData) :
    ℝ :=
  b d

example (d : SlowData) (i : Fin 3) :
    ℝ :=
  Y d i

example (d : SlowData) :
    ℝ :=
  z d

example (d : SlowData) :
    ℝ :=
  minv d

example (d : SlowData) (i : Fin 3) :
    ℝ :=
  Vp d i

example (d : SlowData) (i : Fin 3) :
    ℝ :=
  Ap d i

example (d : SlowData) (i : Fin 3) :
    ℝ :=
  lw d i

example (d : SlowData) (i : Fin 3) :
    ℝ :=
  darwin d i

example (K c : ℝ) :
    Set SlowData :=
  admissible K c

end SlowData

namespace SlowData

example (d : SlowData) (i : Fin 3) :
    ℝ :=
  c₂ d i

variable {K c : ℝ}

example {d : SlowData} (hd : d ∈ admissible K c) (k : Fin 3) :
    |d.n k| ≤ 1 :=
  abs_n_le hd k

example {d : SlowData} (hd : d ∈ admissible K c) :
    0 ≤ K :=
  K_nonneg hd

example {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x * y| ≤ X * Y :=
  abs_mul_le hx hy

example {d : SlowData} (hd : d ∈ admissible K c) :
    |d.b| ≤ 3 * K :=
  abs_b_le hd

end SlowData

namespace SlowData

variable {K c : ℝ}

example {d : SlowData} (hd : d ∈ admissible K c) (k : Fin 3) :
    |d.n k| ≤ K + 1 ∧ |d.β k| ≤ K + 1 ∧ |d.α k| ≤ K + 1 ∧ |d.ρX k| ≤ K + 1 ∧
      |d.ρV k| ≤ K + 1 ∧ |d.ρA k| ≤ K + 1 ∧ |d.R| ≤ K + 1 :=
  bounds hd k

example (i : Fin 3) :
    Jet (admissible K c) SlowData.ε (fun d => d.lw i)
    (fun d => d.n i) (fun d => 3 * d.b * d.n i - d.β i) (fun d => d.c₂ i) :=
  jet_lw i

end SlowData

namespace SlowData

variable {K c : ℝ}

example (hc : 0 < c) (i : Fin 3) :
    Jet (admissible K c) SlowData.ε
    (fun d => d.darwin i) (fun d => d.n i) (fun d => 3 * d.b * d.n i - d.β i)
    (fun d => d.c₂ i) :=
  jet_darwin hc i

end SlowData

namespace SlowData

variable {K c : ℝ}

example (hc : 0 < c) (i : Fin 3) :
    ∃ C, ∀ d ∈ admissible K c, |d.lw i - d.darwin i| ≤ C * |d.ε| ^ 3 :=
  abs_lw_sub_darwin_le hc i

example (k : Fin 3) :
    Jet (admissible K c) SlowData.ε (fun d => d.Y k) (fun d => d.n k)
    (fun d => -d.β k) (fun d => -(d.R * d.α k / 2)) :=
  jet_Y k

example (k : Fin 3) :
    Jet (admissible K c) SlowData.ε (fun d => d.Vp k)
    (fun d => d.β k) (fun d => d.R * d.α k) (fun d => d.ρV k) :=
  jet_Vp k

example (hc : 0 < c) :
    Jet (admissible K c) SlowData.ε (fun d => d.minv)
    (fun _ => 1) (fun d => -(-2 * d.b / 2))
    (fun d => -((∑ k, d.β k * d.β k - d.R * ∑ k, d.n k * d.α k) / 2) +
      3 * (-2 * d.b) ^ 2 / 8) :=
  jet_minv hc

example (d : SlowData) (i : Fin 3) :
    ℝ :=
  lwB d i

example (d : SlowData) (i : Fin 3) :
    ℝ :=
  darwinB d i

example (hc : 0 < c) (i : Fin 3) :
    ∃ C, ∀ d ∈ admissible K c, |d.lwB i - d.darwinB i| ≤ C * |d.ε| ^ 2 :=
  abs_lwB_sub_darwinB_le hc i

end SlowData

example {Z : ℝ → E3} {Z' : E3} {s : ℝ} (hZ : HasDerivAt Z Z' s) (h0 : Z s ≠ 0) :
    HasDerivAt (fun s => ‖Z s‖) (inner ℝ (Z s) Z' / ‖Z s‖) s :=
  hasDerivAt_norm_path hZ h0

example {Z : ℝ → E3} {Z' : E3} {s : ℝ} (hZ : HasDerivAt Z Z' s) (k : Fin 3) :
    HasDerivAt (fun s => Z s k) (Z' k) s :=
  hasDerivAt_component_path hZ k

example {Z W : ℝ → E3} {Z' W' : E3} {s : ℝ} (hZ : HasDerivAt Z Z' s) (hW : HasDerivAt W W' s)
    (h0 : Z s ≠ 0) (k : Fin 3) :
    HasDerivAt (fun s => W s k / ‖Z s‖ + inner ℝ (W s) (Z s) * Z s k / ‖Z s‖ ^ 3)
      (W' k / ‖Z s‖ - W s k * inner ℝ (Z s) Z' / ‖Z s‖ ^ 3 +
        (inner ℝ W' (Z s) + inner ℝ (W s) Z') * Z s k / ‖Z s‖ ^ 3 +
        inner ℝ (W s) (Z s) * Z' k / ‖Z s‖ ^ 3 -
        3 * inner ℝ (W s) (Z s) * Z s k * inner ℝ (Z s) Z' / ‖Z s‖ ^ 5) s :=
  hasDerivAt_darwinProfile hZ hW h0 k

example (e : ℝ) (c : ℝ → E3) (k : Fin 3) (p : ℝ × E3) :
    pointVector e c k p = e / (8 * π) * (deriv c p.1 k / ‖p.2 - c p.1‖ +
      inner ℝ (deriv c p.1) (p.2 - c p.1) * (p.2 - c p.1) k / ‖p.2 - c p.1‖ ^ 3) :=
  pointVector_eq e c k p

example {F : ℝ × E3 → ℝ} {s : ℝ} {y : E3} (hF : DifferentiableAt ℝ F (s, y)) (i : Fin 3) {v : ℝ}
    (h : HasDerivAt (fun l : ℝ => F (s, y + l • EuclideanSpace.single i 1)) v 0) :
    spaceDeriv i F (s, y) = v :=
  spaceDeriv_eq_of_hasDerivAt hF i h

example {F : ℝ × E3 → ℝ} {s : ℝ} {y : E3} (hF : DifferentiableAt ℝ F (s, y)) {v : ℝ}
    (h : HasDerivAt (fun s' => F (s', y)) v s) :
    timeDeriv F (s, y) = v :=
  timeDeriv_eq_of_hasDerivAt hF h

section PointFields

variable {e : ℝ} {c : ℝ → E3}

example (hc : ContDiff ℝ ∞ c) {s : ℝ} {y : E3} (hy : y ≠ c s) (i : Fin 3) :
    spaceDeriv i (pointScalar e c) (s, y) =
      -(e * (4 * π * inner ℝ (y - c s) (EuclideanSpace.single i 1) / ‖y - c s‖)) /
        (4 * π * ‖y - c s‖) ^ 2 :=
  spaceDeriv_pointScalar hc hy i

example (hc : ContDiff ℝ ∞ c) {s : ℝ} {y : E3} (hy : y ≠ c s) (k : Fin 3) :
    timeDeriv (pointVector e c k) (s, y) = e / (8 * π) *
      (deriv (deriv c) s k / ‖y - c s‖ - deriv c s k * inner ℝ (y - c s) (-deriv c s) /
          ‖y - c s‖ ^ 3 +
        (inner ℝ (deriv (deriv c) s) (y - c s) + inner ℝ (deriv c s) (-deriv c s)) *
          (y - c s) k / ‖y - c s‖ ^ 3 +
        inner ℝ (deriv c s) (y - c s) * (-deriv c s) k / ‖y - c s‖ ^ 3 -
        3 * inner ℝ (deriv c s) (y - c s) * (y - c s) k * inner ℝ (y - c s) (-deriv c s) /
          ‖y - c s‖ ^ 5) :=
  timeDeriv_pointVector hc hy k

example (hc : ContDiff ℝ ∞ c) {s : ℝ} {y : E3} (hy : y ≠ c s) (j k : Fin 3) :
    spaceDeriv j (pointVector e c k) (s, y) = e / (8 * π) *
      ((0 : E3) k / ‖y - c s‖ - deriv c s k * inner ℝ (y - c s) (EuclideanSpace.single j 1) /
          ‖y - c s‖ ^ 3 +
        (inner ℝ (0 : E3) (y - c s) + inner ℝ (deriv c s) (EuclideanSpace.single j 1)) *
          (y - c s) k / ‖y - c s‖ ^ 3 +
        inner ℝ (deriv c s) (y - c s) * (EuclideanSpace.single j 1 : E3) k / ‖y - c s‖ ^ 3 -
        3 * inner ℝ (deriv c s) (y - c s) * (y - c s) k *
          inner ℝ (y - c s) (EuclideanSpace.single j 1) / ‖y - c s‖ ^ 5) :=
  spaceDeriv_pointVector hc hy j k

end PointFields

example {R₁ : ℝ → E3} (hR : ContDiff ℝ ∞ R₁) {A₃ : ℝ} (hA3 : ∀ s, ‖deriv^[3] R₁ s‖ ≤ A₃) (σ : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (k : Fin 3) :
    |R₁ (σ + u) k - (R₁ σ k + u * deriv R₁ σ k + u ^ 2 / 2 * deriv (deriv R₁) σ k)| ≤
        A₃ * u ^ 3 / 6 ∧
      |deriv R₁ (σ + u) k - (deriv R₁ σ k + u * deriv (deriv R₁) σ k)| ≤ A₃ * u ^ 2 / 2 ∧
      |deriv (deriv R₁) (σ + u) k - deriv (deriv R₁) σ k| ≤ A₃ * u :=
  taylor_path hR hA3 σ hu k

example (R₁ : ℝ → E3) (w : SubluminalWorldline) (κ t : ℝ) (x : E3) :
    SlowData :=
  slowData R₁ w κ t x

section SlowCharge

variable {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}

example (t : ℝ) (x : E3) :
    κ * t = κ * w.retardedTime t x + κ * ‖w.retardedSeparation t x‖ :=
  slowData_time t x

example (hκ : κ ≠ 0) (hx : x ≠ w.r t) (k : Fin 3) :
    (slowData R₁ w κ t x).Y k = (x - R₁ (κ * t)) k / ‖w.retardedSeparation t x‖ :=
  slowData_Y hκ hx k

example (hκ : κ ≠ 0) (k : Fin 3) :
    (slowData R₁ w κ t x).Vp k = deriv R₁ (κ * t) k :=
  slowData_Vp hκ k

example (hκ : κ ≠ 0) (k : Fin 3) :
    (slowData R₁ w κ t x).Ap k = deriv (deriv R₁) (κ * t) k :=
  slowData_Ap hκ k

example (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s)) (s : ℝ) :
    deriv w.r s = κ • deriv R₁ (κ * s) ∧
      deriv (deriv w.r) s = κ • κ • deriv (deriv R₁) (κ * s) :=
  deriv_slow_worldline hR hw s

end SlowCharge

section SlowCharge

variable {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}

example (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s)) (hx : x ≠ w.r t) (e : ℝ) (i : Fin 3) :
    (LienardWiechert.velocityField e w t x + LienardWiechert.accelerationField e w t x) i =
      e / (4 * π * ‖w.retardedSeparation t x‖ ^ 2) * (slowData R₁ w κ t x).lw i :=
  lw_slowData hR hw hx e i

end SlowCharge

section SlowCharge

variable {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}

example (hR : ContDiff ℝ ∞ R₁) (κ s : ℝ) :
    deriv (fun s => R₁ (κ * s)) s = κ • deriv R₁ (κ * s) ∧
      deriv (deriv fun s => R₁ (κ * s)) s = κ • κ • deriv (deriv R₁) (κ * s) :=
  deriv_slowPath_two hR κ s

example (hκ : κ ≠ 0) (hx : x ≠ w.r t) :
    ‖x - R₁ (κ * t)‖ = ‖w.retardedSeparation t x‖ * √(1 + (slowData R₁ w κ t x).z) :=
  norm_present_slowData hκ hx

example (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s)) (hκ : κ ≠ 0) (hx : x ≠ w.r t)
    (e : ℝ) (i : Fin 3) :
    electricOf (pointScalar e fun s => R₁ (κ * s)) (pointVector e fun s => R₁ (κ * s)) i (t, x) =
      e / (4 * π * ‖w.retardedSeparation t x‖ ^ 2) * (slowData R₁ w κ t x).darwin i :=
  darwin_slowData hR hw hκ hx e i

end SlowCharge

section SlowCharge

variable {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}

example (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s)) (hκ : κ ≠ 0) (hx : x ≠ w.r t)
    (e : ℝ) (i : Fin 3) :
    magneticOf (pointVector e fun s => R₁ (κ * s)) (t, x) i =
      e / (4 * π * ‖w.retardedSeparation t x‖ ^ 2) * (slowData R₁ w κ t x).darwinB i :=
  darwinB_slowData hR hw hκ hx e i

end SlowCharge

section SlowCharge

variable {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}

example (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s)) {V₁ A₂ A₃ : ℝ}
    (hV : ∀ s, ‖deriv R₁ s‖ ≤ V₁) (hA : ∀ s, ‖deriv (deriv R₁) s‖ ≤ A₂)
    (hA3 : ∀ s, ‖deriv^[3] R₁ s‖ ≤ A₃) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hκV : κ * V₁ ≤ 1 / 2) {δ ρ : ℝ}
    (hδ : 0 < δ) (hxδ : δ ≤ ‖x - R₁ (κ * t)‖) (hxρ : ‖x - R₁ (κ * t)‖ ≤ ρ) :
    x ≠ w.r t ∧ 2 * δ / 3 ≤ ‖w.retardedSeparation t x‖ ∧
      slowData R₁ w κ t x ∈ SlowData.admissible (2 * ρ + V₁ + A₂ + 4 * ρ ^ 2 * A₃ + 2 * ρ * A₃)
        (δ / (2 * ρ)) :=
  slowData_admissible hR hw hV hA hA3 hκ hκ1 hκV hδ hxδ hxρ

end SlowCharge

example {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3} (hR : ContDiff ℝ ∞ R₁)
    (hw : ∀ s, w.r s = R₁ (κ * s)) (hx : x ≠ w.r t) (e : ℝ) (i : Fin 3) :
    crossProduct (WithLp.ofLp (w.retardedDirection t x))
        (WithLp.ofLp (LienardWiechert.velocityField e w t x +
          LienardWiechert.accelerationField e w t x)) i =
      e / (4 * π * ‖w.retardedSeparation t x‖ ^ 2) * (slowData R₁ w κ t x).lwB i :=
  lwB_slowData hR hw hx e i

example (e : ℝ) {R₁ : ℝ → E3} (hR : ContDiff ℝ ∞ R₁) {V₁ A₂ A₃ : ℝ} (hV : ∀ s, ‖deriv R₁ s‖ ≤ V₁)
    (hA : ∀ s, ‖deriv (deriv R₁) s‖ ≤ A₂) (hA3 : ∀ s, ‖deriv^[3] R₁ s‖ ≤ A₃) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) :
    ∃ C, ∀ κ, 0 < κ → κ ≤ 1 → κ * V₁ ≤ 1 / 2 → ∀ w : SubluminalWorldline,
      (∀ s, w.r s = R₁ (κ * s)) → ∀ (t : ℝ) (x : E3), δ ≤ ‖x - R₁ (κ * t)‖ →
        ‖x - R₁ (κ * t)‖ ≤ ρ → ∀ i : Fin 3,
          |(LienardWiechert.velocityField e w t x + LienardWiechert.accelerationField e w t x) i -
              electricOf (pointScalar e fun s => R₁ (κ * s)) (pointVector e fun s => R₁ (κ * s))
                i (t, x)| ≤ C * κ ^ 3 ∧
          |crossProduct (WithLp.ofLp (w.retardedDirection t x))
              (WithLp.ofLp (LienardWiechert.velocityField e w t x +
                LienardWiechert.accelerationField e w t x)) i -
              magneticOf (pointVector e fun s => R₁ (κ * s)) (t, x) i| ≤ C * κ ^ 2 :=
  lienardWiechert_sub_darwin e hR hV hA hA3 hδ hδρ

example {ι : Type*} (s : Finset ι) {φ : ι → ℝ × E3 → ℝ} {A : ι → Fin 3 → ℝ × E3 → ℝ} {p : ℝ × E3}
    (hφ : ∀ b ∈ s, DifferentiableAt ℝ (φ b) p) (hA : ∀ b ∈ s, ∀ k, DifferentiableAt ℝ (A b k) p)
    (v : E3) (i : Fin 3) :
    lorentzDensity (fun q => ∑ b ∈ s, φ b q) (fun k q => ∑ b ∈ s, A b k q) v i p =
      ∑ b ∈ s, lorentzDensity (φ b) (A b) v i p :=
  lorentzDensity_sum s hφ hA v i

example (v : E3) (u : Fin 3 → ℝ) {M : ℝ} (hu : ∀ k, |u k| ≤ M) (i : Fin 3) :
    |crossProduct (WithLp.ofLp v) u i| ≤ 2 * ‖v‖ * M :=
  abs_crossProduct_le v u hu i

example {N : ℕ} (m e : Fin N → ℝ) {R : Fin N → ℝ → E3} (hR : ∀ b, ContDiff ℝ ∞ (R b))
    {V₁ A₂ A₃ : ℝ} (hV : ∀ b s, ‖deriv (R b) s‖ ≤ V₁) (hA : ∀ b s, ‖deriv (deriv (R b)) s‖ ≤ A₂)
    (hA3 : ∀ b s, ‖deriv^[3] (R b) s‖ ≤ A₃) {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (a : Fin N) :
    ∃ C, ∀ κ, 0 < κ → κ ≤ 1 → κ * V₁ ≤ 1 / 2 → ∀ w : Fin N → SubluminalWorldline,
      (∀ b s, (w b).r s = R b (κ * s)) → ∀ t : ℝ,
      (∀ b c, b ≠ c → R b (κ * t) ≠ R c (κ * t)) →
      (∀ b, b ≠ a → δ ≤ ‖R a (κ * t) - R b (κ * t)‖ ∧ ‖R a (κ * t) - R b (κ * t)‖ ≤ ρ) →
      ∀ i : Fin 3,
        |(∑ b ∈ ({a}ᶜ : Finset (Fin N)), e a *
            ((LienardWiechert.velocityField (e b) (w b) t (R a (κ * t)) +
                LienardWiechert.accelerationField (e b) (w b) t (R a (κ * t))) i +
              crossProduct (WithLp.ofLp (deriv (fun s => R a (κ * s)) t))
                (crossProduct (WithLp.ofLp ((w b).retardedDirection t (R a (κ * t))))
                  (WithLp.ofLp (LienardWiechert.velocityField (e b) (w b) t (R a (κ * t)) +
                    LienardWiechert.accelerationField (e b) (w b) t (R a (κ * t))))) i)) -
          (Mechanics.eulerLagrange (darwinLagrangian m e) (fun s b => R b (κ * s)) t
              (Pi.single a (EuclideanSpace.single i 1)) +
            deriv (fun s => m a * (1 + ‖deriv (fun s => R a (κ * s)) s‖ ^ 2 / 2) *
              deriv (fun s => R a (κ * s)) s i) t)| ≤ C * κ ^ 3 :=
  force_eq_darwinLagrangian m e hR hV hA hA3 hδ hδρ a

example :
    Fin 2 → ℝ → E3 :=
  oscillatingPaths

example (b : Fin 2) :
    ContDiff ℝ ∞ (oscillatingPaths b) :=
  contDiff_oscillatingPaths b

example (b : Fin 2) (s : ℝ) :
    ‖deriv (oscillatingPaths b) s‖ ≤ 1 ∧ ‖deriv (deriv (oscillatingPaths b)) s‖ ≤ 1 ∧
      ‖deriv^[3] (oscillatingPaths b) s‖ ≤ 1 :=
  norm_deriv_oscillatingPaths_le b s

example (s : ℝ) :
    5 ≤ ‖oscillatingPaths 0 s - oscillatingPaths 1 s‖ ∧
      ‖oscillatingPaths 0 s - oscillatingPaths 1 s‖ ≤ 6 :=
  norm_sub_oscillatingPaths s

example (m e : Fin 2 → ℝ) :
    ∃ C, ∀ κ, 0 < κ → κ ≤ 1 / 2 → ∀ w : Fin 2 → SubluminalWorldline,
      (∀ b s, (w b).r s = oscillatingPaths b (κ * s)) → ∀ (t : ℝ) (i : Fin 3),
        |(∑ b ∈ ({0}ᶜ : Finset (Fin 2)), e 0 *
            ((LienardWiechert.velocityField (e b) (w b) t (oscillatingPaths 0 (κ * t)) +
                LienardWiechert.accelerationField (e b) (w b) t (oscillatingPaths 0 (κ * t))) i +
              crossProduct (WithLp.ofLp (deriv (fun s => oscillatingPaths 0 (κ * s)) t))
                (crossProduct (WithLp.ofLp ((w b).retardedDirection t
                    (oscillatingPaths 0 (κ * t))))
                  (WithLp.ofLp (LienardWiechert.velocityField (e b) (w b) t
                      (oscillatingPaths 0 (κ * t)) +
                    LienardWiechert.accelerationField (e b) (w b) t
                      (oscillatingPaths 0 (κ * t))))) i)) -
          (Mechanics.eulerLagrange (darwinLagrangian m e)
              (fun s b => oscillatingPaths b (κ * s)) t
              (Pi.single 0 (EuclideanSpace.single i 1)) +
            deriv (fun s => m 0 * (1 + ‖deriv (fun s => oscillatingPaths 0 (κ * s)) s‖ ^ 2 / 2) *
              deriv (fun s => oscillatingPaths 0 (κ * s)) s i) t)| ≤ C * κ ^ 3 :=
  force_eq_darwinLagrangian_example m e

end ProjectAinos.Electrodynamics

end DarwinPointCharge
