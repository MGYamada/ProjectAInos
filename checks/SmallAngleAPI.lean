/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.Mechanics.Scattering.SmallAngleExpansion

/-! Typed contracts for small-angle scattering: the remainder of a first-order
expansion uniformly on a compact set of parameters, the radicand in the
variable `u = ρ/r` with its factorization at the closest approach, the motion,
the angle as an integral over `0 ≤ ψ ≤ π/2`, the turning point as a smooth
function of the parameters, and the expansion of the angle of deflection in
the strength of the field with the remainder. These examples use default
elaborator options. -/

open ProjectAInos ProjectAInos.Mechanics ProjectAInos.Mechanics.Scattering
open ProjectAInos.Mechanics.Scattering.SmallAngle ProjectAInos.Mechanics.OneDim
open ProjectAInos.SmoothAlgebra
open Set Filter MeasureTheory
open scoped Real Topology

noncomputable section

section SecondOrderBound

open Variational

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

example {f f' f'' : ℝ → ℝ} {δ M : ℝ}
    (hf : ∀ x ∈ Icc (-δ) δ, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (-δ) δ, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc (-δ) δ, |f'' x| ≤ M) {ε : ℝ} (hε : |ε| ≤ δ) :
    |f ε - f 0 - ε * f' 0| ≤ M * ε ^ 2 :=
  abs_sub_sub_le_of_abs_le hf hf' hM hε

example {Q : Type*} [TopologicalSpace Q] {K : Set Q}
    (hK : IsCompact K) {U : Set (ℝ × Q)} (hU : IsOpen U) (h : ∀ l ∈ K, ((0 : ℝ), l) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ → (ε, l) ∈ U :=
  exists_pos_forall_abs_le_mem hK hU h

example {f : ℝ × Q → ℝ} {K : Set Q} (hK : IsCompact K)
    (hf : ∀ l ∈ K, ContDiffAt ℝ 2 f (0, l)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ →
      |f (ε, l) - f (0, l) - ε * deriv (fun e => f (e, l)) 0| ≤ M * ε ^ 2 :=
  exists_second_order_bound hK hf

end SecondOrderBound

section OneVariable

open scoped ContDiff

variable {f : ℝ → ℝ} {ρ vinf ε c : ℝ}

example (f : ℝ → ℝ) (p : ℝ × ℝ) :
    radicand f p =
      1 - p.2 ^ 2 - p.1 * f p.2 := rfl

example (f : ℝ → ℝ) (c u : ℝ) :
    ratio f c u =
      dividedDifference f (c, u) / (c + u) := rfl

example (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (radicand f) :=
  contDiff_radicand hf

example (hf : ContDiff ℝ ∞ f) {ε c : ℝ} (hc : radicand f (ε, c) = 0) {u : ℝ}
    (hcu : c + u ≠ 0) :
    radicand f (ε, u) = (c ^ 2 - u ^ 2) * (1 + ε * ratio f c u) :=
  radicand_eq hf hc hcu

example (hf : ContDiff ℝ ∞ f) {c u : ℝ} (hcu : c + u ≠ 0) (hne : c - u ≠ 0) :
    ratio f c u = (f c - f u) / (c ^ 2 - u ^ 2) :=
  ratio_eq hf hcu hne

example (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => ratio f q.1 q.2) {q : ℝ × ℝ | q.1 + q.2 ≠ 0} :=
  contDiffOn_ratio hf

example (hf : ContDiff ℝ ∞ f) :
    ContinuousOn (fun ψ => ratio f 1 (Real.sin ψ)) (Icc 0 (π / 2)) :=
  continuousOn_ratio_sin hf

example (hf : ContDiff ℝ ∞ f) {ψ : ℝ} (hψ : ψ ∈ Ioo (0 : ℝ) (π / 2)) :
    HasDerivAt (fun x => ratio f 1 (Real.sin x) * (Real.sin x * Real.cos x))
      (ratio f 1 (Real.sin ψ) - Real.sin ψ * deriv f (Real.sin ψ)) ψ :=
  hasDerivAt_ratio_mul hf hψ

example (hf : ContDiff ℝ ∞ f) :
    ∫ ψ in (0 : ℝ)..π / 2, ratio f 1 (Real.sin ψ) =
      ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * deriv f (Real.sin ψ) :=
  integral_ratio_eq hf

example {ε c : ℝ} (h : IsClosest f ε c) : 0 < c := h.pos

example {ε c : ℝ} (h : IsClosest f ε c) : radicand f (ε, c) = 0 := h.radicand_eq_zero

example {ε c : ℝ} (h : IsClosest f ε c) {u : ℝ} (hu : u ∈ Icc 0 c) :
    0 < 1 + ε * ratio f c u := h.factor_pos u hu

example (f : ℝ → ℝ) :
    IsClosest f 0 1 :=
  isClosest_zero f

example (hf : ContDiff ℝ ∞ f) {ε c : ℝ} (h : IsClosest f ε c) {u : ℝ}
    (hu : u ∈ Ico 0 c) :
    0 < radicand f (ε, u) :=
  IsClosest.radicand_pos hf h hu

example (hf : ContDiff ℝ ∞ f) {ε c c' : ℝ} (h : IsClosest f ε c)
    (h' : IsClosest f ε c') :
    c = c' :=
  IsClosest.unique hf h h'

example (f : ℝ → ℝ) (ρ vinf ε r : ℝ) :
    speedSq f ρ vinf ε r =
      vinf ^ 2 * radicand f (ε, ρ / r) := rfl

example (f : ℝ → ℝ) (ρ vinf ε c r : ℝ) :
    factor f ρ vinf ε c r =
      vinf ^ 2 * (c / r) * (c + ρ / r) * (1 + ε * ratio f c (ρ / r)) := rfl

example (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (vinf : ℝ) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) {r : ℝ} (hr : 0 < r) :
    speedSq f ρ vinf ε r = (r - ρ / c) * factor f ρ vinf ε c r :=
  speedSq_eq hf hρ vinf hc0 hc hr

example (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiffOn ℝ ∞ (fun u => ratio f c u) {u : ℝ | c + u ≠ 0} :=
  contDiffOn_ratio_right hf c

example (hf : ContDiff ℝ ∞ f) (hc0 : 0 < c) :
    ContinuousOn (fun u => ratio f c u) (Icc 0 c) :=
  continuousOn_ratio_right hf hc0

example (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hv : 0 < vinf) (hc0 : 0 < c)
    (hpos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u) :
    ∃ C : ℝ, IsFactor (factor f ρ vinf ε c) (ρ / c) C :=
  exists_isFactor hf hρ hv hc0 hpos

example {ψ : ℝ} (hψ : ψ ∈ Ioo (0 : ℝ) (π / 2)) :
    Real.sin ψ ∈ Ioo (0 : ℝ) 1 :=
  sin_mem_Ioo hψ

example {ψ : ℝ} (hψ : ψ ∈ Ioo (0 : ℝ) (π / 2)) :
    0 < Real.cos ψ :=
  cos_pos_of_mem_Ioo hψ

example (b : ℝ) {ψ : ℝ} (hs : Real.sin ψ ≠ 0) :
    HasDerivAt (fun x => b / Real.sin x) (-(b * Real.cos ψ / Real.sin ψ ^ 2)) ψ :=
  hasDerivAt_div_sin b hs

example {b : ℝ} (hb : 0 < b) :
    (fun ψ => b / Real.sin ψ) '' Ioo 0 (π / 2) = Ioi b :=
  image_div_sin hb

example {b : ℝ} (hb : 0 < b) :
    InjOn (fun ψ => b / Real.sin ψ) (Ioo 0 (π / 2)) :=
  injOn_div_sin hb

example {b : ℝ} (hb : 0 < b) (G : ℝ → ℝ) :
    EqOn (fun ψ => |(-(b * Real.cos ψ / Real.sin ψ ^ 2))| • G (b / Real.sin ψ))
      (fun ψ => b * Real.cos ψ / Real.sin ψ ^ 2 * G (b / Real.sin ψ)) (Ioo 0 (π / 2)) :=
  abs_deriv_div_sin_smul hb G

example {b : ℝ} (hb : 0 < b) (G : ℝ → ℝ) :
    ∫ r in Ioi b, G r =
      ∫ ψ in Ioo (0 : ℝ) (π / 2), b * Real.cos ψ / Real.sin ψ ^ 2 * G (b / Real.sin ψ) :=
  integral_Ioi_eq_integral_sin hb G

example {b : ℝ} (hb : 0 < b) (G : ℝ → ℝ) :
    IntegrableOn G (Ioi b) ↔ IntegrableOn
      (fun ψ => b * Real.cos ψ / Real.sin ψ ^ 2 * G (b / Real.sin ψ)) (Ioo (0 : ℝ) (π / 2)) :=
  integrableOn_Ioi_iff_integrableOn_sin hb G

example (f : ℝ → ℝ) (ε c ψ : ℝ) :
    angleKernel f ε c ψ =
      1 / √(1 + ε * ratio f c (c * Real.sin ψ)) := rfl

example (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hv : 0 < vinf) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) {ψ : ℝ} (hψ : ψ ∈ Ioo (0 : ℝ) (π / 2)) :
    ρ / c * Real.cos ψ / Real.sin ψ ^ 2 *
        angleDensity (ρ * vinf) (speedSq f ρ vinf ε) (ρ / c / Real.sin ψ) =
      angleKernel f ε c ψ :=
  angleDensity_div_sin hf hρ hv hc0 hc hψ

example (hc0 : 0 < c) {ψ : ℝ} (hψ : ψ ∈ Icc (0 : ℝ) (π / 2)) :
    c * Real.sin ψ ∈ Icc 0 c :=
  mul_sin_mem_Icc hc0 hψ

example (hf : ContDiff ℝ ∞ f) (hc0 : 0 < c)
    (hpos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u) :
    ContinuousOn (angleKernel f ε c) (Icc 0 (π / 2)) :=
  continuousOn_angleKernel hf hc0 hpos

example (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hv : 0 < vinf) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) (hpos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u) :
    IntegrableOn (angleDensity (ρ * vinf) (speedSq f ρ vinf ε)) (Ioi (ρ / c)) ∧
      ∫ r in Ioi (ρ / c), angleDensity (ρ * vinf) (speedSq f ρ vinf ε) r =
        ∫ ψ in (0 : ℝ)..π / 2, angleKernel f ε c ψ :=
  integral_angleDensity hf hρ hv hc0 hc hpos

example (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hv : 0 < vinf) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) (hpos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u) :
    deflectionAngle (ρ * vinf) (speedSq f ρ vinf ε) (ρ / c) =
      π - 2 * ∫ ψ in (0 : ℝ)..π / 2, angleKernel f ε c ψ :=
  deflectionAngle_eq hf hρ hv hc0 hc hpos

example (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hv : 0 < vinf) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) (hpos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u) {C : ℝ}
    (h : IsFactor (factor f ρ vinf ε c) (ρ / c) C) :
    Tendsto (angle (factor f ρ vinf ε c) (ρ / c) (ρ * vinf)) atTop
      (𝓝 (∫ ψ in (0 : ℝ)..π / 2, angleKernel f ε c ψ)) :=
  tendsto_angle_atTop hf hρ hv hc0 hc hpos h

example (hf : ContDiff ℝ ∞ f) (ρ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r => f (ρ / r)) (deriv f (ρ / r) * -(ρ / r ^ 2)) r :=
  hasDerivAt_comp_div hf ρ hr

example (hf : ContDiff ℝ ∞ f) (ρ vinf ε : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (speedSq f ρ vinf ε)
      (vinf ^ 2 * (2 * ρ ^ 2 / r ^ 3 + ε * (deriv f (ρ / r) * (ρ / r ^ 2)))) r :=
  hasDerivAt_speedSq hf ρ vinf ε hr

example (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0) (ρ vinf ε : ℝ) :
    Tendsto (speedSq f ρ vinf ε) atTop (𝓝 (vinf ^ 2)) :=
  tendsto_speedSq_atTop hf hf0 ρ vinf ε

example (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0) (hρ : 0 < ρ)
    (hv : 0 < vinf) (hc0 : 0 < c) (hc : radicand f (ε, c) = 0) {C : ℝ}
    (h : IsFactor (factor f ρ vinf ε c) (ρ / c) C) :
    Tendsto (radialVelocity (factor f ρ vinf ε c) (ρ / c)) atTop (𝓝 vinf) :=
  tendsto_radialVelocity_atTop hf hf0 hρ hv hc0 hc h

example (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) {C : ℝ} (h : IsFactor (factor f ρ vinf ε c) (ρ / c) C)
    (t : ℝ) :
    HasDerivAt (velocity (factor f ρ vinf ε c) (ρ / c) (ρ * vinf))
      ((-deriv (fun r => vinf ^ 2 / 2 * (ε * f (ρ / r)))
          (radius (factor f ρ vinf ε c) (ρ / c) t)) •
        (Real.cos (angle (factor f ρ vinf ε c) (ρ / c) (ρ * vinf) t),
          Real.sin (angle (factor f ρ vinf ε c) (ρ / c) (ρ * vinf) t))) t :=
  hasDerivAt_velocity hf hρ hc0 hc h t

example (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) :
    ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * deriv f (Real.sin ψ) =
      -ρ * ∫ r in Ioi ρ, deriv (fun r => f (ρ / r)) r / √(r ^ 2 - ρ ^ 2) :=
  integral_sin_mul_deriv_eq hf hρ

end OneVariable

section Family

open scoped ContDiff

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
variable {g : Q × ℝ → ℝ} {J : Set (ℝ × Q)} {c : ℝ × Q → ℝ}

example (g : Q × ℝ → ℝ) (w : (ℝ × Q) × ℝ) :
    familyRadicand g w =
      radicand (fun u => g (w.1.2, u)) (w.1.1, w.2) := rfl

example (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (familyRadicand g) :=
  contDiff_familyRadicand hg

example (hg : ContDiff ℝ ∞ g) (s : ℝ × Q) (x : ℝ) :
    slopeOf (familyRadicand g) (s, x) = -2 * x - s.1 * slopeOf g (s.2, x) :=
  slopeOf_familyRadicand hg s x

example (h : IsTurning g J c) : IsOpen J := h.isOpen

example (h : IsTurning g J c) : ContDiffOn ℝ ∞ c J := h.contDiffOn

example (h : IsTurning g J c) {s : ℝ × Q} (hs : s ∈ J) : 0 < c s := h.pos s hs

example (h : IsTurning g J c) {s : ℝ × Q} (hs : s ∈ J) :
    radicand (fun u => g (s.2, u)) (s.1, c s) = 0 := h.radicand_eq_zero s hs

example (h : IsTurning g J c) {l : Q} (hl : ((0 : ℝ), l) ∈ J) :
    c (0, l) = 1 :=
  IsTurning.eq_one h hl

example :
    IsTurning (fun _ : Q × ℝ => (0 : ℝ)) univ fun _ => 1 :=
  isTurning_zero

example (hg : ContDiff ℝ ∞ g) (l₀ : Q) :
    ∃ (J : Set (ℝ × Q)) (c : ℝ × Q → ℝ), IsTurning g J c ∧ ((0 : ℝ), l₀) ∈ J :=
  exists_isTurning hg l₀

example [ProperSpace Q] (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun q : Q × ℝ × ℝ =>
      dividedDifference (fun y => g (q.1, y)) (q.2.1, q.2.2) :=
  contDiff_dividedDifference_family hg

example (hg : ContDiff ℝ ∞ g) :
    ContDiffOn ℝ ∞ (fun q : Q × ℝ × ℝ => ratio (fun y => g (q.1, y)) q.2.1 q.2.2)
      {q : Q × ℝ × ℝ | q.2.1 + q.2.2 ≠ 0} :=
  contDiffOn_ratio_family hg

example (g : Q × ℝ → ℝ) (c : ℝ × Q → ℝ) (p : (ℝ × Q) × ℝ) :
    kernel g c p =
      angleKernel (fun u => g (p.1.2, u)) p.1.1 (c p.1) p.2 := rfl

example (g : Q × ℝ → ℝ) (c : ℝ × Q → ℝ) (s : ℝ × Q) :
    halfAngle g c s =
      ∫ ψ in (0 : ℝ)..π / 2, kernel g c (s, ψ) := rfl

example (J : Set (ℝ × Q)) :
    turningBase J =
      Prod.fst ⁻¹' J ∩ (fun p : (ℝ × Q) × ℝ => Real.sin p.2) ⁻¹' Ioi (-1) := rfl

example (g : Q × ℝ → ℝ) (J : Set (ℝ × Q)) (c : ℝ × Q → ℝ) :
    kernelDomain g J c =
      turningBase J ∩ (fun p : (ℝ × Q) × ℝ =>
      1 + p.1.1 * ratio (fun u => g (p.1.2, u)) (c p.1) (c p.1 * Real.sin p.2)) ⁻¹' Ioi 0 := rfl

example (hJ : IsOpen J) :
    IsOpen (turningBase J) :=
  isOpen_turningBase hJ

example (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) :
    ContDiffOn ℝ ∞ (fun p : (ℝ × Q) × ℝ =>
      ratio (fun u => g (p.1.2, u)) (c p.1) (c p.1 * Real.sin p.2)) (turningBase J) :=
  contDiffOn_ratio_turning hg h

example (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) :
    IsOpen (kernelDomain g J c) :=
  isOpen_kernelDomain hg h

example (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) :
    ContDiffOn ℝ ∞ (kernel g c) (kernelDomain g J c) :=
  contDiffOn_kernel hg h

example {l : Q} (hl : ((0 : ℝ), l) ∈ J) {ψ : ℝ}
    (hψ : ψ ∈ uIcc (0 : ℝ) (π / 2)) :
    (((0 : ℝ), l), ψ) ∈ kernelDomain g J c :=
  mem_kernelDomain_zero hl hψ

example (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) {l : Q}
    (hl : ((0 : ℝ), l) ∈ J) :
    ContDiffAt ℝ ∞ (halfAngle g c) (0, l) :=
  contDiffAt_halfAngle hg h hl

example (g : Q × ℝ → ℝ) (c : ℝ × Q → ℝ) (l : Q) :
    halfAngle g c (0, l) = π / 2 :=
  halfAngle_zero g c l

example (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) {l : Q}
    (hl : ((0 : ℝ), l) ∈ J) {ψ : ℝ} (hψ : ψ ∈ uIcc (0 : ℝ) (π / 2)) :
    HasDerivAt (fun e => kernel g c ((e, l), ψ))
      (-(1 / 2) * ratio (fun u => g (l, u)) 1 (Real.sin ψ)) 0 :=
  hasDerivAt_kernel hg h hl hψ

example (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) {l : Q}
    (hl : ((0 : ℝ), l) ∈ J) :
    HasDerivAt (fun e => halfAngle g c (e, l))
      (-(1 / 2) * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ)) 0 :=
  hasDerivAt_halfAngle hg h hl

example (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) {K : Set Q}
    (hK : IsCompact K) (hKJ : ∀ l ∈ K, ((0 : ℝ), l) ∈ J) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ → ∀ ψ ∈ Icc (0 : ℝ) (π / 2),
      ((ε, l), ψ) ∈ kernelDomain g J c :=
  exists_forall_mem_kernelDomain hg h hK hKJ

example (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) {K : Set Q}
    (hK : IsCompact K) (hKJ : ∀ l ∈ K, ((0 : ℝ), l) ∈ J) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ →
      IsClosest (fun u => g (l, u)) ε (c (ε, l)) ∧
      |π - 2 * (∫ ψ in (0 : ℝ)..π / 2, angleKernel (fun u => g (l, u)) ε (c (ε, l)) ψ) -
        ε * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ)| ≤ M * ε ^ 2 :=
  IsTurning.exists_abs_sub_le hg h hK hKJ

example (hg : ContDiff ℝ ∞ g) {K : Set Q} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ → ∃ c : ℝ,
      IsClosest (fun u => g (l, u)) ε c ∧
      |π - 2 * (∫ ψ in (0 : ℝ)..π / 2, angleKernel (fun u => g (l, u)) ε c ψ) -
        ε * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ)| ≤ M * ε ^ 2 :=
  exists_abs_angle_sub_le hg hK

example (hg : ContDiff ℝ ∞ g) {K : Set Q} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ → ∃ c : ℝ,
      IsClosest (fun u => g (l, u)) ε c ∧ ∀ ρ vinf : ℝ, 0 < ρ → 0 < vinf →
        (∃ C : ℝ, IsFactor (factor (fun u => g (l, u)) ρ vinf ε c) (ρ / c) C) ∧
        |deflectionAngle (ρ * vinf) (speedSq (fun u => g (l, u)) ρ vinf ε) (ρ / c) -
          ε * (-ρ * ∫ r in Ioi ρ, deriv (fun r => g (l, ρ / r)) r / √(r ^ 2 - ρ ^ 2))| ≤
            M * ε ^ 2 :=
  exists_abs_deflectionAngle_sub_le hg hK

example {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ ε : ℝ, |ε| ≤ δ → ∃ c : ℝ, IsClosest f ε c ∧
      ∀ ρ vinf : ℝ, 0 < ρ → 0 < vinf →
        (∃ C : ℝ, IsFactor (factor f ρ vinf ε c) (ρ / c) C) ∧
        |deflectionAngle (ρ * vinf) (speedSq f ρ vinf ε) (ρ / c) -
          ε * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * deriv f (Real.sin ψ)| ≤ M * ε ^ 2 :=
  exists_abs_deflectionAngle_sub_le_of_contDiff hf

example (a vinf : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    speedSq (fun u => u) ρ vinf (2 * a / ρ) = Coulomb.speedSq a ρ vinf :=
  speedSq_id a vinf hρ

example :
    ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * deriv (fun u : ℝ => u) (Real.sin ψ) = 1 :=
  integral_sin_mul_deriv_id

example {a ρ c : ℝ} (hρ : 0 < ρ)
    (h : IsClosest (fun u => u) (2 * a / ρ) c) :
    ρ / c = Coulomb.closest a ρ :=
  IsClosest.div_eq_closest hρ h

example :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ a ρ : ℝ, 0 < ρ → |2 * a / ρ| ≤ δ →
      |Coulomb.deflection a ρ - 2 * a / ρ| ≤ M * (2 * a / ρ) ^ 2 :=
  exists_abs_coulomb_deflection_sub_le

example (U : ℝ → ℝ) (m ρ vinf r : ℝ) :
    potentialSpeedSq U m ρ vinf r =
      vinf ^ 2 - 2 * U r / m - (ρ * vinf) ^ 2 / r ^ 2 := rfl

example (w : ℝ → ℝ) (n : ℕ) (q : (ℝ × ℝ) × ℝ) :
    scaledPotential w n q =
      2 * q.1.2 * (q.2 ^ n * w (q.1.1 * q.2)) := rfl

example {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (n : ℕ) :
    ContDiff ℝ ∞ (scaledPotential w n) :=
  contDiff_scaledPotential hw n

example {ρ : ℝ} (hρ : ρ ≠ 0) (r : ℝ) :
    1 / ρ * (ρ / r) = 1 / r :=
  one_div_mul_div hρ r

example (w : ℝ → ℝ) (n : ℕ) (ρ r : ℝ) :
    (ρ / r) ^ n * w (1 / r) = ρ ^ n * ((1 / r) ^ n * w (1 / r)) :=
  div_pow_mul_eq w n ρ r

example (w : ℝ → ℝ) (n : ℕ) {m ρ vinf : ℝ} (hm : m ≠ 0) (hρ : ρ ≠ 0)
    (hvinf : vinf ≠ 0) (ε : ℝ) :
    speedSq (fun u => scaledPotential w n ((1 / ρ, 1 / (m * vinf ^ 2)), u)) ρ vinf
        (ε / ρ ^ n) =
      potentialSpeedSq (fun r => ε * ((1 / r) ^ n * w (1 / r))) m ρ vinf :=
  speedSq_scaledPotential w n hm hρ hvinf ε

example {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (n : ℕ)
    {m ρ₁ v₁ : ℝ} (hm : 0 < m) (hρ₁ : 0 < ρ₁) (hv₁ : 0 < v₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ ρ vinf ε : ℝ, ρ₁ ≤ ρ → v₁ ≤ vinf → |ε / ρ ^ n| ≤ δ →
      ∃ (r₀ C : ℝ) (W : ℝ → ℝ), 0 < r₀ ∧ IsFactor W r₀ C ∧
        (∀ r, r₀ ≤ r → potentialSpeedSq (fun r => ε * ((1 / r) ^ n * w (1 / r))) m ρ vinf r =
          (r - r₀) * W r) ∧
        |deflectionAngle (ρ * vinf)
            (potentialSpeedSq (fun r => ε * ((1 / r) ^ n * w (1 / r))) m ρ vinf) r₀ -
          -(2 * ρ / (m * vinf ^ 2)) * ∫ r in Ioi ρ,
            deriv (fun r => ε * ((1 / r) ^ n * w (1 / r))) r / √(r ^ 2 - ρ ^ 2)| ≤
              M * (ε / ρ ^ n) ^ 2 :=
  exists_abs_deflectionAngle_potential_sub_le hw n hm hρ₁ hv₁

end Family
