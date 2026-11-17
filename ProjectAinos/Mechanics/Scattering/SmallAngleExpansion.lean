/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Scattering.SmallAngle
public import ProjectAinos.Mechanics.Scattering.Coulomb
public import ProjectAinos.Mechanics.OneDimension.WellFamily
public import ProjectAinos.Variational.IntervalParameter
public import ProjectAinos.Variational.SecondOrderBound

/-!
# The expansion of the angle of deflection in the strength of the field

Landau–Lifshitz §20 with an estimate of the remainder. The potential profile
`g(l, u)` is smooth in the finite-dimensional parameter `l` and in `u = ρ/r`.
For physical asymptotic data, the profile represents the potential relative
to its value at infinity: `ε g(l, ρ/r) = 2(U(r) − U(∞))/m v∞²`.

* `IsTurning`: a positive zero `c(ε, l)` of the radicand that is a smooth
  function of the parameters on an open set; `exists_isTurning`: one exists
  near every `(0, l₀)`, by the implicit function theorem, with `c(0, l) = 1`.
* `halfAngle`: the angle from the closest approach to infinity as a function
  of `(ε, l)`. It is smooth at `(0, l)` (`contDiffAt_halfAngle`) and its
  derivative in `ε` there is `−½ ∫₀^{π/2} sin ψ ∂g/∂u(l, sin ψ) dψ`
  (`hasDerivAt_halfAngle`).
* `exists_abs_deflectionAngle_sub_le`: for `l` in a compact set there are
  `δ > 0` and `M` such that for `|ε| ≤ δ` the closest approach exists, the
  motion exists, and the angle of deflection differs from
  `−ρ ε ∫_ρ^∞ (d/dr) g(l, ρ/r) dr/√(r² − ρ²)`, which is (20.3), by at most
  `M ε²`.
* `exists_abs_deflectionAngle_potential_sub_le`: the same for the potential
  energy `U(r) = ε r⁻ⁿ w(1/r)` of a particle of mass `m`, uniformly for
  `ρ ≥ ρ₁` and `v∞ ≥ v₁`, with the remainder `M (ε/ρⁿ)²`.
* `exists_abs_coulomb_deflection_sub_le`: the Coulomb field as an instance,
  `|χ − 2a/ρ| ≤ M (2a/ρ)²`.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real ContDiff Topology

namespace ProjectAinos.Mechanics.Scattering.SmallAngle

open SmoothAlgebra OneDim

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {g : Q × ℝ → ℝ}

/-- `h(ε, l, u) = 1 − u² − ε g(l, u)` as a function of the parameters `(ε, l)`
and of `u`. -/
def familyRadicand (g : Q × ℝ → ℝ) (w : (ℝ × Q) × ℝ) : ℝ :=
  radicand (fun u => g (w.1.2, u)) (w.1.1, w.2)

theorem contDiff_familyRadicand (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (familyRadicand g) := by
  have e : familyRadicand g = fun w : (ℝ × Q) × ℝ => 1 - w.2 ^ 2 - w.1.1 * g (w.1.2, w.2) := rfl
  rw [e]
  exact (contDiff_const.sub (contDiff_snd.pow 2)).sub
    ((by fun_prop : ContDiff ℝ ∞ fun w : (ℝ × Q) × ℝ => w.1.1).mul
      (hg.comp (by fun_prop : ContDiff ℝ ∞ fun w : (ℝ × Q) × ℝ => (w.1.2, w.2))))

theorem slopeOf_familyRadicand (hg : ContDiff ℝ ∞ g) (s : ℝ × Q) (x : ℝ) :
    slopeOf (familyRadicand g) (s, x) = -2 * x - s.1 * slopeOf g (s.2, x) := by
  have h1 := hasDerivAt_slice (contDiff_familyRadicand hg) s x
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun y => familyRadicand g (s, y))
      (0 - 2 * x - s.1 * slopeOf g (s.2, x)) x :=
    ((hasDerivAt_const x (1 : ℝ)).sub hsq).sub ((hasDerivAt_slice hg s.2 x).const_mul s.1)
  rw [h1.unique h2]
  ring

/-- A turning point for the parameters in an open set: a positive zero
`c(ε, l)` of the radicand that is a smooth function of the parameters. -/
structure IsTurning (g : Q × ℝ → ℝ) (J : Set (ℝ × Q)) (c : ℝ × Q → ℝ) : Prop where
  /-- The set of parameters is open. -/
  isOpen : IsOpen J
  /-- The turning point is a smooth function of the parameters. -/
  contDiffOn : ContDiffOn ℝ ∞ c J
  /-- The turning point is at a finite distance. -/
  pos : ∀ s ∈ J, 0 < c s
  /-- The radial velocity vanishes at the turning point. -/
  radicand_eq_zero : ∀ s ∈ J, radicand (fun u => g (s.2, u)) (s.1, c s) = 0

section Turning

variable {J : Set (ℝ × Q)} {c : ℝ × Q → ℝ}

/-- Without a field the turning point is at the impact parameter. -/
theorem IsTurning.eq_one (h : IsTurning g J c) {l : Q} (hl : ((0 : ℝ), l) ∈ J) :
    c (0, l) = 1 := by
  have h1 := h.radicand_eq_zero _ hl
  have h2 := h.pos _ hl
  simp only [radicand, zero_mul, sub_zero] at h1
  have h3 : (c (0, l) - 1) * (c (0, l) + 1) = 0 := by linear_combination (-1 : ℝ) * h1
  rcases mul_eq_zero.mp h3 with h4 | h4 <;> linarith

/-- For the field zero the turning point is the impact parameter for all
values of the parameters. -/
theorem isTurning_zero : IsTurning (fun _ : Q × ℝ => (0 : ℝ)) univ fun _ => 1 where
  isOpen := isOpen_univ
  contDiffOn := contDiffOn_const
  pos _ _ := one_pos
  radicand_eq_zero _ _ := by simp [radicand]

variable [FiniteDimensional ℝ Q]

/-- The turning point exists near every value of the parameter for a small
strength, by the implicit function theorem. -/
theorem exists_isTurning (hg : ContDiff ℝ ∞ g) (l₀ : Q) :
    ∃ (J : Set (ℝ × Q)) (c : ℝ × Q → ℝ), IsTurning g J c ∧ ((0 : ℝ), l₀) ∈ J := by
  have hd : slopeOf (familyRadicand g) (((0 : ℝ), l₀), (1 : ℝ)) ≠ 0 := by
    rw [slopeOf_familyRadicand hg]
    norm_num
  obtain ⟨J, ξ, hJ, hmem, hξ₀, hξ, hsol⟩ := exists_level_point_family (V := familyRadicand g)
    (contDiff_familyRadicand hg) (ℰ := fun _ => 0) contDiff_const (s₀ := ((0 : ℝ), l₀))
    (x₀ := 1) (by simp [familyRadicand, radicand]) hd
  have hopen : IsOpen (J ∩ ξ ⁻¹' Ioi 0) :=
    hξ.continuousOn.isOpen_inter_preimage hJ isOpen_Ioi
  refine ⟨J ∩ ξ ⁻¹' Ioi 0, ξ, ⟨hopen, hξ.mono inter_subset_left, fun s hs => hs.2,
    fun s hs => hsol s hs.1⟩, hmem, ?_⟩
  change (0 : ℝ) < ξ (0, l₀)
  rw [hξ₀]
  exact one_pos

/-! ### The integrand of the angle as a function of the parameters -/

omit [FiniteDimensional ℝ Q] in
theorem contDiff_dividedDifference_family [ProperSpace Q] (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun q : Q × ℝ × ℝ =>
      dividedDifference (fun y => g (q.1, y)) (q.2.1, q.2.2) := by
  have hF : ContDiff ℝ ∞ fun r : (Q × ℝ × ℝ) × ℝ =>
      slopeOf g (r.1.1, r.1.2.2 + r.2 * (r.1.2.1 - r.1.2.2)) :=
    (contDiff_slopeOf hg).comp (by fun_prop)
  have h := contDiff_infty_parametric_intervalIntegral hF 0 1
  have e : (fun q : Q × ℝ × ℝ => dividedDifference (fun y => g (q.1, y)) (q.2.1, q.2.2)) =
      fun q => ∫ t in (0 : ℝ)..1, slopeOf g (q.1, q.2.2 + t * (q.2.1 - q.2.2)) := by
    funext q
    rw [dividedDifference, deriv_slice hg q.1]
  rw [e]
  exact h

theorem contDiffOn_ratio_family (hg : ContDiff ℝ ∞ g) :
    ContDiffOn ℝ ∞ (fun q : Q × ℝ × ℝ => ratio (fun y => g (q.1, y)) q.2.1 q.2.2)
      {q : Q × ℝ × ℝ | q.2.1 + q.2.2 ≠ 0} :=
  (contDiff_dividedDifference_family hg).contDiffOn.div
    (by fun_prop : ContDiff ℝ ∞ fun q : Q × ℝ × ℝ => q.2.1 + q.2.2).contDiffOn fun _ hq => hq

/-- The integrand of the angle as a function of the parameters and `ψ`. -/
def kernel (g : Q × ℝ → ℝ) (c : ℝ × Q → ℝ) (p : (ℝ × Q) × ℝ) : ℝ :=
  angleKernel (fun u => g (p.1.2, u)) p.1.1 (c p.1) p.2

/-- The angle from the closest approach to infinity as a function of the
parameters. -/
def halfAngle (g : Q × ℝ → ℝ) (c : ℝ × Q → ℝ) (s : ℝ × Q) : ℝ :=
  ∫ ψ in (0 : ℝ)..π / 2, kernel g c (s, ψ)

/-- The parameters in `J` and the angles with `sin ψ ≠ −1`. -/
def turningBase (J : Set (ℝ × Q)) : Set ((ℝ × Q) × ℝ) :=
  Prod.fst ⁻¹' J ∩ (fun p : (ℝ × Q) × ℝ => Real.sin p.2) ⁻¹' Ioi (-1)

/-- The open set on which the integrand is smooth. -/
def kernelDomain (g : Q × ℝ → ℝ) (J : Set (ℝ × Q)) (c : ℝ × Q → ℝ) : Set ((ℝ × Q) × ℝ) :=
  turningBase J ∩ (fun p : (ℝ × Q) × ℝ =>
    1 + p.1.1 * ratio (fun u => g (p.1.2, u)) (c p.1) (c p.1 * Real.sin p.2)) ⁻¹' Ioi 0

omit [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] in
theorem isOpen_turningBase (hJ : IsOpen J) : IsOpen (turningBase J) :=
  (hJ.preimage continuous_fst).inter
    (isOpen_Ioi.preimage (Real.continuous_sin.comp continuous_snd))

theorem contDiffOn_ratio_turning (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) :
    ContDiffOn ℝ ∞ (fun p : (ℝ × Q) × ℝ =>
      ratio (fun u => g (p.1.2, u)) (c p.1) (c p.1 * Real.sin p.2)) (turningBase J) := by
  have hc1 : ContDiffOn ℝ ∞ (fun p : (ℝ × Q) × ℝ => c p.1) (turningBase J) :=
    h.contDiffOn.comp contDiffOn_fst fun p hp => hp.1
  have hl : ContDiffOn ℝ ∞ (fun p : (ℝ × Q) × ℝ => p.1.2) (turningBase J) :=
    (by fun_prop : ContDiff ℝ ∞ fun p : (ℝ × Q) × ℝ => p.1.2).contDiffOn
  have hpair : ContDiffOn ℝ ∞ (fun p : (ℝ × Q) × ℝ =>
      ((p.1.2, c p.1, c p.1 * Real.sin p.2) : Q × ℝ × ℝ)) (turningBase J) :=
    hl.prodMk (hc1.prodMk (hc1.mul (Real.contDiff_sin.comp contDiff_snd).contDiffOn))
  refine ContDiffOn.comp (g := fun q : Q × ℝ × ℝ => ratio (fun y => g (q.1, y)) q.2.1 q.2.2)
    (f := fun p : (ℝ × Q) × ℝ => ((p.1.2, c p.1, c p.1 * Real.sin p.2) : Q × ℝ × ℝ))
    (contDiffOn_ratio_family hg) hpair fun p hp => ?_
  have h1 := h.pos _ hp.1
  have h2 : (-1 : ℝ) < Real.sin p.2 := hp.2
  have h3 : 0 < c p.1 * (1 + Real.sin p.2) := mul_pos h1 (by linarith)
  change c p.1 + c p.1 * Real.sin p.2 ≠ 0
  nlinarith

theorem isOpen_kernelDomain (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) :
    IsOpen (kernelDomain g J c) := by
  have hb : ContinuousOn (fun p : (ℝ × Q) × ℝ =>
      1 + p.1.1 * ratio (fun u => g (p.1.2, u)) (c p.1) (c p.1 * Real.sin p.2))
      (turningBase J) :=
    continuousOn_const.add
      ((continuous_fst.comp continuous_fst).continuousOn.mul
        (contDiffOn_ratio_turning hg h).continuousOn)
  exact hb.isOpen_inter_preimage (isOpen_turningBase h.isOpen) isOpen_Ioi

theorem contDiffOn_kernel (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) :
    ContDiffOn ℝ ∞ (kernel g c) (kernelDomain g J c) := by
  have hb : ContDiffOn ℝ ∞ (fun p : (ℝ × Q) × ℝ =>
      1 + p.1.1 * ratio (fun u => g (p.1.2, u)) (c p.1) (c p.1 * Real.sin p.2))
      (kernelDomain g J c) :=
    contDiffOn_const.add
      ((by fun_prop : ContDiff ℝ ∞ fun p : (ℝ × Q) × ℝ => p.1.1).contDiffOn.mul
        ((contDiffOn_ratio_turning hg h).mono inter_subset_left))
  have e : kernel g c = fun p : (ℝ × Q) × ℝ =>
      1 / √(1 + p.1.1 * ratio (fun u => g (p.1.2, u)) (c p.1) (c p.1 * Real.sin p.2)) := rfl
  rw [e]
  exact contDiffOn_const.div (hb.sqrt fun p hp => (ne_of_gt hp.2))
    fun p hp => (Real.sqrt_pos.mpr hp.2).ne'

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] in
theorem mem_kernelDomain_zero {l : Q} (hl : ((0 : ℝ), l) ∈ J) {ψ : ℝ}
    (hψ : ψ ∈ uIcc (0 : ℝ) (π / 2)) : (((0 : ℝ), l), ψ) ∈ kernelDomain g J c := by
  rw [uIcc_of_le (by positivity)] at hψ
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 (by linarith [hψ.2, Real.pi_pos])
  refine ⟨⟨hl, ?_⟩, ?_⟩
  · change (-1 : ℝ) < Real.sin ψ
    linarith
  · change (0 : ℝ) < 1 + (0 : ℝ) * ratio (fun u => g (l, u)) (c (0, l)) (c (0, l) * Real.sin ψ)
    rw [zero_mul, add_zero]
    exact one_pos

/-- The angle is a smooth function of the strength and the parameter at the
strength zero. -/
theorem contDiffAt_halfAngle (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) {l : Q}
    (hl : ((0 : ℝ), l) ∈ J) : ContDiffAt ℝ ∞ (halfAngle g c) (0, l) := by
  have h1 := Variational.contDiffAt_parametric_intervalIntegral (E := ℝ × Q) (f := kernel g c)
    (U := kernelDomain g J c) (a := 0) (b := π / 2) (x₀ := ((0 : ℝ), l))
    (isOpen_kernelDomain hg h) (contDiffOn_kernel hg h)
    fun _ hψ => mem_kernelDomain_zero hl hψ
  exact h1

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] in
theorem halfAngle_zero (g : Q × ℝ → ℝ) (c : ℝ × Q → ℝ) (l : Q) :
    halfAngle g c (0, l) = π / 2 := by
  simp [halfAngle, kernel, angleKernel]

/-- The derivative of the integrand in the strength, at zero. -/
theorem hasDerivAt_kernel (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) {l : Q}
    (hl : ((0 : ℝ), l) ∈ J) {ψ : ℝ} (hψ : ψ ∈ uIcc (0 : ℝ) (π / 2)) :
    HasDerivAt (fun e => kernel g c ((e, l), ψ))
      (-(1 / 2) * ratio (fun u => g (l, u)) 1 (Real.sin ψ)) 0 := by
  have hmem : (((0 : ℝ), l), ψ) ∈ turningBase J := (mem_kernelDomain_zero (g := g) (c := c) hl hψ).1
  have hRd : DifferentiableAt ℝ (fun p : (ℝ × Q) × ℝ =>
      ratio (fun u => g (p.1.2, u)) (c p.1) (c p.1 * Real.sin p.2)) (((0 : ℝ), l), ψ) :=
    ((contDiffOn_ratio_turning hg h).contDiffAt
      ((isOpen_turningBase h.isOpen).mem_nhds hmem)).differentiableAt (by simp)
  have hline : HasDerivAt (fun e : ℝ => (((e, l), ψ) : (ℝ × Q) × ℝ))
      (((1 : ℝ), (0 : Q)), (0 : ℝ)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) l)).prodMk
      (hasDerivAt_const (0 : ℝ) ψ)
  have hR := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hRd.hasFDerivAt hline
  have hR : HasDerivAt (fun e : ℝ => ratio (fun u => g (l, u)) (c (e, l)) (c (e, l) * Real.sin ψ))
      (fderiv ℝ (fun p : (ℝ × Q) × ℝ =>
        ratio (fun u => g (p.1.2, u)) (c p.1) (c p.1 * Real.sin p.2)) ((0, l), ψ)
          ((1, 0), 0)) 0 := hR
  have hm : HasDerivAt
      (fun e : ℝ => 1 + e * ratio (fun u => g (l, u)) (c (e, l)) (c (e, l) * Real.sin ψ))
      (ratio (fun u => g (l, u)) 1 (Real.sin ψ)) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul hR).const_add 1
    refine h1.congr_deriv ?_
    simp [h.eq_one hl]
  have hval : (1 : ℝ) + 0 * ratio (fun u => g (l, u)) (c (0, l)) (c (0, l) * Real.sin ψ) = 1 := by
    ring
  have hsqrt := hm.sqrt (by rw [hval]; norm_num)
  have hinv := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div hsqrt
    (by rw [hval, Real.sqrt_one]; norm_num)
  refine hinv.congr_deriv ?_
  rw [hval, Real.sqrt_one]
  ring

/-- The derivative of the angle in the strength, at zero. -/
theorem hasDerivAt_halfAngle (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) {l : Q}
    (hl : ((0 : ℝ), l) ∈ J) :
    HasDerivAt (fun e => halfAngle g c (e, l))
      (-(1 / 2) * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ)) 0 := by
  have hmap : ContDiff ℝ 1 fun q : ℝ × ℝ => (((q.1, l), q.2) : (ℝ × Q) × ℝ) := by fun_prop
  have h1 := Variational.hasDerivAt_intervalIntegral_of_contDiffAt
    (F := fun q : ℝ × ℝ => kernel g c ((q.1, l), q.2))
    (D := fun ψ => -(1 / 2) * ratio (fun u => g (l, u)) 1 (Real.sin ψ)) (ε₀ := 0) (a := 0)
    (b := π / 2)
    (fun ψ hψ => ContDiffAt.comp (x := ((0 : ℝ), ψ)) (g := kernel g c)
      (f := fun q : ℝ × ℝ => (((q.1, l), q.2) : (ℝ × Q) × ℝ))
      (((contDiffOn_kernel hg h).contDiffAt ((isOpen_kernelDomain hg h).mem_nhds
        (mem_kernelDomain_zero hl hψ))).of_le (by simp)) hmap.contDiffAt)
    (fun ψ hψ => hasDerivAt_kernel hg h hl hψ)
  rw [intervalIntegral.integral_const_mul, integral_ratio_eq (contDiff_slice hg l),
    deriv_slice hg l] at h1
  exact h1

/-! ### The expansion, uniformly for the parameter in a compact set -/

/-- For the parameter in a compact set and a small strength the integrand is
defined for all `0 ≤ ψ ≤ π/2`. -/
theorem exists_forall_mem_kernelDomain (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) {K : Set Q}
    (hK : IsCompact K) (hKJ : ∀ l ∈ K, ((0 : ℝ), l) ∈ J) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ → ∀ ψ ∈ Icc (0 : ℝ) (π / 2),
      ((ε, l), ψ) ∈ kernelDomain g J c := by
  have hopen := isOpen_kernelDomain hg h
  have hU : IsOpen {s : ℝ × Q | ∀ ψ ∈ Icc (0 : ℝ) (π / 2), (s, ψ) ∈ kernelDomain g J c} := by
    refine isOpen_iff_mem_nhds.mpr fun s hs => ?_
    obtain ⟨S, W, hS, _, hsS, hKW, hSW⟩ := generalized_tube_lemma
      (isCompact_singleton (x := s)) (isCompact_Icc (a := (0 : ℝ)) (b := π / 2)) hopen (by
        rintro ⟨s', ψ⟩ ⟨hs', hψ⟩
        rw [mem_singleton_iff] at hs'
        subst hs'
        exact hs ψ hψ)
    exact mem_of_superset (hS.mem_nhds (hsS rfl)) fun s' hs' ψ hψ => hSW ⟨hs', hKW hψ⟩
  exact Variational.exists_pos_forall_abs_le_mem hK hU fun l hl ψ hψ =>
    mem_kernelDomain_zero (hKJ l hl) (by rw [uIcc_of_le (by positivity)]; exact hψ)

/-- The expansion of the angle for a turning point given on an open set of
parameters. -/
theorem IsTurning.exists_abs_sub_le (hg : ContDiff ℝ ∞ g) (h : IsTurning g J c) {K : Set Q}
    (hK : IsCompact K) (hKJ : ∀ l ∈ K, ((0 : ℝ), l) ∈ J) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ →
      IsClosest (fun u => g (l, u)) ε (c (ε, l)) ∧
      |π - 2 * (∫ ψ in (0 : ℝ)..π / 2, angleKernel (fun u => g (l, u)) ε (c (ε, l)) ψ) -
        ε * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ)| ≤ M * ε ^ 2 := by
  obtain ⟨δ₁, hδ₁, M, hM⟩ := Variational.exists_second_order_bound hK (f := halfAngle g c)
    fun l hl => (contDiffAt_halfAngle hg h (hKJ l hl)).of_le (by simp)
  obtain ⟨δ₂, hδ₂, hdom⟩ := exists_forall_mem_kernelDomain hg h hK hKJ
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, 2 * M, fun l hl ε hε => ⟨?_, ?_⟩⟩
  · have hmem := hdom l hl ε (hε.trans (min_le_right _ _))
    have hJ : (ε, l) ∈ J := (hmem 0 ⟨le_rfl, by positivity⟩).1.1
    have hc0 := h.pos _ hJ
    refine ⟨hc0, h.radicand_eq_zero _ hJ, fun u hu => ?_⟩
    have hx0 : 0 ≤ u / c (ε, l) := div_nonneg hu.1 hc0.le
    have hx1 : u / c (ε, l) ≤ 1 := (div_le_one hc0).mpr hu.2
    have hψ : Real.arcsin (u / c (ε, l)) ∈ Icc (0 : ℝ) (π / 2) :=
      ⟨Real.arcsin_nonneg.mpr hx0, Real.arcsin_le_pi_div_two _⟩
    have h1 : (0 : ℝ) < 1 + ε * ratio (fun y => g (l, y)) (c (ε, l))
        (c (ε, l) * Real.sin (Real.arcsin (u / c (ε, l)))) := (hmem _ hψ).2
    have e2 : c (ε, l) * (u / c (ε, l)) = u := by field_simp
    rw [Real.sin_arcsin (by linarith) hx1, e2] at h1
    exact h1
  · have h1 := hM l hl ε (hε.trans (min_le_left _ _))
    rw [(hasDerivAt_halfAngle hg h (hKJ l hl)).deriv, halfAngle_zero] at h1
    have e : π - 2 * halfAngle g c (ε, l) -
        ε * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ) =
        -2 * (halfAngle g c (ε, l) - π / 2 -
          ε * (-(1 / 2) * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ))) := by
      ring
    change |π - 2 * halfAngle g c (ε, l) -
      ε * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ)| ≤ 2 * M * ε ^ 2
    rw [e, abs_mul, abs_neg, abs_two]
    linarith

end Turning

variable [FiniteDimensional ℝ Q]

/-- The angle from the closest approach to infinity to the second order in the
strength, with a remainder that is uniform for the parameter in a compact
set. -/
theorem exists_abs_angle_sub_le (hg : ContDiff ℝ ∞ g) {K : Set Q} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ → ∃ c : ℝ,
      IsClosest (fun u => g (l, u)) ε c ∧
      |π - 2 * (∫ ψ in (0 : ℝ)..π / 2, angleKernel (fun u => g (l, u)) ε c ψ) -
        ε * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ)| ≤ M * ε ^ 2 := by
  refine hK.induction_on (p := fun t : Set Q => ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ l ∈ t, ∀ ε : ℝ,
    |ε| ≤ δ → ∃ c : ℝ, IsClosest (fun u => g (l, u)) ε c ∧
      |π - 2 * (∫ ψ in (0 : ℝ)..π / 2, angleKernel (fun u => g (l, u)) ε c ψ) -
        ε * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ)| ≤ M * ε ^ 2)
    ?_ ?_ ?_ ?_
  · exact ⟨1, one_pos, 0, fun l hl => hl.elim⟩
  · rintro s t hst ⟨δ, hδ, M, hM⟩
    exact ⟨δ, hδ, M, fun l hl => hM l (hst hl)⟩
  · rintro s t ⟨δ₁, hδ₁, M₁, hM₁⟩ ⟨δ₂, hδ₂, M₂, hM₂⟩
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max M₁ M₂, fun l hl ε hε => ?_⟩
    rcases hl with hl | hl
    · obtain ⟨c, hc, hb⟩ := hM₁ l hl ε (hε.trans (min_le_left _ _))
      exact ⟨c, hc, hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ε))⟩
    · obtain ⟨c, hc, hb⟩ := hM₂ l hl ε (hε.trans (min_le_right _ _))
      exact ⟨c, hc, hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg ε))⟩
  · intro x _
    obtain ⟨J, c, hT, hmem⟩ := exists_isTurning hg x
    have hN : IsOpen {l : Q | ((0 : ℝ), l) ∈ J} :=
      hT.isOpen.preimage (continuous_const.prodMk continuous_id)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN x hmem
    have hsub : ∀ l ∈ Metric.closedBall x (r / 2), ((0 : ℝ), l) ∈ J := fun l hl =>
      hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hl) (by linarith)))
    obtain ⟨δ, hδ, M, hM⟩ := hT.exists_abs_sub_le hg (isCompact_closedBall x (r / 2)) hsub
    exact ⟨Metric.closedBall x (r / 2),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x (by positivity)),
      δ, hδ, M, fun l hl ε hε => ⟨c (ε, l), hM l hl ε hε⟩⟩

/-- Small-angle scattering (Landau–Lifshitz (20.3)) with a remainder. For `l`
in a compact set and `|ε| ≤ δ`, the radicand determines a closest approach
and a motion for all positive scales `ρ` and `vinf`. Its deflection differs
from the first-order term by at most `M ε²`. When `g(l, 0) = 0`, `vinf` is the
speed at infinity and `ρ` is the impact parameter. -/
theorem exists_abs_deflectionAngle_sub_le (hg : ContDiff ℝ ∞ g) {K : Set Q} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ → ∃ c : ℝ,
      IsClosest (fun u => g (l, u)) ε c ∧ ∀ ρ vinf : ℝ, 0 < ρ → 0 < vinf →
        (∃ C : ℝ, IsFactor (factor (fun u => g (l, u)) ρ vinf ε c) (ρ / c) C) ∧
        |deflectionAngle (ρ * vinf) (speedSq (fun u => g (l, u)) ρ vinf ε) (ρ / c) -
          ε * (-ρ * ∫ r in Ioi ρ, deriv (fun r => g (l, ρ / r)) r / √(r ^ 2 - ρ ^ 2))| ≤
            M * ε ^ 2 := by
  obtain ⟨δ, hδ, M, hM⟩ := exists_abs_angle_sub_le hg hK
  refine ⟨δ, hδ, M, fun l hl ε hε => ?_⟩
  obtain ⟨c, hc, hb⟩ := hM l hl ε hε
  have hf := contDiff_slice hg l
  refine ⟨c, hc, fun ρ vinf hρ hv => ⟨exists_isFactor hf hρ hv hc.pos hc.factor_pos, ?_⟩⟩
  have h20 : ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * slopeOf g (l, Real.sin ψ) =
      -ρ * ∫ r in Ioi ρ, deriv (fun r => g (l, ρ / r)) r / √(r ^ 2 - ρ ^ 2) := by
    have h1 := integral_sin_mul_deriv_eq hf hρ
    rw [deriv_slice hg l] at h1
    exact h1
  rw [deflectionAngle_eq hf hρ hv hc.pos hc.radicand_eq_zero hc.factor_pos, ← h20]
  exact hb

/-- The same for a potential without a parameter. -/
theorem exists_abs_deflectionAngle_sub_le_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ ε : ℝ, |ε| ≤ δ → ∃ c : ℝ, IsClosest f ε c ∧
      ∀ ρ vinf : ℝ, 0 < ρ → 0 < vinf →
        (∃ C : ℝ, IsFactor (factor f ρ vinf ε c) (ρ / c) C) ∧
        |deflectionAngle (ρ * vinf) (speedSq f ρ vinf ε) (ρ / c) -
          ε * ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * deriv f (Real.sin ψ)| ≤ M * ε ^ 2 := by
  have hg : ContDiff ℝ ∞ fun q : ℝ × ℝ => f q.2 := hf.comp contDiff_snd
  obtain ⟨δ, hδ, M, hM⟩ := exists_abs_angle_sub_le hg (isCompact_singleton (x := (0 : ℝ)))
  refine ⟨δ, hδ, M, fun ε hε => ?_⟩
  obtain ⟨c, hc, hb⟩ := hM 0 (mem_singleton 0) ε hε
  have hc' : IsClosest f ε c := hc
  have hs : ∀ x : ℝ, slopeOf (fun q : ℝ × ℝ => f q.2) ((0 : ℝ), x) = deriv f x := fun x =>
    (congrFun (deriv_slice hg 0) x).symm
  simp only [hs] at hb
  refine ⟨c, hc', fun ρ vinf hρ hv => ⟨exists_isFactor hf hρ hv hc'.pos hc'.factor_pos, ?_⟩⟩
  rw [deflectionAngle_eq hf hρ hv hc'.pos hc'.radicand_eq_zero hc'.factor_pos]
  exact hb

/-! ### The Coulomb field -/

/-- The Coulomb field `U = α/r` is the potential `f(u) = u` with the strength
`ε = 2a/ρ`, `a = α/m v∞²`. -/
theorem speedSq_id (a vinf : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    speedSq (fun u => u) ρ vinf (2 * a / ρ) = Coulomb.speedSq a ρ vinf := by
  funext r
  have e : 2 * a / ρ * (ρ / r) = 2 * a / r := by
    rcases eq_or_ne r 0 with rfl | hr
    · simp
    · field_simp
  simp only [speedSq, radicand, Coulomb.speedSq, e, div_pow]
  ring

theorem integral_sin_mul_deriv_id :
    ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * deriv (fun u : ℝ => u) (Real.sin ψ) = 1 := by
  simp

theorem IsClosest.div_eq_closest {a ρ c : ℝ} (hρ : 0 < ρ)
    (h : IsClosest (fun u => u) (2 * a / ρ) c) : ρ / c = Coulomb.closest a ρ := by
  have hc := h.pos
  have h0 := h.radicand_eq_zero
  simp only [radicand] at h0
  have hr : 0 < ρ / c := div_pos hρ hc
  have hq : (ρ / c - Coulomb.closest a ρ) * (ρ / c + Coulomb.conjugate a ρ) = 0 := by
    have e : (ρ / c) ^ 2 - 2 * a * (ρ / c) - ρ ^ 2 =
        ρ ^ 2 / c ^ 2 * (1 - c ^ 2 - 2 * a / ρ * c) := by
      field_simp
      ring
    rw [Coulomb.sub_mul_add, e, h0, mul_zero]
  rcases mul_eq_zero.mp hq with h1 | h1
  · linarith
  · have h2 := Coulomb.conjugate_pos a hρ
    linarith

/-- The expansion for the Coulomb field: Rutherford's angle of deflection is
`2a/ρ` up to a term of the second order in `a/ρ`. -/
theorem exists_abs_coulomb_deflection_sub_le :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ a ρ : ℝ, 0 < ρ → |2 * a / ρ| ≤ δ →
      |Coulomb.deflection a ρ - 2 * a / ρ| ≤ M * (2 * a / ρ) ^ 2 := by
  obtain ⟨δ, hδ, M, hM⟩ :=
    exists_abs_deflectionAngle_sub_le_of_contDiff (f := fun u : ℝ => u) contDiff_id
  refine ⟨δ, hδ, M, fun a ρ hρ hε => ?_⟩
  obtain ⟨c, hc, hmot⟩ := hM (2 * a / ρ) hε
  have h1 := (hmot ρ 1 hρ one_pos).2
  rw [hc.div_eq_closest hρ, speedSq_id a 1 hρ.ne',
    ← Coulomb.deflection_eq_deflectionAngle a hρ one_pos, integral_sin_mul_deriv_id,
    mul_one] at h1
  exact h1

/-! ### A potential energy that is a smooth function of `1/r` -/

/-- The square of the radial velocity for potential energy `U` measured relative
to its value at infinity, mass `m`, asymptotic speed `v∞`, and impact parameter `ρ`. -/
def potentialSpeedSq (U : ℝ → ℝ) (m ρ vinf r : ℝ) : ℝ :=
  vinf ^ 2 - 2 * U r / m - (ρ * vinf) ^ 2 / r ^ 2

/-- The potential `U(r) = ε r⁻ⁿ w(1/r)` relative to its value at infinity. -/
def relativePotentialEnergy (w : ℝ → ℝ) (n : ℕ) (ε r : ℝ) : ℝ :=
  ε * (((1 / r) ^ n * w (1 / r)) - 0 ^ n * w 0)

/-- The normalized profile in `u = ρ/r` with parameters `κ = 1/ρ` and
`ω = 1/m v∞²`. Multiplying by `ε/ρⁿ` gives `2(U(r) − U(∞))/m v∞²`. -/
def scaledPotential (w : ℝ → ℝ) (n : ℕ) (q : (ℝ × ℝ) × ℝ) : ℝ :=
  2 * q.1.2 * (q.2 ^ n * w (q.1.1 * q.2) - 0 ^ n * w 0)

theorem contDiff_scaledPotential {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (n : ℕ) :
    ContDiff ℝ ∞ (scaledPotential w n) := by
  have e : scaledPotential w n =
      fun q : (ℝ × ℝ) × ℝ => 2 * q.1.2 * (q.2 ^ n * w (q.1.1 * q.2) - 0 ^ n * w 0) := rfl
  rw [e]
  exact (by fun_prop : ContDiff ℝ ∞ fun q : (ℝ × ℝ) × ℝ => 2 * q.1.2).mul
    (((contDiff_snd.pow n).mul
      (hw.comp (by fun_prop : ContDiff ℝ ∞ fun q : (ℝ × ℝ) × ℝ => q.1.1 * q.2))).sub
      contDiff_const)

theorem one_div_mul_div {ρ : ℝ} (hρ : ρ ≠ 0) (r : ℝ) : 1 / ρ * (ρ / r) = 1 / r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · field_simp

theorem div_pow_mul_eq (w : ℝ → ℝ) (n : ℕ) (ρ r : ℝ) :
    (ρ / r) ^ n * w (1 / r) = ρ ^ n * ((1 / r) ^ n * w (1 / r)) := by
  rw [div_pow, one_div, inv_pow, div_eq_mul_inv]
  ring

theorem speedSq_scaledPotential (w : ℝ → ℝ) (n : ℕ) {m ρ vinf : ℝ} (hm : m ≠ 0) (hρ : ρ ≠ 0)
    (hvinf : vinf ≠ 0) (ε : ℝ) :
    speedSq (fun u => scaledPotential w n ((1 / ρ, 1 / (m * vinf ^ 2)), u)) ρ vinf
        (ε / ρ ^ n) =
      potentialSpeedSq (relativePotentialEnergy w n ε) m ρ vinf := by
  funext r
  have h1 : vinf ^ 2 * (ρ / r) ^ 2 = (ρ * vinf) ^ 2 / r ^ 2 := by ring
  have hρn : ρ ^ n ≠ 0 := pow_ne_zero n hρ
  have hzero : ρ ^ n * (0 : ℝ) ^ n = 0 ^ n := by rw [← mul_pow, mul_zero]
  have hprofile : (ρ / r) ^ n * w (1 / r) - 0 ^ n * w 0 =
      ρ ^ n * (((1 / r) ^ n * w (1 / r)) - 0 ^ n * w 0) := by
    rw [div_pow_mul_eq, mul_sub, ← mul_assoc (ρ ^ n) ((0 : ℝ) ^ n) (w 0), hzero]
  have h2 : vinf ^ 2 * (ε / ρ ^ n * (2 * (1 / (m * vinf ^ 2)) *
        ((ρ / r) ^ n * w (1 / r) - 0 ^ n * w 0))) =
      2 * relativePotentialEnergy w n ε r / m := by
    rw [hprofile, relativePotentialEnergy]
    field_simp
  simp only [speedSq, radicand, scaledPotential, potentialSpeedSq, one_div_mul_div hρ r]
  linear_combination (-1 : ℝ) * h1 - h2

/-- Subtracting the limiting potential makes `vinf` the asymptotic speed. -/
theorem tendsto_potentialSpeedSq_atTop {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (n : ℕ)
    {m ρ vinf : ℝ} (hm : m ≠ 0) (hρ : ρ ≠ 0) (hv : vinf ≠ 0) (ε : ℝ) :
    Tendsto (potentialSpeedSq (relativePotentialEnergy w n ε) m ρ vinf) atTop (𝓝 (vinf ^ 2)) := by
  rw [← speedSq_scaledPotential w n hm hρ hv ε]
  exact tendsto_speedSq_atTop (contDiff_slice (contDiff_scaledPotential hw n) _)
    (by simp [scaledPotential]) ρ vinf (ε / ρ ^ n)

/-- Small-angle scattering (Landau–Lifshitz (20.3)) for the potential energy
`U(r) = ε r⁻ⁿ w(1/r)` with `w` smooth, uniformly for the impact parameters
`ρ ≥ ρ₁` and the asymptotic speeds `v∞ ≥ v₁`. With the potential measured
relative to its value at infinity, if `|ε/ρⁿ| ≤ δ` the motion exists, with the
closest approach `r₀`, and its angle of deflection differs from
`−(2ρ/m v∞²) ∫_ρ^∞ U′(r) dr/√(r² − ρ²)` by at most `M (ε/ρⁿ)²`. For `n = 0`
this is the expansion in a small coupling; for `n ≥ 1` and a fixed `ε` it is
the statement for a large impact parameter. -/
theorem exists_abs_deflectionAngle_potential_sub_le {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (n : ℕ)
    {m ρ₁ v₁ : ℝ} (hm : 0 < m) (hρ₁ : 0 < ρ₁) (hv₁ : 0 < v₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ ρ vinf ε : ℝ, ρ₁ ≤ ρ → v₁ ≤ vinf → |ε / ρ ^ n| ≤ δ →
      ∃ (r₀ C : ℝ) (W : ℝ → ℝ), 0 < r₀ ∧ IsFactor W r₀ C ∧
        (∀ r, r₀ ≤ r → potentialSpeedSq (relativePotentialEnergy w n ε) m ρ vinf r =
          (r - r₀) * W r) ∧
        |deflectionAngle (ρ * vinf)
            (potentialSpeedSq (relativePotentialEnergy w n ε) m ρ vinf) r₀ -
          -(2 * ρ / (m * vinf ^ 2)) * ∫ r in Ioi ρ,
            deriv (fun r => ε * ((1 / r) ^ n * w (1 / r))) r / √(r ^ 2 - ρ ^ 2)| ≤
              M * (ε / ρ ^ n) ^ 2 := by
  have hg := contDiff_scaledPotential hw n
  have hK : IsCompact (Icc (0 : ℝ) (1 / ρ₁) ×ˢ Icc (0 : ℝ) (1 / (m * v₁ ^ 2))) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ, hδ, M, hM⟩ := exists_abs_deflectionAngle_sub_le hg hK
  refine ⟨δ, hδ, M, fun ρ vinf ε hρ hvinf hε => ?_⟩
  have hρ0 : 0 < ρ := hρ₁.trans_le hρ
  have hv0 : 0 < vinf := hv₁.trans_le hvinf
  have hρn : ρ ^ n ≠ 0 := pow_ne_zero n hρ0.ne'
  have hl : ((1 / ρ, 1 / (m * vinf ^ 2)) : ℝ × ℝ) ∈
      Icc (0 : ℝ) (1 / ρ₁) ×ˢ Icc (0 : ℝ) (1 / (m * v₁ ^ 2)) := by
    refine ⟨⟨by positivity, one_div_le_one_div_of_le hρ₁ hρ⟩, ⟨by positivity,
      one_div_le_one_div_of_le (by positivity) ?_⟩⟩
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv₁.le hvinf 2) hm.le
  obtain ⟨c, hc, hmot⟩ := hM _ hl (ε / ρ ^ n) hε
  obtain ⟨⟨C, hC⟩, hb⟩ := hmot ρ vinf hρ0 hv0
  have hF := speedSq_scaledPotential w n hm.ne' hρ0.ne' hv0.ne' ε
  have hf : ContDiff ℝ ∞ fun u => scaledPotential w n ((1 / ρ, 1 / (m * vinf ^ 2)), u) :=
    contDiff_slice hg _
  refine ⟨ρ / c, C, _, div_pos hρ0 hc.pos, hC, fun r hr => ?_, ?_⟩
  · rw [← hF]
    exact speedSq_eq hf hρ0 vinf hc.pos hc.radicand_eq_zero ((div_pos hρ0 hc.pos).trans_le hr)
  · have hterm : ε / ρ ^ n * (-ρ * ∫ r in Ioi ρ,
        deriv (fun r => scaledPotential w n ((1 / ρ, 1 / (m * vinf ^ 2)), ρ / r)) r /
          √(r ^ 2 - ρ ^ 2)) =
        -(2 * ρ / (m * vinf ^ 2)) * ∫ r in Ioi ρ,
          deriv (fun r => ε * ((1 / r) ^ n * w (1 / r))) r / √(r ^ 2 - ρ ^ 2) := by
      have e1 : (fun r : ℝ => scaledPotential w n ((1 / ρ, 1 / (m * vinf ^ 2)), ρ / r)) =
          fun r => 2 * (1 / (m * vinf ^ 2)) * ρ ^ n * ((1 / r) ^ n * w (1 / r)) -
            2 * (1 / (m * vinf ^ 2)) * (0 ^ n * w 0) := by
        funext r
        simp only [scaledPotential, one_div_mul_div hρ0.ne' r]
        rw [div_pow_mul_eq w n ρ r]
        ring
      rw [e1]
      simp only [deriv_sub_const, deriv_const_mul_field, mul_div_assoc]
      rw [integral_const_mul, integral_const_mul]
      field_simp
    rw [hF, hterm] at hb
    exact hb

end ProjectAinos.Mechanics.Scattering.SmallAngle
