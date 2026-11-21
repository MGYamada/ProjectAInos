/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CurvedLinearization
public import ProjectAinos.GeneralRelativity.ExactPlaneWave
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Short gravitational waves on a curved background

Landau–Lifshitz, §108. On a background coordinate metric `g` on an open set `U`, a short wave is
`h = a cos(ψ/ε)`, with a smooth symmetric amplitude `a`, a smooth phase `ψ` and the wave covector
`k = dψ` (`gradientCovector`). Its linearized Ricci tensor is the Palatini form of
`SmoothGeometry/Lorentzian/CurvedLinearization.lean`.

* `familyRicciDeriv_phase`: for a smooth profile `F`, exactly,
  `δRic[F(ψ) a] = F(ψ) δRic[a] + F'(ψ) R₁ − F''(ψ) S(k, a)`, with
  `R₁ = Λ(k, δΓ[a]) + ∇·Q(k, a)` (`transportTerm`, `gradientContraction`) and the symbol
  `S(k, a)_{jl} = ½ g(k,k) a_{jl} − ½ k_j (k·a)_l − ½ k_l (k·a)_j + ½ k_j k_l tr a`
  (`shortWaveSymbol`; `gradientContraction_symbolChristoffel`: `Λ(k, Q(k, a)) = −S`).
* `familyRicciDeriv_shortWave`: for `F(u) = cos(u/ε)` and every `ε`,
  `δRic[a cos(ψ/ε)] = ε⁻² cos(ψ/ε) S − ε⁻¹ sin(ψ/ε) R₁ + cos(ψ/ε) δRic[a]`, where `S`, `R₁` and
  `δRic[a]` do not depend on `ε`; `tendsto_shortWave`: `ε² δRic − cos(ψ/ε) S → 0` as `ε → 0`.
* **The eikonal equation.** In the gauge `k^a ā_{ab} = 0` (`IsShortWaveGauge`; by
  `isShortWaveGauge_iff` it is `(k·a)_b = ½ k_b tr a`) the symbol is `½ g(k, k) a`
  (`shortWaveSymbol_of_gauge`), so for a nonzero amplitude the `ε⁻²` term vanishes exactly when
  `k` is null (`shortWaveSymbol_eq_zero_iff`). The rays, the integral curves of `k^♯`, are then
  null geodesics (`isGeodesicOn_ray`).
* **Instances.** Flat: `covectorNorm_minkowski` (`η(k, k)`) and the straight null rays of a linear
  phase (`isGeodesicOn_minkowski_ray`). Curved, on the plane waves of §109 (`ExactPlaneWave`):
  the retarded time `u` has a null gradient, its rays `x₀ + τ (−1, 0, 0, −1)` are null geodesics
  (`isGeodesicOn_planeWave_ray`, `form_curveVelocity_planeWave_ray`), and the cross amplitude is
  in the gauge with a vanishing symbol (`isShortWaveGauge_cross`, `shortWaveSymbol_cross`). On the
  Ricci-flat strong wave `δRic[L_X g] = 0` (`familyRicciDeriv_lie_strong`).

Not stated here: the transport equation `2 k^l ∇_l a + (∇·k) a = 0` as the vanishing of `R₁` in
the gauge (`R₁` is given as an exact array); the effective stress of the waves as the source of
the background curvature, which needs the second order with an average over wavelengths; and the
approximation of exact solutions of the Einstein equations by short waves, which needs local
well-posedness.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.ShortWave

open SmoothGeometry CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-! ### The algebra of the wave covector -/

section Algebra

variable (g : CoordinateMetric σ d U)

/-- The raised covector `k^l = g^{lm} k_m`. -/
def raiseCovector (k : Fin (d + 1) → ℝ) (x : MinkowskiModel d) (l : Fin (d + 1)) : ℝ :=
  ∑ m, (g.coefficient x)⁻¹ l m * k m

/-- The squared norm `g(k, k) = g^{lm} k_l k_m` of a covector. -/
def covectorNorm (k : Fin (d + 1) → ℝ) (x : MinkowskiModel d) : ℝ :=
  ∑ l, ∑ m, (g.coefficient x)⁻¹ l m * k l * k m

/-- The trace `tr a = g^{lm} a_{lm}` of an amplitude. -/
def amplitudeTrace (a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) : ℝ :=
  ∑ l, ∑ m, (g.coefficient x)⁻¹ l m * a l m

/-- The contraction `(k·a)_j = k^m a_{mj}`. -/
def contractAmplitude (k : Fin (d + 1) → ℝ) (a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j : Fin (d + 1)) : ℝ :=
  ∑ m, raiseCovector g k x m * a m j

/-- **The short-wave symbol**
`S(k, a)_{jl} = ½ g(k,k) a_{jl} − ½ k_j (k·a)_l − ½ k_l (k·a)_j + ½ k_j k_l tr a`, the coefficient
of `ε⁻² cos(ψ/ε)` in the linearized Ricci tensor of `a cos(ψ/ε)`. -/
def shortWaveSymbol (k : Fin (d + 1) → ℝ) (a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j l : Fin (d + 1)) : ℝ :=
  covectorNorm g k x / 2 * a j l - k j * contractAmplitude g k a x l / 2 -
    k l * contractAmplitude g k a x j / 2 + k j * k l * amplitudeTrace g a x / 2

/-- **The gauge** `k^a ā_{ab} = 0` of the amplitude, with the trace reverse
`ā_{ab} = a_{ab} − ½ g_{ab} tr a`. -/
def IsShortWaveGauge (k : Fin (d + 1) → ℝ) (a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : Prop :=
  ∀ b, ∑ m, raiseCovector g k x m * (a m b - g.coefficient x m b * amplitudeTrace g a x / 2) = 0

end Algebra

/-- The contraction `Λ(w, P)_{jk} = w_i P^i_{jk} − w_j P^i_{ik}`. -/
def gradientContraction (w : Fin (d + 1) → ℝ) (P : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (j k : Fin (d + 1)) : ℝ :=
  ∑ i, (w i * P i j k - w j * P i i k)

section AlgebraLemmas

variable {g : CoordinateMetric σ d U} {x : MinkowskiModel d}

/-- Lowering the raised covector: `k^m g_{mb} = k_b`. -/
theorem sum_raiseCovector_mul_coefficient (hx : x ∈ U) (k : Fin (d + 1) → ℝ) (b : Fin (d + 1)) :
    ∑ m, raiseCovector g k x m * g.coefficient x m b = k b := by
  have hdet := g.coefficient_det_ne_zero ⟨x, hx⟩
  have hGC : (g.coefficient x)⁻¹ * g.coefficient x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have h (l : Fin (d + 1)) : ∑ m, (g.coefficient x)⁻¹ m l * g.coefficient x m b =
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) l b := by
    rw [← hGC, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [g.coefficient_inv_symmetric hx m l]
  unfold raiseCovector
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h' (l : Fin (d + 1)) : ∑ m, (g.coefficient x)⁻¹ m l * k l * g.coefficient x m b =
      k l * (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) l b := by
    rw [← h l, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [h', Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The gauge `k^a ā_{ab} = 0` is `(k·a)_b = ½ k_b tr a`. -/
theorem isShortWaveGauge_iff (hx : x ∈ U) (k : Fin (d + 1) → ℝ)
    (a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    IsShortWaveGauge g k a x ↔
      ∀ b, contractAmplitude g k a x b = k b * amplitudeTrace g a x / 2 := by
  have h (b : Fin (d + 1)) :
      ∑ m, raiseCovector g k x m * (a m b - g.coefficient x m b * amplitudeTrace g a x / 2) =
      contractAmplitude g k a x b - k b * amplitudeTrace g a x / 2 := by
    rw [← sum_raiseCovector_mul_coefficient hx k b, Finset.sum_mul, Finset.sum_div,
      contractAmplitude, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  unfold IsShortWaveGauge
  simp only [h, sub_eq_zero]

/-- **The leading term is the symbol**: `Λ(k, Q(k, a)) = −S(k, a)` for a symmetric amplitude. -/
theorem gradientContraction_symbolChristoffel (hx : x ∈ U) (k : Fin (d + 1) → ℝ)
    {a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (ha : ∀ i j, a i j = a j i) (j l : Fin (d + 1)) :
    gradientContraction k (g.symbolChristoffel k a x) j l = -shortWaveSymbol g k a x j l := by
  have hGs (p q : Fin (d + 1)) : (g.coefficient x)⁻¹ p q = (g.coefficient x)⁻¹ q p :=
    g.coefficient_inv_symmetric hx p q
  have hR (c : Fin (d + 1)) : contractAmplitude g k a x c =
      ∑ m, ∑ i, (g.coefficient x)⁻¹ m i * k i * a m c := by
    unfold contractAmplitude raiseCovector
    simp only [Finset.sum_mul]
  have hN : covectorNorm g k x = ∑ m, ∑ i, (g.coefficient x)⁻¹ m i * k m * k i := rfl
  have hT : amplitudeTrace g a x = ∑ m, ∑ i, (g.coefficient x)⁻¹ m i * a m i := rfl
  -- `∑_i k_i Q^i_{jl}`
  have h1 : ∑ i, k i * g.symbolChristoffel k a x i j l =
      ∑ m, ∑ i, (g.coefficient x)⁻¹ m i * k i * (k j * a m l + k l * a m j) / 2 -
        ∑ m, ∑ i, (g.coefficient x)⁻¹ m i * k m * k i * a j l / 2 := by
    unfold symbolChristoffel
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGs i m, ha l m]
    ring
  -- `∑_i Q^i_{il}`
  have h2 : ∑ i, g.symbolChristoffel k a x i i l =
      ∑ m, ∑ i, (g.coefficient x)⁻¹ m i * (k m * a l i) / 2 +
        ∑ m, ∑ i, (g.coefficient x)⁻¹ m i * (k l * a i m) / 2 -
        ∑ m, ∑ i, (g.coefficient x)⁻¹ m i * (k i * a m l) / 2 := by
    unfold symbolChristoffel
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∑ m, ∑ i, (g.coefficient x)⁻¹ m i * (k i * a m l) / 2 =
      ∑ m, ∑ i, (g.coefficient x)⁻¹ m i * (k m * a l i) / 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by
      rw [hGs m i, ha m l]
  unfold gradientContraction
  rw [Finset.sum_sub_distrib, h1, ← Finset.mul_sum, h2, h3]
  unfold shortWaveSymbol
  rw [hR l, hR j, hN, hT]
  rw [← sub_eq_zero]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  rw [sub_neg_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ha i m]
  ring

/-- **In the gauge the symbol is `½ g(k, k) a`.** -/
theorem shortWaveSymbol_of_gauge (hx : x ∈ U) {k : Fin (d + 1) → ℝ}
    {a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (hg : IsShortWaveGauge g k a x) (j l : Fin (d + 1)) :
    shortWaveSymbol g k a x j l = covectorNorm g k x / 2 * a j l := by
  have h := (isShortWaveGauge_iff hx k a).mp hg
  unfold shortWaveSymbol
  rw [h j, h l]
  ring

/-- **The eikonal equation** (target of §108): in the gauge `k^a ā_{ab} = 0`, the leading
coefficient of a nonzero amplitude vanishes exactly when `k` is null. -/
theorem shortWaveSymbol_eq_zero_iff (hx : x ∈ U) {k : Fin (d + 1) → ℝ}
    {a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (hg : IsShortWaveGauge g k a x) (ha : a ≠ 0) :
    (∀ j l, shortWaveSymbol g k a x j l = 0) ↔ covectorNorm g k x = 0 := by
  simp only [shortWaveSymbol_of_gauge hx hg]
  constructor
  · intro h
    by_contra hN
    apply ha
    ext j l
    have := h j l
    simp only [Matrix.zero_apply]
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (by linarith : covectorNorm g k x = 0) hN
    · exact h'
  · intro h j l
    rw [h]
    ring

end AlgebraLemmas

/-! ### The expansion of the linearized Ricci tensor of a wave -/

section Expansion

variable (g : CoordinateMetric σ d U)

/-- The coefficient `R₁ = Λ(dψ, δΓ[a]) + ∇·Q(dψ, a)` of `F'(ψ)` in the linearized Ricci tensor
of `F(ψ) a`. -/
def transportTerm (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  gradientContraction (gradientCovector ψ x) (g.curvedChristoffel a x) j k +
    g.palatini (fun z => g.symbolChristoffel (gradientCovector ψ z) (a z) z) x j k

variable {g}

theorem contDiffOn_symbolChristoffel {ψ : MinkowskiModel d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (b c e : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.symbolChristoffel (gradientCovector ψ z) (a z) z b c e) U := by
  unfold symbolChristoffel
  exact ContDiffOn.sum fun l _ => ((g.contDiffOn_coefficient_inv b l).mul
    ((((contDiffOn_gradientCovector hψ c).mul (ha e l)).add
      ((contDiffOn_gradientCovector hψ e).mul (ha l c))).sub
      ((contDiffOn_gradientCovector hψ l).mul (ha c e)))).div_const 2

/-- **The phase expansion.** For a smooth profile `F`, a smooth phase `ψ` and a smooth symmetric
amplitude `a`, the linearized Ricci tensor of `h = F(ψ) a` on the background `g` is
`δRic[F(ψ) a] = F(ψ) δRic[a] + F'(ψ) R₁ − F''(ψ) S(dψ, a)`, exactly. -/
theorem familyRicciDeriv_phase {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {ψ : MinkowskiModel d → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ U) {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (g.perturbationFamily (fun z => F (ψ z) • a z)) x j k =
      F (ψ x) * familyRicciDeriv (g.perturbationFamily a) x j k +
        deriv F (ψ x) * transportTerm g ψ a x j k -
        deriv (deriv F) (ψ x) * shortWaveSymbol g (gradientCovector ψ x) (a x) x j k := by
  have hU := U.isOpen.mem_nhds hx
  have hF1 : ContDiff ℝ ∞ (deriv F) := by simpa using hF.iterate_deriv 1
  have hFd (u : ℝ) : DifferentiableAt ℝ F u := hF.differentiable (by simp) u
  have hF1d (u : ℝ) : DifferentiableAt ℝ (deriv F) u := hF1.differentiable (by simp) u
  have hψd {z : MinkowskiModel d} (hz : z ∈ U) : DifferentiableAt ℝ ψ z :=
    (hψ.contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have had {z : MinkowskiModel d} (hz : z ∈ U) (p q : Fin (d + 1)) :
      DifferentiableAt ℝ (fun y => a y p q) z :=
    ((ha p q).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hFψ : ContDiffOn ℝ ∞ (fun z => F (ψ z)) U := hF.comp_contDiffOn hψ
  have hF1ψ : ContDiffOn ℝ ∞ (fun z => deriv F (ψ z)) U := hF1.comp_contDiffOn hψ
  have hw : ∀ i j, ContDiffOn ℝ ∞ (fun z => (F (ψ z) • a z) i j) U :=
    fun i j => hFψ.mul (ha i j)
  have hws : ∀ z ∈ U, ∀ i j, (F (ψ z) • a z) i j = (F (ψ z) • a z) j i := fun z hz i j => by
    simp only [Matrix.smul_apply, has z hz i j]
  set Q : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ :=
    fun z => g.symbolChristoffel (gradientCovector ψ z) (a z) z
  have hΓw : g.curvedChristoffel (fun z => F (ψ z) • a z) =ᶠ[𝓝 x]
      fun z => F (ψ z) • g.curvedChristoffel a z + deriv F (ψ z) • Q z := by
    filter_upwards [hU] with z hz
    funext b c e
    rw [curvedChristoffel_smul (f := fun z => F (ψ z)) ((hFd _).comp z (hψd hz)) (had hz) b c e]
    have hgc : gradientCovector (fun z => F (ψ z)) z = deriv F (ψ z) • gradientCovector ψ z :=
      funext fun i => gradientCovector_comp (hFd _) (hψd hz) i
    rw [hgc, symbolChristoffel_smul]
    rfl
  have hΓd (b c e : Fin (d + 1)) : DifferentiableAt ℝ (fun z => g.curvedChristoffel a z b c e) x :=
    ((contDiffOn_curvedChristoffel ha b c e).contDiffAt hU).differentiableAt (by simp)
  have hQd (b c e : Fin (d + 1)) : DifferentiableAt ℝ (fun z => Q z b c e) x :=
    ((contDiffOn_symbolChristoffel hψ ha b c e).contDiffAt hU).differentiableAt (by simp)
  have hQ'd (b c e : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => (deriv F (ψ z) • Q z) b c e) x :=
    ((hF1d _).comp x (hψd hx)).mul (hQd b c e)
  rw [familyRicciDeriv_eq hw hws hx, familyRicciDeriv_eq ha has hx, palatini_congr hΓw,
    palatini_smul_add (f := fun z => F (ψ z)) ((hFd _).comp x (hψd hx)) hΓd hQ'd,
    palatini_smul (f := fun z => deriv F (ψ z)) ((hF1d _).comp x (hψd hx)) hQd]
  simp only [gradientCovector_comp (hFd _) (hψd hx), gradientCovector_comp (hF1d _) (hψd hx)]
  have hS := gradientContraction_symbolChristoffel (g := g) hx (gradientCovector ψ x)
    (has x hx) j k
  have e1 : ∑ i, (deriv F (ψ x) * gradientCovector ψ x i * g.curvedChristoffel a x i j k -
      deriv F (ψ x) * gradientCovector ψ x j * g.curvedChristoffel a x i i k) =
      deriv F (ψ x) * gradientContraction (gradientCovector ψ x) (g.curvedChristoffel a x) j k := by
    unfold gradientContraction
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (deriv (deriv F) (ψ x) * gradientCovector ψ x i * Q x i j k -
      deriv (deriv F) (ψ x) * gradientCovector ψ x j * Q x i i k) =
      deriv (deriv F) (ψ x) * gradientContraction (gradientCovector ψ x) (Q x) j k := by
    unfold gradientContraction
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, hS]
  unfold transportTerm
  ring

/-- **The short-wave expansion** (target of §108). For the wave `h = a cos(ψ/ε)` on the
background `g`, exactly,
`δRic[h] = ε⁻² cos(ψ/ε) S(dψ, a) − ε⁻¹ sin(ψ/ε) R₁ + cos(ψ/ε) δRic[a]`;
the coefficients `S`, `R₁` and `δRic[a]` do not depend on `ε`. -/
theorem familyRicciDeriv_shortWave {ψ : MinkowskiModel d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (ε : ℝ) (j k : Fin (d + 1)) :
    familyRicciDeriv (g.perturbationFamily (fun z => Real.cos (ψ z / ε) • a z)) x j k =
      ε⁻¹ ^ 2 * Real.cos (ψ x / ε) * shortWaveSymbol g (gradientCovector ψ x) (a x) x j k -
        ε⁻¹ * Real.sin (ψ x / ε) * transportTerm g ψ a x j k +
        Real.cos (ψ x / ε) * familyRicciDeriv (g.perturbationFamily a) x j k := by
  have hF : ContDiff ℝ ∞ (fun u => Real.cos (u / ε)) :=
    Real.contDiff_cos.comp (contDiff_id.div_const ε)
  have hd1 (u : ℝ) : HasDerivAt (fun u => Real.cos (u / ε)) (-(Real.sin (u / ε) * ε⁻¹)) u := by
    have h := ((hasDerivAt_id u).div_const ε).cos
    simpa [div_eq_mul_inv] using h
  have hd1' : deriv (fun u => Real.cos (u / ε)) = fun u => -(Real.sin (u / ε) * ε⁻¹) :=
    funext fun u => (hd1 u).deriv
  have hd2 (u : ℝ) : HasDerivAt (fun u => -(Real.sin (u / ε) * ε⁻¹))
      (-(Real.cos (u / ε) * ε⁻¹ * ε⁻¹)) u := by
    have h := (((hasDerivAt_id u).div_const ε).sin.mul_const ε⁻¹).fun_neg
    simpa [div_eq_mul_inv] using h
  have hd2' : deriv (deriv (fun u => Real.cos (u / ε))) =
      fun u => -(Real.cos (u / ε) * ε⁻¹ * ε⁻¹) := by
    rw [hd1']
    exact funext fun u => (hd2 u).deriv
  have h := familyRicciDeriv_phase (g := g) hF hψ ha has hx j k
  rw [hd2', hd1'] at h
  rw [h]
  ring

end Expansion

/-! ### The leading order -/

section Leading

variable {g : CoordinateMetric σ d U}

/-- **The `ε⁻²` term**: `ε² δRic[a cos(ψ/ε)] − cos(ψ/ε) S(dψ, a) → 0` as `ε → 0`. -/
theorem tendsto_shortWave {ψ : MinkowskiModel d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    Tendsto (fun ε : ℝ => ε ^ 2 *
        familyRicciDeriv (g.perturbationFamily (fun z => Real.cos (ψ z / ε) • a z)) x j k -
      Real.cos (ψ x / ε) * shortWaveSymbol g (gradientCovector ψ x) (a x) x j k)
      (𝓝[≠] 0) (𝓝 0) := by
  set R₁ := transportTerm g ψ a x j k
  set R₀ := familyRicciDeriv (g.perturbationFamily a) x j k
  have hexp (ε : ℝ) (hε : ε ≠ 0) : ε ^ 2 *
        familyRicciDeriv (g.perturbationFamily (fun z => Real.cos (ψ z / ε) • a z)) x j k -
      Real.cos (ψ x / ε) * shortWaveSymbol g (gradientCovector ψ x) (a x) x j k =
      -(ε * Real.sin (ψ x / ε) * R₁) + ε ^ 2 * Real.cos (ψ x / ε) * R₀ := by
    rw [familyRicciDeriv_shortWave hψ ha has hx ε j k]
    field_simp
    ring
  refine squeeze_zero_norm' (a := fun ε : ℝ => |ε| * |R₁| + ε ^ 2 * |R₀|) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hexp ε hε, Real.norm_eq_abs]
    have h1 : |ε * Real.sin (ψ x / ε) * R₁| ≤ |ε| * |R₁| := by
      rw [abs_mul, abs_mul]
      have := Real.abs_sin_le_one (ψ x / ε)
      nlinarith [abs_nonneg ε, abs_nonneg R₁, mul_nonneg (abs_nonneg ε) (abs_nonneg R₁),
        abs_nonneg (Real.sin (ψ x / ε))]
    have h2 : |ε ^ 2 * Real.cos (ψ x / ε) * R₀| ≤ ε ^ 2 * |R₀| := by
      rw [abs_mul, abs_mul, abs_pow, sq_abs]
      have := Real.abs_cos_le_one (ψ x / ε)
      nlinarith [sq_nonneg ε, abs_nonneg R₀, mul_nonneg (sq_nonneg ε) (abs_nonneg R₀),
        abs_nonneg (Real.cos (ψ x / ε))]
    calc |-(ε * Real.sin (ψ x / ε) * R₁) + ε ^ 2 * Real.cos (ψ x / ε) * R₀|
        ≤ |-(ε * Real.sin (ψ x / ε) * R₁)| + |ε ^ 2 * Real.cos (ψ x / ε) * R₀| := abs_add_le _ _
      _ ≤ |ε| * |R₁| + ε ^ 2 * |R₀| := by rw [abs_neg]; linarith
  · have hc : Continuous fun ε : ℝ => |ε| * |R₁| + ε ^ 2 * |R₀| := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

end Leading

/-! ### Instances -/

section Flat

/-- On the Minkowski background the norm of a covector is `η(k, k) = Σ_a η^{aa} k_a²`. -/
theorem covectorNorm_minkowski (k : Fin (d + 1) → ℝ) (z : MinkowskiModel d) :
    covectorNorm (minkowski σ d U) k z = ∑ a, lorentzSign σ a * k a ^ 2 := by
  have hc : (minkowski σ d U).coefficient z = Minkowski.metricMatrix σ d := by
    rw [minkowski_coefficient]; rfl
  simp only [covectorNorm, hc, metricMatrix_inv, metricMatrix_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The gradient of a linear phase `ψ(z) = κ_i z^i` is `κ`. -/
theorem gradientCovector_linear (κ : Fin (d + 1) → ℝ) (z : MinkowskiModel d) (j : Fin (d + 1)) :
    gradientCovector (fun y : MinkowskiModel d => ∑ i, κ i * y i) z j = κ j := by
  unfold gradientCovector
  rw [fderiv_sum_mul_apply Finset.univ (F := fun i (y : MinkowskiModel d) => y i)
    (fun i _ => (hasFDerivAt_apply i z).differentiableAt) κ]
  have hc (i : Fin (d + 1)) : fderiv ℝ (fun y : MinkowskiModel d => y i) z (Pi.single j 1) =
      (Pi.single j 1 : MinkowskiModel d) i := by
    rw [(hasFDerivAt_apply i z).fderiv]
    rfl
  simp only [hc, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The raised gradient of a linear phase on the Minkowski background is `η κ`. -/
theorem gradientField_minkowski_linear (κ : Fin (d + 1) → ℝ) (z : MinkowskiModel d) :
    (minkowski σ d U).gradientField (fun y => ∑ i, κ i * y i) z =
      fun i => lorentzSign σ i * κ i := by
  have hc : (minkowski σ d U).coefficient z = Minkowski.metricMatrix σ d := by
    rw [minkowski_coefficient]; rfl
  funext i
  simp only [gradientField, hc, metricMatrix_inv, gradientCovector_linear]
  exact sum_metricMatrix_mul κ i

/-- The norm of the gradient of a linear phase on the Minkowski background is `η(κ, κ)`. -/
theorem gradientNorm_minkowski_linear (κ : Fin (d + 1) → ℝ) (z : MinkowskiModel d) :
    (minkowski σ d U).gradientNorm (fun y => ∑ i, κ i * y i) z =
      ∑ a, lorentzSign σ a * κ a ^ 2 := by
  rw [← covectorNorm_minkowski (U := U) κ z]
  simp only [gradientNorm, covectorNorm, gradientCovector_linear]

/-- **The flat rays are straight null lines** (the flat instance of `isGeodesicOn_ray`): for a
null covector `κ`, `η(κ, κ) = 0`, the integral curves `t ↦ x₀ + t η κ` of the raised gradient of
the phase `κ_i x^i` are geodesics of the Minkowski metric on the whole model space. -/
theorem isGeodesicOn_minkowski_ray (κ : Fin (d + 1) → ℝ)
    (hκ : ∑ a, lorentzSign σ a * κ a ^ 2 = 0) (x₀ : MinkowskiModel d) :
    (minkowski σ d ⊤).toLorentzMetric.IsGeodesicOn univ
      (fun t => (⟨x₀ + t • fun i => lorentzSign σ i * κ i, trivial⟩ :
        (⊤ : Opens (MinkowskiModel d)))) := by
  refine isGeodesicOn_ray (ContDiff.sum fun i _ => contDiff_const.mul
      (contDiff_apply ℝ (fun _ : Fin (d + 1) => ℝ) i)).contDiffOn
    (fun z _ => by rw [gradientNorm_minkowski_linear, hκ]) isOpen_univ fun t _ => ?_
  rw [gradientField_minkowski_linear]
  simpa using ((hasDerivAt_id t).smul_const (fun i => lorentzSign σ i * κ i)).const_add x₀

end Flat

namespace PlaneWave

open ExactPlaneWave
open LorentzMetric (curveVelocity)

variable {D : Data}

/-- The gradient of the retarded time `u = t − z` is `ℓ = (1, 0, 0, −1)`. -/
theorem gradientCovector_retarded (z : MinkowskiModel 3) (i : Fin 4) :
    gradientCovector retarded z i = nullCovector i := by
  unfold gradientCovector
  rw [(hasFDerivAt_retarded z).fderiv]
  fin_cases i <;> simp [nullCovector]

/-- The inverse coefficients of the plane wave are `diag(−1, a⁻², b⁻², 1)`. -/
theorem coefficient_inv_metric {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    ((metric D).coefficient z)⁻¹ = Matrix.diagonal fun l => (coefficients D z l)⁻¹ := by
  rw [coefficient_metric]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with l
  exact inv_mul_cancel₀ (coefficients_ne_zero hz l)

/-- The direction `(−1, 0, 0, −1)` of the rays. -/
def rayDirection : MinkowskiModel 3 := ![-1, 0, 0, -1]

/-- The raised gradient of the retarded time is the ray direction. -/
theorem raiseCovector_nullCovector {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    raiseCovector (metric D) nullCovector z = rayDirection := by
  funext i
  simp only [raiseCovector, coefficient_inv_metric hz, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  fin_cases i <;> simp [coefficients, nullCovector, rayDirection]

theorem gradientField_retarded {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    (metric D).gradientField retarded z = rayDirection := by
  rw [← raiseCovector_nullCovector hz]
  funext i
  simp only [gradientField, raiseCovector, gradientCovector_retarded]

/-- The gradient of the retarded time is null: `g(du, du) = 0`. -/
theorem covectorNorm_nullCovector {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    covectorNorm (metric D) nullCovector z = 0 := by
  rw [← nullCovector_isNull (D := D) z]
  simp only [covectorNorm, coefficient_inv_metric hz, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem gradientNorm_retarded {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    (metric D).gradientNorm retarded z = 0 := by
  rw [← covectorNorm_nullCovector hz]
  simp only [gradientNorm, covectorNorm, gradientCovector_retarded]

/-- The ray through `x₀` keeps its retarded time. -/
theorem retarded_add_ray (x₀ : MinkowskiModel 3) (τ : ℝ) :
    retarded (x₀ + τ • rayDirection) = retarded x₀ := by
  simp [retarded, rayDirection]

/-- The ray `τ ↦ x₀ + τ (−1, 0, 0, −1)` of the plane wave through `x₀`. -/
def ray (x₀ : domain D) (τ : ℝ) : domain D :=
  ⟨(x₀ : MinkowskiModel 3) + τ • rayDirection, by
    change retarded _ ∈ D.J
    rw [retarded_add_ray]
    exact x₀.2⟩

theorem hasDerivAt_ray (x₀ : domain D) (t : ℝ) :
    HasDerivAt (fun t => (ray x₀ t : MinkowskiModel 3)) ((metric D).gradientField retarded
      (ray x₀ t)) t := by
  rw [gradientField_retarded (ray x₀ t).2]
  change HasDerivAt (fun t => (x₀ : MinkowskiModel 3) + t • rayDirection) rayDirection t
  simpa using ((hasDerivAt_id t).smul_const rayDirection).const_add (x₀ : MinkowskiModel 3)

/-- **The rays of a plane wave are null geodesics** (an instance of `isGeodesicOn_ray` on a
curved background): along `u = const` the lines `τ ↦ x₀ + τ (−1, 0, 0, −1)` are affinely
parametrized geodesics of every diagonal plane wave of §109, with null velocity. -/
theorem isGeodesicOn_planeWave_ray (x₀ : domain D) :
    (metric D).toLorentzMetric.IsGeodesicOn univ (ray x₀) :=
  isGeodesicOn_ray contDiff_retarded.contDiffOn (fun _ hz => gradientNorm_retarded hz)
    isOpen_univ fun t _ => hasDerivAt_ray x₀ t

theorem form_curveVelocity_planeWave_ray (x₀ : domain D) (t : ℝ) :
    (metric D).toLorentzMetric.form (ray x₀ t) (curveVelocity (ray x₀) t)
      (curveVelocity (ray x₀) t) = 0 :=
  form_curveVelocity_ray (fun _ hz => gradientNorm_retarded hz) (hasDerivAt_ray x₀ t)

/-- **Gauge invariance on a curved vacuum** (an instance of `familyRicciDeriv_lie_eq_zero`): on
the strong wave of §109, which is Ricci flat and curved, `δRic[L_X g] = 0` for every smooth `X`. -/
theorem familyRicciDeriv_lie_strong {X : MinkowskiModel 3 → MinkowskiModel 3}
    (hX : ContDiffOn ℝ ∞ X (domain strong.toData)) {x : MinkowskiModel 3}
    (hx : x ∈ domain strong.toData) (j k : Fin 4) :
    familyRicciDeriv ((metric strong.toData).perturbationFamily
      (coordinateLieMetric X (metric strong.toData))) x j k = 0 :=
  familyRicciDeriv_lie_eq_zero ricciOf_strong hX hx j k

/-- The cross amplitude `a_{12} = a_{21} = 1`. -/
def crossAmplitude : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]]

theorem crossAmplitude_ne_zero : crossAmplitude ≠ 0 := by
  intro h
  have := congrFun (congrFun h 1) 2
  simp [crossAmplitude] at this

/-- **The gauge holds for the cross amplitude** of every plane wave: `k·a = 0` and `tr a = 0`
for `k = du`. -/
theorem isShortWaveGauge_cross {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    IsShortWaveGauge (metric D) nullCovector crossAmplitude z := by
  rw [isShortWaveGauge_iff hz]
  intro b
  have htr : amplitudeTrace (metric D) crossAmplitude z = 0 := by
    simp [amplitudeTrace, coefficient_inv_metric hz, Matrix.diagonal_apply, Fin.sum_univ_four,
      crossAmplitude]
  rw [htr]
  simp only [contractAmplitude, raiseCovector_nullCovector hz, mul_zero, zero_div]
  fin_cases b <;> simp [rayDirection, crossAmplitude, Fin.sum_univ_four]

/-- The leading coefficient of the cross wave `a cos(u/ε)` vanishes on every plane wave, since
`du` is null and the amplitude is in the gauge. -/
theorem shortWaveSymbol_cross {z : MinkowskiModel 3} (hz : z ∈ domain D) (j l : Fin 4) :
    shortWaveSymbol (metric D) nullCovector crossAmplitude z j l = 0 :=
  (shortWaveSymbol_eq_zero_iff hz (isShortWaveGauge_cross hz) crossAmplitude_ne_zero).mpr
    (covectorNorm_nullCovector hz) j l

end PlaneWave

end ProjectAinos.GeneralRelativity.ShortWave
