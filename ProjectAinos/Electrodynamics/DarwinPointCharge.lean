/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.LienardWiechert
public import ProjectAinos.Electrodynamics.DarwinLagrangian
import Mathlib.Tactic

/-!
# The Lagrangian of Darwin for point charges

The Euler–Lagrange expression of the Lagrangian of Darwin (Landau–Lifshitz, *The Classical
Theory of Fields*, (65.7), `darwinLagrangian`) for point charges, with `c = 1` and the units with
`div E = ρ`.

* `slowWorldline`: a smooth path `R₁` with `‖Ṙ₁‖ ≤ V₁` gives the slow subluminal world line
  `t ↦ R₁(κt)` for `κV₁ < 1` (`deriv_slowPath`).
* `pointLagrangian K e φ 𝐚 g`: a point charge with the kinetic Lagrangian `K` in the potentials
  `(φ, 𝐚)`; `eulerLagrange_pointLagrangian`: its residual `∂L/∂r − d/dt ∂L/∂𝐯` is
  `−d/dt ∂K/∂vᵢ + e(Eᵢ + (ṙ × 𝐁)ᵢ)` for potentials differentiable near the world line only.
* `eulerLagrange_update`: in the direction of one charge, the residual of a Lagrangian of `N`
  charges is the residual of the Lagrangian of that charge with the others on their paths.
* `pointScalar`, `pointVector`: the potentials of Darwin `e/(4πR)` and
  `e[ċ + (ċ · 𝐧)𝐧]/(8πR)` of a point charge on a path `c`, smooth off the path;
  `darwinPair_eq_point`: the pair term of (65.7) is the coupling `−eₐφ' + eₐ𝐯ₐ · 𝐚'`.
* `darwinKinetic`, `fderiv_darwinKinetic`: the kinetic Lagrangian `−m + mv²/2 + mv⁴/8` with the
  momentum `m(1 + v²/2)𝐯`; `contDiffAt_darwinLagrangian`: (65.7) is smooth where the charges are
  apart; `darwinLagrangian_update`: (65.7) seen by one charge.
* `eulerLagrange_darwinLagrangian`: **the Euler–Lagrange residual of (65.7) for the charge `a`**
  is `−d/dt[mₐ(1 + vₐ²/2)vₐᵢ] + eₐ(Eᵢ + (𝐯ₐ × 𝐁)ᵢ)` with the fields of the potentials of Darwin of
  the other charges, an exact local identity where the charges are apart;
  `eulerLagrange_darwinLagrangian_example`: two charges on separated straight paths.
* `Jet S ε q q₀ q₁ q₂`: `q = q₀ + εq₁ + ε²q₂ + O(ε³)` uniformly on a set of parameters, with
  the algebra `Jet.add`, `Jet.mul`, `Jet.inv`, `Jet.invSqrt`, `Jet.sum` and the bounds
  `Jet.bound_three`, `Jet.bound_two`.
* `SlowData`: a slow charge seen from a field point in retarded coordinates (the distance `R`
  and direction `n` from the retarded position, the retarded velocity and acceleration of the
  profile, and the Taylor remainders to the present time); `SlowData.lw` and `SlowData.darwin`
  are the two electric fields in units of `e/(4πR²)`, `SlowData.lwB`, `SlowData.darwinB` the
  magnetic ones. **The second-order cancellation**: `SlowData.jet_lw`, `SlowData.jet_darwin`
  (the same expansion to the second order), `SlowData.abs_lw_sub_darwin_le` (`O(ε³)`) and
  `SlowData.abs_lwB_sub_darwinB_le` (`O(ε²)`) on `SlowData.admissible K c`.
* The bridge: `slowData` (with `taylor_path`, `slowData_admissible`), `lw_slowData`,
  `lwB_slowData` (the field of Liénard and Wiechert of the slow world line), and
  `darwin_slowData`, `darwinB_slowData` (the field of `pointScalar`, `pointVector`, from the
  closed forms `spaceDeriv_pointScalar`, `timeDeriv_pointVector`, `spaceDeriv_pointVector`).
* `lienardWiechert_sub_darwin` (target (ii)): `|E_LW − E_D| ≤ Cκ³` and `|B_LW − B_D| ≤ Cκ²` at
  field points `δ ≤ ‖x − R₁(κt)‖ ≤ ρ`, uniformly in `0 < κ ≤ 1` with `κV₁ ≤ 1/2`.
* `force_eq_darwinLagrangian` (target (iv)): the Lorentz force of the fields of Liénard and
  Wiechert of the other charges on a charge of a slow separated configuration is the
  interaction part of the Euler–Lagrange residual of (65.7) up to `Cκ³`;
  `force_eq_darwinLagrangian_example`: an oscillating charge and a charge at rest
  (`oscillatingPaths`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Wave SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### A slow point charge -/

/-- The derivative of the slow path `t ↦ R₁(κt)` is `κ Ṙ₁(κt)`. -/
theorem deriv_slowPath {R₁ : ℝ → E3} (hR : Differentiable ℝ R₁) (κ t : ℝ) :
    deriv (fun t => R₁ (κ * t)) t = κ • deriv R₁ (κ * t) := by
  have h1 : HasDerivAt (fun t : ℝ => κ * t) κ t := by
    simpa using (hasDerivAt_id' t).const_mul κ
  exact ((hR (κ * t)).hasDerivAt.scomp t h1).deriv

/-- **A slow point charge** (target (i)): the path `r_κ(t) = R₁(κt)` of a smooth `R₁` with
`‖Ṙ₁‖ ≤ V₁` is a subluminal world line with the speed bound `κV₁` when `κV₁ < 1`. -/
def slowWorldline (R₁ : ℝ → E3) (hR : ContDiff ℝ ∞ R₁) {V₁ : ℝ}
    (hV : ∀ s, ‖deriv R₁ s‖ ≤ V₁) {κ : ℝ} (hκ : 0 ≤ κ) (hκV : κ * V₁ < 1) :
    SubluminalWorldline where
  r := fun t => R₁ (κ * t)
  contDiff_r := hR.comp (contDiff_const.mul contDiff_id)
  v₀ := κ * V₁
  v₀_nonneg := mul_nonneg hκ ((norm_nonneg _).trans (hV 0))
  v₀_lt_one := hκV
  norm_deriv_le := fun t => by
    rw [deriv_slowPath (hR.differentiable (by simp)), norm_smul, Real.norm_of_nonneg hκ]
    exact mul_le_mul_of_nonneg_left (hV _) hκ

/-! ### The Euler–Lagrange expression of a point charge in given potentials -/

/-- The Lagrangian `K(𝐯) − eφ(t, r) + e 𝐯 · 𝐚(t, r) + g(t)` of a point charge `e` with the kinetic
Lagrangian `K` in the potentials `(φ, 𝐚)`, with an additional function `g` of the time. -/
def pointLagrangian (K : E3 → ℝ) (e : ℝ) (φ : ℝ × E3 → ℝ) (A : Fin 3 → ℝ × E3 → ℝ)
    (g : ℝ → ℝ) : Mechanics.Lagrangian E3 :=
  fun s z => K z.2 - e * φ (s, z.1) + e * ∑ k, z.2 k * A k (s, z.1) + g s

/-- **The Euler–Lagrange expression of a point charge** in potentials that are differentiable
near the world line: the residual `∂L/∂r − d/dt ∂L/∂𝐯` of `pointLagrangian` is
`−d/dt ∂K/∂vᵢ + e(Eᵢ + (ṙ × 𝐁)ᵢ)(t, r(t))`. Only local differentiability is used. -/
theorem eulerLagrange_pointLagrangian {K : E3 → ℝ} (hK : ContDiff ℝ 2 K) (e : ℝ)
    {φ : ℝ × E3 → ℝ} {A : Fin 3 → ℝ × E3 → ℝ} (g : ℝ → ℝ) {r : ℝ → E3} {t : ℝ}
    (hφ : ∀ᶠ p in 𝓝 (t, r t), DifferentiableAt ℝ φ p)
    (hA : ∀ k, ∀ᶠ p in 𝓝 (t, r t), DifferentiableAt ℝ (A k) p)
    (hr : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ r s) (hr' : DifferentiableAt ℝ (deriv r) t)
    (i : Fin 3) :
    Mechanics.eulerLagrange (pointLagrangian K e φ A g) r t (EuclideanSpace.single i 1) =
      -deriv (fun s => fderiv ℝ K (deriv r s) (EuclideanSpace.single i 1)) t +
        e * lorentzDensity φ A (deriv r t) i (t, r t) := by
  set ι : E3 × E3 →L[ℝ] ℝ × E3 := (0 : E3 × E3 →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ E3 E3)
  have hι : ∀ (s : ℝ) (z : E3 × E3), HasFDerivAt (fun z : E3 × E3 => (s, z.1)) ι z := fun s z =>
    (hasFDerivAt_const s z).prodMk hasFDerivAt_fst
  have hK1 : Differentiable ℝ K := hK.differentiable (by simp)
  have hLd : ∀ (s : ℝ) (z : E3 × E3), DifferentiableAt ℝ φ (s, z.1) →
      (∀ k, DifferentiableAt ℝ (A k) (s, z.1)) → HasFDerivAt (pointLagrangian K e φ A g s)
        ((fderiv ℝ K z.2).comp (ContinuousLinearMap.snd ℝ E3 E3) -
          e • (fderiv ℝ φ (s, z.1)).comp ι + e • ∑ k, (z.2 k • (fderiv ℝ (A k) (s, z.1)).comp ι +
            A k (s, z.1) • (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).comp
              (ContinuousLinearMap.snd ℝ E3 E3))) z := by
    intro s z hφz hAz
    have h1 : HasFDerivAt (fun z : E3 × E3 => K z.2)
        ((fderiv ℝ K z.2).comp (ContinuousLinearMap.snd ℝ E3 E3)) z :=
      (hK1 z.2).hasFDerivAt.comp z hasFDerivAt_snd
    have h2 : HasFDerivAt (fun z : E3 × E3 => φ (s, z.1)) ((fderiv ℝ φ (s, z.1)).comp ι) z :=
      hφz.hasFDerivAt.comp z (hι s z)
    have h3 : HasFDerivAt (fun z : E3 × E3 => ∑ k, z.2 k * A k (s, z.1))
        (∑ k, (z.2 k • (fderiv ℝ (A k) (s, z.1)).comp ι +
          A k (s, z.1) • (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).comp
            (ContinuousLinearMap.snd ℝ E3 E3))) z := by
      refine HasFDerivAt.fun_sum fun k _ => ?_
      have hp : HasFDerivAt (fun z : E3 × E3 => z.2 k)
          ((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ E3 E3)) z :=
        (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).hasFDerivAt.comp z hasFDerivAt_snd
      exact hp.mul ((hAz k).hasFDerivAt.comp z (hι s z))
    exact ((h1.sub (h2.const_mul e)).add (h3.const_mul e)).add_const (g s)
  have hcont : ContinuousAt (fun s => (s, r s)) t :=
    continuousAt_id.prodMk hr.self_of_nhds.continuousAt
  have hev : ∀ᶠ s in 𝓝 t,
      DifferentiableAt ℝ φ (s, r s) ∧ ∀ k, DifferentiableAt ℝ (A k) (s, r s) := by
    have hAll : ∀ᶠ p in 𝓝 (t, r t), DifferentiableAt ℝ φ p ∧ ∀ k, DifferentiableAt ℝ (A k) p := by
      filter_upwards [hφ, hA 0, hA 1, hA 2] with p h0 h1 h2 h3
      exact ⟨h0, fun k => by fin_cases k <;> assumption⟩
    exact hcont.eventually hAll
  have hforce : Mechanics.force (pointLagrangian K e φ A g) r t (EuclideanSpace.single i 1) =
      -(e * spaceDeriv i φ (t, r t)) + e * ∑ k, deriv r t k * spaceDeriv i (A k) (t, r t) := by
    rw [Mechanics.force, (hLd t _ hev.self_of_nhds.1 hev.self_of_nhds.2).fderiv]
    simp [ι, spaceDeriv]
  set M : ℝ → E3 →L[ℝ] ℝ := fun s => fderiv ℝ K (deriv r s) +
    e • ∑ k, A k (s, r s) • (EuclideanSpace.proj k : E3 →L[ℝ] ℝ) with hMd
  have hmom : Mechanics.momentum (pointLagrangian K e φ A g) r =ᶠ[𝓝 t] M := by
    filter_upwards [hev] with s hs
    refine ContinuousLinearMap.ext fun w => ?_
    rw [Mechanics.momentum, (hLd s _ hs.1 hs.2).fderiv]
    simp [ι, hMd, mul_comm, Prod.mk_zero_zero, Finset.mul_sum]
  have hpath : ∀ k, HasDerivAt (fun s => A k (s, r s))
      (fderiv ℝ (A k) (t, r t) (1, deriv r t)) t := fun k => by
    have h2 : HasDerivAt (fun s => (s, r s)) ((1 : ℝ), deriv r t) t :=
      HasDerivAt.prodMk (hasDerivAt_id' t) hr.self_of_nhds.hasDerivAt
    exact (hev.self_of_nhds.2 k).hasFDerivAt.comp_hasDerivAt t h2
  have hKd : HasDerivAt (fun s => fderiv ℝ K (deriv r s))
      (fderiv ℝ (fderiv ℝ K) (deriv r t) (deriv (deriv r) t)) t := by
    have hK2 : Differentiable ℝ (fderiv ℝ K) :=
      (hK.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    exact (hK2 _).hasFDerivAt.comp_hasDerivAt t hr'.hasDerivAt
  have hdM : HasDerivAt M (fderiv ℝ (fderiv ℝ K) (deriv r t) (deriv (deriv r) t) +
      e • ∑ k, fderiv ℝ (A k) (t, r t) (1, deriv r t) •
        (EuclideanSpace.proj k : E3 →L[ℝ] ℝ)) t :=
    hKd.add ((HasDerivAt.fun_sum fun k _ => (hpath k).smul_const
      (EuclideanSpace.proj k : E3 →L[ℝ] ℝ)).const_smul e)
  have hKi : deriv (fun s => fderiv ℝ K (deriv r s) (EuclideanSpace.single i 1)) t =
      fderiv ℝ (fderiv ℝ K) (deriv r t) (deriv (deriv r) t) (EuclideanSpace.single i 1) := by
    have := hKd.clm_apply (hasDerivAt_const t (EuclideanSpace.single i 1 : E3))
    simpa using this.deriv
  rw [Mechanics.eulerLagrange, sub_apply, hforce, hmom.deriv_eq, hdM.deriv, hKi]
  simp [PiLp.single_apply]
  rw [clm_apply_one_vec, lorentzDensity, crossProduct_magneticOf, electricOf]
  simp only [timeDeriv, spaceDeriv, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [← Finset.mul_sum]
  ring

/-! ### One charge among `N` -/

/-- **The Euler–Lagrange expression of one charge among `N`**: in the direction of the charge
`a`, the residual of a Lagrangian `L` of `N` charges is the residual of the one-charge
Lagrangian `(r, 𝐯) ↦ L(update q a r, update q̇ a 𝐯)` in which the others follow their paths. -/
theorem eulerLagrange_update {N : ℕ} {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (L : Mechanics.Lagrangian (Fin N → Q)) (q : ℝ → Fin N → Q) (a : Fin N) {t : ℝ}
    (hL : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (L s) (q s, deriv q s))
    (hq : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ q s)
    (hM : DifferentiableAt ℝ (Mechanics.momentum L q) t) (w : Q) :
    Mechanics.eulerLagrange L q t (Pi.single a w) =
      Mechanics.eulerLagrange
        (fun s z => L s (Function.update (q s) a z.1, Function.update (deriv q s) a z.2))
        (fun s => q s a) t w := by
  set J : Q →L[ℝ] (Fin N → Q) := ContinuousLinearMap.pi (Pi.single a (ContinuousLinearMap.id ℝ Q))
    with hJ
  have hJw : ∀ u : Q, J u = Pi.single a u := fun u => by
    funext b
    rcases eq_or_ne b a with rfl | hb
    · simp [hJ]
    · simp [hJ, hb]
  set La : Mechanics.Lagrangian Q :=
    fun s z => L s (Function.update (q s) a z.1, Function.update (deriv q s) a z.2) with hLa
  have hda : ∀ s, DifferentiableAt ℝ q s → deriv (fun s => q s a) s = deriv q s a := fun s hs =>
    (hasDerivAt_pi.mp hs.hasDerivAt a).deriv
  have hfd : ∀ s, DifferentiableAt ℝ (L s) (q s, deriv q s) → DifferentiableAt ℝ q s →
      fderiv ℝ (La s) (q s a, deriv (fun s => q s a) s) =
        (fderiv ℝ (L s) (q s, deriv q s)).comp
          ((J.comp (ContinuousLinearMap.fst ℝ Q Q)).prod (J.comp (ContinuousLinearMap.snd ℝ Q Q)))
      := by
    intro s hLs hqs
    have hι : HasFDerivAt (fun z : Q × Q => (Function.update (q s) a z.1,
        Function.update (deriv q s) a z.2))
        ((J.comp (ContinuousLinearMap.fst ℝ Q Q)).prod (J.comp (ContinuousLinearMap.snd ℝ Q Q)))
        (q s a, deriv (fun s => q s a) s) := by
      have hu1 : HasFDerivAt (Function.update (q s) a) J (q s a) :=
        hasFDerivAt_update (q s) (q s a)
      have hu2 : HasFDerivAt (Function.update (deriv q s) a) J (deriv (fun s => q s a) s) :=
        hasFDerivAt_update (deriv q s) _
      have h1 := hu1.comp (q s a, deriv (fun s => q s a) s)
        (hasFDerivAt_fst (𝕜 := ℝ) (E := Q) (F := Q) (p := (q s a, deriv (fun s => q s a) s)))
      have h2 := hu2.comp (q s a, deriv (fun s => q s a) s)
        (hasFDerivAt_snd (𝕜 := ℝ) (E := Q) (F := Q) (p := (q s a, deriv (fun s => q s a) s)))
      exact h1.prodMk h2
    have hpt : (Function.update (q s) a (q s a, deriv (fun s => q s a) s).1,
        Function.update (deriv q s) a (q s a, deriv (fun s => q s a) s).2) =
        (q s, deriv q s) := by
      simp [hda s hqs]
    rw [← hpt] at hLs
    have := hLs.hasFDerivAt.comp (q s a, deriv (fun s => q s a) s) hι
    rw [hpt] at this
    exact this.fderiv
  have hforce : Mechanics.force La (fun s => q s a) t =
      (Mechanics.force L q t).comp J := by
    rw [Mechanics.force, Mechanics.force, hfd t hL.self_of_nhds hq.self_of_nhds]
    ext u
    simp
  have hmom : Mechanics.momentum La (fun s => q s a) =ᶠ[𝓝 t]
      fun s => (Mechanics.momentum L q s).comp J := by
    filter_upwards [hL, hq] with s hLs hqs
    rw [Mechanics.momentum, Mechanics.momentum, hfd s hLs hqs]
    ext u
    simp
  have hdM : deriv (Mechanics.momentum La (fun s => q s a)) t =
      (deriv (Mechanics.momentum L q) t).comp J := by
    rw [hmom.deriv_eq]
    have := hM.hasDerivAt.clm_comp (hasDerivAt_const t J)
    simpa using this.deriv
  rw [Mechanics.eulerLagrange, Mechanics.eulerLagrange, hforce, hdM, sub_apply, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hJw]

/-! ### The potentials of Darwin of a point charge -/

/-- The scalar potential of Darwin of a point charge `e` on the path `c`, `e/(4π‖x − c(t)‖)`. -/
def pointScalar (e : ℝ) (c : ℝ → E3) (p : ℝ × E3) : ℝ := e * Potential.newtonKernel (p.2 - c p.1)

/-- The vector potential of Darwin of a point charge `e` on the path `c`,
`e [ċ + (ċ · 𝐧)𝐧]/(8π‖x − c(t)‖)` with `𝐧 = (x − c(t))/‖x − c(t)‖`. -/
def pointVector (e : ℝ) (c : ℝ → E3) (i : Fin 3) (p : ℝ × E3) : ℝ :=
  e * ∑ k, deriv c p.1 k * darwinKernel i k (p.2 - c p.1)

/-- The kernel of Darwin is smooth away from the origin. -/
theorem contDiffAt_darwinKernel (i k : Fin 3) {z : E3} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (darwinKernel i k) z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hN : ContDiffAt ℝ ∞ (fun y : E3 => ‖y‖) z := contDiffAt_norm ℝ hz
  have hc : ∀ l : Fin 3, ContDiffAt ℝ ∞ (fun y : E3 => y l) z := fun l =>
    (EuclideanSpace.proj l : E3 →L[ℝ] ℝ).contDiff.contDiffAt
  unfold darwinKernel
  exact ((contDiffAt_const.div hN hn).add (((hc i).mul (hc k)).div (hN.pow 3)
    (pow_ne_zero 3 hn))).div_const _

/-- The scalar potential of Darwin is smooth off the path. -/
theorem contDiffAt_pointScalar (e : ℝ) {c : ℝ → E3} (hc : ContDiff ℝ ∞ c) {p : ℝ × E3}
    (hp : p.2 ≠ c p.1) : ContDiffAt ℝ ∞ (pointScalar e c) p := by
  have hd : ContDiff ℝ ∞ fun p : ℝ × E3 => p.2 - c p.1 := contDiff_snd.sub (hc.comp contDiff_fst)
  have h : ContDiffAt ℝ ∞ (Potential.newtonKernel ∘ fun p : ℝ × E3 => p.2 - c p.1) p :=
    ContDiffAt.comp (g := Potential.newtonKernel) (f := fun p : ℝ × E3 => p.2 - c p.1) p
      (Potential.contDiffAt_newtonKernel (sub_ne_zero.mpr hp)) hd.contDiffAt
  exact contDiffAt_const.mul h

/-- The vector potential of Darwin is smooth off the path. -/
theorem contDiffAt_pointVector (e : ℝ) {c : ℝ → E3} (hc : ContDiff ℝ ∞ c) (i : Fin 3)
    {p : ℝ × E3} (hp : p.2 ≠ c p.1) : ContDiffAt ℝ ∞ (pointVector e c i) p := by
  have hd : ContDiff ℝ ∞ fun p : ℝ × E3 => p.2 - c p.1 := contDiff_snd.sub (hc.comp contDiff_fst)
  have hc' : ContDiff ℝ ∞ (deriv c) := hc.iterate_deriv 1
  refine contDiffAt_const.mul (ContDiffAt.sum fun k _ => ContDiffAt.mul ?_ ?_)
  · exact ((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp (hc'.comp contDiff_fst)).contDiffAt
  · exact ContDiffAt.comp (g := darwinKernel i k) (f := fun p : ℝ × E3 => p.2 - c p.1) p
      (contDiffAt_darwinKernel i k (sub_ne_zero.mpr hp)) hd.contDiffAt

/-- The potentials are differentiable near a point off the path. -/
theorem eventually_differentiableAt_point {F : ℝ × E3 → ℝ} {c : ℝ → E3}
    (hc : Continuous c) (hF : ∀ p : ℝ × E3, p.2 ≠ c p.1 → ContDiffAt ℝ ∞ F p) {p : ℝ × E3}
    (hp : p.2 ≠ c p.1) : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ F q := by
  have hO : IsOpen {q : ℝ × E3 | q.2 ≠ c q.1} :=
    isOpen_ne_fun continuous_snd (hc.comp continuous_fst)
  filter_upwards [hO.mem_nhds hp] with q hq
  exact (hF q hq).differentiableAt (by simp)

/-- **The pair interaction of Darwin as the coupling of one charge to the potentials of the
other**: `darwinPair e₁ e₂ r (c t) 𝐮 ċ(t) = −e₁ φ'(t, r) + e₁ 𝐮 · 𝐚'(t, r)` with the potentials
`pointScalar`, `pointVector` of the charge `e₂` on the path `c`. -/
theorem darwinPair_eq_point (e₁ e₂ : ℝ) (c : ℝ → E3) (s : ℝ) (r u : E3) :
    darwinPair e₁ e₂ r (c s) u (deriv c s) =
      -e₁ * pointScalar e₂ c (s, r) + e₁ * ∑ k, u k * pointVector e₂ c k (s, r) := by
  have hsum := sum_darwinKernel (deriv c s) u (r - c s)
  have hk : ∑ k, u k * pointVector e₂ c k (s, r) =
      e₂ * ∑ k, u k * ∑ j, deriv c s j * darwinKernel k j (r - c s) := by
    simp only [pointVector, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hk, hsum]
  have h1 : c s - r = -(r - c s) := (neg_sub r (c s)).symm
  simp only [darwinPair, pointScalar, Potential.newtonKernel, h1, norm_neg, smul_neg,
    inner_neg_right, real_inner_comm u (deriv c s)]
  rw [show (4 * π * ‖r - c s‖)⁻¹ = 1 / (4 * π * ‖r - c s‖) from (one_div _).symm]
  ring

/-- The kinetic Lagrangian `−m + m v²/2 + m v⁴/8` of the expansion. -/
def darwinKinetic (m : ℝ) (v : E3) : ℝ := -m + m * ‖v‖ ^ 2 / 2 + m * ‖v‖ ^ 4 / 8

/-- The kinetic Lagrangian is smooth. -/
theorem contDiff_darwinKinetic (m : ℝ) : ContDiff ℝ ∞ (darwinKinetic m) := by
  have h2 : ContDiff ℝ ∞ fun v : E3 => ‖v‖ ^ 2 := contDiff_norm_sq ℝ
  have h4 : (fun v : E3 => ‖v‖ ^ 4) = fun v => (‖v‖ ^ 2) ^ 2 := by
    funext v
    ring
  have h4' : ContDiff ℝ ∞ fun v : E3 => ‖v‖ ^ 4 := by
    rw [h4]
    exact h2.pow 2
  unfold darwinKinetic
  exact (contDiff_const.add ((contDiff_const.mul h2).div_const _)).add
    ((contDiff_const.mul h4').div_const _)

/-- The momentum of the kinetic Lagrangian, `∂K/∂vᵢ = m (1 + v²/2) vᵢ`. -/
theorem fderiv_darwinKinetic (m : ℝ) (v : E3) (i : Fin 3) :
    fderiv ℝ (darwinKinetic m) v (EuclideanSpace.single i 1) = m * (1 + ‖v‖ ^ 2 / 2) * v i := by
  have h2 := (hasStrictFDerivAt_norm_sq v).hasFDerivAt
  have h4 : HasFDerivAt (fun v : E3 => (‖v‖ ^ 2) ^ 2) ((2 * (‖v‖ ^ 2) ^ 1) • (2 • innerSL ℝ v)) v :=
    (hasDerivAt_pow 2 _).comp_hasFDerivAt v h2
  have hK : HasFDerivAt (darwinKinetic m)
      ((m / 2) • (2 • innerSL ℝ v) + (m / 8) • ((2 * (‖v‖ ^ 2) ^ 1) • (2 • innerSL ℝ v))) v := by
    have := ((h2.const_mul (m / 2)).const_add (-m)).fun_add (h4.const_mul (m / 8))
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    simp only [darwinKinetic]
    ring
  rw [hK.fderiv]
  simp [EuclideanSpace.inner_single_right, nsmul_eq_mul]
  ring

/-! ### The Euler–Lagrange expression of the Lagrangian of Darwin -/

/-- The Lagrangian of Darwin is smooth where the charges are at distinct positions. -/
theorem contDiffAt_darwinLagrangian {N : ℕ} (m e : Fin N → ℝ) (s : ℝ)
    {z : (Fin N → E3) × (Fin N → E3)} (hz : ∀ b c, b ≠ c → z.1 b ≠ z.1 c) :
    ContDiffAt ℝ ∞ (darwinLagrangian m e s) z := by
  have hp1 : ∀ c, ContDiff ℝ ∞ fun z : (Fin N → E3) × (Fin N → E3) => z.1 c := fun c => by
    fun_prop
  have hp2 : ∀ c, ContDiff ℝ ∞ fun z : (Fin N → E3) × (Fin N → E3) => z.2 c := fun c => by
    fun_prop
  have hkin : ContDiff ℝ ∞ fun z : (Fin N → E3) × (Fin N → E3) =>
      ∑ c, (-m c + m c * ‖z.2 c‖ ^ 2 / 2 + m c * ‖z.2 c‖ ^ 4 / 8) :=
    ContDiff.sum fun c _ => (contDiff_darwinKinetic (m c)).comp (hp2 c)
  refine hkin.contDiffAt.add (ContDiffAt.sum fun c _ => ContDiffAt.sum fun d _ => ?_)
  by_cases hcd : c < d
  · simp only [hcd, ↓reduceIte]
    have hne : z.1 d - z.1 c ≠ 0 := sub_ne_zero.mpr (hz d c (ne_of_gt hcd))
    have hD : ContDiffAt ℝ ∞ (fun z : (Fin N → E3) × (Fin N → E3) => z.1 d - z.1 c) z :=
      ((hp1 d).sub (hp1 c)).contDiffAt
    have hN : ContDiffAt ℝ ∞ (fun z : (Fin N → E3) × (Fin N → E3) => ‖z.1 d - z.1 c‖) z :=
      hD.norm ℝ hne
    have hN0 : ‖z.1 d - z.1 c‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    have hn : ContDiffAt ℝ ∞ (fun z : (Fin N → E3) × (Fin N → E3) =>
        ‖z.1 d - z.1 c‖⁻¹ • (z.1 d - z.1 c)) z := (hN.inv hN0).smul hD
    unfold darwinPair
    exact (contDiffAt_const.div (contDiffAt_const.mul hN) (by positivity)).add
      ((contDiffAt_const.mul ((((hp2 c).contDiffAt).inner ℝ (hp2 d).contDiffAt).add
        ((((hp2 c).contDiffAt).inner ℝ hn).mul (((hp2 d).contDiffAt).inner ℝ hn)))).div
        (contDiffAt_const.mul hN) (by positivity))
  · simp only [hcd, ↓reduceIte]
    exact contDiffAt_const

/-- The terms of the Lagrangian of Darwin without the charge `a`: the kinetic Lagrangians of the
others and their pair interactions. -/
def darwinRest {N : ℕ} (m e : Fin N → ℝ) (Q : Fin N → ℝ → E3) (a : Fin N) (s : ℝ) : ℝ :=
  ∑ c ∈ ({a}ᶜ : Finset (Fin N)), darwinKinetic (m c) (deriv (Q c) s) +
    ∑ c ∈ ({a}ᶜ : Finset (Fin N)), ∑ d ∈ ({a}ᶜ : Finset (Fin N)),
      if c < d then darwinPair (e c) (e d) (Q c s) (Q d s) (deriv (Q c) s) (deriv (Q d) s) else 0

/-- **The Lagrangian of Darwin seen by the charge `a`**: with the other charges on their paths,
(65.7) is the Lagrangian of the charge `a` in the potentials of Darwin of the others, plus terms
of the time alone. -/
theorem darwinLagrangian_update {N : ℕ} (m e : Fin N → ℝ) (Q : Fin N → ℝ → E3) (a : Fin N)
    (s : ℝ) (z : E3 × E3) :
    darwinLagrangian m e s (Function.update (fun b => Q b s) a z.1,
        Function.update (fun b => deriv (Q b) s) a z.2) =
      pointLagrangian (darwinKinetic (m a)) (e a)
        (fun p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointScalar (e b) (Q b) p)
        (fun k p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointVector (e b) (Q b) k p)
        (darwinRest m e Q a) s z := by
  set X := Function.update (fun b => Q b s) a z.1 with hX
  set U := Function.update (fun b => deriv (Q b) s) a z.2 with hU
  have hXa : X a = z.1 := by simp [hX]
  have hUa : U a = z.2 := by simp [hU]
  have hXc : ∀ c ∈ ({a}ᶜ : Finset (Fin N)), X c = Q c s := fun c hc => by
    have hca : c ≠ a := by simpa using hc
    simp [hX, Function.update_of_ne hca]
  have hUc : ∀ c ∈ ({a}ᶜ : Finset (Fin N)), U c = deriv (Q c) s := fun c hc => by
    have hca : c ≠ a := by simpa using hc
    simp [hU, Function.update_of_ne hca]
  set T : Fin N → Fin N → ℝ := fun c d =>
    if c < d then darwinPair (e c) (e d) (X c) (X d) (U c) (U d) else 0 with hT
  set P : Fin N → ℝ := fun b => darwinPair (e a) (e b) z.1 (Q b s) z.2 (deriv (Q b) s) with hP
  have hkin : ∑ c, (-m c + m c * ‖U c‖ ^ 2 / 2 + m c * ‖U c‖ ^ 4 / 8) =
      darwinKinetic (m a) z.2 + ∑ c ∈ ({a}ᶜ : Finset (Fin N)), darwinKinetic (m c) (deriv (Q c) s)
      := by
    rw [Fintype.sum_eq_add_sum_compl a]
    congr 1
    · rw [hUa]
      rfl
    · exact Finset.sum_congr rfl fun c hc => by rw [hUc c hc]; rfl
  have hrow : ∑ d, T a d = ∑ b ∈ ({a}ᶜ : Finset (Fin N)), if a < b then P b else 0 := by
    rw [Fintype.sum_eq_add_sum_compl a]
    simp only [hT, lt_irrefl, ↓reduceIte, zero_add]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hXa, hUa, hXc b hb, hUc b hb]
  have hcol : ∑ c ∈ ({a}ᶜ : Finset (Fin N)), T c a =
      ∑ b ∈ ({a}ᶜ : Finset (Fin N)), if b < a then P b else 0 := by
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [hT, hP]
    rw [hXa, hUa, hXc b hb, hUc b hb, darwinPair_comm]
  have hpair : ∑ c, ∑ d, T c d = ∑ b ∈ ({a}ᶜ : Finset (Fin N)), P b +
      ∑ c ∈ ({a}ᶜ : Finset (Fin N)), ∑ d ∈ ({a}ᶜ : Finset (Fin N)),
        if c < d then darwinPair (e c) (e d) (Q c s) (Q d s) (deriv (Q c) s) (deriv (Q d) s)
          else 0 := by
    rw [Fintype.sum_eq_add_sum_compl a, hrow,
      Finset.sum_congr rfl fun c _ => Fintype.sum_eq_add_sum_compl a (T c),
      Finset.sum_add_distrib, hcol, ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun b hb => ?_
      have hba : b ≠ a := by simpa using hb
      rcases lt_or_gt_of_ne hba with h | h
      · simp [h, not_lt.mpr h.le]
      · simp [h, not_lt.mpr h.le]
    · refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
      simp only [hT]
      rw [hXc c hc, hXc d hd, hUc c hc, hUc d hd]
  have hP' : ∑ b ∈ ({a}ᶜ : Finset (Fin N)), P b =
      -e a * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointScalar (e b) (Q b) (s, z.1) +
        e a * ∑ k, z.2 k * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointVector (e b) (Q b) k (s, z.1) := by
    simp only [hP, darwinPair_eq_point, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  change ∑ c, (-m c + m c * ‖U c‖ ^ 2 / 2 + m c * ‖U c‖ ^ 4 / 8) + ∑ c, ∑ d, T c d = _
  rw [hkin, hpair, hP', pointLagrangian, darwinRest]
  ring

/-- **The Euler–Lagrange expression of the Lagrangian of Darwin** (target (iii)): with the
charges on smooth paths `Q b` at distinct positions at the time `t`, the residual of (65.7) for
the charge `a` in the direction `eᵢ` is

  `−d/dt [mₐ(1 + vₐ²/2) vₐᵢ] + eₐ (Eᵢ + (𝐯ₐ × 𝐁)ᵢ)(t, Qₐ(t))`,

with the fields of the potentials of Darwin `pointScalar`, `pointVector` of the other charges.
The identity is exact and local. -/
theorem eulerLagrange_darwinLagrangian {N : ℕ} (m e : Fin N → ℝ) {Q : Fin N → ℝ → E3}
    (hQ : ∀ b, ContDiff ℝ ∞ (Q b)) {t : ℝ} (hsep : ∀ b c, b ≠ c → Q b t ≠ Q c t) (a : Fin N)
    (i : Fin 3) :
    Mechanics.eulerLagrange (darwinLagrangian m e) (fun s b => Q b s) t
        (Pi.single a (EuclideanSpace.single i 1)) =
      -deriv (fun s => m a * (1 + ‖deriv (Q a) s‖ ^ 2 / 2) * deriv (Q a) s i) t +
        e a * lorentzDensity (fun p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointScalar (e b) (Q b) p)
          (fun k p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointVector (e b) (Q b) k p)
          (deriv (Q a) t) i (t, Q a t) := by
  set q : ℝ → Fin N → E3 := fun s b => Q b s with hqd
  have hq : ContDiff ℝ ∞ q := contDiff_pi.mpr hQ
  have hdQ : ∀ b, ContDiff ℝ ∞ (deriv (Q b)) := fun b => (hQ b).iterate_deriv 1
  have hdq : ∀ s, deriv q s = fun b => deriv (Q b) s := fun s =>
    deriv_pi fun b => ((hQ b).differentiable (by simp)) s
  have hdq' : deriv q = fun s b => deriv (Q b) s := funext hdq
  have hsep' : ∀ᶠ s in 𝓝 t, ∀ b c, b ≠ c → Q b s ≠ Q c s := by
    refine Filter.eventually_all.mpr fun b => Filter.eventually_all.mpr fun c => ?_
    by_cases hbc : b = c
    · exact Eventually.of_forall fun _ h => absurd hbc h
    · have hO : IsOpen {s | Q b s ≠ Q c s} :=
        isOpen_ne_fun (hQ b).continuous (hQ c).continuous
      filter_upwards [hO.mem_nhds (hsep b c hbc)] with s hs _
      exact hs
  have hL0 : ContDiffAt ℝ ∞ (darwinLagrangian m e t) (q t, deriv q t) :=
    contDiffAt_darwinLagrangian m e t (by rw [hdq]; exact hsep)
  have hL : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (darwinLagrangian m e s) (q s, deriv q s) := by
    filter_upwards [hsep'] with s hs
    exact (contDiffAt_darwinLagrangian m e s (by rw [hdq]; exact hs)).differentiableAt (by simp)
  have hM : DifferentiableAt ℝ (Mechanics.momentum (darwinLagrangian m e) q) t := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ (darwinLagrangian m e t)) (q t, deriv q t) :=
      (hL0.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
    have h2 : DifferentiableAt ℝ (fun s => (q s, deriv q s)) t :=
      ((hq.differentiable (by simp)) t).prodMk
        (((contDiff_pi.mpr hdQ).differentiable (by simp) t).congr_of_eventuallyEq
          (Eventually.of_forall fun s => hdq s))
    exact (h1.comp t h2).clm_comp (differentiableAt_const _)
  rw [eulerLagrange_update (darwinLagrangian m e) q a hL
    (Eventually.of_forall fun s => (hq.differentiable (by simp)) s) hM]
  have hLa : (fun s z => darwinLagrangian m e s (Function.update (q s) a z.1,
      Function.update (deriv q s) a z.2)) = pointLagrangian (darwinKinetic (m a)) (e a)
        (fun p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointScalar (e b) (Q b) p)
        (fun k p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointVector (e b) (Q b) k p)
        (darwinRest m e Q a) := by
    funext s z
    rw [hdq s]
    exact darwinLagrangian_update m e Q a s z
  rw [hLa]
  have hQa : (fun s => q s a) = Q a := rfl
  rw [hQa]
  have hevφ : ∀ᶠ p in 𝓝 (t, Q a t), DifferentiableAt ℝ
      (fun p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointScalar (e b) (Q b) p) p := by
    have : ∀ᶠ p in 𝓝 (t, Q a t), ∀ b ∈ ({a}ᶜ : Finset (Fin N)),
        DifferentiableAt ℝ (pointScalar (e b) (Q b)) p := by
      rw [eventually_all_finset]
      intro b hb
      exact eventually_differentiableAt_point (hQ b).continuous
        (fun p hp => contDiffAt_pointScalar (e b) (hQ b) hp)
        (hsep a b (by simpa [eq_comm] using hb))
    filter_upwards [this] with p hp
    exact DifferentiableAt.fun_sum fun b hb => hp b hb
  have hevA : ∀ k, ∀ᶠ p in 𝓝 (t, Q a t), DifferentiableAt ℝ
      (fun p => ∑ b ∈ ({a}ᶜ : Finset (Fin N)), pointVector (e b) (Q b) k p) p := by
    intro k
    have : ∀ᶠ p in 𝓝 (t, Q a t), ∀ b ∈ ({a}ᶜ : Finset (Fin N)),
        DifferentiableAt ℝ (pointVector (e b) (Q b) k) p := by
      rw [eventually_all_finset]
      intro b hb
      exact eventually_differentiableAt_point (hQ b).continuous
        (fun p hp => contDiffAt_pointVector (e b) (hQ b) k hp)
        (hsep a b (by simpa [eq_comm] using hb))
    filter_upwards [this] with p hp
    exact DifferentiableAt.fun_sum fun b hb => hp b hb
  rw [eulerLagrange_pointLagrangian ((contDiff_darwinKinetic (m a)).of_le (by simp)) (e a) _
    hevφ hevA (Eventually.of_forall fun s => ((hQ a).differentiable (by simp)) s)
    ((hdQ a).differentiable (by simp) t) i]
  simp only [fderiv_darwinKinetic]

/-- Two separated straight paths, `t ↦ t (κ e₀)` and `t ↦ 5 e₁ + t (κ e₂)`, slow for small `κ`. -/
def examplePaths (κ : ℝ) : Fin 2 → ℝ → E3 :=
  ![fun s => s • (κ • (EuclideanSpace.single 0 1 : E3)),
    fun s => (5 : ℝ) • (EuclideanSpace.single 1 1 : E3) + s • (κ • EuclideanSpace.single 2 1)]

/-- **An instance**: for two charges on `examplePaths κ` at the time `0`, the residual of (65.7)
for the first charge is the kinetic term plus the Lorentz force of the potentials of Darwin of
the second. -/
theorem eulerLagrange_darwinLagrangian_example (m e : Fin 2 → ℝ) (κ : ℝ) (i : Fin 3) :
    Mechanics.eulerLagrange (darwinLagrangian m e) (fun s b => examplePaths κ b s) 0
        (Pi.single 0 (EuclideanSpace.single i 1)) =
      -deriv (fun s => m 0 * (1 + ‖deriv (examplePaths κ 0) s‖ ^ 2 / 2) *
          deriv (examplePaths κ 0) s i) 0 +
        e 0 * lorentzDensity
          (fun p => ∑ b ∈ ({0}ᶜ : Finset (Fin 2)), pointScalar (e b) (examplePaths κ b) p)
          (fun k p => ∑ b ∈ ({0}ᶜ : Finset (Fin 2)), pointVector (e b) (examplePaths κ b) k p)
          (deriv (examplePaths κ 0) 0) i (0, examplePaths κ 0 0) := by
  refine eulerLagrange_darwinLagrangian m e (fun b => ?_) (fun b c hbc => ?_) 0 i
  · fin_cases b
    · exact contDiff_id.smul contDiff_const
    · exact contDiff_const.add (contDiff_id.smul contDiff_const)
  · fin_cases b <;> fin_cases c
    · exact absurd rfl hbc
    · intro h
      have := congrArg (fun v : E3 => v 1) h
      simp [examplePaths] at this
    · intro h
      have := congrArg (fun v : E3 => v 1) h
      simp [examplePaths] at this
    · exact absurd rfl hbc

/-! ### Second-order expansions with uniform remainders -/

section Jet

variable {P : Type*}

/-- `q = q₀ + εq₁ + ε²q₂ + O(ε³)` uniformly on the set `S` of parameters, with bounded
coefficients. -/
def Jet (S : Set P) (ε q q₀ q₁ q₂ : P → ℝ) : Prop :=
  ∃ C, ∀ p ∈ S, |q p - (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p)| ≤ C * |ε p| ^ 3 ∧
    |q₀ p| ≤ C ∧ |q₁ p| ≤ C ∧ |q₂ p| ≤ C

variable {S : Set P} {ε : P → ℝ}

/-- A polynomial in `ε` of degree three with bounded coefficients. -/
theorem Jet.of_eq {q q₀ q₁ q₂ q₃ : P → ℝ}
    (h : ∀ p ∈ S, q p = q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p + ε p ^ 3 * q₃ p)
    (hb : ∃ C, ∀ p ∈ S, |q₀ p| ≤ C ∧ |q₁ p| ≤ C ∧ |q₂ p| ≤ C ∧ |q₃ p| ≤ C) :
    Jet S ε q q₀ q₁ q₂ := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨C, fun p hp => ⟨?_, (hC p hp).1, (hC p hp).2.1, (hC p hp).2.2.1⟩⟩
  rw [h p hp, show q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p + ε p ^ 3 * q₃ p -
    (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p) = ε p ^ 3 * q₃ p by ring, abs_mul, abs_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC p hp).2.2.2 (by positivity)

/-- A bounded function of the parameters is its own expansion. -/
theorem Jet.const {q : P → ℝ} (hb : ∃ C, ∀ p ∈ S, |q p| ≤ C) :
    Jet S ε q q (fun _ => 0) (fun _ => 0) := by
  obtain ⟨C, hC⟩ := hb
  refine Jet.of_eq (q₃ := fun _ => 0) (fun p _ => by ring) ⟨max C 0, fun p hp => ?_⟩
  simp only [abs_zero]
  exact ⟨(hC p hp).trans (le_max_left _ _), le_max_right _ _, le_max_right _ _,
    le_max_right _ _⟩

/-- The parameter `ε` itself. -/
theorem Jet.eps : Jet S ε ε (fun _ => 0) (fun _ => 1) (fun _ => 0) :=
  Jet.of_eq (q₃ := fun _ => 0) (fun p _ => by ring) ⟨1, fun p _ => by norm_num⟩

/-- The sum of two expansions. -/
theorem Jet.add {q q₀ q₁ q₂ r r₀ r₁ r₂ : P → ℝ} (hq : Jet S ε q q₀ q₁ q₂)
    (hr : Jet S ε r r₀ r₁ r₂) :
    Jet S ε (fun p => q p + r p) (fun p => q₀ p + r₀ p) (fun p => q₁ p + r₁ p)
      (fun p => q₂ p + r₂ p) := by
  obtain ⟨C, hC⟩ := hq
  obtain ⟨D, hD⟩ := hr
  refine ⟨C + D, fun p hp => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hC p hp
  obtain ⟨k1, k2, k3, k4⟩ := hD p hp
  refine ⟨?_, (abs_add_le _ _).trans (by linarith), (abs_add_le _ _).trans (by linarith),
    (abs_add_le _ _).trans (by linarith)⟩
  calc |q p + r p - (q₀ p + r₀ p + ε p * (q₁ p + r₁ p) + ε p ^ 2 * (q₂ p + r₂ p))|
      = |(q p - (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p)) +
          (r p - (r₀ p + ε p * r₁ p + ε p ^ 2 * r₂ p))| := by ring_nf
    _ ≤ C * |ε p| ^ 3 + D * |ε p| ^ 3 := (abs_add_le _ _).trans (add_le_add h1 k1)
    _ = (C + D) * |ε p| ^ 3 := by ring

/-- A constant multiple of an expansion. -/
theorem Jet.const_mul {q q₀ q₁ q₂ : P → ℝ} (c : ℝ) (hq : Jet S ε q q₀ q₁ q₂) :
    Jet S ε (fun p => c * q p) (fun p => c * q₀ p) (fun p => c * q₁ p) (fun p => c * q₂ p) := by
  obtain ⟨C, hC⟩ := hq
  refine ⟨|c| * C, fun p hp => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hC p hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show c * q p - (c * q₀ p + ε p * (c * q₁ p) + ε p ^ 2 * (c * q₂ p)) =
      c * (q p - (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p)) by ring, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h3 (abs_nonneg c)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h4 (abs_nonneg c)

/-- The difference of two expansions. -/
theorem Jet.sub {q q₀ q₁ q₂ r r₀ r₁ r₂ : P → ℝ} (hq : Jet S ε q q₀ q₁ q₂)
    (hr : Jet S ε r r₀ r₁ r₂) :
    Jet S ε (fun p => q p - r p) (fun p => q₀ p - r₀ p) (fun p => q₁ p - r₁ p)
      (fun p => q₂ p - r₂ p) := by
  have := hq.add (hr.const_mul (-1))
  simpa [sub_eq_add_neg] using this

/-- The value of a quadratic polynomial in `ε` with coefficients bounded by `C`, for `|ε| ≤ 1`. -/
theorem abs_poly2_le {a b c e C : ℝ} (he : |e| ≤ 1) (ha : |a| ≤ C) (hb : |b| ≤ C)
    (hc : |c| ≤ C) : |a + e * b + e ^ 2 * c| ≤ 3 * C := by
  have he0 := abs_nonneg e
  have h1 : |e * b| ≤ C := by
    rw [abs_mul]
    calc |e| * |b| ≤ 1 * |b| := mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ ≤ C := by linarith
  have h2 : |e ^ 2 * c| ≤ C := by
    rw [abs_mul, abs_pow]
    calc |e| ^ 2 * |c| ≤ 1 * |c| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ he0 he) (abs_nonneg _)
      _ ≤ C := by linarith
  have := abs_add_le (a + e * b) (e ^ 2 * c)
  have := abs_add_le a (e * b)
  linarith

/-- **The product of two expansions**, for `|ε| ≤ 1`. -/
theorem Jet.mul (hε : ∀ p ∈ S, |ε p| ≤ 1) {q q₀ q₁ q₂ r r₀ r₁ r₂ : P → ℝ}
    (hq : Jet S ε q q₀ q₁ q₂) (hr : Jet S ε r r₀ r₁ r₂) :
    Jet S ε (fun p => q p * r p) (fun p => q₀ p * r₀ p) (fun p => q₀ p * r₁ p + q₁ p * r₀ p)
      (fun p => q₀ p * r₂ p + q₁ p * r₁ p + q₂ p * r₀ p) := by
  obtain ⟨C, hC⟩ := hq
  obtain ⟨D, hD⟩ := hr
  refine ⟨C * (4 * D) + 3 * C * D + 3 * (C * D), fun p hp => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hC p hp
  obtain ⟨k1, k2, k3, k4⟩ := hD p hp
  have he := hε p hp
  have he0 := abs_nonneg (ε p)
  have hCn : 0 ≤ C := (abs_nonneg _).trans h2
  have hDn : 0 ≤ D := (abs_nonneg _).trans k2
  have he3 : |ε p| ^ 3 ≤ 1 := pow_le_one₀ he0 he
  have hQ := abs_poly2_le he h2 h3 h4
  have hRr := abs_poly2_le he k2 k3 k4
  have hR : |r p| ≤ 4 * D := by
    have := abs_sub_abs_le_abs_sub (r p) (r₀ p + ε p * r₁ p + ε p ^ 2 * r₂ p)
    have : D * |ε p| ^ 3 ≤ D := by nlinarith
    linarith
  have hCD : ∀ {x y : ℝ}, |x| ≤ C → |y| ≤ D → |x * y| ≤ C * D := fun hx hy => by
    rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) hCn
  have hid : q p * r p - (q₀ p * r₀ p + ε p * (q₀ p * r₁ p + q₁ p * r₀ p) +
      ε p ^ 2 * (q₀ p * r₂ p + q₁ p * r₁ p + q₂ p * r₀ p)) =
      (q p - (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p)) * r p +
        (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p) * (r p - (r₀ p + ε p * r₁ p + ε p ^ 2 * r₂ p)) +
        ε p ^ 3 * (q₁ p * r₂ p + q₂ p * r₁ p + ε p * (q₂ p * r₂ p)) := by ring
  refine ⟨?_, hCD h2 k2 |>.trans (by nlinarith), ?_, ?_⟩
  · rw [hid]
    have t1 : |(q p - (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p)) * r p| ≤
        C * |ε p| ^ 3 * (4 * D) := by
      rw [abs_mul]; exact mul_le_mul h1 hR (abs_nonneg _) (by positivity)
    have t2 : |(q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p) *
        (r p - (r₀ p + ε p * r₁ p + ε p ^ 2 * r₂ p))| ≤ 3 * C * (D * |ε p| ^ 3) := by
      rw [abs_mul]; exact mul_le_mul hQ k1 (abs_nonneg _) (by positivity)
    have t3 : |ε p ^ 3 * (q₁ p * r₂ p + q₂ p * r₁ p + ε p * (q₂ p * r₂ p))| ≤
        |ε p| ^ 3 * (3 * (C * D)) := by
      rw [abs_mul, abs_pow]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := abs_add_le (q₁ p * r₂ p + q₂ p * r₁ p) (ε p * (q₂ p * r₂ p))
      have := abs_add_le (q₁ p * r₂ p) (q₂ p * r₁ p)
      have h5 : |ε p * (q₂ p * r₂ p)| ≤ C * D := by
        rw [abs_mul]
        calc |ε p| * |q₂ p * r₂ p| ≤ 1 * (C * D) :=
              mul_le_mul he (hCD h4 k4) (abs_nonneg _) zero_le_one
          _ = C * D := one_mul _
      linarith [hCD h3 k4, hCD h4 k3]
    have := abs_add_le ((q p - (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p)) * r p +
      (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p) * (r p - (r₀ p + ε p * r₁ p + ε p ^ 2 * r₂ p)))
      (ε p ^ 3 * (q₁ p * r₂ p + q₂ p * r₁ p + ε p * (q₂ p * r₂ p)))
    have := abs_add_le ((q p - (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p)) * r p)
      ((q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p) * (r p - (r₀ p + ε p * r₁ p + ε p ^ 2 * r₂ p)))
    nlinarith
  · have := abs_add_le (q₀ p * r₁ p) (q₁ p * r₀ p)
    linarith [hCD h2 k3, hCD h3 k2, mul_nonneg hCn hDn]
  · have := abs_add_le (q₀ p * r₂ p + q₁ p * r₁ p) (q₂ p * r₀ p)
    have := abs_add_le (q₀ p * r₂ p) (q₁ p * r₁ p)
    linarith [hCD h2 k4, hCD h3 k3, hCD h4 k2, mul_nonneg hCn hDn]

/-- Two functions within `K|ε|³` of each other have the same expansion. -/
theorem Jet.of_close {q q' q₀ q₁ q₂ : P → ℝ} {K : ℝ}
    (h : ∀ p ∈ S, |q p - q' p| ≤ K * |ε p| ^ 3) (hq : Jet S ε q' q₀ q₁ q₂) :
    Jet S ε q q₀ q₁ q₂ := by
  obtain ⟨C, hC⟩ := hq
  refine ⟨C + |K|, fun p hp => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := abs_add_le (q p - q' p) (q' p - (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p))
    rw [show q p - q' p + (q' p - (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p)) =
      q p - (q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p) by ring] at this
    have hK : K * |ε p| ^ 3 ≤ |K| * |ε p| ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    linarith [h p hp, (hC p hp).1]
  all_goals linarith [(hC p hp).2.1, (hC p hp).2.2.1, (hC p hp).2.2.2, abs_nonneg K]

/-- An expansion can be transported along pointwise equalities on `S`. -/
theorem Jet.congr {q q₀ q₁ q₂ q' a b c : P → ℝ} (hq : Jet S ε q q₀ q₁ q₂)
    (h : ∀ p ∈ S, q' p = q p) (ha : ∀ p ∈ S, a p = q₀ p) (hb : ∀ p ∈ S, b p = q₁ p)
    (hc : ∀ p ∈ S, c p = q₂ p) : Jet S ε q' a b c := by
  obtain ⟨C, hC⟩ := hq
  exact ⟨C, fun p hp => by rw [h p hp, ha p hp, hb p hp, hc p hp]; exact hC p hp⟩

/-- A finite sum of expansions. -/
theorem Jet.sum {ι : Type*} (s : Finset ι) {q q₀ q₁ q₂ : ι → P → ℝ}
    (hq : ∀ k ∈ s, Jet S ε (q k) (q₀ k) (q₁ k) (q₂ k)) :
    Jet S ε (fun p => ∑ k ∈ s, q k p) (fun p => ∑ k ∈ s, q₀ k p) (fun p => ∑ k ∈ s, q₁ k p)
      (fun p => ∑ k ∈ s, q₂ k p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine (Jet.const (q := fun _ => (0 : ℝ)) ⟨0, fun p _ => by simp⟩).congr ?_ ?_ ?_ ?_ <;>
      intro p _ <;> simp
  | insert k s hk ih =>
    have := (hq k (Finset.mem_insert_self k s)).add
      (ih fun k' hk' => hq k' (Finset.mem_insert_of_mem hk'))
    exact this.congr (fun p _ => by simp [Finset.sum_insert hk])
      (fun p _ => by simp [Finset.sum_insert hk]) (fun p _ => by simp [Finset.sum_insert hk])
      (fun p _ => by simp [Finset.sum_insert hk])

/-- An expansion with vanishing coefficients is `O(ε³)`. -/
theorem Jet.bound_three {q : P → ℝ}
    (hq : Jet S ε q (fun _ => 0) (fun _ => 0) (fun _ => 0)) :
    ∃ C, ∀ p ∈ S, |q p| ≤ C * |ε p| ^ 3 := by
  obtain ⟨C, hC⟩ := hq
  exact ⟨C, fun p hp => by simpa using (hC p hp).1⟩

/-- An expansion with vanishing coefficients of the orders `0` and `1` is `O(ε²)`. -/
theorem Jet.bound_two (hε : ∀ p ∈ S, |ε p| ≤ 1) {q q₂ : P → ℝ}
    (hq : Jet S ε q (fun _ => 0) (fun _ => 0) q₂) :
    ∃ C, ∀ p ∈ S, |q p| ≤ C * |ε p| ^ 2 := by
  obtain ⟨C, hC⟩ := hq
  refine ⟨2 * C, fun p hp => ?_⟩
  obtain ⟨h1, -, -, h4⟩ := hC p hp
  have he := hε p hp
  have he0 := abs_nonneg (ε p)
  have hCn : 0 ≤ C := (abs_nonneg _).trans h4
  simp only [zero_add, mul_zero] at h1
  have := abs_sub_abs_le_abs_sub (q p) (ε p ^ 2 * q₂ p)
  rw [abs_mul, abs_pow] at this
  have h3 : C * |ε p| ^ 3 ≤ C * |ε p| ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one he0 he (by norm_num)) hCn
  have h5 : |ε p| ^ 2 * |q₂ p| ≤ C * |ε p| ^ 2 := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right h4 (by positivity)
  linarith

/-- An expansion without a constant term is `O(ε)`. -/
theorem Jet.abs_le_of_zero (hε : ∀ p ∈ S, |ε p| ≤ 1) {q q₁ q₂ : P → ℝ}
    (hq : Jet S ε q (fun _ => 0) q₁ q₂) : ∃ C, ∀ p ∈ S, |q p| ≤ C * |ε p| := by
  obtain ⟨C, hC⟩ := hq
  refine ⟨3 * C, fun p hp => ?_⟩
  obtain ⟨h1, -, h3, h4⟩ := hC p hp
  have he := hε p hp
  have he0 := abs_nonneg (ε p)
  have hCn : 0 ≤ C := (abs_nonneg _).trans h3
  have := abs_sub_abs_le_abs_sub (q p) (0 + ε p * q₁ p + ε p ^ 2 * q₂ p)
  have hp1 : |0 + ε p * q₁ p + ε p ^ 2 * q₂ p| ≤ 2 * C * |ε p| := by
    rw [zero_add]
    have := abs_add_le (ε p * q₁ p) (ε p ^ 2 * q₂ p)
    rw [abs_mul, abs_mul, abs_pow] at this
    have : |ε p| ^ 2 * |q₂ p| ≤ |ε p| * C := by
      calc |ε p| ^ 2 * |q₂ p| = |ε p| * (|ε p| * |q₂ p|) := by ring
        _ ≤ |ε p| * (1 * C) := by gcongr
        _ = _ := by ring
    nlinarith
  have h3' : C * |ε p| ^ 3 ≤ C * |ε p| := by
    have := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one he0 he (by norm_num : 1 ≤ 3)) hCn
    simpa using this
  linarith

/-- **The inverse of an expansion** bounded away from zero. -/
theorem Jet.inv (hε : ∀ p ∈ S, |ε p| ≤ 1) {q q₀ q₁ q₂ : P → ℝ} (hq : Jet S ε q q₀ q₁ q₂)
    {c : ℝ} (hc : 0 < c) (hqc : ∀ p ∈ S, c ≤ |q p| ∧ c ≤ |q₀ p|) :
    Jet S ε (fun p => (q p)⁻¹) (fun p => (q₀ p)⁻¹) (fun p => -(q₁ p / q₀ p ^ 2))
      (fun p => q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2) := by
  obtain ⟨C, hC⟩ := hq
  set L := c⁻¹ with hL
  have hL0 : 0 < L := inv_pos.mpr hc
  have hinv : ∀ {x : ℝ}, c ≤ |x| → |x⁻¹| ≤ L := fun hx => by
    rw [abs_inv]; exact inv_anti₀ hc hx
  set I : P → ℝ := fun p => (q₀ p)⁻¹ + ε p * -(q₁ p / q₀ p ^ 2) +
    ε p ^ 2 * (q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2) with hI
  have hb : ∀ p ∈ S, |(q₀ p)⁻¹| ≤ L ∧ |-(q₁ p / q₀ p ^ 2)| ≤ C * L ^ 2 ∧
      |q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2| ≤ C ^ 2 * L ^ 3 + C * L ^ 2 := by
    intro p hp
    obtain ⟨-, h2, h3, h4⟩ := hC p hp
    have hu := hinv (hqc p hp).2
    have hCn : 0 ≤ C := (abs_nonneg _).trans h2
    refine ⟨hu, ?_, ?_⟩
    · rw [abs_neg, div_eq_mul_inv, abs_mul, ← inv_pow, abs_pow]
      exact mul_le_mul h3 (pow_le_pow_left₀ (abs_nonneg _) hu 2) (by positivity) hCn
    · refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [div_eq_mul_inv, abs_mul, ← inv_pow, abs_pow, abs_pow]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h3 2)
          (pow_le_pow_left₀ (abs_nonneg _) hu 3) (by positivity) (by positivity)
      · rw [div_eq_mul_inv, abs_mul, ← inv_pow, abs_pow]
        exact mul_le_mul h4 (pow_le_pow_left₀ (abs_nonneg _) hu 2) (by positivity) hCn
  have hJI : Jet S ε I (fun p => (q₀ p)⁻¹) (fun p => -(q₁ p / q₀ p ^ 2))
      (fun p => q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2) :=
    Jet.of_eq (q₃ := fun _ => 0) (fun p _ => by simp [hI])
      ⟨L + C * L ^ 2 + (C ^ 2 * L ^ 3 + C * L ^ 2), fun p hp => by
        obtain ⟨b1, b2, b3⟩ := hb p hp
        have : 0 ≤ C * L ^ 2 := (abs_nonneg _).trans b2
        have : 0 ≤ C ^ 2 * L ^ 3 + C * L ^ 2 := (abs_nonneg _).trans b3
        refine ⟨by linarith, by linarith, by linarith, by simp; positivity⟩⟩
  refine Jet.of_close (K := L * ((C * (C ^ 2 * L ^ 3 + C * L ^ 2) + C * (C * L ^ 2) +
    C * (C ^ 2 * L ^ 3 + C * L ^ 2)) + C * (3 * (L + C * L ^ 2 + (C ^ 2 * L ^ 3 + C * L ^ 2)))))
    (fun p hp => ?_) hJI
  obtain ⟨h1, h2, h3, h4⟩ := hC p hp
  obtain ⟨b1, b2, b3⟩ := hb p hp
  have he := hε p hp
  have he0 := abs_nonneg (ε p)
  have hCn : 0 ≤ C := (abs_nonneg _).trans h2
  have hq0 : q₀ p ≠ 0 := fun h => by
    have := (hqc p hp).2; rw [h, abs_zero] at this; linarith
  have hqp : q p ≠ 0 := fun h => by
    have := (hqc p hp).1; rw [h, abs_zero] at this; linarith
  set Q := q₀ p + ε p * q₁ p + ε p ^ 2 * q₂ p with hQ
  set T := q₁ p * (q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2) - q₂ p * (q₁ p / q₀ p ^ 2) +
    ε p * (q₂ p * (q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2)) with hT
  have hQI : Q * I p - 1 = ε p ^ 3 * T := by
    simp only [hQ, hI, hT]
    field_simp
    ring
  have hId : (q p)⁻¹ - I p = (q p)⁻¹ * (-(Q * I p - 1) - (q p - Q) * I p) := by
    field_simp
    ring
  have hTb : |T| ≤ C * (C ^ 2 * L ^ 3 + C * L ^ 2) + C * (C * L ^ 2) +
      C * (C ^ 2 * L ^ 3 + C * L ^ 2) := by
    rw [hT]
    have e1 : |q₁ p * (q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2)| ≤
        C * (C ^ 2 * L ^ 3 + C * L ^ 2) := by
      rw [abs_mul]; exact mul_le_mul h3 b3 (abs_nonneg _) hCn
    have e2 : |q₂ p * (q₁ p / q₀ p ^ 2)| ≤ C * (C * L ^ 2) := by
      rw [abs_mul, ← abs_neg (q₁ p / q₀ p ^ 2)]; exact mul_le_mul h4 b2 (abs_nonneg _) hCn
    have e3 : |ε p * (q₂ p * (q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2))| ≤
        C * (C ^ 2 * L ^ 3 + C * L ^ 2) := by
      rw [abs_mul, abs_mul]
      calc |ε p| * (|q₂ p| * |q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2|) ≤
            1 * (C * (C ^ 2 * L ^ 3 + C * L ^ 2)) :=
          mul_le_mul he (mul_le_mul h4 b3 (abs_nonneg _) hCn) (by positivity) zero_le_one
        _ = _ := one_mul _
    have := abs_add_le (q₁ p * (q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2) -
      q₂ p * (q₁ p / q₀ p ^ 2)) (ε p * (q₂ p * (q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2)))
    have := abs_sub (q₁ p * (q₁ p ^ 2 / q₀ p ^ 3 - q₂ p / q₀ p ^ 2)) (q₂ p * (q₁ p / q₀ p ^ 2))
    linarith
  have hc2 : 0 ≤ C * L ^ 2 := (abs_nonneg _).trans b2
  have hc3 : 0 ≤ C ^ 2 * L ^ 3 + C * L ^ 2 := (abs_nonneg _).trans b3
  have hIb : |I p| ≤ 3 * (L + C * L ^ 2 + (C ^ 2 * L ^ 3 + C * L ^ 2)) :=
    abs_poly2_le he (b1.trans (by linarith)) (b2.trans (by linarith)) (b3.trans (by linarith))
  have hqinv := hinv (hqc p hp).1
  rw [hId, abs_mul]
  have hin : |-(Q * I p - 1) - (q p - Q) * I p| ≤ |ε p| ^ 3 *
      (C * (C ^ 2 * L ^ 3 + C * L ^ 2) + C * (C * L ^ 2) + C * (C ^ 2 * L ^ 3 + C * L ^ 2)) +
      C * |ε p| ^ 3 * (3 * (L + C * L ^ 2 + (C ^ 2 * L ^ 3 + C * L ^ 2))) := by
    rw [hQI]
    have := abs_sub (-(ε p ^ 3 * T)) ((q p - Q) * I p)
    rw [abs_neg, abs_mul, abs_pow, abs_mul] at this
    have k1 : |ε p| ^ 3 * |T| ≤ |ε p| ^ 3 * (C * (C ^ 2 * L ^ 3 + C * L ^ 2) + C * (C * L ^ 2) +
        C * (C ^ 2 * L ^ 3 + C * L ^ 2)) := mul_le_mul_of_nonneg_left hTb (by positivity)
    have k2 : |q p - Q| * |I p| ≤ C * |ε p| ^ 3 * (3 * (L + C * L ^ 2 +
        (C ^ 2 * L ^ 3 + C * L ^ 2))) := mul_le_mul h1 hIb (abs_nonneg _) (by positivity)
    linarith
  calc |(q p)⁻¹| * |-(Q * I p - 1) - (q p - Q) * I p| ≤ L * (|ε p| ^ 3 *
        (C * (C ^ 2 * L ^ 3 + C * L ^ 2) + C * (C * L ^ 2) + C * (C ^ 2 * L ^ 3 + C * L ^ 2)) +
        C * |ε p| ^ 3 * (3 * (L + C * L ^ 2 + (C ^ 2 * L ^ 3 + C * L ^ 2)))) :=
        mul_le_mul hqinv hin (abs_nonneg _) hL0.le
    _ = _ := by ring

/-- Taylor's formula for `1/√(1 + z)` to the second order: for `√(1 + z) ≥ c > 0`,
`|1/√(1 + z) − (1 − z/2 + 3z²/8)| ≤ (3(1 + z) + 9√(1 + z) + 8)/(8c) |z|³`. -/
theorem abs_inv_sqrt_sub_le {z c : ℝ} (hc : 0 < c) (hz : 0 ≤ 1 + z) (hy : c ≤ √(1 + z)) :
    |(√(1 + z))⁻¹ - (1 - z / 2 + 3 * z ^ 2 / 8)| ≤
      (3 * (1 + z) + 9 * √(1 + z) + 8) / (8 * c) * |z| ^ 3 := by
  set y := √(1 + z) with hyd
  have hy0 : 0 < y := hc.trans_le hy
  have hy2 : y ^ 2 = 1 + z := Real.sq_sqrt hz
  have hzy : z = y ^ 2 - 1 := by linarith
  have hid : y⁻¹ - (1 - z / 2 + 3 * z ^ 2 / 8) =
      -(z ^ 3 * (3 * y ^ 2 + 9 * y + 8)) / (8 * y * (y + 1) ^ 3) := by
    rw [hzy]
    field_simp
    ring
  rw [hid, abs_div, abs_neg, abs_mul, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < 8 * y * (y + 1) ^ 3),
    abs_of_pos (by positivity : (0 : ℝ) < 3 * y ^ 2 + 9 * y + 8), ← hy2]
  rw [div_le_iff₀ (by positivity)]
  have h1 : 8 * c ≤ 8 * y * (y + 1) ^ 3 := by
    have : 1 ≤ (y + 1) ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  have h2 : 0 ≤ |z| ^ 3 * (3 * y ^ 2 + 9 * y + 8) := by positivity
  calc |z| ^ 3 * (3 * y ^ 2 + 9 * y + 8) =
        (3 * y ^ 2 + 9 * y + 8) / (8 * c) * |z| ^ 3 * (8 * c) := by
        field_simp
    _ ≤ (3 * y ^ 2 + 9 * y + 8) / (8 * c) * |z| ^ 3 * (8 * y * (y + 1) ^ 3) := by
        gcongr

/-- **The expansion of `1/√(1 + z)`** for an expansion `z = εz₁ + ε²z₂ + O(ε³)` with
`√(1 + z) ≥ c > 0`. -/
theorem Jet.invSqrt (hε : ∀ p ∈ S, |ε p| ≤ 1) {z z₁ z₂ : P → ℝ}
    (hz : Jet S ε z (fun _ => 0) z₁ z₂) {c : ℝ} (hc : 0 < c)
    (hzc : ∀ p ∈ S, 0 ≤ 1 + z p ∧ c ≤ √(1 + z p)) :
    Jet S ε (fun p => (√(1 + z p))⁻¹) (fun _ => 1) (fun p => -(z₁ p / 2))
      (fun p => -(z₂ p / 2) + 3 * z₁ p ^ 2 / 8) := by
  obtain ⟨C₀', hC₀'⟩ := hz.abs_le_of_zero hε
  set C₀ := max C₀' 0 with hC₀d
  have hC0 : 0 ≤ C₀ := le_max_right _ _
  have hC₀ : ∀ p ∈ S, |z p| ≤ C₀ * |ε p| := fun p hp =>
    (hC₀' p hp).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hP : Jet S ε (fun p => 1 - z p / 2 + 3 * z p ^ 2 / 8) (fun _ => 1) (fun p => -(z₁ p / 2))
      (fun p => -(z₂ p / 2) + 3 * z₁ p ^ 2 / 8) := by
    have h1 := ((Jet.const (S := S) (ε := ε) (q := fun _ => (1 : ℝ)) ⟨1, fun _ _ => by simp⟩).add
      (hz.const_mul (-1 / 2))).add ((hz.mul hε hz).const_mul (3 / 8))
    exact h1.congr (fun p _ => by ring) (fun p _ => by ring) (fun p _ => by ring)
      (fun p _ => by ring)
  refine Jet.of_close (K := (3 * (1 + C₀) + 9 * (2 + C₀) + 8) / (8 * c) * C₀ ^ 3)
    (fun p hp => ?_) hP
  have hzb := hC₀ p hp
  have he := hε p hp
  have he0 := abs_nonneg (ε p)
  obtain ⟨hz1, hyc⟩ := hzc p hp
  have hzC : |z p| ≤ C₀ := hzb.trans (by nlinarith)
  have hzle : z p ≤ C₀ := (le_abs_self _).trans hzC
  have hsq : √(1 + z p) ≤ 2 + C₀ := by
    have := Real.sq_sqrt hz1
    nlinarith [Real.sqrt_nonneg (1 + z p), sq_nonneg (√(1 + z p) - 1)]
  have hmain := abs_inv_sqrt_sub_le hc hz1 hyc
  have hz3 : |z p| ^ 3 ≤ C₀ ^ 3 * |ε p| ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hzb 3
  have hnum : 3 * (1 + z p) + 9 * √(1 + z p) + 8 ≤ 3 * (1 + C₀) + 9 * (2 + C₀) + 8 := by
    linarith
  have hnum0 : 0 ≤ 3 * (1 + z p) + 9 * √(1 + z p) + 8 := by
    have := Real.sqrt_nonneg (1 + z p); nlinarith
  calc _ ≤ (3 * (1 + z p) + 9 * √(1 + z p) + 8) / (8 * c) * |z p| ^ 3 := hmain
    _ ≤ (3 * (1 + C₀) + 9 * (2 + C₀) + 8) / (8 * c) * (C₀ ^ 3 * |ε p| ^ 3) := by
        gcongr
    _ = _ := by ring

end Jet

/-! ### The second-order cancellation in the field of a slow point charge -/

/-- The data of a slow point charge seen from a field point: the slowness `ε`, the distance `R`
to the retarded position and the direction `n` from it, the retarded velocity `β` and
acceleration `α` of the profile `R₁` (in its own time), and the remainders `ρX`, `ρV`, `ρA` of
the Taylor expansions from the retarded to the present time. -/
structure SlowData where
  /-- The slowness. -/
  ε : ℝ
  /-- The distance to the retarded position. -/
  R : ℝ
  /-- The unit vector from the retarded position. -/
  n : Fin 3 → ℝ
  /-- The retarded velocity of the profile. -/
  β : Fin 3 → ℝ
  /-- The retarded acceleration of the profile. -/
  α : Fin 3 → ℝ
  /-- The remainder of the position. -/
  ρX : Fin 3 → ℝ
  /-- The remainder of the velocity. -/
  ρV : Fin 3 → ℝ
  /-- The remainder of the acceleration. -/
  ρA : Fin 3 → ℝ

namespace SlowData

/-- `⟨n, β⟩`. -/
def b (d : SlowData) : ℝ := ∑ k, d.n k * d.β k

/-- The present separation divided by `R`, `Y = n − εβ − ε²Rα/2 − ε³ρX`. -/
def Y (d : SlowData) (i : Fin 3) : ℝ :=
  d.n i - d.ε * d.β i - d.ε ^ 2 * (d.R * d.α i / 2) - d.ε ^ 3 * d.ρX i

/-- `‖Y‖² − 1`. -/
def z (d : SlowData) : ℝ := ∑ k, d.Y k * d.Y k - 1

/-- `1/‖Y‖`. -/
def minv (d : SlowData) : ℝ := (√(1 + d.z))⁻¹

/-- The present velocity of the profile, `β + εRα + ε²ρV`. -/
def Vp (d : SlowData) (i : Fin 3) : ℝ := d.β i + d.ε * (d.R * d.α i) + d.ε ^ 2 * d.ρV i

/-- The present acceleration of the profile, `α + ερA`. -/
def Ap (d : SlowData) (i : Fin 3) : ℝ := d.α i + d.ε * d.ρA i

/-- The field of Liénard and Wiechert in units of `e/(4πR²)`:
`(1 − εb)⁻³ [(1 − ε²β²)(n − εβ) + ε²R⟨n, α⟩(n − εβ) − ε²R(1 − εb)α]`. -/
def lw (d : SlowData) (i : Fin 3) : ℝ :=
  ((1 - d.ε * d.b)⁻¹) ^ 3 * ((1 - d.ε ^ 2 * ∑ k, d.β k * d.β k) * (d.n i - d.ε * d.β i) +
    d.ε ^ 2 * (d.R * ∑ k, d.n k * d.α k) * (d.n i - d.ε * d.β i) -
      d.ε ^ 2 * (d.R * (1 - d.ε * d.b)) * d.α i)

/-- The field of the potentials of Darwin in units of `e/(4πR²)`:
`Y/‖Y‖³ − ε²(R/2)(A/‖Y‖ + ⟨A, Y⟩Y/‖Y‖³) + (ε²/2)(V²Y/‖Y‖³ − 3⟨V, Y⟩²Y/‖Y‖⁵)`. -/
def darwin (d : SlowData) (i : Fin 3) : ℝ :=
  d.Y i * d.minv ^ 3 - d.ε ^ 2 * (d.R / 2) * (d.Ap i * d.minv +
      (∑ k, d.Ap k * d.Y k) * d.Y i * d.minv ^ 3) +
    d.ε ^ 2 / 2 * ((∑ k, d.Vp k * d.Vp k) * d.Y i * d.minv ^ 3 -
      3 * (∑ k, d.Vp k * d.Y k) ^ 2 * d.Y i * d.minv ^ 5)

/-- The admissible data with the bound `K` and the lower bound `c` of `‖Y‖`. -/
def admissible (K c : ℝ) : Set SlowData :=
  {d | |d.ε| ≤ 1 ∧ 1 / 2 ≤ 1 - d.ε * d.b ∧ 0 ≤ d.R ∧ d.R ≤ K ∧ ∑ k, d.n k * d.n k = 1 ∧
    (∀ k, |d.β k| ≤ K ∧ |d.α k| ≤ K ∧ |d.ρX k| ≤ K ∧ |d.ρV k| ≤ K ∧ |d.ρA k| ≤ K) ∧
    0 ≤ 1 + d.z ∧ c ≤ √(1 + d.z)}

end SlowData

namespace SlowData

/-- The common second-order coefficient of the two fields. -/
def c₂ (d : SlowData) (i : Fin 3) : ℝ :=
  6 * d.b ^ 2 * d.n i - 3 * d.b * d.β i - (∑ k, d.β k * d.β k) * d.n i +
    d.R * (∑ k, d.n k * d.α k) * d.n i - d.R * d.α i

variable {K c : ℝ}

theorem abs_n_le {d : SlowData} (hd : d ∈ admissible K c) (k : Fin 3) : |d.n k| ≤ 1 := by
  have h := hd.2.2.2.2.1
  rw [Fin.sum_univ_three] at h
  rw [abs_le_one_iff_mul_self_le_one]
  fin_cases k <;> simp <;> nlinarith [mul_self_nonneg (d.n 0), mul_self_nonneg (d.n 1),
    mul_self_nonneg (d.n 2)]

theorem K_nonneg {d : SlowData} (hd : d ∈ admissible K c) : 0 ≤ K :=
  hd.2.2.1.trans hd.2.2.2.1

/-- A bound for products of the components. -/
theorem abs_mul_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem abs_b_le {d : SlowData} (hd : d ∈ admissible K c) : |d.b| ≤ 3 * K := by
  have h : ∀ k, |d.n k * d.β k| ≤ 1 * K := fun k => abs_mul_le (abs_n_le hd k) (hd.2.2.2.2.2.1 k).1
  unfold b
  rw [Fin.sum_univ_three]
  have := abs_add_le (d.n 0 * d.β 0 + d.n 1 * d.β 1) (d.n 2 * d.β 2)
  have := abs_add_le (d.n 0 * d.β 0) (d.n 1 * d.β 1)
  linarith [h 0, h 1, h 2]

end SlowData

namespace SlowData

variable {K c : ℝ}

/-- A crude bound: every component and `R` is at most `K + 1` in absolute value. -/
theorem bounds {d : SlowData} (hd : d ∈ admissible K c) (k : Fin 3) :
    |d.n k| ≤ K + 1 ∧ |d.β k| ≤ K + 1 ∧ |d.α k| ≤ K + 1 ∧ |d.ρX k| ≤ K + 1 ∧
      |d.ρV k| ≤ K + 1 ∧ |d.ρA k| ≤ K + 1 ∧ |d.R| ≤ K + 1 := by
  have hK := K_nonneg hd
  obtain ⟨h1, h2, h3, h4, h5⟩ := hd.2.2.2.2.2.1 k
  refine ⟨(abs_n_le hd k).trans (by linarith), by linarith, by linarith, by linarith,
    by linarith, by linarith, ?_⟩
  rw [abs_of_nonneg hd.2.2.1]
  linarith [hd.2.2.2.1]

/-- The expansion of the field of Liénard and Wiechert. -/
theorem jet_lw (i : Fin 3) : Jet (admissible K c) SlowData.ε (fun d => d.lw i)
    (fun d => d.n i) (fun d => 3 * d.b * d.n i - d.β i) (fun d => d.c₂ i) := by
  set S := admissible K c
  have hε : ∀ d ∈ S, |d.ε| ≤ 1 := fun d hd => hd.1
  -- bounded quantities
  obtain ⟨B, hB⟩ : ∃ B, ∀ d ∈ S, |d.b| ≤ B ∧ |d.n i| ≤ B ∧ |d.β i| ≤ B ∧
      |∑ k, d.β k * d.β k| ≤ B ∧ |d.R * ∑ k, d.n k * d.α k| ≤ B ∧ |d.R * d.α i| ≤ B ∧
      |d.R * d.b * d.α i| ≤ B := by
    refine ⟨3 * (K + 1) ^ 4, fun d hd => ?_⟩
    have hK := K_nonneg hd
    have hb := bounds hd
    have hsum : ∀ (f g : Fin 3 → ℝ), (∀ k, |f k| ≤ K + 1) → (∀ k, |g k| ≤ K + 1) →
        |∑ k, f k * g k| ≤ 3 * (K + 1) ^ 2 := fun f g hf hg => by
      rw [Fin.sum_univ_three]
      have e := fun k => abs_mul_le (hf k) (hg k)
      have := abs_add_le (f 0 * g 0 + f 1 * g 1) (f 2 * g 2)
      have := abs_add_le (f 0 * g 0) (f 1 * g 1)
      nlinarith [e 0, e 1, e 2]
    have hbb : |d.b| ≤ 3 * (K + 1) ^ 2 := hsum _ _ (fun k => (hb k).1) (fun k => (hb k).2.1)
    have hR := (hb i).2.2.2.2.2.2
    have h1 : 1 ≤ K + 1 := by linarith
    have p1 : K + 1 ≤ 3 * (K + 1) ^ 4 := by
      nlinarith [pow_le_pow_right₀ h1 (show 1 ≤ 4 by norm_num), pow_one (K + 1)]
    have p2 : 3 * (K + 1) ^ 2 ≤ 3 * (K + 1) ^ 4 := by
      nlinarith [pow_le_pow_right₀ h1 (show 2 ≤ 4 by norm_num)]
    have p3 : (K + 1) * (3 * (K + 1) ^ 2) ≤ 3 * (K + 1) ^ 4 := by
      nlinarith [pow_le_pow_right₀ h1 (show 3 ≤ 4 by norm_num)]
    have p4 : (K + 1) * (K + 1) ≤ 3 * (K + 1) ^ 4 := by
      nlinarith [pow_le_pow_right₀ h1 (show 2 ≤ 4 by norm_num)]
    refine ⟨hbb.trans p2, (hb i).1.trans p1, (hb i).2.1.trans p1,
      (hsum _ _ (fun k => (hb k).2.1) (fun k => (hb k).2.1)).trans p2, ?_, ?_, ?_⟩
    · exact (abs_mul_le hR (hsum _ _ (fun k => (hb k).1) (fun k => (hb k).2.2.1))).trans p3
    · exact (abs_mul_le hR (hb i).2.2.1).trans p4
    · refine (abs_mul_le (abs_mul_le hR hbb) (hb i).2.2.1).trans ?_
      nlinarith
  have J1 : Jet S SlowData.ε (fun d => 1 - d.ε * d.b) (fun _ => 1) (fun d => -d.b)
      (fun _ => 0) := by
    refine Jet.of_eq (q₃ := fun _ => 0) (fun d _ => by ring) ⟨B + 1, fun d hd => ?_⟩
    have := (hB d hd).1
    have := abs_nonneg d.b
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num; linarith
    · rw [abs_neg]; linarith
    · simp; linarith
    · simp; linarith
  have J2 := J1.inv hε (c := 1 / 2) (by norm_num) (fun d hd => ⟨by
    rw [abs_of_pos (by linarith [hd.2.1])]; exact hd.2.1, by norm_num⟩)
  have J3 := (J2.mul hε J2).mul hε J2
  have J4 : Jet S SlowData.ε (fun d => (1 - d.ε ^ 2 * ∑ k, d.β k * d.β k) * (d.n i - d.ε * d.β i) +
      d.ε ^ 2 * (d.R * ∑ k, d.n k * d.α k) * (d.n i - d.ε * d.β i) -
        d.ε ^ 2 * (d.R * (1 - d.ε * d.b)) * d.α i) (fun d => d.n i) (fun d => -d.β i)
      (fun d => -(∑ k, d.β k * d.β k) * d.n i + d.R * (∑ k, d.n k * d.α k) * d.n i -
        d.R * d.α i) :=
    Jet.of_eq (q₃ := fun d => (∑ k, d.β k * d.β k) * d.β i -
      d.R * (∑ k, d.n k * d.α k) * d.β i + d.R * d.b * d.α i) (fun d _ => by ring)
      ⟨3 * B ^ 2 + 3 * B, fun d hd => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hB d hd
        have hB0 : 0 ≤ B := (abs_nonneg _).trans h1
        refine ⟨by nlinarith, by rw [abs_neg]; nlinarith, ?_, ?_⟩
        · have := abs_mul_le h4 h2
          have := abs_mul_le h5 h2
          have := abs_add_le (-(∑ k, d.β k * d.β k) * d.n i + d.R * (∑ k, d.n k * d.α k) * d.n i)
            (-(d.R * d.α i))
          have := abs_add_le (-(∑ k, d.β k * d.β k) * d.n i) (d.R * (∑ k, d.n k * d.α k) * d.n i)
          rw [neg_mul, abs_neg] at *
          rw [sub_eq_add_neg]
          nlinarith [abs_neg (d.R * d.α i)]
        · have := abs_mul_le h4 h3
          have := abs_mul_le h5 h3
          have := abs_add_le ((∑ k, d.β k * d.β k) * d.β i - d.R * (∑ k, d.n k * d.α k) * d.β i)
            (d.R * d.b * d.α i)
          have := abs_sub ((∑ k, d.β k * d.β k) * d.β i) (d.R * (∑ k, d.n k * d.α k) * d.β i)
          nlinarith⟩
  have J5 := J3.mul hε J4
  refine J5.congr (fun d _ => by simp only [lw]; ring) (fun d _ => by simp) (fun d _ => by
    simp; ring) (fun d _ => by simp [c₂]; ring)

end SlowData

namespace SlowData

variable {K c : ℝ}

/-- The expansion of the field of the potentials of Darwin. -/
theorem jet_darwin (hc : 0 < c) (i : Fin 3) : Jet (admissible K c) SlowData.ε
    (fun d => d.darwin i) (fun d => d.n i) (fun d => 3 * d.b * d.n i - d.β i)
    (fun d => d.c₂ i) := by
  set S := admissible K c
  have hε : ∀ d ∈ S, |d.ε| ≤ 1 := fun d hd => hd.1
  have hB : ∀ d ∈ S, ∀ k, |d.n k| ≤ K + 1 ∧ |d.β k| ≤ K + 1 ∧ |d.α k| ≤ K + 1 ∧
      |d.ρX k| ≤ K + 1 ∧ |d.ρV k| ≤ K + 1 ∧ |d.ρA k| ≤ K + 1 ∧ |d.R| ≤ K + 1 :=
    fun d hd k => bounds hd k
  have hK1 : ∀ d ∈ S, 0 ≤ K + 1 := fun d hd => by linarith [K_nonneg hd]
  have bnd : ∀ (f : SlowData → ℝ), (∀ d ∈ S, |f d| ≤ (K + 1) * (K + 1)) →
      ∃ C, ∀ d ∈ S, |f d| ≤ C := fun f hf => ⟨_, hf⟩
  have JY : ∀ k, Jet S SlowData.ε (fun d => d.Y k) (fun d => d.n k) (fun d => -d.β k)
      (fun d => -(d.R * d.α k / 2)) := fun k =>
    Jet.of_eq (q₃ := fun d => -d.ρX k) (fun d _ => by simp only [Y]; ring)
      ⟨(K + 1) * (K + 1) + (K + 1), fun d hd => by
        obtain ⟨h1, h2, h3, h4, -, -, h7⟩ := hB d hd k
        have := hK1 d hd
        have h8 := abs_mul_le h7 h3
        refine ⟨by nlinarith, by rw [abs_neg]; nlinarith, ?_, by rw [abs_neg]; nlinarith⟩
        rw [abs_neg, abs_div, abs_two]
        nlinarith [abs_nonneg (d.R * d.α k)]⟩
  have Jz0 := (Jet.sum Finset.univ (fun k _ => (JY k).mul hε (JY k))).sub
    (Jet.const (S := S) (ε := SlowData.ε) (q := fun _ => (1 : ℝ)) ⟨1, fun _ _ => by simp⟩)
  have Jz : Jet S SlowData.ε (fun d => d.z) (fun _ => 0) (fun d => -2 * d.b)
      (fun d => ∑ k, d.β k * d.β k - d.R * ∑ k, d.n k * d.α k) := by
    refine Jz0.congr (fun d _ => rfl) (fun d hd => ?_) (fun d _ => ?_) (fun d _ => ?_)
    · have h := hd.2.2.2.2.1
      linarith
    · simp only [b, Fin.sum_univ_three]
      ring
    · simp only [Fin.sum_univ_three]
      ring
  have Jm := Jz.invSqrt hε hc (fun d hd => ⟨hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2⟩)
  have Jm3 := (Jm.mul hε Jm).mul hε Jm
  have Jm5 := (Jm3.mul hε Jm).mul hε Jm
  have JVp : ∀ k, Jet S SlowData.ε (fun d => d.Vp k) (fun d => d.β k) (fun d => d.R * d.α k)
      (fun d => d.ρV k) := fun k =>
    Jet.of_eq (q₃ := fun _ => 0) (fun d _ => by simp only [Vp]; ring)
      ⟨(K + 1) * (K + 1) + (K + 1), fun d hd => by
        obtain ⟨-, h2, h3, -, h5, -, h7⟩ := hB d hd k
        have := hK1 d hd
        have h8 := abs_mul_le h7 h3
        refine ⟨by nlinarith, by nlinarith, by nlinarith, by simp; nlinarith⟩⟩
  have JAp : ∀ k, Jet S SlowData.ε (fun d => d.Ap k) (fun d => d.α k) (fun d => d.ρA k)
      (fun _ => 0) := fun k =>
    Jet.of_eq (q₃ := fun _ => 0) (fun d _ => by simp only [Ap]; ring)
      ⟨(K + 1), fun d hd => by
        obtain ⟨-, -, h3, -, -, h6, -⟩ := hB d hd k
        have := hK1 d hd
        refine ⟨h3, h6, by simp; linarith, by simp; linarith⟩⟩
  have Je2 : Jet S SlowData.ε (fun d => d.ε ^ 2) (fun _ => 0) (fun _ => 0) (fun _ => 1) :=
    (Jet.eps.mul hε Jet.eps).congr (fun d _ => by ring) (fun d _ => by ring)
      (fun d _ => by ring) (fun d _ => by ring)
  have JR : Jet S SlowData.ε (fun d => d.R / 2) (fun d => d.R / 2) (fun _ => 0) (fun _ => 0) :=
    Jet.const ⟨K + 1, fun d hd => by
      have := (hB d hd 0).2.2.2.2.2.2
      rw [abs_div, abs_two]; linarith [abs_nonneg d.R]⟩
  have T1 := (JY i).mul hε Jm3
  have T2 := (Je2.mul hε JR).mul hε (((JAp i).mul hε Jm).add
    (((Jet.sum Finset.univ fun k _ => (JAp k).mul hε (JY k)).mul hε (JY i)).mul hε Jm3))
  have JVY := Jet.sum Finset.univ fun k _ => (JVp k).mul hε (JY k)
  have T3 := (Je2.const_mul (1 / 2)).mul hε
    ((((Jet.sum Finset.univ fun k _ => (JVp k).mul hε (JVp k)).mul hε (JY i)).mul hε Jm3).sub
      ((((JVY.mul hε JVY).const_mul 3).mul hε (JY i)).mul hε Jm5))
  refine ((T1.sub T2).add T3).congr (fun d _ => ?_) (fun d _ => ?_) (fun d _ => ?_)
    (fun d _ => ?_)
  · simp only [darwin, minv]
    ring
  · simp
  · simp [b, Fin.sum_univ_three]
    ring
  · simp [b, c₂, Fin.sum_univ_three]
    ring

end SlowData

namespace SlowData

variable {K c : ℝ}

/-- **The second-order cancellation** (the field of Darwin to the second order): on admissible
data, `|lw − darwin| ≤ C|ε|³`. -/
theorem abs_lw_sub_darwin_le (hc : 0 < c) (i : Fin 3) :
    ∃ C, ∀ d ∈ admissible K c, |d.lw i - d.darwin i| ≤ C * |d.ε| ^ 3 :=
  (((jet_lw (K := K) (c := c) i).sub (jet_darwin hc i)).congr (fun d _ => rfl)
    (fun d _ => by ring) (fun d _ => by ring) (fun d _ => by ring)).bound_three

/-- The expansion of `Y`. -/
theorem jet_Y (k : Fin 3) : Jet (admissible K c) SlowData.ε (fun d => d.Y k) (fun d => d.n k)
    (fun d => -d.β k) (fun d => -(d.R * d.α k / 2)) :=
  Jet.of_eq (q₃ := fun d => -d.ρX k) (fun d _ => by simp only [Y]; ring)
    ⟨(K + 1) * (K + 1) + (K + 1), fun d hd => by
      obtain ⟨h1, h2, h3, h4, -, -, h7⟩ := bounds hd k
      have : 0 ≤ K + 1 := by linarith [K_nonneg hd]
      have h8 := abs_mul_le h7 h3
      refine ⟨by nlinarith, by rw [abs_neg]; nlinarith, ?_, by rw [abs_neg]; nlinarith⟩
      rw [abs_neg, abs_div, abs_two]
      nlinarith [abs_nonneg (d.R * d.α k)]⟩

/-- The expansion of `Vp`. -/
theorem jet_Vp (k : Fin 3) : Jet (admissible K c) SlowData.ε (fun d => d.Vp k)
    (fun d => d.β k) (fun d => d.R * d.α k) (fun d => d.ρV k) :=
  Jet.of_eq (q₃ := fun _ => 0) (fun d _ => by simp only [Vp]; ring)
    ⟨(K + 1) * (K + 1) + (K + 1), fun d hd => by
      obtain ⟨-, h2, h3, -, h5, -, h7⟩ := bounds hd k
      have : 0 ≤ K + 1 := by linarith [K_nonneg hd]
      have h8 := abs_mul_le h7 h3
      refine ⟨by nlinarith, by nlinarith, by nlinarith, by simp; nlinarith⟩⟩

/-- The expansion of `1/‖Y‖`. -/
theorem jet_minv (hc : 0 < c) : Jet (admissible K c) SlowData.ε (fun d => d.minv)
    (fun _ => 1) (fun d => -(-2 * d.b / 2))
    (fun d => -((∑ k, d.β k * d.β k - d.R * ∑ k, d.n k * d.α k) / 2) +
      3 * (-2 * d.b) ^ 2 / 8) := by
  have hε : ∀ d ∈ admissible K c, |d.ε| ≤ 1 := fun d hd => hd.1
  have Jz0 := (Jet.sum Finset.univ (fun k _ => (jet_Y (K := K) (c := c) k).mul hε
    (jet_Y k))).sub (Jet.const (S := admissible K c) (ε := SlowData.ε)
      (q := fun _ => (1 : ℝ)) ⟨1, fun _ _ => by simp⟩)
  have Jz : Jet (admissible K c) SlowData.ε (fun d => d.z) (fun _ => 0) (fun d => -2 * d.b)
      (fun d => ∑ k, d.β k * d.β k - d.R * ∑ k, d.n k * d.α k) := by
    refine Jz0.congr (fun d _ => rfl) (fun d hd => ?_) (fun d _ => ?_) (fun d _ => ?_)
    · have h := hd.2.2.2.2.1
      linarith
    · simp only [b, Fin.sum_univ_three]
      ring
    · simp only [Fin.sum_univ_three]
      ring
  exact Jz.invSqrt hε hc (fun d hd => ⟨hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2⟩)

/-- The magnetic field of Liénard and Wiechert in units of `e/(4πR²)`, `n × lw`. -/
def lwB (d : SlowData) (i : Fin 3) : ℝ := crossProduct d.n (fun k => d.lw k) i

/-- The magnetic field of the potentials of Darwin in units of `e/(4πR²)`,
`ε (V × Y)/‖Y‖³`. -/
def darwinB (d : SlowData) (i : Fin 3) : ℝ :=
  d.ε * crossProduct (fun k => d.Vp k) (fun k => d.Y k) i * d.minv ^ 3

/-- **The magnetic fields agree to the first order**: `|lwB − darwinB| ≤ C ε²`. -/
theorem abs_lwB_sub_darwinB_le (hc : 0 < c) (i : Fin 3) :
    ∃ C, ∀ d ∈ admissible K c, |d.lwB i - d.darwinB i| ≤ C * |d.ε| ^ 2 := by
  have hε : ∀ d ∈ admissible K c, |d.ε| ≤ 1 := fun d hd => hd.1
  have Jn : ∀ k, Jet (admissible K c) SlowData.ε (fun d => d.n k) (fun d => d.n k)
      (fun _ => 0) (fun _ => 0) := fun k => Jet.const ⟨1, fun d hd => abs_n_le hd k⟩
  have Jm := jet_minv (K := K) hc
  have Jm3 := (Jm.mul hε Jm).mul hε Jm
  have JL := fun k => jet_lw (K := K) (c := c) k
  have JY := fun k => jet_Y (K := K) (c := c) k
  have JV := fun k => jet_Vp (K := K) (c := c) k
  have Je := Jet.eps (S := admissible K c) (ε := SlowData.ε)
  have key : ∀ j k : Fin 3, ∃ C, ∀ d ∈ admissible K c,
      |(d.n j * d.lw k - d.n k * d.lw j) - d.ε * (d.Vp j * d.Y k - d.Vp k * d.Y j) * d.minv ^ 3|
        ≤ C * |d.ε| ^ 2 := by
    intro j k
    have J := ((((Jn j).mul hε (JL k)).sub ((Jn k).mul hε (JL j)))).sub
      ((Je.mul hε (((JV j).mul hε (JY k)).sub ((JV k).mul hε (JY j)))).mul hε Jm3)
    refine (J.congr (q₂ := _) (fun d _ => by ring) (fun d _ => ?_) (fun d _ => ?_)
      (fun d _ => rfl)).bound_two hε
    · ring
    · ring
  fin_cases i
  · obtain ⟨C, hC⟩ := key 1 2
    exact ⟨C, fun d hd => by simpa [lwB, darwinB, cross_apply] using hC d hd⟩
  · obtain ⟨C, hC⟩ := key 2 0
    exact ⟨C, fun d hd => by simpa [lwB, darwinB, cross_apply] using hC d hd⟩
  · obtain ⟨C, hC⟩ := key 0 1
    exact ⟨C, fun d hd => by simpa [lwB, darwinB, cross_apply] using hC d hd⟩

end SlowData

/-! ### The fields of the potentials of Darwin of a point charge -/

/-- The derivative of the norm along a path, `d‖Z‖ = ⟨Z, Z'⟩/‖Z‖`. -/
theorem hasDerivAt_norm_path {Z : ℝ → E3} {Z' : E3} {s : ℝ} (hZ : HasDerivAt Z Z' s)
    (h0 : Z s ≠ 0) : HasDerivAt (fun s => ‖Z s‖) (inner ℝ (Z s) Z' / ‖Z s‖) s := by
  have h := (Wave.hasFDerivAt_norm_of_ne_zero h0).comp_hasDerivAt s hZ
  have e : (‖Z s‖⁻¹ • innerSL ℝ (Z s)) Z' = inner ℝ (Z s) Z' / ‖Z s‖ := by
    rw [smul_apply, innerSL_apply_apply, smul_eq_mul, div_eq_inv_mul]
  rw [e] at h
  exact h

/-- The derivative of a component along a path. -/
theorem hasDerivAt_component_path {Z : ℝ → E3} {Z' : E3} {s : ℝ} (hZ : HasDerivAt Z Z' s)
    (k : Fin 3) : HasDerivAt (fun s => Z s k) (Z' k) s :=
  (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s hZ

/-- **The derivative of the profile of the vector potential of Darwin** along paths `Z`, `W`:
`d/ds [Wₖ/‖Z‖ + ⟨W, Z⟩Zₖ/‖Z‖³]`. -/
theorem hasDerivAt_darwinProfile {Z W : ℝ → E3} {Z' W' : E3} {s : ℝ} (hZ : HasDerivAt Z Z' s)
    (hW : HasDerivAt W W' s) (h0 : Z s ≠ 0) (k : Fin 3) :
    HasDerivAt (fun s => W s k / ‖Z s‖ + inner ℝ (W s) (Z s) * Z s k / ‖Z s‖ ^ 3)
      (W' k / ‖Z s‖ - W s k * inner ℝ (Z s) Z' / ‖Z s‖ ^ 3 +
        (inner ℝ W' (Z s) + inner ℝ (W s) Z') * Z s k / ‖Z s‖ ^ 3 +
        inner ℝ (W s) (Z s) * Z' k / ‖Z s‖ ^ 3 -
        3 * inner ℝ (W s) (Z s) * Z s k * inner ℝ (Z s) Z' / ‖Z s‖ ^ 5) s := by
  have hn : ‖Z s‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hN := hasDerivAt_norm_path hZ h0
  have hWk := hasDerivAt_component_path hW k
  have hZk := hasDerivAt_component_path hZ k
  have hI := hW.inner ℝ hZ
  have h1 := hWk.fun_div hN hn
  have h2 := ((hI.fun_mul hZk).fun_div (hN.fun_pow 3) (pow_ne_zero 3 hn))
  convert h1.fun_add h2 using 1
  field_simp
  ring

/-- The closed form of the vector potential of Darwin,
`a'ₖ = e (ċₖ/R + ⟨ċ, Z⟩Zₖ/R³)/(8π)` with `Z = x − c(t)`. -/
theorem pointVector_eq (e : ℝ) (c : ℝ → E3) (k : Fin 3) (p : ℝ × E3) :
    pointVector e c k p = e / (8 * π) * (deriv c p.1 k / ‖p.2 - c p.1‖ +
      inner ℝ (deriv c p.1) (p.2 - c p.1) * (p.2 - c p.1) k / ‖p.2 - c p.1‖ ^ 3) := by
  simp only [pointVector, darwinKernel, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three, star_trivial]
  fin_cases k <;> simp <;> ring

/-- A spatial derivative from the derivative along the line `λ ↦ (t, x + λeᵢ)`. -/
theorem spaceDeriv_eq_of_hasDerivAt {F : ℝ × E3 → ℝ} {s : ℝ} {y : E3}
    (hF : DifferentiableAt ℝ F (s, y)) (i : Fin 3) {v : ℝ}
    (h : HasDerivAt (fun l : ℝ => F (s, y + l • EuclideanSpace.single i 1)) v 0) :
    spaceDeriv i F (s, y) = v := by
  have hp : HasDerivAt (fun l : ℝ => (s, y + l • (EuclideanSpace.single i 1 : E3)))
      ((0 : ℝ), (EuclideanSpace.single i 1 : E3)) 0 :=
    (hasDerivAt_const 0 s).prodMk ((hasDerivAt_id' 0).smul_const _ |>.const_add y |>.congr_deriv
      (by simp))
  have hF' : DifferentiableAt ℝ F (s, y + (0 : ℝ) • (EuclideanSpace.single i 1 : E3)) := by
    simpa using hF
  have h2 : HasDerivAt (fun l : ℝ => F (s, y + l • (EuclideanSpace.single i 1 : E3)))
      (fderiv ℝ F (s, y + (0 : ℝ) • (EuclideanSpace.single i 1 : E3))
        ((0 : ℝ), (EuclideanSpace.single i 1 : E3))) 0 :=
    hF'.hasFDerivAt.comp_hasDerivAt 0 hp
  have := h2.unique h
  simpa [spaceDeriv] using this

/-- The time derivative from the derivative along `s ↦ (s, x)`. -/
theorem timeDeriv_eq_of_hasDerivAt {F : ℝ × E3 → ℝ} {s : ℝ} {y : E3}
    (hF : DifferentiableAt ℝ F (s, y)) {v : ℝ} (h : HasDerivAt (fun s' => F (s', y)) v s) :
    timeDeriv F (s, y) = v :=
  (hasDerivAt_timeSlice_of_differentiableAt hF).unique h

section PointFields

variable {e : ℝ} {c : ℝ → E3}

/-- The gradient of the scalar potential of Darwin, `∂ᵢφ' = −e Zᵢ/(4π‖Z‖³)` with `Z = x − c(t)`. -/
theorem spaceDeriv_pointScalar (hc : ContDiff ℝ ∞ c) {s : ℝ} {y : E3} (hy : y ≠ c s)
    (i : Fin 3) :
    spaceDeriv i (pointScalar e c) (s, y) =
      -(e * (4 * π * inner ℝ (y - c s) (EuclideanSpace.single i 1) / ‖y - c s‖)) /
        (4 * π * ‖y - c s‖) ^ 2 := by
  have h0 : y - c s ≠ 0 := sub_ne_zero.mpr hy
  have hZ : HasDerivAt (fun l : ℝ => y + l • (EuclideanSpace.single i 1 : E3) - c s)
      (EuclideanSpace.single i 1) 0 :=
    (((hasDerivAt_id' 0).smul_const _).const_add y).sub_const (c s) |>.congr_deriv (by simp)
  have hZ0 : y + (0 : ℝ) • (EuclideanSpace.single i 1 : E3) - c s ≠ 0 := by simpa using h0
  have hN := hasDerivAt_norm_path hZ hZ0
  have hn : ‖y + (0 : ℝ) • (EuclideanSpace.single i 1 : E3) - c s‖ ≠ 0 := norm_ne_zero_iff.mpr hZ0
  have h := ((hN.const_mul (4 * π)).inv (by positivity)).const_mul e
  refine spaceDeriv_eq_of_hasDerivAt
    ((contDiffAt_pointScalar e hc (p := (s, y)) hy).differentiableAt (by simp)) i ?_
  convert h using 1
  · funext l
    simp [pointScalar, Potential.newtonKernel]
  · simp
    ring

/-- The time derivative of the vector potential of Darwin, from `hasDerivAt_darwinProfile` with
`Z' = −ċ` and `W = ċ`. -/
theorem timeDeriv_pointVector (hc : ContDiff ℝ ∞ c) {s : ℝ} {y : E3} (hy : y ≠ c s)
    (k : Fin 3) :
    timeDeriv (pointVector e c k) (s, y) = e / (8 * π) *
      (deriv (deriv c) s k / ‖y - c s‖ - deriv c s k * inner ℝ (y - c s) (-deriv c s) /
          ‖y - c s‖ ^ 3 +
        (inner ℝ (deriv (deriv c) s) (y - c s) + inner ℝ (deriv c s) (-deriv c s)) *
          (y - c s) k / ‖y - c s‖ ^ 3 +
        inner ℝ (deriv c s) (y - c s) * (-deriv c s) k / ‖y - c s‖ ^ 3 -
        3 * inner ℝ (deriv c s) (y - c s) * (y - c s) k * inner ℝ (y - c s) (-deriv c s) /
          ‖y - c s‖ ^ 5) := by
  have h0 : y - c s ≠ 0 := sub_ne_zero.mpr hy
  have hc1 : Differentiable ℝ c := hc.differentiable (by simp)
  have hc2 : Differentiable ℝ (deriv c) := (hc.iterate_deriv 1).differentiable (by simp)
  have hZ : HasDerivAt (fun s' => y - c s') (-deriv c s) s :=
    ((hc1 s).hasDerivAt.const_sub y)
  have hW : HasDerivAt (fun s' => deriv c s') (deriv (deriv c) s) s := (hc2 s).hasDerivAt
  have h := (hasDerivAt_darwinProfile hZ hW h0 k).const_mul (e / (8 * π))
  refine timeDeriv_eq_of_hasDerivAt
    ((contDiffAt_pointVector e hc k (p := (s, y)) hy).differentiableAt (by simp)) ?_
  convert h using 1
  funext s'
  exact pointVector_eq e c k (s', y)

/-- The spatial derivatives of the vector potential of Darwin, from `hasDerivAt_darwinProfile`
with `Z' = eⱼ` and `W = ċ` fixed. -/
theorem spaceDeriv_pointVector (hc : ContDiff ℝ ∞ c) {s : ℝ} {y : E3} (hy : y ≠ c s)
    (j k : Fin 3) :
    spaceDeriv j (pointVector e c k) (s, y) = e / (8 * π) *
      ((0 : E3) k / ‖y - c s‖ - deriv c s k * inner ℝ (y - c s) (EuclideanSpace.single j 1) /
          ‖y - c s‖ ^ 3 +
        (inner ℝ (0 : E3) (y - c s) + inner ℝ (deriv c s) (EuclideanSpace.single j 1)) *
          (y - c s) k / ‖y - c s‖ ^ 3 +
        inner ℝ (deriv c s) (y - c s) * (EuclideanSpace.single j 1 : E3) k / ‖y - c s‖ ^ 3 -
        3 * inner ℝ (deriv c s) (y - c s) * (y - c s) k *
          inner ℝ (y - c s) (EuclideanSpace.single j 1) / ‖y - c s‖ ^ 5) := by
  have h0 : y - c s ≠ 0 := sub_ne_zero.mpr hy
  have hZ : HasDerivAt (fun l : ℝ => y + l • (EuclideanSpace.single j 1 : E3) - c s)
      (EuclideanSpace.single j 1) 0 :=
    (((hasDerivAt_id' 0).smul_const _).const_add y).sub_const (c s) |>.congr_deriv (by simp)
  have hZ0 : y + (0 : ℝ) • (EuclideanSpace.single j 1 : E3) - c s ≠ 0 := by simpa using h0
  have hW : HasDerivAt (fun _ : ℝ => deriv c s) (0 : E3) 0 := hasDerivAt_const _ _
  have h := (hasDerivAt_darwinProfile hZ hW hZ0 k).const_mul (e / (8 * π))
  refine spaceDeriv_eq_of_hasDerivAt
    ((contDiffAt_pointVector e hc k (p := (s, y)) hy).differentiableAt (by simp)) j ?_
  convert h using 1
  · funext l
    rw [pointVector_eq]
  · simp

end PointFields

/-! ### The slow point charge seen from a field point -/

/-- **Taylor's formula for a smooth path** with a bound `A₃` of the third derivative, in the
components: the position, the velocity and the acceleration at `σ + u` from those at `σ`. -/
theorem taylor_path {R₁ : ℝ → E3} (hR : ContDiff ℝ ∞ R₁) {A₃ : ℝ}
    (hA3 : ∀ s, ‖deriv^[3] R₁ s‖ ≤ A₃) (σ : ℝ) {u : ℝ} (hu : 0 ≤ u) (k : Fin 3) :
    |R₁ (σ + u) k - (R₁ σ k + u * deriv R₁ σ k + u ^ 2 / 2 * deriv (deriv R₁) σ k)| ≤
        A₃ * u ^ 3 / 6 ∧
      |deriv R₁ (σ + u) k - (deriv R₁ σ k + u * deriv (deriv R₁) σ k)| ≤ A₃ * u ^ 2 / 2 ∧
      |deriv (deriv R₁) (σ + u) k - deriv (deriv R₁) σ k| ≤ A₃ * u := by
  set g : ℕ → ℝ → ℝ := fun j s => (deriv^[j] R₁ (σ + s)) k with hgd
  have hg : ∀ j, ∀ s, HasDerivAt (g j) (g (j + 1) s) s := by
    intro j s
    have hd : Differentiable ℝ (deriv^[j] R₁) := (hR.iterate_deriv j).differentiable (by simp)
    have h1 : HasDerivAt (fun s => deriv^[j] R₁ (σ + s)) (deriv (deriv^[j] R₁) (σ + s)) s :=
      ((hd (σ + s)).hasDerivAt).comp_const_add σ s
    have h2 := hasDerivAt_component_path h1 k
    simpa [hgd, Function.iterate_succ_apply'] using h2
  have hM : ∀ s, |g 3 s| ≤ A₃ := fun s => by
    have h := PiLp.norm_apply_le (deriv^[3] R₁ (σ + s)) k
    rw [Real.norm_eq_abs] at h
    exact h.trans (hA3 _)
  have T3 := abs_sub_taylor_le (g := g) 3 (fun j _ s => hg j s) hu (fun s _ => hM s)
  have T2 := abs_sub_taylor_le (g := fun j => g (j + 1)) 2 (fun j _ s => hg (j + 1) s) hu
    (fun s _ => hM s)
  have T1 := abs_sub_taylor_le (g := fun j => g (j + 2)) 1 (fun j _ s => hg (j + 2) s) hu
    (fun s _ => hM s)
  simp only [hgd, Finset.sum_range_succ, Finset.sum_range_zero, Function.iterate_succ_apply',
    Function.iterate_zero_apply, add_zero, pow_zero, pow_one, zero_add] at T3 T2 T1
  refine ⟨?_, ?_, ?_⟩
  · convert T3 using 2 <;> norm_num [Nat.factorial]
  · convert T2 using 2 <;> norm_num [Nat.factorial]
  · convert T1 using 2 <;> norm_num [Nat.factorial]

/-- The data of a slow world line `w` with `w.r t = R₁(κt)`, seen from the field point
`(t, x)`: the retarded separation `P = x − R₁(κτ)`, `R = ‖P‖`, the retarded velocity and
acceleration of `R₁`, and the Taylor remainders to the present time `κt = κτ + κR`. -/
def slowData (R₁ : ℝ → E3) (w : SubluminalWorldline) (κ t : ℝ) (x : E3) : SlowData where
  ε := κ
  R := ‖w.retardedSeparation t x‖
  n := fun k => w.retardedSeparation t x k / ‖w.retardedSeparation t x‖
  β := fun k => deriv R₁ (κ * w.retardedTime t x) k
  α := fun k => deriv (deriv R₁) (κ * w.retardedTime t x) k
  ρX := fun k => (w.retardedSeparation t x k - (x - R₁ (κ * t)) k -
      κ * ‖w.retardedSeparation t x‖ * deriv R₁ (κ * w.retardedTime t x) k -
      (κ * ‖w.retardedSeparation t x‖) ^ 2 / 2 * deriv (deriv R₁) (κ * w.retardedTime t x) k) /
    (‖w.retardedSeparation t x‖ * κ ^ 3)
  ρV := fun k => (deriv R₁ (κ * t) k - deriv R₁ (κ * w.retardedTime t x) k -
      κ * ‖w.retardedSeparation t x‖ * deriv (deriv R₁) (κ * w.retardedTime t x) k) / κ ^ 2
  ρA := fun k => (deriv (deriv R₁) (κ * t) k - deriv (deriv R₁) (κ * w.retardedTime t x) k) / κ

section SlowCharge

variable {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}

/-- The present time is the retarded time plus the time of flight: `κt = κτ + κR`. -/
theorem slowData_time (t : ℝ) (x : E3) :
    κ * t = κ * w.retardedTime t x + κ * ‖w.retardedSeparation t x‖ := by
  rw [w.norm_retardedSeparation]
  ring

/-- The present separation: `Y = (x − R₁(κt))/R`. -/
theorem slowData_Y (hκ : κ ≠ 0) (hx : x ≠ w.r t) (k : Fin 3) :
    (slowData R₁ w κ t x).Y k = (x - R₁ (κ * t)) k / ‖w.retardedSeparation t x‖ := by
  have hP : ‖w.retardedSeparation t x‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (w.retardedSeparation_ne_zero hx)
  simp only [SlowData.Y, slowData]
  field_simp
  ring

/-- The present velocity of the profile. -/
theorem slowData_Vp (hκ : κ ≠ 0) (k : Fin 3) :
    (slowData R₁ w κ t x).Vp k = deriv R₁ (κ * t) k := by
  simp only [SlowData.Vp, slowData]
  field_simp
  ring

/-- The present acceleration of the profile. -/
theorem slowData_Ap (hκ : κ ≠ 0) (k : Fin 3) :
    (slowData R₁ w κ t x).Ap k = deriv (deriv R₁) (κ * t) k := by
  simp only [SlowData.Ap, slowData]
  field_simp
  ring

/-- The velocity and the acceleration of the slow world line. -/
theorem deriv_slow_worldline (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s)) (s : ℝ) :
    deriv w.r s = κ • deriv R₁ (κ * s) ∧
      deriv (deriv w.r) s = κ • κ • deriv (deriv R₁) (κ * s) := by
  have hwr : w.r = fun s => R₁ (κ * s) := funext hw
  have h1 : deriv w.r = fun s => κ • deriv R₁ (κ * s) := by
    rw [hwr]
    funext s
    exact deriv_slowPath (hR.differentiable (by simp)) κ s
  refine ⟨congrFun h1 s, ?_⟩
  rw [h1]
  have hd : Differentiable ℝ (deriv R₁) := (hR.iterate_deriv 1).differentiable (by simp)
  have h1' : HasDerivAt (fun t : ℝ => κ * t) κ s := by
    simpa using (hasDerivAt_id' s).const_mul κ
  have h2 : HasDerivAt (fun s => κ • deriv R₁ (κ * s)) (κ • κ • deriv (deriv R₁) (κ * s)) s :=
    ((hd (κ * s)).hasDerivAt.scomp s h1').const_smul κ
  exact h2.deriv

end SlowCharge

section SlowCharge

variable {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}

/-- **The field of Liénard and Wiechert of the slow charge** in the data: the velocity and the
acceleration fields at `(t, x)` are `e/(4πR²) · lw`. -/
theorem lw_slowData (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s))
    (hx : x ≠ w.r t) (e : ℝ) (i : Fin 3) :
    (LienardWiechert.velocityField e w t x + LienardWiechert.accelerationField e w t x) i =
      e / (4 * π * ‖w.retardedSeparation t x‖ ^ 2) * (slowData R₁ w κ t x).lw i := by
  set τ := w.retardedTime t x with hτ
  set P := w.retardedSeparation t x with hPd
  set R := ‖P‖ with hRd
  set β := deriv R₁ (κ * τ) with hβ
  set α := deriv (deriv R₁) (κ * τ) with hα
  have hP0 : P ≠ 0 := w.retardedSeparation_ne_zero hx
  have hR0 : R ≠ 0 := norm_ne_zero_iff.mpr hP0
  obtain ⟨hv, ha⟩ := deriv_slow_worldline hR hw τ
  have hvel : w.retardedVelocity t x = κ • β := hv
  have hacc : w.retardedAcceleration t x = κ • κ • α := ha
  have hD := w.retardedDenominator_pos hx
  have hDe : w.retardedDenominator t x = R * (1 - κ * (inner ℝ P β / R)) := by
    rw [SubluminalWorldline.retardedDenominator, hvel, inner_smul_right, ← hPd, ← hRd]
    field_simp
  have hb : (slowData R₁ w κ t x).b = inner ℝ P β / R := by
    simp only [SlowData.b, slowData]
    simp only [← hτ, ← hPd]
    simp only [← hRd, ← hβ, LienardWiechert.inner_eq_sum, Fin.sum_univ_three]
    field_simp
  have hbb : ∑ k, (slowData R₁ w κ t x).β k * (slowData R₁ w κ t x).β k = ‖β‖ ^ 2 := by
    simp only [slowData]
    simp only [← hτ, ← hβ, LienardWiechert.norm_sq_eq_sum, Fin.sum_univ_three]
    ring
  have hna : ∑ k, (slowData R₁ w κ t x).n k * (slowData R₁ w κ t x).α k = inner ℝ P α / R := by
    simp only [slowData]
    simp only [← hτ, ← hPd]
    simp only [← hRd, ← hα, LienardWiechert.inner_eq_sum, Fin.sum_univ_three]
    field_simp
  have h1b : 1 - κ * (inner ℝ P β / R) ≠ 0 := by
    intro h
    rw [hDe, h, mul_zero] at hD
    exact lt_irrefl 0 hD
  have hPP : inner ℝ P P = R ^ 2 := real_inner_self_eq_norm_sq P
  simp only [SlowData.lw, hb, hbb, hna]
  simp only [LienardWiechert.velocityField, LienardWiechert.accelerationField, PiLp.add_apply,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hDe, hvel, hacc, ← hPd, ← hRd]
  rw [inner_smul_right, inner_smul_right, inner_sub_right, inner_smul_right, inner_smul_right,
    hPP, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [slowData]
  simp only [← hτ, ← hPd]
  simp only [← hRd, ← hβ, ← hα]
  field_simp
  ring

end SlowCharge

section SlowCharge

variable {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}

/-- The velocity and the acceleration of the slow path `s ↦ R₁(κs)`. -/
theorem deriv_slowPath_two (hR : ContDiff ℝ ∞ R₁) (κ s : ℝ) :
    deriv (fun s => R₁ (κ * s)) s = κ • deriv R₁ (κ * s) ∧
      deriv (deriv fun s => R₁ (κ * s)) s = κ • κ • deriv (deriv R₁) (κ * s) := by
  have h1 : deriv (fun s => R₁ (κ * s)) = fun s => κ • deriv R₁ (κ * s) :=
    funext fun s => deriv_slowPath (hR.differentiable (by simp)) κ s
  refine ⟨congrFun h1 s, ?_⟩
  rw [h1]
  have hd : Differentiable ℝ (deriv R₁) := (hR.iterate_deriv 1).differentiable (by simp)
  have h1' : HasDerivAt (fun t : ℝ => κ * t) κ s := by
    simpa using (hasDerivAt_id' s).const_mul κ
  exact (((hd (κ * s)).hasDerivAt.scomp s h1').const_smul κ).deriv

/-- The norm of the present separation, `‖x − R₁(κt)‖ = R √(1 + z)`. -/
theorem norm_present_slowData (hκ : κ ≠ 0) (hx : x ≠ w.r t) :
    ‖x - R₁ (κ * t)‖ = ‖w.retardedSeparation t x‖ * √(1 + (slowData R₁ w κ t x).z) := by
  have hP : ‖w.retardedSeparation t x‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (w.retardedSeparation_ne_zero hx)
  have hY := fun k => slowData_Y (R₁ := R₁) (w := w) (t := t) hκ hx k
  have hz : 1 + (slowData R₁ w κ t x).z =
      ‖x - R₁ (κ * t)‖ ^ 2 / ‖w.retardedSeparation t x‖ ^ 2 := by
    rw [LienardWiechert.norm_sq_eq_sum (x - R₁ (κ * t))]
    simp only [SlowData.z, hY, Fin.sum_univ_three]
    field_simp
    ring
  rw [hz, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  field_simp

/-- **The field of the potentials of Darwin of the slow charge** in the data: the electric
field at `(t, x)` is `e/(4πR²) · darwin`. -/
theorem darwin_slowData (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s)) (hκ : κ ≠ 0)
    (hx : x ≠ w.r t) (e : ℝ) (i : Fin 3) :
    electricOf (pointScalar e fun s => R₁ (κ * s)) (pointVector e fun s => R₁ (κ * s)) i (t, x) =
      e / (4 * π * ‖w.retardedSeparation t x‖ ^ 2) * (slowData R₁ w κ t x).darwin i := by
  have hc : ContDiff ℝ ∞ fun s => R₁ (κ * s) := hR.comp (contDiff_const.mul contDiff_id)
  have hxc : x ≠ R₁ (κ * t) := by rwa [← hw]
  have hP : ‖w.retardedSeparation t x‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (w.retardedSeparation_ne_zero hx)
  set d := slowData R₁ w κ t x with hd
  set R := ‖w.retardedSeparation t x‖ with hRd
  have hm : 0 < √(1 + d.z) := by
    have h0 : 0 < ‖x - R₁ (κ * t)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
    rw [norm_present_slowData (w := w) hκ hx] at h0
    exact pos_of_mul_pos_right h0 (norm_nonneg _)
  have hY : ∀ k, (x - R₁ (κ * t)) k = R * d.Y k := fun k => by
    rw [hd, slowData_Y hκ hx k, ← hRd]
    field_simp
  have hN : ‖x - R₁ (κ * t)‖ = R * √(1 + d.z) := norm_present_slowData hκ hx
  obtain ⟨h1, h2⟩ := deriv_slowPath_two hR κ t
  have hV : ∀ k, deriv R₁ (κ * t) k = d.Vp k := fun k => (slowData_Vp hκ k).symm
  have hA : ∀ k, deriv (deriv R₁) (κ * t) k = d.Ap k := fun k => (slowData_Ap hκ k).symm
  rw [electricOf, spaceDeriv_pointScalar hc hxc, timeDeriv_pointVector hc hxc, h1, h2, hN]
  simp only [LienardWiechert.inner_eq_sum, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, hY,
    hV, hA, PiLp.single_apply]
  simp only [SlowData.darwin, SlowData.minv, Fin.sum_univ_three]
  have hε : d.ε = κ := rfl
  have hRR : d.R = R := rfl
  rw [hε, hRR]
  fin_cases i <;> simp <;> field_simp <;> ring

end SlowCharge

section SlowCharge

variable {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}

/-- **The magnetic field of the potentials of Darwin of the slow charge** in the data: the
magnetic field at `(t, x)` is `e/(4πR²) · darwinB`. -/
theorem darwinB_slowData (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s)) (hκ : κ ≠ 0)
    (hx : x ≠ w.r t) (e : ℝ) (i : Fin 3) :
    magneticOf (pointVector e fun s => R₁ (κ * s)) (t, x) i =
      e / (4 * π * ‖w.retardedSeparation t x‖ ^ 2) * (slowData R₁ w κ t x).darwinB i := by
  have hc : ContDiff ℝ ∞ fun s => R₁ (κ * s) := hR.comp (contDiff_const.mul contDiff_id)
  have hxc : x ≠ R₁ (κ * t) := by rwa [← hw]
  have hP : ‖w.retardedSeparation t x‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (w.retardedSeparation_ne_zero hx)
  set d := slowData R₁ w κ t x with hd
  set R := ‖w.retardedSeparation t x‖ with hRd
  have hm : 0 < √(1 + d.z) := by
    have h0 : 0 < ‖x - R₁ (κ * t)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
    rw [norm_present_slowData (w := w) hκ hx] at h0
    exact pos_of_mul_pos_right h0 (norm_nonneg _)
  have hY : ∀ k, (x - R₁ (κ * t)) k = R * d.Y k := fun k => by
    rw [hd, slowData_Y hκ hx k, ← hRd]
    field_simp
  have hN : ‖x - R₁ (κ * t)‖ = R * √(1 + d.z) := norm_present_slowData hκ hx
  obtain ⟨h1, -⟩ := deriv_slowPath_two hR κ t
  have hV : ∀ k, deriv R₁ (κ * t) k = d.Vp k := fun k => (slowData_Vp hκ k).symm
  have hε : d.ε = κ := rfl
  simp only [magneticOf, SlowData.darwinB, SlowData.minv, cross_apply, hε]
  fin_cases i <;>
  · simp only [spaceDeriv_pointVector hc hxc, h1, hN]
    simp only [LienardWiechert.inner_eq_sum, PiLp.smul_apply, smul_eq_mul, hY, hV,
      PiLp.single_apply, PiLp.zero_apply]
    simp
    field_simp
    ring

end SlowCharge

section SlowCharge

variable {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}

/-- **The data of a slow charge are admissible**: for `0 < κ ≤ 1`, `κV₁ ≤ 1/2` and
`δ ≤ ‖x − R₁(κt)‖ ≤ ρ`, with the bounds `V₁`, `A₂`, `A₃` of the first three derivatives of `R₁`,
the data lie in `admissible K (δ/(2ρ))` with `K = 2ρ + V₁ + A₂ + 4ρ²A₃ + 2ρA₃`, and the distance
to the retarded position is at least `2δ/3`. -/
theorem slowData_admissible (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s))
    {V₁ A₂ A₃ : ℝ} (hV : ∀ s, ‖deriv R₁ s‖ ≤ V₁) (hA : ∀ s, ‖deriv (deriv R₁) s‖ ≤ A₂)
    (hA3 : ∀ s, ‖deriv^[3] R₁ s‖ ≤ A₃) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hκV : κ * V₁ ≤ 1 / 2)
    {δ ρ : ℝ} (hδ : 0 < δ) (hxδ : δ ≤ ‖x - R₁ (κ * t)‖) (hxρ : ‖x - R₁ (κ * t)‖ ≤ ρ) :
    x ≠ w.r t ∧ 2 * δ / 3 ≤ ‖w.retardedSeparation t x‖ ∧
      slowData R₁ w κ t x ∈ SlowData.admissible (2 * ρ + V₁ + A₂ + 4 * ρ ^ 2 * A₃ + 2 * ρ * A₃)
        (δ / (2 * ρ)) := by
  have hρ : 0 < ρ := hδ.trans_le (hxδ.trans hxρ)
  have hV0 : 0 ≤ V₁ := (norm_nonneg _).trans (hV 0)
  have hA0 : 0 ≤ A₂ := (norm_nonneg _).trans (hA 0)
  have hA30 : 0 ≤ A₃ := (norm_nonneg _).trans (hA3 0)
  have hxc : x ≠ R₁ (κ * t) := fun h => by
    rw [h, sub_self, norm_zero] at hxδ; linarith
  have hx : x ≠ w.r t := by rwa [hw]
  set τ := w.retardedTime t x with hτ
  set P := w.retardedSeparation t x with hPd
  set R := ‖P‖ with hRd
  have hP0 : P ≠ 0 := w.retardedSeparation_ne_zero hx
  have hR0 : 0 < R := norm_pos_iff.mpr hP0
  have htime : κ * t = κ * τ + κ * R := slowData_time t x
  have hPx : P = x - R₁ (κ * τ) := by rw [hPd, SubluminalWorldline.retardedSeparation, hw]
  -- the Lipschitz bound of the path
  have hlip : ‖R₁ (κ * t) - R₁ (κ * τ)‖ ≤ V₁ * (κ * R) := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := R₁) (C := V₁)
      (fun s _ => (hR.differentiable (by simp)) s) (fun s _ => hV s) convex_univ
      (mem_univ (κ * τ)) (mem_univ (κ * t))
    have he : κ * t - κ * τ = κ * R := by linarith [htime]
    rw [Real.norm_eq_abs, he, abs_of_nonneg (by positivity)] at h
    exact h
  have hXP : x - R₁ (κ * t) = P - (R₁ (κ * t) - R₁ (κ * τ)) := by rw [hPx]; abel
  have hRup : R ≤ 2 * ρ := by
    have := norm_sub_le P (R₁ (κ * t) - R₁ (κ * τ))
    have h2 := norm_le_norm_add_norm_sub' P (R₁ (κ * t) - R₁ (κ * τ))
    rw [← hXP] at h2
    nlinarith
  have hRlo : 2 * δ / 3 ≤ R := by
    have := norm_sub_le P (R₁ (κ * t) - R₁ (κ * τ))
    rw [← hXP] at this
    nlinarith
  refine ⟨hx, hRlo, ?_⟩
  -- the Taylor remainders
  have T := fun k => taylor_path hR hA3 (κ * τ) (u := κ * R) (by positivity) k
  rw [← htime] at T
  set d := slowData R₁ w κ t x with hd
  have hκ0 : κ ≠ 0 := hκ.ne'
  set K := 2 * ρ + V₁ + A₂ + 4 * ρ ^ 2 * A₃ + 2 * ρ * A₃ with hK
  have hR2 : R ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith
  have hβk : ∀ k, |d.β k| ≤ V₁ := fun k => by
    have := PiLp.norm_apply_le (deriv R₁ (κ * τ)) k
    rw [Real.norm_eq_abs] at this
    exact this.trans (hV _)
  have hαk : ∀ k, |d.α k| ≤ A₂ := fun k => by
    have := PiLp.norm_apply_le (deriv (deriv R₁) (κ * τ)) k
    rw [Real.norm_eq_abs] at this
    exact this.trans (hA _)
  have hρX : ∀ k, |d.ρX k| ≤ A₃ * R ^ 2 / 6 := fun k => by
    have h := (T k).1
    have hnum : w.retardedSeparation t x k - (x - R₁ (κ * t)) k - κ * R * deriv R₁ (κ * τ) k -
        (κ * R) ^ 2 / 2 * deriv (deriv R₁) (κ * τ) k = R₁ (κ * t) k -
          (R₁ (κ * τ) k + κ * R * deriv R₁ (κ * τ) k +
            (κ * R) ^ 2 / 2 * deriv (deriv R₁) (κ * τ) k) := by
      rw [← hPd, hPx]
      simp only [PiLp.sub_apply]
      ring
    simp only [hd, slowData, ← hτ, ← hPd, ← hRd]
    rw [hnum, abs_div, abs_of_pos (by positivity : 0 < R * κ ^ 3), div_le_iff₀ (by positivity)]
    calc _ ≤ A₃ * (κ * R) ^ 3 / 6 := h
      _ = A₃ * R ^ 2 / 6 * (R * κ ^ 3) := by ring
  have hρV : ∀ k, |d.ρV k| ≤ A₃ * R ^ 2 / 2 := fun k => by
    have h := (T k).2.1
    simp only [hd, slowData, ← hτ, ← hPd, ← hRd]
    rw [show deriv R₁ (κ * t) k - deriv R₁ (κ * τ) k - κ * R * deriv (deriv R₁) (κ * τ) k =
      deriv R₁ (κ * t) k - (deriv R₁ (κ * τ) k + κ * R * deriv (deriv R₁) (κ * τ) k) by ring,
      abs_div, abs_of_pos (by positivity : 0 < κ ^ 2), div_le_iff₀ (by positivity)]
    calc _ ≤ A₃ * (κ * R) ^ 2 / 2 := h
      _ = A₃ * R ^ 2 / 2 * κ ^ 2 := by ring
  have hρA : ∀ k, |d.ρA k| ≤ A₃ * R := fun k => by
    have h := (T k).2.2
    simp only [hd, slowData, ← hτ]
    rw [abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
    calc _ ≤ A₃ * (κ * R) := h
      _ = A₃ * R * κ := by ring
  have hb : d.b = inner ℝ P (deriv R₁ (κ * τ)) / R := by
    simp only [hd, SlowData.b, slowData]
    simp only [← hτ, ← hPd]
    simp only [← hRd, LienardWiechert.inner_eq_sum, Fin.sum_univ_three]
    field_simp
  have hbV : |d.b| ≤ V₁ := by
    rw [hb, abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
    calc |inner ℝ P (deriv R₁ (κ * τ))| ≤ ‖P‖ * ‖deriv R₁ (κ * τ)‖ := abs_real_inner_le_norm _ _
      _ ≤ R * V₁ := mul_le_mul_of_nonneg_left (hV _) hR0.le
      _ = V₁ * R := mul_comm _ _
  have hYk : ∀ k, d.Y k = (x - R₁ (κ * t)) k / R := fun k => slowData_Y hκ0 hx k
  have hN : ‖x - R₁ (κ * t)‖ = R * √(1 + d.z) := norm_present_slowData hκ0 hx
  have h1z : 1 + d.z = ‖x - R₁ (κ * t)‖ ^ 2 / R ^ 2 := by
    rw [LienardWiechert.norm_sq_eq_sum (x - R₁ (κ * t))]
    simp only [SlowData.z, hYk, Fin.sum_univ_three]
    field_simp
    ring
  refine ⟨?_, ?_, hR0.le, ?_, ?_, fun k => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [hd, slowData]; rw [abs_of_pos hκ]; exact hκ1
  · show 1 / 2 ≤ 1 - κ * d.b
    have : κ * d.b ≤ κ * V₁ := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hbV) hκ.le
    linarith
  · show R ≤ K
    nlinarith
  · simp only [hd, slowData, ← hPd, ← hRd]
    have := LienardWiechert.norm_sq_eq_sum P
    rw [← hRd] at this
    simp only [Fin.sum_univ_three]
    field_simp
    linarith
  · exact (hβk k).trans (by nlinarith)
  · exact (hαk k).trans (by nlinarith)
  · exact (hρX k).trans (by nlinarith)
  · exact (hρV k).trans (by nlinarith)
  · exact (hρA k).trans (by nlinarith)
  · rw [h1z]; positivity
  · rw [show √(1 + d.z) = ‖x - R₁ (κ * t)‖ / R by
      rw [hN]; field_simp]
    rw [div_le_div_iff₀ (by positivity) hR0]
    nlinarith
end SlowCharge

/-- The magnetic field of Liénard and Wiechert of the slow charge in the data. -/
theorem lwB_slowData {R₁ : ℝ → E3} {w : SubluminalWorldline} {κ t : ℝ} {x : E3}
    (hR : ContDiff ℝ ∞ R₁) (hw : ∀ s, w.r s = R₁ (κ * s)) (hx : x ≠ w.r t) (e : ℝ) (i : Fin 3) :
    crossProduct (WithLp.ofLp (w.retardedDirection t x))
        (WithLp.ofLp (LienardWiechert.velocityField e w t x +
          LienardWiechert.accelerationField e w t x)) i =
      e / (4 * π * ‖w.retardedSeparation t x‖ ^ 2) * (slowData R₁ w κ t x).lwB i := by
  have hL := fun k => lw_slowData (κ := κ) hR hw hx e k
  have hn : ∀ k, (w.retardedDirection t x) k = (slowData R₁ w κ t x).n k := fun k => by
    simp only [SubluminalWorldline.retardedDirection, PiLp.smul_apply, smul_eq_mul, slowData]
    ring
  simp only [SlowData.lwB, cross_apply]
  fin_cases i <;> simp [hL, hn] <;> ring

/-- **The field of a slow point charge to the second order** (target (ii)): for a smooth path
`R₁` with `‖Ṙ₁‖ ≤ V₁`, `‖R̈₁‖ ≤ A₂`, `‖R₁⁽³⁾‖ ≤ A₃`, a world line `w` on `t ↦ R₁(κt)` with
`0 < κ ≤ 1`, `κV₁ ≤ 1/2`, and a field point with `δ ≤ ‖x − R₁(κt)‖ ≤ ρ`, the field of
Liénard and Wiechert (`velocityField`, `accelerationField`, and `𝐁 = 𝐧 × 𝐄`) and the field
`electricOf`, `magneticOf` of the potentials of Darwin `pointScalar`, `pointVector` satisfy

  `|E_LW − E_D| ≤ C κ³`,  `|B_LW − B_D| ≤ C κ²`

with one constant `C` for all `κ`, `t`, `x`. The proof expands both fields in retarded
coordinates (`slowData`) with uniform remainders (`Jet`) and finds the same expansion to the
second order (`SlowData.abs_lw_sub_darwin_le`, `SlowData.abs_lwB_sub_darwinB_le`). -/
theorem lienardWiechert_sub_darwin (e : ℝ) {R₁ : ℝ → E3} (hR : ContDiff ℝ ∞ R₁)
    {V₁ A₂ A₃ : ℝ} (hV : ∀ s, ‖deriv R₁ s‖ ≤ V₁) (hA : ∀ s, ‖deriv (deriv R₁) s‖ ≤ A₂)
    (hA3 : ∀ s, ‖deriv^[3] R₁ s‖ ≤ A₃) {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) :
    ∃ C, ∀ κ, 0 < κ → κ ≤ 1 → κ * V₁ ≤ 1 / 2 → ∀ w : SubluminalWorldline,
      (∀ s, w.r s = R₁ (κ * s)) → ∀ (t : ℝ) (x : E3), δ ≤ ‖x - R₁ (κ * t)‖ →
        ‖x - R₁ (κ * t)‖ ≤ ρ → ∀ i : Fin 3,
          |(LienardWiechert.velocityField e w t x + LienardWiechert.accelerationField e w t x) i -
              electricOf (pointScalar e fun s => R₁ (κ * s)) (pointVector e fun s => R₁ (κ * s))
                i (t, x)| ≤ C * κ ^ 3 ∧
          |crossProduct (WithLp.ofLp (w.retardedDirection t x))
              (WithLp.ofLp (LienardWiechert.velocityField e w t x +
                LienardWiechert.accelerationField e w t x)) i -
              magneticOf (pointVector e fun s => R₁ (κ * s)) (t, x) i| ≤ C * κ ^ 2 := by
  set K := 2 * ρ + V₁ + A₂ + 4 * ρ ^ 2 * A₃ + 2 * ρ * A₃ with hK
  set c := δ / (2 * ρ) with hc
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hc0 : 0 < c := by positivity
  have hE := fun i => SlowData.abs_lw_sub_darwin_le (K := K) hc0 i
  have hB := fun i => SlowData.abs_lwB_sub_darwinB_le (K := K) hc0 i
  choose C₁ hC₁ using hE
  choose C₂ hC₂ using hB
  set L := |e| / (4 * π * (2 * δ / 3) ^ 2) with hL
  refine ⟨L * ∑ i, (|C₁ i| + |C₂ i|), fun κ hκ hκ1 hκV w hw t x hxδ hxρ i => ?_⟩
  obtain ⟨hx, hRlo, hadm⟩ := slowData_admissible (w := w) (t := t) hR hw hV hA hA3 hκ hκ1 hκV
    hδ hxδ hxρ
  set R := ‖w.retardedSeparation t x‖ with hRd
  have hR0 : 0 < R := by linarith
  have hfac : |e / (4 * π * R ^ 2)| ≤ L := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * π * R ^ 2), hL]
    gcongr
  have hL0 : 0 ≤ L := by positivity
  have hsum : |C₁ i| + |C₂ i| ≤ ∑ j, (|C₁ j| + |C₂ j|) :=
    Finset.single_le_sum (f := fun j => |C₁ j| + |C₂ j|) (fun j _ => by positivity)
      (Finset.mem_univ i)
  have hκa : |(slowData R₁ w κ t x).ε| = κ := abs_of_pos hκ
  refine ⟨?_, ?_⟩
  · rw [lw_slowData hR hw hx e i, darwin_slowData hR hw hκ.ne' hx e i, ← mul_sub, abs_mul]
    have h1 := hC₁ i _ hadm
    rw [hκa] at h1
    calc |e / (4 * π * R ^ 2)| * |(slowData R₁ w κ t x).lw i - (slowData R₁ w κ t x).darwin i|
        ≤ L * (|C₁ i| * κ ^ 3) :=
          mul_le_mul hfac (h1.trans (by gcongr; exact le_abs_self _)) (abs_nonneg _) hL0
      _ ≤ L * (∑ j, (|C₁ j| + |C₂ j|)) * κ ^ 3 := by
          rw [mul_assoc]
          gcongr
          linarith [abs_nonneg (C₂ i)]
  · rw [lwB_slowData hR hw hx e i, darwinB_slowData hR hw hκ.ne' hx e i, ← mul_sub, abs_mul]
    have h2 := hC₂ i _ hadm
    rw [hκa] at h2
    calc |e / (4 * π * R ^ 2)| * |(slowData R₁ w κ t x).lwB i - (slowData R₁ w κ t x).darwinB i|
        ≤ L * (|C₂ i| * κ ^ 2) :=
          mul_le_mul hfac (h2.trans (by gcongr; exact le_abs_self _)) (abs_nonneg _) hL0
      _ ≤ L * (∑ j, (|C₁ j| + |C₂ j|)) * κ ^ 2 := by
          rw [mul_assoc]
          gcongr
          linarith [abs_nonneg (C₁ i)]

/-! ### The force of the retarded fields on a slow charge -/

/-- The Lorentz density is additive in the potentials. -/
theorem lorentzDensity_sum {ι : Type*} (s : Finset ι) {φ : ι → ℝ × E3 → ℝ}
    {A : ι → Fin 3 → ℝ × E3 → ℝ} {p : ℝ × E3} (hφ : ∀ b ∈ s, DifferentiableAt ℝ (φ b) p)
    (hA : ∀ b ∈ s, ∀ k, DifferentiableAt ℝ (A b k) p) (v : E3) (i : Fin 3) :
    lorentzDensity (fun q => ∑ b ∈ s, φ b q) (fun k q => ∑ b ∈ s, A b k q) v i p =
      ∑ b ∈ s, lorentzDensity (φ b) (A b) v i p := by
  simp only [lorentzDensity, crossProduct_magneticOf, electricOf]
  rw [spaceDeriv_fun_sum s hφ, timeDeriv_fun_sum s (fun b hb => hA b hb i)]
  simp only [fun j => spaceDeriv_fun_sum s (fun b hb => hA b hb j) i,
    fun j => spaceDeriv_fun_sum s (fun b hb => hA b hb i) j]
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ), Finset.sum_sub_distrib, Finset.sum_neg_distrib]

/-- A component of a cross product is bounded by the norms of the factors. -/
theorem abs_crossProduct_le (v : E3) (u : Fin 3 → ℝ) {M : ℝ} (hu : ∀ k, |u k| ≤ M)
    (i : Fin 3) : |crossProduct (WithLp.ofLp v) u i| ≤ 2 * ‖v‖ * M := by
  have hv : ∀ k, |v k| ≤ ‖v‖ := fun k => by simpa using PiLp.norm_apply_le v k
  have h := fun j k => SlowData.abs_mul_le (hv j) (hu k)
  rw [cross_apply]
  fin_cases i
  · have := abs_sub (v 1 * u 2) (v 2 * u 1)
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    linarith [h 1 2, h 2 1]
  · have := abs_sub (v 2 * u 0) (v 0 * u 2)
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith [h 2 0, h 0 2]
  · have := abs_sub (v 0 * u 1) (v 1 * u 0)
    simp
    linarith [h 0 1, h 1 0]

/-- **The force of the fields of Liénard and Wiechert and the Lagrangian of Darwin**
(target (iv), Landau–Lifshitz §65): for `N` charges on prescribed slow paths `t ↦ R_b(κt)`
(world lines `w b`) with `‖Ṙ_b‖ ≤ V₁`, `‖R̈_b‖ ≤ A₂`, `‖R_b⁽³⁾‖ ≤ A₃`, apart at the time `t`,
the charge `a` at the distances `δ ≤ ‖R_a − R_b‖ ≤ ρ` from the others, the Lorentz force
`Σ_{b ≠ a} eₐ(𝐄_b + 𝐯ₐ × 𝐁_b)` of the retarded fields of the other charges equals the
interaction part of the Euler–Lagrange residual of (65.7) for the charge `a` up to `C κ³`,
with one constant for all `0 < κ ≤ 1` with `κV₁ ≤ 1/2` and all such times. The interaction part
is the residual plus `d/dt[mₐ(1 + vₐ²/2)vₐ]`, the derivative of the momentum of the kinetic
expansion. -/
theorem force_eq_darwinLagrangian {N : ℕ} (m e : Fin N → ℝ) {R : Fin N → ℝ → E3}
    (hR : ∀ b, ContDiff ℝ ∞ (R b)) {V₁ A₂ A₃ : ℝ} (hV : ∀ b s, ‖deriv (R b) s‖ ≤ V₁)
    (hA : ∀ b s, ‖deriv (deriv (R b)) s‖ ≤ A₂) (hA3 : ∀ b s, ‖deriv^[3] (R b) s‖ ≤ A₃)
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (a : Fin N) :
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
              deriv (fun s => R a (κ * s)) s i) t)| ≤ C * κ ^ 3 := by
  have hb := fun b => lienardWiechert_sub_darwin (e b) (hR b) (hV b) (hA b) (hA3 b) hδ hδρ
  choose C hC using hb
  have hV0 : 0 ≤ V₁ := (norm_nonneg _).trans (hV a 0)
  refine ⟨|e a| * ∑ b, (|C b| + 2 * V₁ * |C b|),
    fun κ hκ hκ1 hκV w hw t hsep hdist i => ?_⟩
  have hQ : ∀ b, ContDiff ℝ ∞ (fun s => R b (κ * s)) := fun b =>
    (hR b).comp (contDiff_const.mul contDiff_id)
  have hEL := eulerLagrange_darwinLagrangian m e (Q := fun b s => R b (κ * s)) hQ (t := t)
    hsep a i
  beta_reduce at hEL
  have hsepa : ∀ b ∈ ({a}ᶜ : Finset (Fin N)), R a (κ * t) ≠ R b (κ * t) := fun b hb =>
    hsep a b (by simpa [eq_comm] using hb)
  rw [lorentzDensity_sum _ (fun b hb => (contDiffAt_pointScalar (e b) (hQ b)
      (p := (t, R a (κ * t))) (hsepa b hb)).differentiableAt (by simp))
    (fun b hb k => (contDiffAt_pointVector (e b) (hQ b) k
      (p := (t, R a (κ * t))) (hsepa b hb)).differentiableAt (by simp))] at hEL
  have hEL' : Mechanics.eulerLagrange (darwinLagrangian m e) (fun s b => R b (κ * s)) t
      (Pi.single a (EuclideanSpace.single i 1)) +
      deriv (fun s => m a * (1 + ‖deriv (fun s => R a (κ * s)) s‖ ^ 2 / 2) *
        deriv (fun s => R a (κ * s)) s i) t =
      e a * ∑ b ∈ ({a}ᶜ : Finset (Fin N)),
        lorentzDensity (pointScalar (e b) fun s => R b (κ * s))
          (pointVector (e b) fun s => R b (κ * s)) (deriv (fun s => R a (κ * s)) t) i
          (t, R a (κ * t)) := by
    rw [hEL]
    ring
  rw [hEL', Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hva : ‖deriv (fun s => R a (κ * s)) t‖ ≤ κ * V₁ := by
    rw [deriv_slowPath ((hR a).differentiable (by simp)), norm_smul, Real.norm_of_nonneg hκ.le]
    exact mul_le_mul_of_nonneg_left (hV a _) hκ.le
  have hterm : ∀ b ∈ ({a}ᶜ : Finset (Fin N)),
      |e a * ((LienardWiechert.velocityField (e b) (w b) t (R a (κ * t)) +
          LienardWiechert.accelerationField (e b) (w b) t (R a (κ * t))) i +
        crossProduct (WithLp.ofLp (deriv (fun s => R a (κ * s)) t))
          (crossProduct (WithLp.ofLp ((w b).retardedDirection t (R a (κ * t))))
            (WithLp.ofLp (LienardWiechert.velocityField (e b) (w b) t (R a (κ * t)) +
              LienardWiechert.accelerationField (e b) (w b) t (R a (κ * t))))) i) -
        e a * lorentzDensity (pointScalar (e b) fun s => R b (κ * s))
          (pointVector (e b) fun s => R b (κ * s))
          (deriv (fun s => R a (κ * s)) t) i (t, R a (κ * t))| ≤
        |e a| * (|C b| + 2 * V₁ * |C b|) * κ ^ 3 := by
    intro b hb
    have hba : b ≠ a := by simpa using hb
    obtain ⟨h1, h2⟩ := hdist b hba
    have hE := fun j => hC b κ hκ hκ1 hκV (w b) (hw b) t (R a (κ * t)) h1 h2 j
    rw [← mul_sub, abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simp only [lorentzDensity]
    have hcross : crossProduct (WithLp.ofLp (deriv (fun s => R a (κ * s)) t))
        (crossProduct (WithLp.ofLp ((w b).retardedDirection t (R a (κ * t))))
          (WithLp.ofLp (LienardWiechert.velocityField (e b) (w b) t (R a (κ * t)) +
            LienardWiechert.accelerationField (e b) (w b) t (R a (κ * t))))) i -
        crossProduct (WithLp.ofLp (deriv (fun s => R a (κ * s)) t))
          (magneticOf (pointVector (e b) fun s => R b (κ * s))
          (t, R a (κ * t))) i =
        crossProduct (WithLp.ofLp (deriv (fun s => R a (κ * s)) t))
          (fun j => crossProduct (WithLp.ofLp ((w b).retardedDirection t (R a (κ * t))))
            (WithLp.ofLp (LienardWiechert.velocityField (e b) (w b) t (R a (κ * t)) +
              LienardWiechert.accelerationField (e b) (w b) t (R a (κ * t)))) j -
            magneticOf (pointVector (e b) fun s => R b (κ * s)) (t, R a (κ * t)) j) i := by
      rw [← Pi.sub_apply, ← map_sub]
      rfl
    have hB : |crossProduct (WithLp.ofLp (deriv (fun s => R a (κ * s)) t))
          (fun j => crossProduct (WithLp.ofLp ((w b).retardedDirection t (R a (κ * t))))
            (WithLp.ofLp (LienardWiechert.velocityField (e b) (w b) t (R a (κ * t)) +
              LienardWiechert.accelerationField (e b) (w b) t (R a (κ * t)))) j -
            magneticOf (pointVector (e b) fun s => R b (κ * s)) (t, R a (κ * t)) j) i| ≤
        2 * (κ * V₁) * (|C b| * κ ^ 2) := by
      refine (abs_crossProduct_le _ _ (fun j => ((hE j).2).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg κ))) i).trans ?_
      have : 0 ≤ |C b| * κ ^ 2 := by positivity
      nlinarith
    have hEi := (hE i).1
    calc _ = |((LienardWiechert.velocityField (e b) (w b) t (R a (κ * t)) +
            LienardWiechert.accelerationField (e b) (w b) t (R a (κ * t))) i -
          electricOf (pointScalar (e b) fun s => R b (κ * s))
            (pointVector (e b) fun s => R b (κ * s)) i (t, R a (κ * t))) +
          (crossProduct (WithLp.ofLp (deriv (fun s => R a (κ * s)) t))
            (crossProduct (WithLp.ofLp ((w b).retardedDirection t (R a (κ * t))))
              (WithLp.ofLp (LienardWiechert.velocityField (e b) (w b) t (R a (κ * t)) +
                LienardWiechert.accelerationField (e b) (w b) t (R a (κ * t))))) i -
            crossProduct (WithLp.ofLp (deriv (fun s => R a (κ * s)) t))
          (magneticOf (pointVector (e b) fun s => R b (κ * s))
              (t, R a (κ * t))) i)| := by ring_nf
      _ ≤ |C b| * κ ^ 3 + 2 * (κ * V₁) * (|C b| * κ ^ 2) := by
          rw [hcross]
          refine (abs_add_le _ _).trans (add_le_add (hEi.trans ?_) hB)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = (|C b| + 2 * V₁ * |C b|) * κ ^ 3 := by ring
  calc _ ≤ ∑ b ∈ ({a}ᶜ : Finset (Fin N)), |e a| * (|C b| + 2 * V₁ * |C b|) * κ ^ 3 :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ ≤ ∑ b, |e a| * (|C b| + 2 * V₁ * |C b|) * κ ^ 3 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun b _ _ => by positivity)
    _ = (|e a| * ∑ b, (|C b| + 2 * V₁ * |C b|)) * κ ^ 3 := by
        rw [Finset.mul_sum, Finset.sum_mul]

/-! ### An instance: an oscillating charge and a charge at rest -/

/-- The paths of the instance: `s ↦ (sin s) e₀` and the point `5 e₁` at rest. -/
def oscillatingPaths : Fin 2 → ℝ → E3 :=
  ![fun s => Real.sin s • (EuclideanSpace.single 0 1 : E3),
    fun _ => (5 : ℝ) • (EuclideanSpace.single 1 1 : E3)]

/-- The paths of the instance are smooth. -/
theorem contDiff_oscillatingPaths (b : Fin 2) : ContDiff ℝ ∞ (oscillatingPaths b) := by
  fin_cases b
  · exact Real.contDiff_sin.smul contDiff_const
  · exact contDiff_const

/-- The derivatives of the paths of the instance are bounded by `1`. -/
theorem norm_deriv_oscillatingPaths_le (b : Fin 2) (s : ℝ) :
    ‖deriv (oscillatingPaths b) s‖ ≤ 1 ∧ ‖deriv (deriv (oscillatingPaths b)) s‖ ≤ 1 ∧
      ‖deriv^[3] (oscillatingPaths b) s‖ ≤ 1 := by
  have he : ‖(EuclideanSpace.single 0 1 : E3)‖ = 1 := by simp
  fin_cases b
  · have h1 : deriv (fun s => Real.sin s • (EuclideanSpace.single 0 1 : E3)) =
        fun s => Real.cos s • (EuclideanSpace.single 0 1 : E3) :=
      funext fun s => ((Real.hasDerivAt_sin s).smul_const _).deriv
    have h2 : deriv (fun s => Real.cos s • (EuclideanSpace.single 0 1 : E3)) =
        fun s => (-Real.sin s) • (EuclideanSpace.single 0 1 : E3) :=
      funext fun s => ((Real.hasDerivAt_cos s).smul_const _).deriv
    have h3 : deriv (fun s => (-Real.sin s) • (EuclideanSpace.single 0 1 : E3)) =
        fun s => (-Real.cos s) • (EuclideanSpace.single 0 1 : E3) :=
      funext fun s => ((Real.hasDerivAt_sin s).fun_neg.smul_const _).deriv
    simp only [oscillatingPaths, Fin.zero_eta, Matrix.cons_val_zero,
      Function.iterate_succ_apply', Function.iterate_zero_apply, h1, h2, h3]
    simp only [norm_smul, he, mul_one, Real.norm_eq_abs, abs_neg]
    exact ⟨Real.abs_cos_le_one _, Real.abs_sin_le_one _, Real.abs_cos_le_one _⟩
  · simp [oscillatingPaths]

/-- The two charges of the instance stay at distances between `5` and `6`. -/
theorem norm_sub_oscillatingPaths (s : ℝ) :
    5 ≤ ‖oscillatingPaths 0 s - oscillatingPaths 1 s‖ ∧
      ‖oscillatingPaths 0 s - oscillatingPaths 1 s‖ ≤ 6 := by
  have hv : oscillatingPaths 0 s - oscillatingPaths 1 s =
      Real.sin s • (EuclideanSpace.single 0 1 : E3) - (5 : ℝ) • EuclideanSpace.single 1 1 := rfl
  rw [hv]
  have h := LienardWiechert.norm_sq_eq_sum
    (Real.sin s • (EuclideanSpace.single 0 1 : E3) - (5 : ℝ) • EuclideanSpace.single 1 1)
  simp at h
  have hn := norm_nonneg
    (Real.sin s • (EuclideanSpace.single 0 1 : E3) - (5 : ℝ) • EuclideanSpace.single 1 1)
  have hs := Real.sin_sq_le_one s
  constructor <;> nlinarith [sq_nonneg (Real.sin s)]

/-- **An instance of `force_eq_darwinLagrangian`**: for the oscillating charge `0` on
`t ↦ sin(κt) e₀` and the charge `1` at rest at `5e₁` (world lines `w b` on these paths, for
example `slowWorldline`), the force of the field of Liénard and Wiechert of the charge `1` on
the charge `0` is the interaction part of the residual of (65.7) up to `C κ³`, for
`0 < κ ≤ 1/2`. -/
theorem force_eq_darwinLagrangian_example (m e : Fin 2 → ℝ) :
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
              deriv (fun s => oscillatingPaths 0 (κ * s)) s i) t)| ≤ C * κ ^ 3 := by
  obtain ⟨C, hC⟩ := force_eq_darwinLagrangian m e contDiff_oscillatingPaths
    (fun b s => (norm_deriv_oscillatingPaths_le b s).1)
    (fun b s => (norm_deriv_oscillatingPaths_le b s).2.1)
    (fun b s => (norm_deriv_oscillatingPaths_le b s).2.2) (δ := 5) (ρ := 6) (by norm_num)
    (by norm_num) 0
  refine ⟨C, fun κ hκ hκ2 w hw t i => hC κ hκ (by linarith) (by linarith) w hw t ?_ ?_ i⟩
  · have hne : oscillatingPaths 0 (κ * t) ≠ oscillatingPaths 1 (κ * t) := fun h => by
      have := (norm_sub_oscillatingPaths (κ * t)).1
      rw [h, sub_self, norm_zero] at this
      norm_num at this
    intro b c hbc
    fin_cases b <;> fin_cases c
    · exact absurd rfl hbc
    · simpa using hne
    · simpa using hne.symm
    · exact absurd rfl hbc
  · intro b hb
    fin_cases b
    · exact absurd rfl hb
    · simpa using norm_sub_oscillatingPaths (κ * t)

end ProjectAinos.Electrodynamics
