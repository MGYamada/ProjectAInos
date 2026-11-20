/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Potential.Laplacian
public import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Tactic

/-!
# The maximum principle and the uniqueness of decaying harmonic functions

Space is `EuclideanSpace ℝ (Fin n)` with `n ≠ 0`.

* `deriv_deriv_nonpos_of_isLocalMax`: at an interior maximum of a continuous function of one
  variable the second derivative is nonpositive (a positive one would make the point a local
  minimum too, so the function would be locally constant).
* `coordLaplacian_nonpos_of_isLocalMax`: at a local maximum of a `C²` function the Laplacian is
  nonpositive.
* `le_of_laplacian_nonneg`: **the weak maximum principle** on a closed ball, proved with the
  perturbation `u + δ‖x − c‖²`, whose Laplacian is positive.
* `abs_le_of_laplacian_eq_zero`: a harmonic function is bounded in a ball by its bound on the
  sphere.
* `eq_zero_of_harmonic_of_tendsto`: a `C²` function that is harmonic on all of space and tends
  to `0` at infinity is zero.
-/

@[expose] public section

noncomputable section

open Filter Set Metric
open scoped Topology Laplacian ContDiff

namespace ProjectAinos.SmoothGeometry.Potential

variable {n : ℕ}

/-- At a local maximum of a function of one variable that is continuous there, the second
derivative is nonpositive. -/
theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {s₀ : ℝ} (h : IsLocalMax g s₀)
    (hc : ContinuousAt g s₀) : deriv (deriv g) s₀ ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hmin : IsLocalMin g s₀ := isLocalMin_of_deriv_deriv_pos hpos h.deriv_eq_zero hc
  have hconst : g =ᶠ[𝓝 s₀] fun _ => g s₀ := by
    filter_upwards [h, hmin] with s h1 h2 using le_antisymm h1 h2
  have hd : deriv g =ᶠ[𝓝 s₀] fun _ => 0 := by
    filter_upwards [hconst.eventuallyEq_nhds] with s hs
    rw [hs.deriv_eq, deriv_const]
  rw [hd.deriv_eq, deriv_const] at hpos
  exact lt_irrefl _ hpos

/-- At a local maximum of a function that is `C²` there, the Laplacian is nonpositive. -/
theorem coordLaplacian_nonpos_of_isLocalMax {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ 2 u p) (hmax : IsLocalMax u p) :
    coordLaplacian u p ≤ 0 := by
  refine Finset.sum_nonpos fun i _ => ?_
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1 with he
  set γ : ℝ → EuclideanSpace ℝ (Fin n) := fun s => p + s • e with hγ
  have hγc : Continuous γ := by fun_prop
  have hγ0 : γ 0 = p := by simp [hγ]
  have hγd (s : ℝ) : HasDerivAt γ e s := by
    simpa [hγ] using ((hasDerivAt_id s).smul_const e).const_add p
  have hg : IsLocalMax (u ∘ γ) 0 := by
    rw [← hγ0] at hmax
    exact hmax.comp_continuous hγc.continuousAt
  have hgc : ContinuousAt (u ∘ γ) 0 :=
    ContinuousAt.comp (by rw [hγ0]; exact hu.continuousAt) hγc.continuousAt
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 u (γ s) := by
    have h1 := hu.eventually (by simp)
    rw [← hγ0] at h1
    exact hγc.continuousAt.eventually h1
  have hd : deriv (u ∘ γ) =ᶠ[𝓝 0] fun s => fderiv ℝ u (γ s) e := by
    filter_upwards [hev] with s hs
    exact ((hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hγd s)).deriv
  have hD : DifferentiableAt ℝ (fun y => fderiv ℝ u y e) p :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const e)
  have hDγ : HasDerivAt (fun s => fderiv ℝ u (γ s) e)
      (fderiv ℝ (fun y => fderiv ℝ u y e) p e) 0 := by
    have hl : HasFDerivAt (fun y => fderiv ℝ u y e) (fderiv ℝ (fun y => fderiv ℝ u y e) p)
        (γ 0) := by
      rw [hγ0]
      exact hD.hasFDerivAt
    exact hl.comp_hasDerivAt 0 (hγd 0)
  have := deriv_deriv_nonpos_of_isLocalMax hg hgc
  rw [hd.deriv_eq, hDγ.deriv] at this
  exact this

/-- **The weak maximum principle on a ball.** A function that is `C²` at every point of the
closed ball `closedBall c R`, with `Δu ≥ 0` in the open ball and `u ≤ M` on the sphere, satisfies
`u ≤ M` on the closed ball. -/
theorem le_of_laplacian_nonneg [NeZero n] {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {R M : ℝ} (hu : ∀ x ∈ closedBall c R, ContDiffAt ℝ 2 u x)
    (hΔ : ∀ x ∈ ball c R, 0 ≤ Δ u x) (hM : ∀ x ∈ sphere c R, u x ≤ M) :
    ∀ x ∈ closedBall c R, u x ≤ M := by
  intro x hx
  have hR : 0 ≤ R := nonempty_closedBall.mp ⟨x, hx⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have key (δ : ℝ) (hδ : 0 < δ) : u x ≤ M + δ * R ^ 2 := by
    set w : EuclideanSpace ℝ (Fin n) → ℝ := fun y => δ * ‖y - c‖ ^ 2 with hw
    have hwc : ContDiff ℝ 2 w :=
      contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
    set v : EuclideanSpace ℝ (Fin n) → ℝ := u + w with hv
    have hvc : ContinuousOn v (closedBall c R) := fun y hy =>
      ((hu y hy).continuousAt.add hwc.continuous.continuousAt).continuousWithinAt
    obtain ⟨p, hp, hpmax⟩ := (isCompact_closedBall c R).exists_isMaxOn ⟨x, hx⟩ hvc
    have hvx : u x ≤ v x := by
      simp only [hv, hw, Pi.add_apply]
      have : 0 ≤ δ * ‖x - c‖ ^ 2 := by positivity
      linarith
    have hwle (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ closedBall c R) : w y ≤ δ * R ^ 2 := by
      simp only [hw]
      have h1 : ‖y - c‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hy
      have h2 : ‖y - c‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      exact mul_le_mul_of_nonneg_left h2 hδ.le
    by_cases hps : p ∈ sphere c R
    · calc u x ≤ v x := hvx
        _ ≤ v p := hpmax hx
        _ = u p + w p := rfl
        _ ≤ M + δ * R ^ 2 := add_le_add (hM p hps) (hwle p hp)
    · exfalso
      have hpb : p ∈ ball c R := by
        rw [mem_sphere] at hps
        rw [mem_closedBall] at hp
        exact mem_ball.mpr (lt_of_le_of_ne hp hps)
      have hloc : IsLocalMax v p :=
        hpmax.isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hpb) ball_subset_closedBall)
      have hvd : ContDiffAt ℝ 2 v p := (hu p hp).add hwc.contDiffAt
      have hle := coordLaplacian_nonpos_of_isLocalMax hvd hloc
      rw [coordLaplacian_eq_laplacian hvd, ContDiffAt.laplacian_add (hu p hp) hwc.contDiffAt,
        ← coordLaplacian_eq_laplacian hwc.contDiffAt] at hle
      have hwl : coordLaplacian w p = δ * (2 * n) := by
        rw [← coordLaplacian_normSq_sub c p,
          coordLaplacian_eq_laplacian hwc.contDiffAt]
        have hs : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ‖y - c‖ ^ 2) p :=
          ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt
        rw [coordLaplacian_eq_laplacian hs]
        change Δ (δ • fun y : EuclideanSpace ℝ (Fin n) => ‖y - c‖ ^ 2) p = _
        rw [InnerProductSpace.laplacian_smul δ hs, smul_eq_mul]
      have := hΔ p hpb
      rw [hwl] at hle
      have : 0 < δ * (2 * n) := by positivity
      linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hR2 : 0 < R ^ 2 + 1 := by positivity
  have h1 := key (ε / (R ^ 2 + 1)) (div_pos hε hR2)
  have h2 : ε / (R ^ 2 + 1) * R ^ 2 ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hR2]
    nlinarith
  linarith

/-- A harmonic function is bounded in absolute value in a ball by its bound on the sphere. -/
theorem abs_le_of_laplacian_eq_zero [NeZero n] {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {R M : ℝ} (hu : ∀ x ∈ closedBall c R, ContDiffAt ℝ 2 u x)
    (hΔ : ∀ x ∈ ball c R, Δ u x = 0) (hM : ∀ x ∈ sphere c R, |u x| ≤ M) :
    ∀ x ∈ closedBall c R, |u x| ≤ M := by
  intro x hx
  have h1 := le_of_laplacian_nonneg hu (fun y hy => (hΔ y hy).ge)
    (fun y hy => (le_abs_self _).trans (hM y hy)) x hx
  have h2 := le_of_laplacian_nonneg (u := -u) (fun y hy => (hu y hy).neg)
    (fun y hy => by rw [InnerProductSpace.laplacian_neg, Pi.neg_apply, hΔ y hy, neg_zero])
    (fun y hy => (neg_le_abs _).trans (hM y hy)) x hx
  rw [Pi.neg_apply] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- **Uniqueness of decaying harmonic functions.** A function that is `C²` and harmonic on all of
space and tends to `0` at infinity is zero. -/
theorem eq_zero_of_harmonic_of_tendsto [NeZero n] {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (hΔ : ∀ x, Δ u x = 0)
    (hlim : Tendsto u (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)) : u = 0 := by
  funext x
  refine abs_nonpos_iff.mp (le_of_forall_pos_le_add fun η hη => ?_)
  rw [zero_add]
  have hev := hlim.eventually (closedBall_mem_nhds (0 : ℝ) hη)
  obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hev
  obtain ⟨r, hr⟩ := ht.isBounded.subset_closedBall 0
  set R := max r ‖x‖ + 1 with hR
  have hsph : ∀ y ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) R, |u y| ≤ η := by
    intro y hy
    have hyt : y ∈ tᶜ := by
      intro hyt
      have h1 := hr hyt
      rw [mem_closedBall, dist_zero_right] at h1
      rw [mem_sphere, dist_zero_right] at hy
      have : r < R := by rw [hR]; linarith [le_max_left r ‖x‖]
      linarith
    have := hts hyt
    rwa [mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs] at this
  have hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    rw [mem_closedBall, dist_zero_right, hR]
    linarith [le_max_right r ‖x‖]
  exact abs_le_of_laplacian_eq_zero (fun y _ => hu.contDiffAt) (fun y _ => hΔ y) hsph x hx

end ProjectAinos.SmoothGeometry.Potential
