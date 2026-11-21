/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorChristoffel
public import ProjectAinos.SmoothGeometry.Euclidean.SphereIntegral
public import ProjectAinos.SmoothGeometry.Wave.RetardedIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# The flux of the superpotential through spheres

Landau–Lifshitz, §96, (96.16)–(96.17): the energy and momentum of matter and field as surface
integrals of the superpotential `h^{ikl}` on the slices `x⁰ = t` of a coordinate metric on
`MinkowskiModel 3`, and the divergence theorem on spheres and shells of `ℝ³` that turns them into
volume integrals of the total `|g| (κ T^{i0} + t^{i0})`.

**Calculus on spheres** (namespace `Sphere`, for `ℝ³ = EuclideanSpace ℝ (Fin 3)` with the surface
measure `sphereMeasure` of `SphereIntegral.lean`):

* `hasDerivAt_integral_sphere`, `continuousAt_integral_sphere`: differentiation and continuity of
  `s ↦ ∫ F(s, n) dσ(n)` for `F`, `∂ₛF` continuous on an open set containing `{s₀} × S²`.
* `rotation`, `rotationIsometry`: the rotations in a co-ordinate plane; `integral_fderiv_angular`:
  **the integral of an angular derivative `∂F(r n)(r J_{jk} n)` over a sphere vanishes**, because
  the rotations preserve the surface measure.
* `flux V R = R² ∫ Σ_α V_α(R n) n_α dσ` and `divergence V = Σ_α ∂_α V_α`; `hasDerivAt_flux_eq`:
  `∂_R flux = R² ∫ div V(R n) dσ`, from the identity `flux_algebra` that writes the radial
  derivative as `r² div V` minus angular derivatives of `x_j V_k`.
* `integral_eq_integral_Ioi_sphere`: polar co-ordinates `∫ F = ∫₀^∞ r² ∫ F(r n) dσ dr` for an
  integrable `F`.
* `flux_sub_flux`: **the divergence theorem on a shell** `R₁ < ‖x‖ < R₂` (`shell`), for a field
  of class `C¹` on an open set containing the closed shell; with `R₁ = 0`, on a ball.
* `integral_divergence_antisymm`: the flux `∫ Σ ∂_β A^{αβ} n_α dσ` of the divergence of an
  antisymmetric field through a sphere vanishes.

**The charges** (namespace `CoordinateMetric`, for `g : CoordinateMetric σ 3 U`):

* `superpotential_self`: `h^{ikk} = 0`; `totalDensity`: `|g| (G^{ik} + t^{ik})`, which is
  `|g| (κ T^{ik} + t^{ik})` under the Einstein equations (`totalDensity_eq`);
  `sum_fderiv_superpotential`: `∂_l h^{ikl} = 2 |g| (G^{ik} + t^{ik})` on `U`.
* `chargeField`, `surfaceCharge`: `P^i(t, R) = ½ ∮_{r = R} h^{i0α} n_α dA` on the slice
  `x⁰ = t`; `divergence_chargeField`: the spatial divergence of `h^{i0α}` is
  `2 |g| (G^{i0} + t^{i0})`, since `h^{i00} = 0`.
* `surfaceCharge_sub_surfaceCharge`, `surfaceCharge_sub_surfaceCharge_eq`: **the shell
  identity**, the difference of the charges on two spheres is the integral of
  `|g| (κ T^{i0} + t^{i0})` over the shell; `surfaceCharge_eq_integral_ball`: the charge is the
  integral over the ball.
* `totalFlux`: the flux `∮ |g| (G^{iα} + t^{iα}) n_α dA`; `hasDerivAt_surfaceCharge_time` and
  `surfaceCharge_sub_surfaceCharge_time`: **the balance of the charge in a sphere**,
  `∂ₜ P^i(t, R) = −totalFlux`, from `∂_l h^{iαl} = 2|g|(G^{iα} + t^{iα})` and the antisymmetry of
  `h^{iαβ}`.
* `abs_pseudoBraces_le`: the braces of (96.9) are at most `18 n⁴ K² B²` for inverse metric
  entries at most `K` and Christoffel symbols at most `B`, the bound behind the decay
  `t^{ik} = O(r⁻⁴)` of the pseudotensor.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.Sphere

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Integrals over the sphere that depend on a parameter -/

/-- An open set of `ℝ × ℝ³` that contains `{s₀} × S²` contains `[s₀ − δ, s₀ + δ] × S²` for
some `δ > 0`. -/
theorem exists_prod_subset {O : Set (ℝ × E3)} (hO : IsOpen O) {s₀ : ℝ}
    (hs₀ : ∀ n ∈ sphere (0 : E3) 1, (s₀, n) ∈ O) :
    ∃ δ > 0, ∀ s, |s - s₀| ≤ δ → ∀ n ∈ sphere (0 : E3) 1, (s, n) ∈ O := by
  have hK : IsCompact ({s₀} ×ˢ sphere (0 : E3) 1) :=
    isCompact_singleton.prod (isCompact_sphere 0 1)
  have hKO : {s₀} ×ˢ sphere (0 : E3) 1 ⊆ O := by
    rintro ⟨s, n⟩ ⟨hs, hn⟩
    rw [mem_singleton_iff] at hs
    subst hs
    exact hs₀ n hn
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨δ / 2, by positivity, fun s hs n hn => hsub ?_⟩
  rw [mem_thickening_iff]
  refine ⟨(s₀, n), ⟨rfl, hn⟩, ?_⟩
  rw [Prod.dist_eq, dist_self, Real.dist_eq]
  exact max_lt (by linarith) hδ

/-- The restriction of a function continuous on `O ⊇ {s} × S²` to the sphere is continuous. -/
theorem continuous_restrict_sphere {G : ℝ → E3 → ℝ} {O : Set (ℝ × E3)}
    (hG : ContinuousOn (Function.uncurry G) O) {s : ℝ}
    (hs : ∀ n ∈ sphere (0 : E3) 1, (s, n) ∈ O) :
    Continuous fun n : sphere (0 : E3) 1 => G s n := by
  have h : Continuous fun n : sphere (0 : E3) 1 => ((s, (n : E3)) : ℝ × E3) := by fun_prop
  exact hG.comp_continuous h fun n => hs n n.2

/-- **Continuity of a parametric integral over the sphere.** -/
theorem continuousAt_integral_sphere {G : ℝ → E3 → ℝ} {O : Set (ℝ × E3)} (hO : IsOpen O)
    {s₀ : ℝ} (hs₀ : ∀ n ∈ sphere (0 : E3) 1, (s₀, n) ∈ O)
    (hG : ContinuousOn (Function.uncurry G) O) :
    ContinuousAt (fun s => ∫ n : sphere (0 : E3) 1, G s n ∂sphereMeasure) s₀ := by
  obtain ⟨δ, hδ, hsub⟩ := exists_prod_subset hO hs₀
  have hK : IsCompact (closedBall s₀ δ ×ˢ sphere (0 : E3) 1) :=
    (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKO : closedBall s₀ δ ×ˢ sphere (0 : E3) 1 ⊆ O := fun p hp =>
    hsub p.1 (by simpa [mem_closedBall, Real.dist_eq] using hp.1) p.2 hp.2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hG.mono hKO)
  have hball : ball s₀ δ ∈ 𝓝 s₀ := ball_mem_nhds s₀ hδ
  refine continuousAt_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_
  · filter_upwards [hball] with s hs
    exact (continuous_restrict_sphere hG fun n hn =>
      hsub s (by rw [mem_ball, Real.dist_eq] at hs; exact hs.le) n hn).aestronglyMeasurable
  · filter_upwards [hball] with s hs
    exact Eventually.of_forall fun n => hC (s, n) ⟨ball_subset_closedBall hs, n.2⟩
  · refine Eventually.of_forall fun n => ?_
    have hc : ContinuousAt (Function.uncurry G) (s₀, (n : E3)) :=
      hG.continuousAt (hO.mem_nhds (hs₀ n n.2))
    exact hc.comp (f := fun s : ℝ => ((s, (n : E3)) : ℝ × E3)) (by fun_prop)

/-- **Differentiation under the integral over the sphere**: if `F` and `∂ₛF = F'` are continuous
on an open set `O ⊇ {s₀} × S²`, then `d/ds ∫ F(s, n) dσ = ∫ F'(s₀, n) dσ` at `s₀`. -/
theorem hasDerivAt_integral_sphere {F F' : ℝ → E3 → ℝ} {O : Set (ℝ × E3)} (hO : IsOpen O)
    {s₀ : ℝ} (hs₀ : ∀ n ∈ sphere (0 : E3) 1, (s₀, n) ∈ O)
    (hF : ContinuousOn (Function.uncurry F) O) (hF' : ContinuousOn (Function.uncurry F') O)
    (hd : ∀ p ∈ O, HasDerivAt (fun s => F s p.2) (F' p.1 p.2) p.1) :
    HasDerivAt (fun s => ∫ n : sphere (0 : E3) 1, F s n ∂sphereMeasure)
      (∫ n : sphere (0 : E3) 1, F' s₀ n ∂sphereMeasure) s₀ := by
  obtain ⟨δ, hδ, hsub⟩ := exists_prod_subset hO hs₀
  have hK : IsCompact (closedBall s₀ δ ×ˢ sphere (0 : E3) 1) :=
    (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKO : closedBall s₀ δ ×ˢ sphere (0 : E3) 1 ⊆ O := fun p hp =>
    hsub p.1 (by simpa [mem_closedBall, Real.dist_eq] using hp.1) p.2 hp.2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF'.mono hKO)
  have hmem {s : ℝ} (hs : s ∈ ball s₀ δ) : |s - s₀| ≤ δ := by
    rw [mem_ball, Real.dist_eq] at hs
    exact hs.le
  have h0 : |s₀ - s₀| ≤ δ := by simpa using hδ.le
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (F := fun s (n : sphere (0 : E3) 1) => F s n) (F' := fun s (n : sphere (0 : E3) 1) => F' s n)
    (ball_mem_nhds s₀ hδ) ?_ ?_ ?_ ?_ (integrable_const (μ := sphereMeasure) C) ?_).2
  · filter_upwards [ball_mem_nhds s₀ hδ] with s hs
    exact (continuous_restrict_sphere hF fun n hn => hsub s (hmem hs) n hn).aestronglyMeasurable
  · exact integrable_of_continuous (continuous_restrict_sphere hF fun n hn => hsub s₀ h0 n hn)
  · exact (continuous_restrict_sphere hF' fun n hn => hsub s₀ h0 n hn).aestronglyMeasurable
  · exact Eventually.of_forall fun n s hs => hC (s, n) ⟨ball_subset_closedBall hs, n.2⟩
  · exact Eventually.of_forall fun n s hs => hd (s, n) (hsub s (hmem hs) n n.2)

/-! ### Rotations in a co-ordinate plane -/

/-- The rotation by the angle `θ` in the plane of the axes `j` and `k`, from `e_j` towards
`e_k`. -/
def rotation (j k : Fin 3) (θ : ℝ) (v : E3) : E3 :=
  v + (cos θ - 1) • (v j • EuclideanSpace.single j 1 + v k • EuclideanSpace.single k 1) +
    sin θ • (v j • EuclideanSpace.single k 1 - v k • EuclideanSpace.single j 1)

/-- The derivative of the rotation with respect to the angle. -/
def rotationDeriv (j k : Fin 3) (θ : ℝ) (v : E3) : E3 :=
  (-sin θ) • (v j • EuclideanSpace.single j 1 + v k • EuclideanSpace.single k 1) +
    cos θ • (v j • EuclideanSpace.single k 1 - v k • EuclideanSpace.single j 1)

/-- The generator `J_{jk} v = v_j e_k − v_k e_j` of the rotations in the plane of `j` and `k`. -/
def angular (j k : Fin 3) (v : E3) : E3 :=
  v j • EuclideanSpace.single k 1 - v k • EuclideanSpace.single j 1

theorem rotation_zero (j k : Fin 3) (v : E3) : rotation j k 0 v = v := by
  simp [rotation]

theorem rotationDeriv_zero (j k : Fin 3) (v : E3) : rotationDeriv j k 0 v = angular j k v := by
  simp [rotationDeriv, angular]

theorem hasDerivAt_rotation (j k : Fin 3) (θ : ℝ) (v : E3) :
    HasDerivAt (fun θ => rotation j k θ v) (rotationDeriv j k θ v) θ :=
  ((((hasDerivAt_cos θ).sub_const 1).smul_const
    (v j • EuclideanSpace.single j 1 + v k • EuclideanSpace.single k 1)).const_add v).add
    ((hasDerivAt_sin θ).smul_const
      (v j • EuclideanSpace.single k 1 - v k • EuclideanSpace.single j 1))

theorem continuous_rotation (j k : Fin 3) :
    Continuous fun p : ℝ × E3 => rotation j k p.1 p.2 := by
  unfold rotation
  fun_prop

theorem continuous_rotationDeriv (j k : Fin 3) :
    Continuous fun p : ℝ × E3 => rotationDeriv j k p.1 p.2 := by
  unfold rotationDeriv
  fun_prop

theorem rotation_add (j k : Fin 3) (θ : ℝ) (v w : E3) :
    rotation j k θ (v + w) = rotation j k θ v + rotation j k θ w := by
  ext i
  simp only [rotation, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

theorem rotation_smul (j k : Fin 3) (θ c : ℝ) (v : E3) :
    rotation j k θ (c • v) = c • rotation j k θ v := by
  ext i
  simp only [rotation, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

theorem norm_rotation {j k : Fin 3} (hjk : j ≠ k) (θ : ℝ) (v : E3) :
    ‖rotation j k θ v‖ = ‖v‖ := by
  have h : ‖rotation j k θ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    fin_cases j <;> fin_cases k <;> simp at hjk <;>
      simp [rotation, Fin.sum_univ_three] <;> ring_nf <;> simp only [sin_sq] <;> ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The rotation as a linear isometry of `ℝ³`. -/
def rotationIsometry {j k : Fin 3} (hjk : j ≠ k) (θ : ℝ) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := rotation j k θ
      map_add' := rotation_add j k θ
      map_smul' := rotation_smul j k θ
      norm_map' := norm_rotation hjk θ } rfl

@[simp] theorem rotationIsometry_apply {j k : Fin 3} (hjk : j ≠ k) (θ : ℝ) (v : E3) :
    rotationIsometry hjk θ v = rotation j k θ v := rfl

/-! ### Angular derivatives integrate to zero -/

/-- A function continuous on `W` restricted to the sphere of radius `r ⊆ W` is continuous. -/
theorem continuous_comp_smul_sphere {X : Type*} [TopologicalSpace X] {G : E3 → X} {W : Set E3}
    (hG : ContinuousOn G W) {r : ℝ}
    (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W) :
    Continuous fun n : sphere (0 : E3) 1 => G (r • (n : E3)) :=
  hG.comp_continuous (by fun_prop) fun n => hr n n.2

/-- **The integral of an angular derivative over a sphere vanishes**: for `F` of class `C¹` on
an open set that contains the sphere of radius `|r|`, `∫ ∂F(r n)(r J_{jk} n) dσ(n) = 0`, because
the rotations in the plane of `j` and `k` preserve the surface measure. -/
theorem integral_fderiv_angular {F : E3 → ℝ} {W : Set E3} (hW : IsOpen W)
    (hF : ContDiffOn ℝ 1 F W) {r : ℝ} (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W)
    (j k : Fin 3) :
    ∫ n : sphere (0 : E3) 1, fderiv ℝ F (r • (n : E3)) (r • angular j k n) ∂sphereMeasure =
      0 := by
  by_cases hjk : j = k
  · subst hjk
    simp [angular]
  set O : Set (ℝ × E3) := {p | r • rotation j k p.1 p.2 ∈ W} with hOdef
  have hrot : Continuous fun p : ℝ × E3 => r • rotation j k p.1 p.2 :=
    (continuous_rotation j k).const_smul r
  have hO : IsOpen O := hW.preimage hrot
  have hs₀ : ∀ n ∈ sphere (0 : E3) 1, ((0 : ℝ), n) ∈ O := fun n hn => by
    simpa [hOdef, rotation_zero] using hr n hn
  have hdF : ContinuousOn (fderiv ℝ F) W := hF.continuousOn_fderiv_of_isOpen hW le_rfl
  have hD := hasDerivAt_integral_sphere (F := fun θ n => F (r • rotation j k θ n))
    (F' := fun θ n => fderiv ℝ F (r • rotation j k θ n) (r • rotationDeriv j k θ n)) hO hs₀
    (hF.continuousOn.comp hrot.continuousOn fun p hp => hp)
    ((hdF.comp hrot.continuousOn fun p hp => hp).clm_apply
      ((continuous_rotationDeriv j k).const_smul r).continuousOn)
    (fun p hp => by
      have hd : DifferentiableAt ℝ F (r • rotation j k p.1 p.2) :=
        (hF.differentiableOn one_ne_zero _ hp).differentiableAt (hW.mem_nhds hp)
      exact hd.hasFDerivAt.comp_hasDerivAt p.1 ((hasDerivAt_rotation j k p.1 p.2).const_smul r))
  have hconst : (fun θ => ∫ n : sphere (0 : E3) 1, F (r • rotation j k θ n) ∂sphereMeasure) =
      fun _ => ∫ n : sphere (0 : E3) 1, F (r • (n : E3)) ∂sphereMeasure := by
    funext θ
    exact integral_comp_linearIsometryEquiv (rotationIsometry hjk θ) (fun y => F (r • y))
  rw [hconst] at hD
  have h := hD.unique (hasDerivAt_const _ _)
  simpa [rotation_zero, rotationDeriv_zero] using h

/-! ### The flux through a sphere and the divergence theorem on a shell -/

/-- The flux `R² ∫ Σ_α V_α(R n) n_α dσ(n)` of a vector field `V` on `ℝ³` through the sphere of
radius `R` about the origin. -/
def flux (V : Fin 3 → E3 → ℝ) (R : ℝ) : ℝ :=
  ∫ n : sphere (0 : E3) 1, R ^ 2 * ∑ α, V α (R • (n : E3)) * (n : E3) α ∂sphereMeasure

/-- The divergence `Σ_α ∂_α V_α` of a vector field on `ℝ³`. -/
def divergence (V : Fin 3 → E3 → ℝ) (x : E3) : ℝ :=
  ∑ α, fderiv ℝ (V α) x (EuclideanSpace.single α 1)

/-- The flux through the sphere of radius `0` vanishes. -/
@[simp] theorem flux_zero (V : Fin 3 → E3 → ℝ) : flux V 0 = 0 := by
  simp [flux]

/-- The derivative of the flux with respect to the radius. -/
theorem hasDerivAt_flux {V : Fin 3 → E3 → ℝ} {W : Set E3} (hW : IsOpen W)
    (hV : ∀ α, ContDiffOn ℝ 1 (V α) W) {r : ℝ} (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W) :
    HasDerivAt (flux V) (∫ n : sphere (0 : E3) 1, (2 * r * ∑ α, V α (r • (n : E3)) * (n : E3) α +
      r ^ 2 * ∑ α, fderiv ℝ (V α) (r • (n : E3)) n * (n : E3) α) ∂sphereMeasure) r := by
  set O : Set (ℝ × E3) := {p | p.1 • p.2 ∈ W} with hOdef
  have hsm : Continuous fun p : ℝ × E3 => p.1 • p.2 := by fun_prop
  have hO : IsOpen O := hW.preimage hsm
  have hcV (α : Fin 3) : ContinuousOn (fun p : ℝ × E3 => V α (p.1 • p.2)) O :=
    (hV α).continuousOn.comp hsm.continuousOn fun p hp => hp
  have hcD (α : Fin 3) : ContinuousOn (fun p : ℝ × E3 => fderiv ℝ (V α) (p.1 • p.2) p.2) O :=
    (((hV α).continuousOn_fderiv_of_isOpen hW le_rfl).comp hsm.continuousOn
      fun p hp => hp).clm_apply continuousOn_snd
  have hcoord (α : Fin 3) : Continuous fun p : ℝ × E3 => p.2 α := by fun_prop
  refine hasDerivAt_integral_sphere (F := fun s n => s ^ 2 * ∑ α, V α (s • n) * n α)
    (F' := fun s n => 2 * s * ∑ α, V α (s • n) * n α +
      s ^ 2 * ∑ α, fderiv ℝ (V α) (s • n) n * n α) hO (fun n hn => hr n hn) ?_ ?_ ?_
  · exact (continuousOn_fst.pow 2).mul
      (continuousOn_finsetSum _ fun α _ => (hcV α).mul (hcoord α).continuousOn)
  · exact ((continuousOn_const.mul continuousOn_fst).mul
      (continuousOn_finsetSum _ fun α _ => (hcV α).mul (hcoord α).continuousOn)).add
      ((continuousOn_fst.pow 2).mul
        (continuousOn_finsetSum _ fun α _ => (hcD α).mul (hcoord α).continuousOn))
  · intro p hp
    have hd (α : Fin 3) : HasDerivAt (fun s => V α (s • p.2)) (fderiv ℝ (V α) (p.1 • p.2) p.2)
        p.1 := by
      have hd' : DifferentiableAt ℝ (V α) (p.1 • p.2) :=
        ((hV α).differentiableOn one_ne_zero _ hp).differentiableAt (hW.mem_nhds hp)
      have hl : HasDerivAt (fun s : ℝ => s • p.2) p.2 p.1 := by
        simpa using (hasDerivAt_id p.1).smul_const p.2
      exact hd'.hasFDerivAt.comp_hasDerivAt p.1 hl
    have hsum : HasDerivAt (fun s => ∑ α, V α (s • p.2) * p.2 α)
        (∑ α, fderiv ℝ (V α) (p.1 • p.2) p.2 * p.2 α) p.1 :=
      HasDerivAt.fun_sum fun α _ => (hd α).mul_const (p.2 α)
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * p.1) p.1 := by
      simpa using hasDerivAt_pow 2 p.1
    exact hsq.mul hsum

/-- The algebra behind the divergence theorem on a sphere: with `x = r n`, `|n| = 1`, `V_α = V α`
and `D_{iα} = ∂_i V_α`, the radial derivative `∂_r (r² V(r n) · n)` is `r² div V − Σ_{j,k}
∂(x_j V_k)(r J_{jk} n)`. -/
theorem flux_algebra (r : ℝ) (n V : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ)
    (hn : ∑ α, n α ^ 2 = 1) :
    2 * r * ∑ α, V α * n α + r ^ 2 * ∑ α, (∑ i, n i * D i α) * n α =
      r ^ 2 * ∑ α, D α α - ∑ j, ∑ k, (r * n j * (r * (n j * D k k - n k * D j k)) +
        V k * (r * (n j * (if j = k then 1 else 0) - n k))) := by
  simp only [Fin.sum_univ_three, Fin.isValue] at hn ⊢
  simp only [Fin.isValue, ite_true, show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ite_false]
  linear_combination r ^ 2 * (D 0 0 + D 1 1 + D 2 2) * hn

/-- A point of the unit sphere has `Σ_α n_α² = 1`. -/
theorem sum_sq_of_mem_sphere (n : sphere (0 : E3) 1) : ∑ α, (n : E3) α ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq (n : E3)
  rw [norm_eq_of_mem_sphere n, one_pow] at h
  exact h.symm

/-- A vector of `ℝ³` in the standard basis. -/
theorem eq_sum_single (v : E3) : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three]

/-- The derivative of a function along a vector, in the partial derivatives. -/
theorem fderiv_apply_eq_sum (G : E3 → ℝ) (x v : E3) :
    fderiv ℝ G x v = ∑ i, v i * fderiv ℝ G x (EuclideanSpace.single i 1) := by
  conv_lhs => rw [eq_sum_single v]
  simp [map_sum, map_smul, smul_eq_mul]

/-- The derivative of `x ↦ x_j G(x)`. -/
theorem fderiv_coord_mul {G : E3 → ℝ} {x : E3} (hG : DifferentiableAt ℝ G x) (j : Fin 3)
    (v : E3) : fderiv ℝ (fun y : E3 => y j * G y) x v = x j * fderiv ℝ G x v + G x * v j := by
  have hj : HasFDerivAt (fun y : E3 => y j) (EuclideanSpace.proj j : E3 →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj j : E3 →L[ℝ] ℝ).hasFDerivAt
  rw [(hj.fun_mul hG.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  simp [EuclideanSpace.proj]

/-- `x ↦ x_j G(x)` is of class `C¹` where `G` is. -/
theorem contDiffOn_coord_mul {G : E3 → ℝ} {W : Set E3} (hG : ContDiffOn ℝ 1 G W) (j : Fin 3) :
    ContDiffOn ℝ 1 (fun y : E3 => y j * G y) W :=
  ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ).contDiff.contDiffOn).mul hG

/-- The derivative of a `C¹` function, applied along a continuous field, on a sphere in `W`. -/
theorem continuous_fderiv_sphere {G : E3 → ℝ} {W : Set E3} (hW : IsOpen W)
    (hG : ContDiffOn ℝ 1 G W) {r : ℝ} (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W)
    {u : E3 → E3} (hu : Continuous u) :
    Continuous fun n : sphere (0 : E3) 1 => fderiv ℝ G (r • (n : E3)) (u n) :=
  (continuous_comp_smul_sphere (G := fun y => fderiv ℝ G y) (hG.continuousOn_fderiv_of_isOpen hW
    le_rfl) hr).clm_apply (hu.comp continuous_subtype_val)

/-- The divergence of a `C¹` field is continuous. -/
theorem continuousOn_divergence {V : Fin 3 → E3 → ℝ} {W : Set E3} (hW : IsOpen W)
    (hV : ∀ α, ContDiffOn ℝ 1 (V α) W) : ContinuousOn (divergence V) W :=
  continuousOn_finsetSum _ fun α _ =>
    ((hV α).continuousOn_fderiv_of_isOpen hW le_rfl).clm_apply continuousOn_const

/-- **The radial derivative of the flux** is `r² ∫ div V(r n) dσ(n)`. -/
theorem hasDerivAt_flux_eq {V : Fin 3 → E3 → ℝ} {W : Set E3} (hW : IsOpen W)
    (hV : ∀ α, ContDiffOn ℝ 1 (V α) W) {r : ℝ} (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W) :
    HasDerivAt (flux V)
      (r ^ 2 * ∫ n : sphere (0 : E3) 1, divergence V (r • (n : E3)) ∂sphereMeasure) r := by
  have h := hasDerivAt_flux hW hV hr
  convert h using 1
  set A : sphere (0 : E3) 1 → ℝ := fun n => fderiv ℝ (fun y : E3 => y 0 * V 0 y) (r • (n : E3))
    (r • angular 0 0 n) with hA
  have hF (j k : Fin 3) : ContDiffOn ℝ 1 (fun y : E3 => y j * V k y) W :=
    contDiffOn_coord_mul (hV k) j
  have hang (j k : Fin 3) : Continuous fun n : sphere (0 : E3) 1 =>
      fderiv ℝ (fun y : E3 => y j * V k y) (r • (n : E3)) (r • angular j k n) :=
    continuous_fderiv_sphere hW (hF j k) hr (u := fun v => r • angular j k v)
      (by unfold angular; fun_prop)
  have hpt (n : sphere (0 : E3) 1) :
      2 * r * ∑ α, V α (r • (n : E3)) * (n : E3) α +
        r ^ 2 * ∑ α, fderiv ℝ (V α) (r • (n : E3)) n * (n : E3) α =
      r ^ 2 * divergence V (r • (n : E3)) - ∑ j, ∑ k,
        fderiv ℝ (fun y : E3 => y j * V k y) (r • (n : E3)) (r • angular j k n) := by
    have hd (k : Fin 3) : DifferentiableAt ℝ (V k) (r • (n : E3)) :=
      ((hV k).differentiableOn one_ne_zero _ (hr n n.2)).differentiableAt
        (hW.mem_nhds (hr n n.2))
    simp only [fderiv_coord_mul (hd _)]
    have hang' (j k : Fin 3) : fderiv ℝ (V k) (r • (n : E3)) (r • angular j k n) =
        r * ((n : E3) j * fderiv ℝ (V k) (r • (n : E3)) (EuclideanSpace.single k 1) -
          (n : E3) k * fderiv ℝ (V k) (r • (n : E3)) (EuclideanSpace.single j 1)) := by
      simp [angular, map_sub, map_smul, smul_eq_mul]
    have hcomp (j k : Fin 3) : (r • angular j k n) j =
        r * ((n : E3) j * (if j = k then 1 else 0) - (n : E3) k) := by
      simp [angular]
    simp only [hang', hcomp, fderiv_apply_eq_sum _ _ (n : E3), divergence]
    have halg := flux_algebra r (fun α => (n : E3) α) (fun α => V α (r • (n : E3)))
      (fun i α => fderiv ℝ (V α) (r • (n : E3)) (EuclideanSpace.single i 1))
      (sum_sq_of_mem_sphere n)
    simp only [PiLp.smul_apply, smul_eq_mul] at halg ⊢
    rw [halg]
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have hdiv : Continuous fun n : sphere (0 : E3) 1 => r ^ 2 * divergence V (r • (n : E3)) :=
    continuous_const.mul (continuous_comp_smul_sphere (continuousOn_divergence hW hV) hr)
  rw [integral_sub (integrable_of_continuous hdiv)
    (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_of_continuous (hang j k)),
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_of_continuous (hang j k)]
  simp only [integral_finsetSum _ fun k _ => integrable_of_continuous (hang _ k),
    integral_fderiv_angular hW (hF _ _) hr, Finset.sum_const_zero, sub_zero]
  rw [integral_const_mul]

/-- **Polar co-ordinates** in `ℝ³` for an integrable function:
`∫ F = ∫₀^∞ r² ∫ F(r n) dσ(n) dr`. -/
theorem integral_eq_integral_Ioi_sphere {F : E3 → ℝ} (hF : Integrable F) :
    ∫ x, F x = ∫ r in Ioi (0 : ℝ),
      r ^ 2 * ∫ n : sphere (0 : E3) 1, F (r • (n : E3)) ∂sphereMeasure := by
  have h1 : ∫ x, F x =
      ∫ x : ({(0 : E3)}ᶜ : Set E3), F x ∂((volume : Measure E3).comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl fun x ↦ F x,
      restrict_compl_singleton]
  set G : sphere (0 : E3) 1 × Ioi (0 : ℝ) → ℝ := fun p => F (p.2.1 • (p.1 : E3)) with hG
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E3)
  have hGh (x : ({(0 : E3)}ᶜ : Set E3)) : G (homeomorphUnitSphereProd E3 x) = F x := by
    have hx0 : (x : E3) ≠ 0 := x.2
    have hx : 0 < ‖(x : E3)‖ := norm_pos_iff.mpr hx0
    simp only [hG]
    congr 1
    simp [smul_smul, hx.ne']
  have h3 : ∫ x : ({(0 : E3)}ᶜ : Set E3), F x ∂((volume : Measure E3).comap (↑)) =
      ∫ x : ({(0 : E3)}ᶜ : Set E3), G (homeomorphUnitSphereProd E3 x)
        ∂((volume : Measure E3).comap (↑)) :=
    integral_congr_ae (Eventually.of_forall fun x => (hGh x).symm)
  have h2 := hmp.integral_comp (Homeomorph.measurableEmbedding _) G
  have hcomp : Integrable (G ∘ homeomorphUnitSphereProd E3)
      ((volume : Measure E3).comap (↑)) := by
    have h : Integrable (fun x : ({(0 : E3)}ᶜ : Set E3) => F x)
        ((volume : Measure E3).comap (↑)) :=
      (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hF.integrableOn
    exact h.congr (Eventually.of_forall fun x => (hGh x).symm)
  have hGi := (hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)).mp hcomp
  rw [h1, h3, h2, integral_prod_symm G hGi]
  simp only [hG, Measure.volumeIoiPow, ENNReal.ofReal, finrank_euclideanSpace_fin, Nat.reduceSub]
  rw [integral_withDensity_eq_integral_smul
      ((measurable_subtype_coe.pow_const _).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi (fun a => Real.toNNReal (a ^ 2) •
      ∫ n : sphere (0 : E3) 1, F (a • (n : E3)) ∂sphereMeasure)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) _), smul_eq_mul]

/-- The open shell `R₁ < ‖x‖ < R₂`. -/
def shell (R₁ R₂ : ℝ) : Set E3 := {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}

theorem measurableSet_shell (R₁ R₂ : ℝ) : MeasurableSet (shell R₁ R₂) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- The points `r n`, `r ≥ 0`, of the shell. -/
theorem smul_mem_shell {R₁ R₂ r : ℝ} (hr : 0 ≤ r) (n : sphere (0 : E3) 1) :
    r • (n : E3) ∈ shell R₁ R₂ ↔ r ∈ Ioo R₁ R₂ := by
  simp [shell, norm_smul, norm_eq_of_mem_sphere n, abs_of_nonneg hr]

/-- A function continuous on a neighbourhood of the closed shell is integrable on the shell. -/
theorem integrableOn_shell {G : E3 → ℝ} {W : Set E3} (hG : ContinuousOn G W) {R₁ R₂ : ℝ}
    (hsub : ∀ x : E3, R₁ ≤ ‖x‖ → ‖x‖ ≤ R₂ → x ∈ W) : IntegrableOn G (shell R₁ R₂) := by
  have hK : IsCompact {x : E3 | R₁ ≤ ‖x‖ ∧ ‖x‖ ≤ R₂} :=
    (isCompact_closedBall (0 : E3) R₂).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      fun x hx => by simpa using hx.2
  exact ((hG.mono fun x hx => hsub x hx.1 hx.2).integrableOn_compact hK).mono_set
    fun x hx => ⟨hx.1.le, hx.2.le⟩

/-- **The divergence theorem on a shell**: for a vector field of class `C¹` on an open set that
contains the closed shell `R₁ ≤ ‖x‖ ≤ R₂` (`0 ≤ R₁ ≤ R₂`), the difference of the fluxes through
the two spheres is the integral of the divergence over the shell. With `R₁ = 0` it is the
divergence theorem on a ball. -/
theorem flux_sub_flux {V : Fin 3 → E3 → ℝ} {W : Set E3} (hW : IsOpen W)
    (hV : ∀ α, ContDiffOn ℝ 1 (V α) W) {R₁ R₂ : ℝ} (h0 : 0 ≤ R₁) (h12 : R₁ ≤ R₂)
    (hsub : ∀ x : E3, R₁ ≤ ‖x‖ → ‖x‖ ≤ R₂ → x ∈ W) :
    flux V R₂ - flux V R₁ = ∫ x in shell R₁ R₂, divergence V x := by
  have hr {r : ℝ} (hr : r ∈ Icc R₁ R₂) : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W := fun n hn =>
    hsub _ (by rw [norm_smul, norm_eq_of_mem_sphere ⟨n, hn⟩, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (h0.trans hr.1)]; exact hr.1)
      (by rw [norm_smul, norm_eq_of_mem_sphere ⟨n, hn⟩, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (h0.trans hr.1)]; exact hr.2)
  set Ψ : ℝ → ℝ := fun r =>
    r ^ 2 * ∫ n : sphere (0 : E3) 1, divergence V (r • (n : E3)) ∂sphereMeasure with hΨ
  have hderiv : ∀ r ∈ uIcc R₁ R₂, HasDerivAt (flux V) (Ψ r) r := fun r hr' => by
    rw [uIcc_of_le h12] at hr'
    exact hasDerivAt_flux_eq hW hV (hr hr')
  have hO : IsOpen {p : ℝ × E3 | p.1 • p.2 ∈ W} :=
    hW.preimage (by fun_prop : Continuous fun p : ℝ × E3 => p.1 • p.2)
  have hcont : ContinuousOn Ψ (uIcc R₁ R₂) := fun r hr' => by
    rw [uIcc_of_le h12] at hr'
    refine (continuousAt_id.pow 2 |>.mul (continuousAt_integral_sphere
      (G := fun s n => divergence V (s • n)) hO (hr hr') ?_)).continuousWithinAt
    exact (continuousOn_divergence hW hV).comp
      (by fun_prop : Continuous fun p : ℝ × E3 => p.1 • p.2).continuousOn fun p hp => hp
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hint : Integrable ((shell R₁ R₂).indicator (divergence V)) :=
    (integrable_indicator_iff (measurableSet_shell R₁ R₂)).mpr
      (integrableOn_shell (continuousOn_divergence hW hV) hsub)
  rw [← integral_indicator (measurableSet_shell R₁ R₂), integral_eq_integral_Ioi_sphere hint,
    intervalIntegral.integral_of_le h12, integral_Ioc_eq_integral_Ioo]
  have hsplit : ∀ r ∈ Ioi (0 : ℝ), r ^ 2 * ∫ n : sphere (0 : E3) 1,
      (shell R₁ R₂).indicator (divergence V) (r • (n : E3)) ∂sphereMeasure =
      (Ioo R₁ R₂).indicator Ψ r := fun r hr0 => by
    by_cases hrs : r ∈ Ioo R₁ R₂
    · rw [indicator_of_mem hrs]
      simp only [hΨ]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun n => ?_)
      exact indicator_of_mem ((smul_mem_shell (le_of_lt hr0) n).mpr hrs) _
    · rw [indicator_of_notMem hrs]
      have h : ∀ n : sphere (0 : E3) 1,
          (shell R₁ R₂).indicator (divergence V) (r • (n : E3)) = 0 := fun n =>
        indicator_of_notMem (fun h => hrs ((smul_mem_shell (le_of_lt hr0) n).mp h)) _
      simp [h]
  have hIoo : Ioo R₁ R₂ ∩ Ioi (0 : ℝ) = Ioo R₁ R₂ :=
    inter_eq_left.mpr fun r hr' => lt_of_le_of_lt h0 hr'.1
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, hIoo]

/-- **The flux of the divergence of an antisymmetric field through a sphere vanishes**: if
`A^{αβ} = −A^{βα}` on `W` and `r ≠ 0`, then `∫ Σ_{α,β} ∂_β A^{αβ}(r n) n_α dσ(n) = 0`, since
`2 r Σ n_α ∂_β A^{αβ} = Σ_{α,β} ∂A^{αβ}(r J_{αβ} n)` is a sum of angular derivatives. -/
theorem integral_divergence_antisymm {A : Fin 3 → Fin 3 → E3 → ℝ} {W : Set E3} (hW : IsOpen W)
    (hA : ∀ α β, ContDiffOn ℝ 1 (A α β) W) (hanti : ∀ x ∈ W, ∀ α β, A α β x = -A β α x)
    {r : ℝ} (hr0 : r ≠ 0) (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W) :
    ∫ n : sphere (0 : E3) 1, ∑ α, ∑ β, fderiv ℝ (A α β) (r • (n : E3))
      (EuclideanSpace.single β 1) * (n : E3) α ∂sphereMeasure = 0 := by
  have hang (α β : Fin 3) : Continuous fun n : sphere (0 : E3) 1 =>
      fderiv ℝ (A α β) (r • (n : E3)) (r • angular α β n) :=
    continuous_fderiv_sphere hW (hA α β) hr (u := fun v => r • angular α β v)
      (by unfold angular; fun_prop)
  have hpt (n : sphere (0 : E3) 1) : ∑ α, ∑ β, fderiv ℝ (A α β) (r • (n : E3))
      (EuclideanSpace.single β 1) * (n : E3) α = (2 * r)⁻¹ * ∑ α, ∑ β,
        fderiv ℝ (A α β) (r • (n : E3)) (r • angular α β n) := by
    have hx := hr n n.2
    have hd (α β : Fin 3) : fderiv ℝ (A α β) (r • (n : E3)) =
        -fderiv ℝ (A β α) (r • (n : E3)) := by
      have he : A α β =ᶠ[𝓝 (r • (n : E3))] fun y => -A β α y :=
        eventually_of_mem (hW.mem_nhds hx) fun y hy => hanti y hy α β
      rw [he.fderiv_eq, fderiv_fun_neg]
    have hexp (α β : Fin 3) : fderiv ℝ (A α β) (r • (n : E3)) (r • angular α β n) =
        r * ((n : E3) α * fderiv ℝ (A α β) (r • (n : E3)) (EuclideanSpace.single β 1) -
          (n : E3) β * fderiv ℝ (A α β) (r • (n : E3)) (EuclideanSpace.single α 1)) := by
      simp [angular, map_sub, map_smul, smul_eq_mul]
    simp only [hexp]
    have hswap : ∑ α, ∑ β, (n : E3) β *
        fderiv ℝ (A α β) (r • (n : E3)) (EuclideanSpace.single α 1) =
        -∑ α, ∑ β, (n : E3) α *
          fderiv ℝ (A α β) (r • (n : E3)) (EuclideanSpace.single β 1) := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [hd β α]
      simp
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at hswap ⊢
    rw [hswap]
    field_simp
    congr 1
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => mul_comm _ _
    · norm_num
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      integrable_of_continuous (hang α β)]
  simp only [integral_finsetSum _ fun β _ => integrable_of_continuous (hang _ β),
    integral_fderiv_angular hW (hA _ _) hr, Finset.sum_const_zero, mul_zero]

end ProjectAinos.SmoothGeometry.Sphere

namespace ProjectAinos.SmoothGeometry

open TopologicalSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Slices of space-time -/

namespace Minkowski

/-- The event `(s, y)` moves along the time axis with `s`. -/
theorem hasDerivAt_vector_time (s : ℝ) (y : E3) :
    HasDerivAt (fun s : ℝ => vector s y) (Pi.single 0 1 : MinkowskiModel 3) s := by
  have h : (fun s : ℝ => vector s y) = fun s => s • (Pi.single 0 1 : MinkowskiModel 3) +
      vector 0 y := by
    funext s
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [vector, Fin.succ_ne_zero]
  rw [h]
  simpa using ((hasDerivAt_id s).smul_const (Pi.single 0 1 : MinkowskiModel 3)).add_const
    (vector 0 y)

/-- The slice `y ↦ (t, y)` has the derivative `v ↦ (0, v)`. -/
theorem hasFDerivAt_vector_space (t : ℝ) (y : E3) :
    HasFDerivAt (fun y : E3 => vector t y)
      ((Wave.timeSpaceEquiv.symm : ℝ × E3 →L[ℝ] MinkowskiModel 3).comp
        (ContinuousLinearMap.inr ℝ ℝ E3)) y :=
  Wave.timeSpaceEquiv.symm.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)

/-- The axis `α` of space is the axis `α + 1` of space-time. -/
theorem vector_zero_single (α : Fin 3) :
    vector 0 (EuclideanSpace.single α 1) = (Pi.single α.succ 1 : MinkowskiModel 3) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [vector, (Fin.succ_ne_zero α).symm]
  · simp [vector, Pi.single_apply, Fin.succ_inj]

/-- The derivative of a function of space-time along a slice. -/
theorem fderiv_comp_vector {f : MinkowskiModel 3 → ℝ} {t : ℝ} {y : E3}
    (hf : DifferentiableAt ℝ f (vector t y)) (v : E3) :
    fderiv ℝ (fun y : E3 => f (vector t y)) y v = fderiv ℝ f (vector t y) (vector 0 v) := by
  have h := hf.hasFDerivAt.comp y (hasFDerivAt_vector_space t y)
  rw [show (fun y : E3 => f (vector t y)) = f ∘ fun y : E3 => vector t y from rfl, h.fderiv]
  rfl

/-- The derivative along the axis `α` of a slice is the derivative along `e_{α+1}`. -/
theorem fderiv_comp_vector_single {f : MinkowskiModel 3 → ℝ} {t : ℝ} {y : E3}
    (hf : DifferentiableAt ℝ f (vector t y)) (α : Fin 3) :
    fderiv ℝ (fun y : E3 => f (vector t y)) y (EuclideanSpace.single α 1) =
      fderiv ℝ f (vector t y) (Pi.single α.succ 1) := by
  rw [fderiv_comp_vector hf, vector_zero_single]

/-- The slice `y ↦ (t, y)` is smooth. -/
theorem contDiff_vector_space (t : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y : E3 => vector t y) :=
  Wave.timeSpaceEquiv.symm.contDiff.comp (contDiff_const.prodMk contDiff_id)

/-- The slice `x⁰ = t` meets an open set in an open set. -/
theorem isOpen_slice {U : Set (MinkowskiModel 3)} (hU : IsOpen U) (t : ℝ) :
    IsOpen {y : E3 | vector t y ∈ U} :=
  hU.preimage (contDiff_vector_space t (n := 0)).continuous

end Minkowski

namespace CoordinateMetric

open Minkowski

/-! ### The superpotential and the total -/

section General

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}
  (g : CoordinateMetric σ d U)

/-- `h^{ikk} = 0`, from the antisymmetry of the superpotential. -/
theorem superpotential_self (z : MinkowskiModel d) (i k : Fin (d + 1)) :
    g.superpotential z i k k = 0 := by
  linarith [g.superpotential_antisymm z i k k]

/-- The total density `|g| (G^{ik} + t^{ik})`; with the Einstein equations `G^{ik} = κ T^{ik}` it
is `|g| (κ T^{ik} + t^{ik})`. -/
def totalDensity (z : MinkowskiModel d) (i k : Fin (d + 1)) : ℝ :=
  densityOf g.coefficient z ^ 2 * (g.raisedEinstein z i k + g.pseudotensor z i k)

/-- **The divergence of the superpotential is twice the total**: `∂_l h^{ikl} = 2 |g| (G^{ik} +
t^{ik})` on `U`, the definition of `t^{ik}`. -/
theorem sum_fderiv_superpotential {z : MinkowskiModel d} (hz : z ∈ U) (i k : Fin (d + 1)) :
    ∑ l, fderiv ℝ (fun w => g.superpotential w i k l) z (Pi.single l 1) =
      2 * g.totalDensity z i k := by
  have hpos := g.densityOf_pos hz
  unfold totalDensity pseudotensor
  field_simp
  ring

/-- With the Einstein equations, the total density is `|g| (κ T^{ik} + t^{ik})`. -/
theorem totalDensity_eq {κ : ℝ} {T : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {z : MinkowskiModel d}
    (hz : z ∈ U) (i k : Fin (d + 1)) :
    g.totalDensity z i k = densityOf g.coefficient z ^ 2 * (κ * T z i k + g.pseudotensor z i k) :=
  by rw [totalDensity, hT z hz]

theorem contDiffOn_totalDensity (i k : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.totalDensity z i k) U := by
  have h : ∀ z ∈ U, g.totalDensity z i k = (1 / 2 : ℝ) *
      ∑ l, fderiv ℝ (fun w => g.superpotential w i k l) z (Pi.single l 1) := fun z hz => by
    rw [g.sum_fderiv_superpotential hz]
    ring
  refine (contDiffOn_const.mul (ContDiffOn.sum fun l _ =>
    ((g.contDiffOn_superpotential i k l).fderiv_of_isOpen U.isOpen (m := ∞)
      (by simp)).clm_apply contDiffOn_const)).congr h

end General

variable {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} (g : CoordinateMetric σ 3 U)

/-! ### The surface charges -/

/-- The field `V_α(x) = h^{i0α}(t, x)` on the slice `x⁰ = t`, whose flux is the charge. -/
def chargeField (t : ℝ) (i : Fin 4) (α : Fin 3) (x : E3) : ℝ :=
  g.superpotential (vector t x) i 0 α.succ

/-- **The surface charge** `P^i(t, R) = ½ ∮_{r = R} h^{i0α} n_α dA` on the sphere of radius `R` of
the slice `x⁰ = t`, Landau–Lifshitz (96.17), in the normalization `∂_l h^{ikl} = 2|g|(G^{ik} +
t^{ik})`. -/
def surfaceCharge (t R : ℝ) (i : Fin 4) : ℝ := Sphere.flux (g.chargeField t i) R / 2

/-- The field `S_α(x) = |g| (G^{iα} + t^{iα})(t, x)` of the total density on a slice. -/
def totalFluxField (t : ℝ) (i : Fin 4) (α : Fin 3) (x : E3) : ℝ :=
  g.totalDensity (vector t x) i α.succ

/-- The flux `∮_{r = R} |g| (G^{iα} + t^{iα}) n_α dA` of the total through a sphere. -/
def totalFlux (t R : ℝ) (i : Fin 4) : ℝ := Sphere.flux (g.totalFluxField t i) R

theorem contDiffOn_chargeField (t : ℝ) (i : Fin 4) (α : Fin 3) :
    ContDiffOn ℝ ∞ (g.chargeField t i α) {y : E3 | vector t y ∈ U} :=
  (g.contDiffOn_superpotential i 0 α.succ).comp (contDiff_vector_space t).contDiffOn
    fun _ hy => hy

/-- **The spatial divergence of the charge field is twice the total**: since `h^{i00} = 0`,
`Σ_α ∂_α h^{i0α} = ∂_l h^{i0l} = 2 |g| (G^{i0} + t^{i0})` on the slice. -/
theorem divergence_chargeField {t : ℝ} {x : E3} (hx : vector t x ∈ U) (i : Fin 4) :
    Sphere.divergence (g.chargeField t i) x = 2 * g.totalDensity (vector t x) i 0 := by
  have hU := U.isOpen.mem_nhds hx
  have hd (l : Fin 4) : DifferentiableAt ℝ (fun w => g.superpotential w i 0 l) (vector t x) :=
    ((g.contDiffOn_superpotential i 0 l).contDiffAt hU).differentiableAt (by simp)
  rw [← g.sum_fderiv_superpotential hx, Fin.sum_univ_succ]
  have h0 : fderiv ℝ (fun w => g.superpotential w i 0 0) (vector t x) (Pi.single 0 1) = 0 := by
    simp [g.superpotential_self]
  rw [h0, zero_add]
  exact Finset.sum_congr rfl fun α _ => fderiv_comp_vector_single (hd α.succ) α

/-- **The shell identity**: the difference of the surface charges on two spheres of the slice
`x⁰ = t` is the integral of the total `|g| (G^{i0} + t^{i0})` over the shell between them, when
the closed shell lies in `U`. -/
theorem surfaceCharge_sub_surfaceCharge {t R₁ R₂ : ℝ} (h0 : 0 ≤ R₁) (h12 : R₁ ≤ R₂)
    (hU : ∀ x : E3, R₁ ≤ ‖x‖ → ‖x‖ ≤ R₂ → vector t x ∈ U) (i : Fin 4) :
    g.surfaceCharge t R₂ i - g.surfaceCharge t R₁ i =
      ∫ x in Sphere.shell R₁ R₂, g.totalDensity (vector t x) i 0 := by
  have h := Sphere.flux_sub_flux (isOpen_slice U.isOpen t)
    (fun α => (g.contDiffOn_chargeField t i α).of_le (by simp)) h0 h12 hU
  unfold surfaceCharge
  rw [← sub_div, h, ← integral_div]
  refine setIntegral_congr_fun (Sphere.measurableSet_shell R₁ R₂) fun x hx => ?_
  rw [g.divergence_chargeField (hU x hx.1.le hx.2.le)]
  ring

/-- The shell identity with the Einstein equations `G^{ik} = κ T^{ik}`: the difference of the
charges is the integral of `|g| (κ T^{i0} + t^{i0})` over the shell. -/
theorem surfaceCharge_sub_surfaceCharge_eq {κ : ℝ}
    {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {t R₁ R₂ : ℝ} (h0 : 0 ≤ R₁)
    (h12 : R₁ ≤ R₂) (hU : ∀ x : E3, R₁ ≤ ‖x‖ → ‖x‖ ≤ R₂ → vector t x ∈ U) (i : Fin 4) :
    g.surfaceCharge t R₂ i - g.surfaceCharge t R₁ i =
      ∫ x in Sphere.shell R₁ R₂, densityOf g.coefficient (vector t x) ^ 2 *
        (κ * T (vector t x) i 0 + g.pseudotensor (vector t x) i 0) := by
  rw [g.surfaceCharge_sub_surfaceCharge h0 h12 hU]
  exact setIntegral_congr_fun (Sphere.measurableSet_shell R₁ R₂) fun x hx =>
    g.totalDensity_eq hT (hU x hx.1.le hx.2.le) i 0

/-- The charge on the sphere of radius `0` vanishes. -/
@[simp] theorem surfaceCharge_zero (t : ℝ) (i : Fin 4) : g.surfaceCharge t 0 i = 0 := by
  simp [surfaceCharge]

/-- Up to the origin, the shell `0 < ‖x‖ < R` is the ball. -/
theorem _root_.ProjectAinos.SmoothGeometry.Sphere.shell_zero_ae_eq (R : ℝ) :
    Sphere.shell 0 R =ᵐ[volume] ball (0 : E3) R := by
  have h : Sphere.shell 0 R = ball (0 : E3) R \ {0} := by
    ext x
    simp [Sphere.shell, and_comm]
  rw [h]
  exact sdiff_null_ae_eq_self (measure_singleton 0)

/-- **The surface charge is the integral of the total over the ball**, when the closed ball of the
slice lies in `U`. -/
theorem surfaceCharge_eq_integral_ball {t R : ℝ} (hR : 0 ≤ R)
    (hU : ∀ x : E3, ‖x‖ ≤ R → vector t x ∈ U) (i : Fin 4) :
    g.surfaceCharge t R i = ∫ x in ball (0 : E3) R, g.totalDensity (vector t x) i 0 := by
  have h := g.surfaceCharge_sub_surfaceCharge le_rfl hR (t := t) (fun x _ hx => hU x hx) i
  rw [surfaceCharge_zero, sub_zero] at h
  rw [h]
  exact setIntegral_congr_set (Sphere.shell_zero_ae_eq R)

/-- The map `(s, n) ↦ (s, R n)` into space-time is continuous. -/
theorem _root_.ProjectAinos.SmoothGeometry.Minkowski.continuous_vector_smul (R : ℝ) :
    Continuous fun p : ℝ × E3 => vector p.1 (R • p.2) :=
  Wave.timeSpaceEquiv.symm.continuous.comp (continuous_fst.prodMk (continuous_snd.const_smul R))

/-- The total flux through a sphere is continuous in the time. -/
theorem continuousAt_totalFlux {t R : ℝ} (hR : 0 < R)
    (hU : ∀ x : E3, ‖x‖ = R → vector t x ∈ U) (i : Fin 4) :
    ContinuousAt (fun s => g.totalFlux s R i) t := by
  have hcv := continuous_vector_smul R
  have hO : IsOpen {p : ℝ × E3 | vector p.1 (R • p.2) ∈ U} := U.isOpen.preimage hcv
  have hs₀ : ∀ n ∈ sphere (0 : E3) 1, (t, n) ∈ {p : ℝ × E3 | vector p.1 (R • p.2) ∈ U} :=
    fun n hn => hU _ (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, mem_sphere_zero_iff_norm.mp hn, mul_one])
  refine Sphere.continuousAt_integral_sphere
    (G := fun s n => R ^ 2 * ∑ α, g.totalDensity (vector s (R • n)) i α.succ * n α) hO hs₀ ?_
  exact continuousOn_const.mul (continuousOn_finsetSum _ fun α _ =>
    (((g.contDiffOn_totalDensity i α.succ).continuousOn.comp hcv.continuousOn
      fun p hp => hp)).mul (by fun_prop : Continuous fun p : ℝ × E3 => p.2 α).continuousOn)

/-- **The balance of the charge in a sphere**: `∂ₜ P^i(t, R) = −∮_{r = R} |g| (G^{iα} + t^{iα})
n_α dA`. The time derivative of `h^{i0α}` is `∂_β h^{iαβ} − 2|g|(G^{iα} + t^{iα})`, and the flux of
the divergence of the antisymmetric `h^{iαβ}` through the sphere vanishes. -/
theorem hasDerivAt_surfaceCharge_time {t R : ℝ} (hR : 0 < R)
    (hU : ∀ x : E3, ‖x‖ = R → vector t x ∈ U) (i : Fin 4) :
    HasDerivAt (fun s => g.surfaceCharge s R i) (-g.totalFlux t R i) t := by
  have hcv := continuous_vector_smul R
  have hO : IsOpen {p : ℝ × E3 | vector p.1 (R • p.2) ∈ U} := U.isOpen.preimage hcv
  have hmemR (n : E3) (hn : n ∈ sphere (0 : E3) 1) : ‖R • n‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, mem_sphere_zero_iff_norm.mp hn, mul_one]
  have hs₀ : ∀ n ∈ sphere (0 : E3) 1, (t, n) ∈ {p : ℝ × E3 | vector p.1 (R • p.2) ∈ U} :=
    fun n hn => hU _ (hmemR n hn)
  have hH (l k : Fin 4) : ContDiffOn ℝ ∞ (fun w => g.superpotential w i l k) U :=
    g.contDiffOn_superpotential i l k
  have hcoord (α : Fin 3) : Continuous fun p : ℝ × E3 => p.2 α := by fun_prop
  have hD := Sphere.hasDerivAt_integral_sphere
    (F := fun s n => R ^ 2 * ∑ α, g.superpotential (vector s (R • n)) i 0 α.succ * n α)
    (F' := fun s n => R ^ 2 * ∑ α, fderiv ℝ (fun w => g.superpotential w i 0 α.succ)
      (vector s (R • n)) (Pi.single 0 1) * n α) hO hs₀
    (continuousOn_const.mul (continuousOn_finsetSum _ fun α _ =>
      ((hH 0 α.succ).continuousOn.comp hcv.continuousOn fun p hp => hp).mul
        (hcoord α).continuousOn))
    (continuousOn_const.mul (continuousOn_finsetSum _ fun α _ =>
      ((((hH 0 α.succ).continuousOn_fderiv_of_isOpen U.isOpen (by simp)).comp hcv.continuousOn
        fun p hp => hp).clm_apply continuousOn_const).mul (hcoord α).continuousOn))
    (fun p hp => by
      refine (HasDerivAt.fun_sum fun α _ => ?_).const_mul (R ^ 2)
      have hd : DifferentiableAt ℝ (fun w => g.superpotential w i 0 α.succ)
          (vector p.1 (R • p.2)) :=
        ((hH 0 α.succ).contDiffAt (U.isOpen.mem_nhds hp)).differentiableAt (by simp)
      exact (hd.hasFDerivAt.comp_hasDerivAt p.1
        (hasDerivAt_vector_time p.1 (R • p.2))).mul_const _)
  have hfun : (fun s => g.surfaceCharge s R i) = fun s =>
      (∫ n : sphere (0 : E3) 1, R ^ 2 * ∑ α, g.superpotential (vector s (R • (n : E3))) i 0
        α.succ * (n : E3) α ∂Sphere.sphereMeasure) / 2 := rfl
  rw [hfun]
  convert hD.div_const 2 using 1
  -- the derivative
  set W : Set E3 := {y | vector t y ∈ U} with hW
  have hWo : IsOpen W := isOpen_slice U.isOpen t
  set A : Fin 3 → Fin 3 → E3 → ℝ := fun α β x => g.superpotential (vector t x) i α.succ β.succ
    with hA
  have hAc (α β : Fin 3) : ContDiffOn ℝ 1 (A α β) W :=
    ((hH α.succ β.succ).comp (contDiff_vector_space t).contDiffOn fun _ hy => hy).of_le
      (by simp)
  have hr : ∀ n ∈ sphere (0 : E3) 1, R • n ∈ W := fun n hn => hU _ (hmemR n hn)
  have hpt (n : sphere (0 : E3) 1) :
      R ^ 2 * ∑ α, fderiv ℝ (fun w => g.superpotential w i 0 α.succ)
        (vector t (R • (n : E3))) (Pi.single 0 1) * (n : E3) α =
      R ^ 2 * ∑ α, ∑ β, fderiv ℝ (A α β) (R • (n : E3)) (EuclideanSpace.single β 1) *
        (n : E3) α - 2 * (R ^ 2 * ∑ α, g.totalDensity (vector t (R • (n : E3))) i α.succ *
          (n : E3) α) := by
    have hz : vector t (R • (n : E3)) ∈ U := hr n n.2
    have hzn := U.isOpen.mem_nhds hz
    have hcomp (α : Fin 3) : fderiv ℝ (fun w => g.superpotential w i 0 α.succ)
        (vector t (R • (n : E3))) (Pi.single 0 1) =
        ∑ β, fderiv ℝ (A α β) (R • (n : E3)) (EuclideanSpace.single β 1) -
          2 * g.totalDensity (vector t (R • (n : E3))) i α.succ := by
      have hs := g.sum_fderiv_superpotential hz i α.succ
      rw [Fin.sum_univ_succ] at hs
      have hneg : (fun w => g.superpotential w i α.succ 0) =
          fun w => -g.superpotential w i 0 α.succ :=
        funext fun w => g.superpotential_antisymm w i α.succ 0
      rw [hneg, fderiv_fun_neg, neg_apply] at hs
      have hβ (β : Fin 3) : fderiv ℝ (A α β) (R • (n : E3)) (EuclideanSpace.single β 1) =
          fderiv ℝ (fun w => g.superpotential w i α.succ β.succ) (vector t (R • (n : E3)))
            (Pi.single β.succ 1) :=
        fderiv_comp_vector_single (((hH α.succ β.succ).contDiffAt hzn).differentiableAt
          (by simp)) β
      simp only [hβ]
      linarith
    simp only [hcomp, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_sub, Finset.mul_sum]
    ring_nf
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have hc1 : Continuous fun n : sphere (0 : E3) 1 => ∑ α, ∑ β,
      fderiv ℝ (A α β) (R • (n : E3)) (EuclideanSpace.single β 1) * (n : E3) α :=
    continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
      (Sphere.continuous_fderiv_sphere hWo (hAc α β) hr continuous_const).mul (by fun_prop)
  have hc2 : Continuous fun n : sphere (0 : E3) 1 => R ^ 2 * ∑ α,
      g.totalDensity (vector t (R • (n : E3))) i α.succ * (n : E3) α :=
    continuous_const.mul (continuous_finsetSum _ fun α _ =>
      (Sphere.continuous_comp_smul_sphere (G := fun y => g.totalDensity (vector t y) i α.succ)
        ((g.contDiffOn_totalDensity i α.succ).continuousOn.comp
          (contDiff_vector_space t (n := 0)).continuous.continuousOn fun _ hy => hy) hr).mul
        (by fun_prop))
  rw [integral_sub ((Sphere.integrable_of_continuous hc1).const_mul _)
    ((Sphere.integrable_of_continuous hc2).const_mul _), integral_const_mul, integral_const_mul,
    Sphere.integral_divergence_antisymm hWo hAc
      (fun x _ α β => g.superpotential_antisymm (vector t x) i α.succ β.succ) hR.ne' hr]
  simp only [totalFlux, Sphere.flux, totalFluxField]
  ring

/-- **The charge in a sphere changes by the flux through it**: `P^i(t₂, R) − P^i(t₁, R) =
−∫_{t₁}^{t₂} ∮_{r = R} |g| (G^{iα} + t^{iα}) n_α dA dt`. -/
theorem surfaceCharge_sub_surfaceCharge_time {t₁ t₂ R : ℝ} (ht : t₁ ≤ t₂) (hR : 0 < R)
    (hU : ∀ t ∈ Icc t₁ t₂, ∀ x : E3, ‖x‖ = R → vector t x ∈ U) (i : Fin 4) :
    g.surfaceCharge t₂ R i - g.surfaceCharge t₁ R i =
      -∫ t in t₁..t₂, g.totalFlux t R i := by
  rw [← intervalIntegral.integral_neg]
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => g.surfaceCharge s R i)
    (f' := fun t => -g.totalFlux t R i) (fun t ht' => ?_) ?_).symm
  · rw [uIcc_of_le ht] at ht'
    exact g.hasDerivAt_surfaceCharge_time hR (hU t ht') i
  · refine ContinuousOn.intervalIntegrable fun t ht' => ?_
    rw [uIcc_of_le ht] at ht'
    exact (g.continuousAt_totalFlux hR (hU t ht') i).neg.continuousWithinAt

end CoordinateMetric

/-! ### A bound for the braces of (96.9) -/

/-- A sum of `n` terms bounded by `c` is bounded by `n c`. -/
theorem abs_sum_fin_le {n : ℕ} {f : Fin n → ℝ} {c : ℝ} (h : ∀ a, |f a| ≤ c) :
    |∑ a, f a| ≤ n * c := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun a _ => h a).trans ?_)
  simp

/-- A product of bounded factors is bounded by the product of the bounds. -/
theorem abs_mul_le_mul_of_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- **The braces of (96.9) are quadratic in the Christoffel symbols**: if the entries of `G` are
at most `K` and those of `Γ` at most `B`, the braces are at most `18 n⁴ K² B²`. -/
theorem abs_pseudoBraces_le {n : ℕ} {G : Fin n → Fin n → ℝ} {Γ : Fin n → Fin n → Fin n → ℝ}
    {K B : ℝ} (hG : ∀ a b, |G a b| ≤ K) (hΓ : ∀ a b c, |Γ a b c| ≤ B) (i k : Fin n) :
    |pseudoBraces G Γ i k| ≤ 18 * n ^ 4 * K ^ 2 * B ^ 2 := by
  have hGG (a b c e : Fin n) : |G a b * G c e| ≤ K ^ 2 := by
    rw [sq]; exact abs_mul_le_mul_of_le (hG a b) (hG c e)
  have hΓΓ (a b c e p q : Fin n) : |Γ a b c * Γ e p q| ≤ B ^ 2 := by
    rw [sq]; exact abs_mul_le_mul_of_le (hΓ a b c) (hΓ e p q)
  have h3 {x y z : ℝ} (hx : |x| ≤ B ^ 2) (hy : |y| ≤ B ^ 2) (hz : |z| ≤ B ^ 2) :
      |2 * x - y - z| ≤ 4 * B ^ 2 := by
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    obtain ⟨hz1, hz2⟩ := abs_le.mp hz
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h4 {x y z w : ℝ} (hx : |x| ≤ B ^ 2) (hy : |y| ≤ B ^ 2) (hz : |z| ≤ B ^ 2)
      (hw : |w| ≤ B ^ 2) : |x + y - z - w| ≤ 4 * B ^ 2 := by
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    obtain ⟨hz1, hz2⟩ := abs_le.mp hz
    obtain ⟨hw1, hw2⟩ := abs_le.mp hw
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h2 {x y : ℝ} (hx : |x| ≤ K ^ 2) (hy : |y| ≤ K ^ 2) : |x - y| ≤ 2 * K ^ 2 := by
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h2' {x y : ℝ} (hx : |x| ≤ B ^ 2) (hy : |y| ≤ B ^ 2) : |x - y| ≤ 2 * B ^ 2 := by
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have t1 : |∑ l, ∑ m, (∑ a, ∑ b, (2 * Γ a l m * Γ b a b - Γ a l b * Γ b m a -
      Γ a l a * Γ b m b)) * (G i l * G k m - G i k * G l m)| ≤
        n * (n * ((n * (n * (4 * B ^ 2))) * (2 * K ^ 2))) :=
    abs_sum_fin_le fun l => abs_sum_fin_le fun m => abs_mul_le_mul_of_le
      (abs_sum_fin_le fun a => abs_sum_fin_le fun b => by
        rw [mul_assoc]; exact h3 (hΓΓ _ _ _ _ _ _) (hΓΓ _ _ _ _ _ _) (hΓΓ _ _ _ _ _ _))
      (h2 (hGG _ _ _ _) (hGG _ _ _ _))
  have t2 (p q : Fin n) : |∑ l, ∑ m, ∑ a, G p l * G m a * ∑ b, (Γ q l b * Γ b m a +
      Γ q m a * Γ b l b - Γ q a b * Γ b l m - Γ q l m * Γ b a b)| ≤
        n * (n * (n * (K ^ 2 * (n * (4 * B ^ 2))))) :=
    abs_sum_fin_le fun l => abs_sum_fin_le fun m => abs_sum_fin_le fun a =>
      abs_mul_le_mul_of_le (hGG _ _ _ _) (abs_sum_fin_le fun b =>
        h4 (hΓΓ _ _ _ _ _ _) (hΓΓ _ _ _ _ _ _) (hΓΓ _ _ _ _ _ _) (hΓΓ _ _ _ _ _ _))
  have t4 : |∑ l, ∑ m, ∑ a, ∑ b, G l m * G a b * (Γ i a l * Γ k b m - Γ i l m * Γ k a b)| ≤
      n * (n * (n * (n * (K ^ 2 * (2 * B ^ 2))))) :=
    abs_sum_fin_le fun l => abs_sum_fin_le fun m => abs_sum_fin_le fun a =>
      abs_sum_fin_le fun b => abs_mul_le_mul_of_le (hGG _ _ _ _)
        (h2' (hΓΓ _ _ _ _ _ _) (hΓΓ _ _ _ _ _ _))
  unfold pseudoBraces
  calc _ ≤ _ := abs_add_three _ _ _ |>.trans (by gcongr) |> fun h => (abs_add_le _ _).trans
          (add_le_add h le_rfl)
    _ ≤ n * (n * ((n * (n * (4 * B ^ 2))) * (2 * K ^ 2))) +
        n * (n * (n * (K ^ 2 * (n * (4 * B ^ 2))))) +
        n * (n * (n * (K ^ 2 * (n * (4 * B ^ 2))))) +
        n * (n * (n * (n * (K ^ 2 * (2 * B ^ 2))))) :=
      add_le_add (add_le_add (add_le_add t1 (t2 i k)) (t2 k i)) t4
    _ = 18 * n ^ 4 * K ^ 2 * B ^ 2 := by ring
