/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.NewtonianAccelerationBounds
public import ProjectAinos.GeneralRelativity.NewtonianExamples
public import ProjectAinos.Mechanics.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.LinearCombination

/-! # The motion of a test body in the second approximation

Landau–Lifshitz, §106, for a test body in a prescribed post-Newtonian metric (decision 15 on
#135), in the physical coordinates `(t, x)` and the signature `(−, +, +, +)` of
`NewtonianMetricFamily`, with `ε = c⁻²` (`epsilon`).

A post-Newtonian family (`PostNewtonianMetricFamily U`) is a Newtonian family whose corrections
have the form
`g_tt = −c² − 2Φ − 2(Φ² + ψ)/c² + A_c/c⁴`, `g_ti = B_i/c² + B'_{c,i}/c⁴`,
`g_ij = (1 − 2Φ/c²) δ_ij + H_{c,ij}/c⁴`:
the normalization `g₀₀ = 1 + 2φ/c² + 2(φ² + ψ)/c⁴`, `g_αβ = −(1 − 2φ/c²) δ_αβ` of §106 with
`x⁰ = ct` and the signature reversed, so that `Φ = φ` and `B_i = −c³ g₀ᵢ`. The potentials `Φ`,
`ψ`, `B` may depend on time but not on `c`; one constant `K` bounds them and the remainders
`A_c`, `B'_c`, `H_c` through two derivatives for `c ≥ 1`.

* `coefficient_acceleration`: for every Newtonian family, the coordinate-time geodesic equation
  with the index lowered, `Σ_m g_{lm} a^m = w₀ (g u)_l − Σ_{ij} Γ_{l,ij} u^i u^j`, `u = (1, v)`,
  `w₀ = Γ⁰_{ij} u^i u^j`. With it the comparison needs no second-order expansion of the inverse
  metric.
* `postNewtonianCorrection`, `postNewtonianAcceleration`: the acceleration of the second
  approximation, `a_PN = −∇Φ + a₁/c²` with
  `a₁ = −v²∇Φ − 4Φ∇Φ − ∇ψ + 3 ∂_tΦ v + 4 (v·∇Φ) v + ∇(B·v) − ∂_t B − (v·∇)B`.
* `acceleration_sub_eq`: **the exact comparison**, `a − a_PN = −X/c⁴` for the coordinate-time
  geodesic acceleration `a` of the family, with an explicit remainder `X`
  (`accelerationRemainder`).
* `acceleration_error`: **the uniform estimate**, `‖a − a_PN‖ ≤ C/c⁴` on the whole domain for
  `‖v‖ ≤ V` and `c ≥ 24K + 2`. `native_acceleration_error` states it for the acceleration of the
  Levi-Civita connection of the native metric, and `geodesic_acceleration_error` for affine
  geodesics reparametrized by the physical time.
* `lagrangian`: the test-body Lagrangian of §106,
  `L = −mc² + mv²/2 − mΦ + (m/c²)(v⁴/8 − (3/2)Φv² − Φ²/2 − ψ + B·v)`, the expansion of
  `−mc √(−g(u, u))` to order `c⁻²`. `eulerLagrange_lagrangian`: its Euler–Lagrange residual
  (`Mechanics.eulerLagrange`) along a `C²` path is `m (F − ṗ)`, with the force `F`
  (`lagrangianForce`) and the rate `ṗ` of the momentum (`momentumRate`).
* `eulerLagrange_acceleration_error`: a path satisfying the Euler–Lagrange equations has the
  acceleration `a_PN` up to `C/c⁴`; `eulerLagrange_sub_acceleration`: it is within `C/c⁴` of the
  geodesic acceleration at the same position and velocity.
* Instances: `Example.family`, with polynomial potentials and nonzero remainders on the ball
  `‖q‖ < 2`; `exists_eulerLagrange_rest`, a path at rest that satisfies the Euler–Lagrange
  equations at a given time.

Not stated: the Einstein–Infeld–Hoffmann Lagrangian (106.17) of `N` bodies, and the field
equations of the potentials (the Einstein residual of the ansatz). That the EIH dynamics
approximate solutions of the Einstein equations is out of reach: point masses have no
distributional Einstein equations and their self-fields diverge, and for extended bodies the
expansion needs the well-posedness of the Einstein–Euler system, which neither the library nor
Mathlib has.
-/

@[expose] public section
noncomputable section

open ContinuousLinearMap Set TopologicalSpace Metric Filter
open scoped ContDiff Topology Matrix Manifold

namespace ProjectAinos.GeneralRelativity.PostNewtonian

open NewtonianMetricFamily

local notation "E" => NewtonianCoordinates
local notation "S" => NewtonianSpace

/-- The post-Newtonian scaling class: a Newtonian metric family whose corrections are
`g_tt = −c² − 2Φ − 2(Φ² + ψ)/c² + A_c/c⁴`, `g_ti = B_i/c² + B'_{c,i}/c⁴` and
`g_ij = (1 − 2Φ/c²) δ_ij + H_{c,ij}/c⁴`. The potentials `Φ`, `ψ` and `B` do not depend on `c`;
the remainders `A_c`, `B'_c` and `H_c` may, and one constant bounds them through two derivatives
for `c ≥ 1`. -/
structure PostNewtonianMetricFamily (U : Opens NewtonianCoordinates) extends
    NewtonianMetricFamily U where
  /-- The second scalar potential `ψ` of `g_tt`. -/
  scalarPotential : NewtonianCoordinates → ℝ
  /-- The vector potential `B` of `g_ti`. -/
  vectorPotential : NewtonianCoordinates → NewtonianSpace
  /-- The remainder `A_c` of `g_tt` at order `c⁻⁴`. -/
  timeRemainder : ℝ → NewtonianCoordinates → ℝ
  /-- The remainder `B'_c` of `g_ti` at order `c⁻⁴`. -/
  mixedRemainder : ℝ → NewtonianCoordinates → NewtonianSpace
  /-- The remainder `H_c` of `g_ij` at order `c⁻⁴`. -/
  spatialRemainder : ℝ → NewtonianCoordinates → NewtonianSpatialMatrix
  time_eq : ∀ c q, timeCorrection c q =
    -2 * (potential q ^ 2 + scalarPotential q) + epsilon c * timeRemainder c q
  mixed_eq : ∀ c q i, mixedCorrection c q i =
    vectorPotential q i + epsilon c * mixedRemainder c q i
  spatial_eq : ∀ c q i j, spatialCorrection c q i j =
    -2 * potential q * (if i = j then 1 else 0) + epsilon c * spatialRemainder c q i j
  scalar_smooth : ContDiffOn ℝ ∞ scalarPotential U
  vector_smooth : ContDiffOn ℝ ∞ vectorPotential U
  timeRemainder_smooth : ∀ c > 0, ContDiffOn ℝ ∞ (timeRemainder c) U
  mixedRemainder_smooth : ∀ c > 0, ContDiffOn ℝ ∞ (mixedRemainder c) U
  spatialRemainder_smooth : ∀ c > 0, ContDiffOn ℝ ∞ (spatialRemainder c) U
  scalar_bound : CoordinateC2Bound U bound scalarPotential
  vector_bound : CoordinateC2Bound U bound vectorPotential
  timeRemainder_bound : ∀ c ≥ 1, CoordinateC2Bound U bound (timeRemainder c)
  mixedRemainder_bound : ∀ c ≥ 1, CoordinateC2Bound U bound (mixedRemainder c)
  spatialRemainder_bound : ∀ c ≥ 1, CoordinateC2Bound U bound (spatialRemainder c)

/-- A sum `f + a g` with `|a| ≤ 1` of functions with C² bounds `K` and `L` has the bound
`K + L`. -/
theorem coordinateC2Bound_add_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {K L a : ℝ} {f g : E → F} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hbf : CoordinateC2Bound U K f) (hbg : CoordinateC2Bound U L g) (ha : |a| ≤ 1) :
    CoordinateC2Bound U (K + L) (fun q => f q + a • g q) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hD : fderiv ℝ (fun q => f q + a • g q) = fun q => fderiv ℝ f q + a • fderiv ℝ g q := by
    funext q
    have hs : DifferentiableAt ℝ (fun y => a • g y) q := (hg1 q).const_smul a
    rw [fderiv_fun_add (hf1 q) hs, fderiv_fun_const_smul (hg1 q)]
  have hD2 : fderiv ℝ (fderiv ℝ (fun q => f q + a • g q)) =
      fun q => fderiv ℝ (fderiv ℝ f) q + a • fderiv ℝ (fderiv ℝ g) q := by
    rw [hD]
    funext q
    have hs : DifferentiableAt ℝ (fun y => a • fderiv ℝ g y) q := (hdg q).const_smul a
    rw [fderiv_fun_add (hdf q) hs, fderiv_fun_const_smul (hdg q)]
  have hn : ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] (x y : G), ‖x‖ ≤ K →
      ‖y‖ ≤ L → ‖x + a • y‖ ≤ K + L := by
    intro G _ _ x y hx hy
    refine (norm_add_le _ _).trans (add_le_add hx ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hy
  refine ⟨fun q hq => hn F _ _ (hbf.value q hq) (hbg.value q hq), fun q hq => ?_,
    fun q hq => ?_⟩
  · rw [hD]
    exact hn (E →L[ℝ] F) _ _ (hbf.first q hq) (hbg.first q hq)
  · rw [hD2]
    exact hn (E →L[ℝ] E →L[ℝ] F) _ _ (hbf.second q hq) (hbg.second q hq)

/-! ### An instance with polynomial potentials -/

namespace Example

/-- `Φ = t x¹`. -/
def potential (q : E) : ℝ := q 0 * q 1
/-- `ψ = (x²)²`. -/
def scalarPotential (q : E) : ℝ := q 2 ^ 2
/-- `B_i = t xⁱ`. -/
def vectorPotential (q : E) : S := fun i => q 0 * q i.succ
/-- `A = t²`. -/
def timeRemainder (q : E) : ℝ := q 0 ^ 2
/-- `B'_i = xⁱ`. -/
def mixedRemainder (q : E) : S := fun i => q i.succ
/-- `H_ij = t δ_ij`. -/
def spatialRemainder (q : E) : NewtonianSpatialMatrix := fun i j => if i = j then q 0 else 0
/-- The `c⁻²` part `−2(Φ² + ψ)` of `g_tt`. -/
def timeLeading (q : E) : ℝ := -2 * (potential q ^ 2 + scalarPotential q)
/-- The `c⁻²` part `−2Φ δ_ij` of `g_ij`. -/
def spatialLeading (q : E) : NewtonianSpatialMatrix := fun i j =>
  -2 * potential q * (if i = j then 1 else 0)

private theorem contDiff_matrix {g : E → NewtonianSpatialMatrix}
    (hg : ∀ i j, ContDiff ℝ ∞ (fun q => g q i j)) : ContDiff ℝ ∞ g :=
  contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => hg i j

private theorem contDiff_potential : ContDiff ℝ ∞ potential := by unfold potential; fun_prop
private theorem contDiff_scalarPotential : ContDiff ℝ ∞ scalarPotential := by
  unfold scalarPotential; fun_prop
private theorem contDiff_vectorPotential : ContDiff ℝ ∞ vectorPotential := by
  unfold vectorPotential; fun_prop
private theorem contDiff_timeRemainder : ContDiff ℝ ∞ timeRemainder := by
  unfold timeRemainder; fun_prop
private theorem contDiff_mixedRemainder : ContDiff ℝ ∞ mixedRemainder := by
  unfold mixedRemainder; fun_prop
private theorem contDiff_spatialRemainder : ContDiff ℝ ∞ spatialRemainder := by
  refine contDiff_matrix fun i j => ?_
  by_cases hij : i = j <;> simp only [spatialRemainder, hij, ite_true, ite_false] <;> fun_prop
private theorem contDiff_timeLeading : ContDiff ℝ ∞ timeLeading := by
  unfold timeLeading potential scalarPotential; fun_prop
private theorem contDiff_spatialLeading : ContDiff ℝ ∞ spatialLeading := by
  refine contDiff_matrix fun i j => ?_
  by_cases hij : i = j <;> simp only [spatialLeading, potential, hij, ite_true, ite_false] <;>
    fun_prop

theorem exists_family : ∃ f : PostNewtonianMetricFamily NewtonianExamples.domain,
    f.potential = potential ∧ f.scalarPotential = scalarPotential ∧
      f.vectorPotential = vectorPotential ∧
      f.timeRemainder = (fun _ => timeRemainder) ∧
      f.mixedRemainder = (fun _ => mixedRemainder) ∧
      f.spatialRemainder = (fun _ => spatialRemainder) := by
  have hdom : (NewtonianExamples.domain : Set E) ⊆ closedBall 0 2 := ball_subset_closedBall
  have hK := isCompact_closedBall (0 : E) 2
  have h2 {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
      (hg : ContDiff ℝ ∞ g) : ContDiff ℝ 2 g := hg.of_le (by simp)
  obtain ⟨Kp, hKp, hbp⟩ := exists_coordinateC2Bound (h2 contDiff_potential) hK hdom
  obtain ⟨Ks, hKs, hbs⟩ := exists_coordinateC2Bound (h2 contDiff_scalarPotential) hK hdom
  obtain ⟨Kv, hKv, hbv⟩ := exists_coordinateC2Bound (h2 contDiff_vectorPotential) hK hdom
  obtain ⟨Ka, hKa, hba⟩ := exists_coordinateC2Bound (h2 contDiff_timeRemainder) hK hdom
  obtain ⟨Km, hKm, hbm⟩ := exists_coordinateC2Bound (h2 contDiff_mixedRemainder) hK hdom
  obtain ⟨Kh, hKh, hbh⟩ := exists_coordinateC2Bound (h2 contDiff_spatialRemainder) hK hdom
  obtain ⟨Kt, hKt, hbt⟩ := exists_coordinateC2Bound (h2 contDiff_timeLeading) hK hdom
  obtain ⟨Kl, hKl, hbl⟩ := exists_coordinateC2Bound (h2 contDiff_spatialLeading) hK hdom
  have he (c : ℝ) (hc : 1 ≤ c) : |epsilon c| ≤ 1 := by
    rw [abs_of_nonneg (epsilon_nonneg c)]
    exact epsilon_le_one hc
  let K := Kp + Ks + Kv + Ka + Km + Kh + Kt + Kl
  have hmono {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {L : ℝ}
      (hg : CoordinateC2Bound NewtonianExamples.domain L g) (hL : L ≤ K) :
      CoordinateC2Bound NewtonianExamples.domain K g := hg.mono (Subset.refl _) hL
  refine ⟨{
    potential := potential
    timeCorrection := fun c q => timeLeading q + epsilon c • timeRemainder q
    mixedCorrection := fun c q => vectorPotential q + epsilon c • mixedRemainder q
    spatialCorrection := fun c q => spatialLeading q + epsilon c • spatialRemainder q
    potential_smooth := contDiff_potential.contDiffOn
    time_smooth := fun c _ =>
      (contDiff_timeLeading.add (contDiff_timeRemainder.const_smul (epsilon c))).contDiffOn
    mixed_smooth := fun c _ =>
      (contDiff_vectorPotential.add (contDiff_mixedRemainder.const_smul (epsilon c))).contDiffOn
    spatial_smooth := fun c _ =>
      (contDiff_spatialLeading.add
        (contDiff_spatialRemainder.const_smul (epsilon c))).contDiffOn
    spatial_symmetric := fun _ _ _ _ i j => by
      simp [spatialLeading, spatialRemainder, eq_comm]
    bound := K
    bound_nonneg := by positivity
    potential_bound := hmono hbp (by dsimp [K]; linarith)
    time_bound := fun c hc => hmono (coordinateC2Bound_add_smul (h2 contDiff_timeLeading)
      (h2 contDiff_timeRemainder) hbt hba (he c hc)) (by dsimp [K]; linarith)
    mixed_bound := fun c hc => hmono (coordinateC2Bound_add_smul (h2 contDiff_vectorPotential)
      (h2 contDiff_mixedRemainder) hbv hbm (he c hc)) (by dsimp [K]; linarith)
    spatial_bound := fun c hc => hmono (coordinateC2Bound_add_smul
      (h2 contDiff_spatialLeading) (h2 contDiff_spatialRemainder) hbl hbh (he c hc))
      (by dsimp [K]; linarith)
    scalarPotential := scalarPotential
    vectorPotential := vectorPotential
    timeRemainder := fun _ => timeRemainder
    mixedRemainder := fun _ => mixedRemainder
    spatialRemainder := fun _ => spatialRemainder
    time_eq := fun c q => by simp [timeLeading]
    mixed_eq := fun c q i => by simp
    spatial_eq := fun c q i j => by simp [spatialLeading]
    scalar_smooth := contDiff_scalarPotential.contDiffOn
    vector_smooth := contDiff_vectorPotential.contDiffOn
    timeRemainder_smooth := fun _ _ => contDiff_timeRemainder.contDiffOn
    mixedRemainder_smooth := fun _ _ => contDiff_mixedRemainder.contDiffOn
    spatialRemainder_smooth := fun _ _ => contDiff_spatialRemainder.contDiffOn
    scalar_bound := hmono hbs (by dsimp [K]; linarith)
    vector_bound := hmono hbv (by dsimp [K]; linarith)
    timeRemainder_bound := fun _ _ => hmono hba (by dsimp [K]; linarith)
    mixedRemainder_bound := fun _ _ => hmono hbm (by dsimp [K]; linarith)
    spatialRemainder_bound := fun _ _ => hmono hbh (by dsimp [K]; linarith)
  }, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The post-Newtonian family with the polynomial potentials above on the ball `‖q‖ < 2`. -/
def family : PostNewtonianMetricFamily NewtonianExamples.domain := Classical.choose exists_family

@[simp] theorem family_potential : family.potential = potential :=
  (Classical.choose_spec exists_family).1
@[simp] theorem family_scalarPotential : family.scalarPotential = scalarPotential :=
  (Classical.choose_spec exists_family).2.1
@[simp] theorem family_vectorPotential : family.vectorPotential = vectorPotential :=
  (Classical.choose_spec exists_family).2.2.1
@[simp] theorem family_timeRemainder : family.timeRemainder = (fun _ => timeRemainder) :=
  (Classical.choose_spec exists_family).2.2.2.1
@[simp] theorem family_mixedRemainder : family.mixedRemainder = (fun _ => mixedRemainder) :=
  (Classical.choose_spec exists_family).2.2.2.2.1
@[simp] theorem family_spatialRemainder :
    family.spatialRemainder = (fun _ => spatialRemainder) :=
  (Classical.choose_spec exists_family).2.2.2.2.2

end Example

/-! ### The lowered geodesic equation in coordinate time -/

/-- The contraction `Σ_{ij} Γ_{l,ij} u^i u^j` of the Christoffel symbols of the first kind built
from an array `D m a b = ∂_m g_{ab}` of metric derivatives. -/
def lowerContraction (D : Fin 4 → Fin 4 → Fin 4 → ℝ) (u : E) (l : Fin 4) : ℝ :=
  ∑ i, ∑ j, (D i j l + D j l i - D l i j) / 2 * u i * u j

/-- The array `∂_m g_{ab}` of first coordinate derivatives of a Newtonian family. -/
def metricDerivative {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ) (q : E) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun m a b => coordinatePartial (fun x => f.coefficient c x a b) q m

theorem sum_lowerChristoffel {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ) (q u : E)
    (l : Fin 4) :
    ∑ i, ∑ j, f.lowerChristoffel c q l i j * u i * u j =
      lowerContraction (metricDerivative f c q) u l := rfl

/-- The coordinate-time contraction `w₀ = Σ_{ij} Γ⁰_{ij} u^i u^j` for `u = (1, v)`. -/
def timeContraction {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ) (q : E) (v : S) : ℝ :=
  ∑ i, ∑ j, f.christoffel c q 0 i j * timeVelocity v i * timeVelocity v j

/-- The coordinate-time geodesic equation with the index lowered by the metric: for
`u = (1, v)` and the coordinate-time acceleration `a`,
`Σ_m g_{l,m} a^m = w₀ (g u)_l − Σ_{ij} Γ_{l,ij} u^i u^j` with `w₀ = Γ⁰_{ij} u^i u^j`. -/
theorem coefficient_acceleration {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c ^ 2) (q : U) (v : S) (l : Fin 4) :
    ∑ m : Fin 3, f.coefficient c q l m.succ * f.acceleration c q v m =
      timeContraction f c q v * (∑ n, f.coefficient c q l n * timeVelocity v n) -
        lowerContraction (metricDerivative f c q) (timeVelocity v) l := by
  set G := f.coefficient c q
  set u := timeVelocity v
  set F : E := fun l => lowerContraction (metricDerivative f c q) u l
  set W := G⁻¹ *ᵥ F
  have hΓ (k : Fin 4) : ∑ i, ∑ j, f.christoffel c q k i j * u i * u j = W k := by
    have h (i j : Fin 4) :
        f.christoffel c q k i j = ∑ n, G⁻¹ k n * f.lowerChristoffel c q n i j := by
      unfold christoffel lowerChristoffel coordinatePartial
      exact Finset.sum_congr rfl fun n _ => mul_div_assoc _ _ _
    simp only [h, W, Matrix.mulVec, dotProduct, F, ← sum_lowerChristoffel, Finset.sum_mul,
      Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  have ha (k : Fin 3) : f.acceleration c q v k = -W k.succ + v k * W 0 := by
    simp only [acceleration]
    rw [hΓ, hΓ]
  have hα : (Fin.cons 0 (f.acceleration c q v) : E) = -W + W 0 • u := by
    funext n
    refine Fin.cases ?_ (fun k => ?_) n
    · simp [u, timeVelocity]
    · simp [ha, u, timeVelocity]
      ring
  have hGW : G *ᵥ W = F := by
    simp only [W, Matrix.mulVec_mulVec, G, f.coefficient_mul_inverse hc hlarge q,
      Matrix.one_mulVec]
  have hsum : ∑ m : Fin 3, G l m.succ * f.acceleration c q v m =
      (G *ᵥ (Fin.cons 0 (f.acceleration c q v) : E)) l := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hw : timeContraction f c q v = W 0 := hΓ 0
  rw [hsum, hα, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, hGW, hw]
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, F]
  ring

/-! ### Coordinate derivatives -/

section Partial

variable {g h : E → ℝ} {q : E}

private theorem partial_add (hg : DifferentiableAt ℝ g q) (hh : DifferentiableAt ℝ h q)
    (m : Fin 4) :
    coordinatePartial (fun x => g x + h x) q m =
      coordinatePartial g q m + coordinatePartial h q m := by
  simp [coordinatePartial, fderiv_fun_add hg hh]

private theorem partial_sub (hg : DifferentiableAt ℝ g q) (hh : DifferentiableAt ℝ h q)
    (m : Fin 4) :
    coordinatePartial (fun x => g x - h x) q m =
      coordinatePartial g q m - coordinatePartial h q m := by
  simp [coordinatePartial, fderiv_fun_sub hg hh]

private theorem partial_mul (hg : DifferentiableAt ℝ g q) (hh : DifferentiableAt ℝ h q)
    (m : Fin 4) :
    coordinatePartial (fun x => g x * h x) q m =
      g q * coordinatePartial h q m + h q * coordinatePartial g q m := by
  simp [coordinatePartial, fderiv_fun_mul hg hh]

private theorem partial_const_mul (a : ℝ) (hg : DifferentiableAt ℝ g q) (m : Fin 4) :
    coordinatePartial (fun x => a * g x) q m = a * coordinatePartial g q m := by
  simp [coordinatePartial, fderiv_const_mul hg]

private theorem partial_pow_two (hg : DifferentiableAt ℝ g q) (m : Fin 4) :
    coordinatePartial (fun x => g x ^ 2) q m = 2 * g q * coordinatePartial g q m := by
  simp only [pow_two]
  rw [partial_mul hg hg]
  ring

private theorem partial_const (a : ℝ) (m : Fin 4) : coordinatePartial (fun _ => a) q m = 0 := by
  simp [coordinatePartial]

end Partial

/-! ### Block arrays -/

/-- The array whose `m`-th matrix has time-time entry `p m`, mixed entries `b m` and spatial
block `h m`. -/
def blockArray (p : Fin 4 → ℝ) (b : Fin 4 → S) (h : Fin 4 → NewtonianSpatialMatrix) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun m => Fin.cons (Fin.cons (p m) (b m) : Fin 4 → ℝ)
    (fun i => (Fin.cons (b m i) (h m i) : Fin 4 → ℝ))

theorem lowerContraction_add_mul (D D' : Fin 4 → Fin 4 → Fin 4 → ℝ) (r : ℝ) (u : E)
    (l : Fin 4) :
    lowerContraction (fun m a b => D m a b + r * D' m a b) u l =
      lowerContraction D u l + r * lowerContraction D' u l := by
  simp only [lowerContraction, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem lowerContraction_block_zero (p : Fin 4 → ℝ) (b : Fin 4 → S)
    (h : Fin 4 → NewtonianSpatialMatrix) (v : S) :
    lowerContraction (blockArray p b h) (timeVelocity v) 0 =
      p 0 / 2 + ∑ j, v j * p j.succ + ∑ i, ∑ j, v i * b i.succ j * v j -
        (∑ i, ∑ j, h 0 i j * v i * v j) / 2 := by
  simp only [lowerContraction, blockArray, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    timeVelocity, Fin.sum_univ_zero]
  ring

theorem lowerContraction_block_succ (p : Fin 4 → ℝ) (b : Fin 4 → S)
    (h : Fin 4 → NewtonianSpatialMatrix) (v : S) (k : Fin 3) :
    lowerContraction (blockArray p b h) (timeVelocity v) k.succ =
      b 0 k + ∑ i, v i * b i.succ k +
        ((∑ j, (h 0 j k + h 0 k j) * v j) +
          ∑ i, v i * ∑ j, (h i.succ j k + h i.succ k j) * v j) / 2 -
        p k.succ / 2 - ∑ j, b k.succ j * v j - (∑ i, ∑ j, h k.succ i j * v i * v j) / 2 := by
  simp only [lowerContraction, blockArray, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    timeVelocity, Fin.sum_univ_zero]
  ring

/-! ### The coefficients of a post-Newtonian family and their derivatives -/

namespace PostNewtonianMetricFamily

variable {U : Opens E} (f : PostNewtonianMetricFamily U)

theorem coefficient_zero_zero (c : ℝ) (q : E) :
    f.coefficient c q 0 0 = -c ^ 2 - 2 * f.potential q + epsilon c *
      (-2 * (f.potential q ^ 2 + f.scalarPotential q) + epsilon c * f.timeRemainder c q) := by
  rw [coefficient_time, f.time_eq]

theorem coefficient_zero_succ (c : ℝ) (q : E) (j : Fin 3) :
    f.coefficient c q 0 j.succ =
      epsilon c * (f.vectorPotential q j + epsilon c * f.mixedRemainder c q j) := by
  rw [coefficient_mixed, f.mixed_eq]

theorem coefficient_succ_zero (c : ℝ) (q : E) (i : Fin 3) :
    f.coefficient c q i.succ 0 =
      epsilon c * (f.vectorPotential q i + epsilon c * f.mixedRemainder c q i) := by
  change epsilon c * f.mixedCorrection c q i = _
  rw [f.mixed_eq]

theorem coefficient_succ_succ (c : ℝ) (q : E) (i j : Fin 3) :
    f.coefficient c q i.succ j.succ = (if i = j then 1 else 0) + epsilon c *
      (-2 * f.potential q * (if i = j then 1 else 0) + epsilon c * f.spatialRemainder c q i j) := by
  rw [coefficient_spatial, f.spatial_eq]

/-- The leading derivative array: only `∂_m g_tt = −2 ∂_m Φ` survives. -/
def leadingArray (q : E) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  blockArray (fun m => -2 * coordinatePartial f.potential q m) 0 0

/-- The derivative array at order `c⁻²`. -/
def firstArray (q : E) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  blockArray (fun m => -2 * (2 * f.potential q * coordinatePartial f.potential q m +
      coordinatePartial f.scalarPotential q m))
    (fun m j => coordinatePartial (fun x => f.vectorPotential x j) q m)
    (fun m i j => -2 * coordinatePartial f.potential q m * (if i = j then 1 else 0))

/-- The derivative array of the remainders, at order `c⁻⁴`. -/
def secondArray (c : ℝ) (q : E) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  blockArray (fun m => coordinatePartial (f.timeRemainder c) q m)
    (fun m j => coordinatePartial (fun x => f.mixedRemainder c x j) q m)
    (fun m i j => coordinatePartial (fun x => f.spatialRemainder c x i j) q m)

theorem metricDerivative_eq {c : ℝ} (hc : 0 < c) {q : E} (hq : q ∈ U) (m a b : Fin 4) :
    metricDerivative f.toNewtonianMetricFamily c q m a b =
      f.leadingArray q m a b + epsilon c * f.firstArray q m a b +
        epsilon c ^ 2 * f.secondArray c q m a b := by
  have hn : (U : Set E) ∈ 𝓝 q := U.isOpen.mem_nhds hq
  have hd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
      (hg : ContDiffOn ℝ ∞ g U) : DifferentiableAt ℝ g q :=
    (hg.contDiffAt hn).differentiableAt (by simp)
  have hΦ := hd f.potential_smooth
  have hψ := hd f.scalar_smooth
  have hA := hd (f.timeRemainder_smooth c hc)
  have hB (j : Fin 3) : DifferentiableAt ℝ (fun x => f.vectorPotential x j) q :=
    differentiableAt_pi.mp (hd f.vector_smooth) j
  have hB' (j : Fin 3) : DifferentiableAt ℝ (fun x => f.mixedRemainder c x j) q :=
    differentiableAt_pi.mp (hd (f.mixedRemainder_smooth c hc)) j
  have hH (i j : Fin 3) : DifferentiableAt ℝ (fun x => f.spatialRemainder c x i j) q :=
    differentiableAt_pi.mp (differentiableAt_pi.mp (hd (f.spatialRemainder_smooth c hc)) i) j
  unfold metricDerivative
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  · simp only [coefficient_zero_zero]
    simp (disch := fun_prop) only [partial_add, partial_sub, partial_const_mul, partial_pow_two,
      partial_const]
    simp [leadingArray, firstArray, secondArray, blockArray]
    ring
  · simp only [coefficient_zero_succ]
    simp (disch := fun_prop) only [partial_add, partial_const_mul]
    simp [leadingArray, firstArray, secondArray, blockArray]
    ring
  · simp only [coefficient_succ_zero]
    simp (disch := fun_prop) only [partial_add, partial_const_mul]
    simp [leadingArray, firstArray, secondArray, blockArray]
    ring
  · simp only [coefficient_succ_succ]
    simp (disch := fun_prop) only [partial_add, partial_const_mul, partial_mul, partial_const]
    simp [leadingArray, firstArray, secondArray, blockArray]
    split_ifs <;> ring

theorem lowerContraction_metricDerivative {c : ℝ} (hc : 0 < c) {q : E} (hq : q ∈ U) (u : E)
    (l : Fin 4) :
    lowerContraction (metricDerivative f.toNewtonianMetricFamily c q) u l =
      lowerContraction (f.leadingArray q) u l + epsilon c * lowerContraction (f.firstArray q) u l +
        epsilon c ^ 2 * lowerContraction (f.secondArray c q) u l := by
  have h : metricDerivative f.toNewtonianMetricFamily c q = fun m a b =>
      (f.leadingArray q m a b + epsilon c * f.firstArray q m a b) +
        epsilon c ^ 2 * f.secondArray c q m a b := by
    funext m a b
    exact f.metricDerivative_eq hc hq m a b
  rw [h, lowerContraction_add_mul, lowerContraction_add_mul (f.leadingArray q)]

private theorem lowerContraction_leading_zero (q : E) (v : S) :
    lowerContraction (f.leadingArray q) (timeVelocity v) 0 =
      -coordinatePartial f.potential q 0 -
        2 * ∑ j, v j * coordinatePartial f.potential q j.succ := by
  rw [leadingArray, lowerContraction_block_zero]
  have h : ∑ j, v j * (-2 * coordinatePartial f.potential q j.succ) =
      -2 * ∑ j, v j * coordinatePartial f.potential q j.succ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_div,
    sub_zero, h]
  ring

private theorem lowerContraction_leading_succ (q : E) (v : S) (k : Fin 3) :
    lowerContraction (f.leadingArray q) (timeVelocity v) k.succ =
      coordinatePartial f.potential q k.succ := by
  rw [leadingArray, lowerContraction_block_succ]
  simp only [Pi.zero_apply, add_zero, mul_zero, Finset.sum_const_zero, zero_div, sub_zero,
    mul_comm]
  ring

private theorem sum_coefficient_time_velocity (c : ℝ) (q : E) (v : S) :
    ∑ n, f.coefficient c q 0 n * timeVelocity v n =
      -c ^ 2 - 2 * f.potential q + epsilon c *
        (-2 * (f.potential q ^ 2 + f.scalarPotential q) + epsilon c * f.timeRemainder c q) +
        epsilon c * ∑ j, (f.vectorPotential q j + epsilon c * f.mixedRemainder c q j) * v j := by
  rw [Fin.sum_univ_succ]
  simp only [coefficient_zero_zero, coefficient_zero_succ, timeVelocity, Fin.cons_zero,
    Fin.cons_succ, mul_one, Finset.mul_sum, mul_assoc]

private theorem sum_coefficient_time_succ (c : ℝ) (q : E) (w : S) :
    ∑ m : Fin 3, f.coefficient c q 0 m.succ * w m =
      epsilon c * ∑ j, (f.vectorPotential q j + epsilon c * f.mixedRemainder c q j) * w j := by
  simp only [coefficient_zero_succ, Finset.mul_sum, mul_assoc]

private theorem sum_coefficient_space_velocity (c : ℝ) (q : E) (v : S) (k : Fin 3) :
    ∑ n, f.coefficient c q k.succ n * timeVelocity v n =
      epsilon c * (f.vectorPotential q k + epsilon c * f.mixedRemainder c q k) + v k +
        epsilon c * (-2 * f.potential q * v k +
          epsilon c * ∑ j, f.spatialRemainder c q k j * v j) := by
  rw [Fin.sum_univ_succ]
  simp only [coefficient_succ_zero, coefficient_succ_succ, timeVelocity, Fin.cons_zero,
    Fin.cons_succ, mul_one]
  have h (j : Fin 3) : ((if k = j then 1 else 0) + epsilon c * (-2 * f.potential q *
      (if k = j then 1 else 0) + epsilon c * f.spatialRemainder c q k j)) * v j =
      (if k = j then (1 - 2 * epsilon c * f.potential q) * v j else 0) +
        epsilon c ^ 2 * (f.spatialRemainder c q k j * v j) := by
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.mul_sum]
  ring

private theorem sum_coefficient_space_succ (c : ℝ) (q : E) (w : S) (k : Fin 3) :
    ∑ m : Fin 3, f.coefficient c q k.succ m.succ * w m =
      (1 - 2 * epsilon c * f.potential q) * w k +
        epsilon c ^ 2 * ∑ j, f.spatialRemainder c q k j * w j := by
  simp only [coefficient_succ_succ]
  have h (j : Fin 3) : ((if k = j then 1 else 0) + epsilon c * (-2 * f.potential q *
      (if k = j then 1 else 0) + epsilon c * f.spatialRemainder c q k j)) * w j =
      (if k = j then (1 - 2 * epsilon c * f.potential q) * w j else 0) +
        epsilon c ^ 2 * (f.spatialRemainder c q k j * w j) := by
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.mul_sum]

/-! ### The first post-Newtonian acceleration -/

/-- The first post-Newtonian correction to the acceleration of a test body,
`a₁ = −v²∇Φ − 4Φ∇Φ − ∇ψ + 3 ∂_tΦ v + 4 (v·∇Φ) v + ∇(B·v) − ∂_t B − (v·∇)B`, the
Euler–Lagrange acceleration of the test-body Lagrangian of §106 at order `c⁻²`. -/
def postNewtonianCorrection (q : E) (v : S) : S := fun k =>
  -(∑ j, v j ^ 2) * coordinatePartial f.potential q k.succ -
    4 * f.potential q * coordinatePartial f.potential q k.succ -
    coordinatePartial f.scalarPotential q k.succ +
    3 * coordinatePartial f.potential q 0 * v k +
    4 * (∑ j, v j * coordinatePartial f.potential q j.succ) * v k +
    ∑ j, v j * coordinatePartial (fun x => f.vectorPotential x j) q k.succ -
    coordinatePartial (fun x => f.vectorPotential x k) q 0 -
    ∑ j, v j * coordinatePartial (fun x => f.vectorPotential x k) q j.succ

/-- The acceleration `−∇Φ + a₁/c²` of a test body in the second approximation. -/
def postNewtonianAcceleration (c : ℝ) (q : E) (v : S) : S := fun k =>
  -coordinatePartial f.potential q k.succ + epsilon c * f.postNewtonianCorrection q v k

theorem postNewtonianCorrection_eq (q : E) (v : S) (k : Fin 3) :
    f.postNewtonianCorrection q v k =
      -(lowerContraction (f.firstArray q) (timeVelocity v) k.succ +
        2 * f.potential q * coordinatePartial f.potential q k.succ +
        v k * (-coordinatePartial f.potential q 0 -
          2 * ∑ j, v j * coordinatePartial f.potential q j.succ)) := by
  rw [firstArray, lowerContraction_block_succ]
  simp only [postNewtonianCorrection]
  fin_cases k <;> simp [Fin.sum_univ_succ] <;> ring

/-- The remainder of the comparison, as a function of the values entering it. -/
def coreError (ε Φ ψ A ak Φk vk Bk β γ η θ F00 R0 F1k Rk : ℝ) : ℝ :=
  (2 * (Φ ^ 2 + ψ) - ε * A - γ) * (ak + Φk) + (η + Rk) +
    (2 * Φ + ε * (2 * (Φ ^ 2 + ψ) - ε * A - γ)) * (-2 * Φ * ak + F1k) + vk * (β + R0) +
    (Bk - 2 * Φ * vk + ε * θ) * F00 +
    ε * ((2 * Φ + ε * (2 * (Φ ^ 2 + ψ) - ε * A - γ)) * (η + Rk) +
      (Bk - 2 * Φ * vk + ε * θ) * (β + R0))

private theorem core_identity {ε c Φ ψ A ak Φk vk Bk β γ η θ w0 F0 Fk F00 R0 F1k Rk : ℝ}
    (hε : ε * c ^ 2 = 1)
    (hT : ε * β = w0 * (-c ^ 2 - 2 * Φ + ε * (-2 * (Φ ^ 2 + ψ) + ε * A) + ε * γ) - F0)
    (hS : (1 - 2 * ε * Φ) * ak + ε ^ 2 * η =
      w0 * (ε * Bk + vk + ε * (-2 * Φ * vk + ε * θ)) - Fk)
    (hF0 : F0 = F00 + ε * R0) (hFk : Fk = Φk + ε * F1k + ε ^ 2 * Rk) :
    ak - (-Φk + ε * -(F1k + 2 * Φ * Φk + vk * F00)) =
      -(ε ^ 2 * coreError ε Φ ψ A ak Φk vk Bk β γ η θ F00 R0 F1k Rk) := by
  subst hF0 hFk
  unfold coreError
  linear_combination (-ε * (-c ^ 2 - 2 * Φ + ε * (-2 * (Φ ^ 2 + ψ) + ε * A) + ε * γ)) * hS +
    (ε * (ε * Bk + vk + ε * (-2 * Φ * vk + ε * θ))) * hT -
    ((1 - 2 * ε * Φ) * ak + ε ^ 2 * η + (Φk + ε * F1k + ε ^ 2 * Rk)) * hε

/-- The explicit remainder `X` of `a − a_PN = −X/c⁴`. -/
def accelerationRemainder (c : ℝ) (q : E) (v : S) (k : Fin 3) : ℝ :=
  coreError (epsilon c) (f.potential q) (f.scalarPotential q) (f.timeRemainder c q)
    (f.acceleration c q v k) (coordinatePartial f.potential q k.succ) (v k)
    (f.vectorPotential q k + epsilon c * f.mixedRemainder c q k)
    (∑ j, (f.vectorPotential q j + epsilon c * f.mixedRemainder c q j) * f.acceleration c q v j)
    (∑ j, (f.vectorPotential q j + epsilon c * f.mixedRemainder c q j) * v j)
    (∑ j, f.spatialRemainder c q k j * f.acceleration c q v j)
    (∑ j, f.spatialRemainder c q k j * v j)
    (-coordinatePartial f.potential q 0 - 2 * ∑ j, v j * coordinatePartial f.potential q j.succ)
    (lowerContraction (f.firstArray q) (timeVelocity v) 0 +
      epsilon c * lowerContraction (f.secondArray c q) (timeVelocity v) 0)
    (lowerContraction (f.firstArray q) (timeVelocity v) k.succ)
    (lowerContraction (f.secondArray c q) (timeVelocity v) k.succ)

/-- **The geodesic acceleration in the second approximation, exactly.** For every member with
`c ≥ 1` and `9K < c²`, the coordinate-time acceleration of the family's geodesics differs from
the post-Newtonian acceleration by `−X/c⁴`, with the explicit remainder `X`
(`accelerationRemainder`). -/
theorem acceleration_sub_eq {c : ℝ} (hc : 1 ≤ c) (hlarge : 9 * f.bound < c ^ 2) (q : U)
    (v : S) (k : Fin 3) :
    f.acceleration c q v k - f.postNewtonianAcceleration c q v k =
      -(epsilon c ^ 2 * f.accelerationRemainder c q v k) := by
  have hc0 : 0 < c := by linarith
  have hε : epsilon c * c ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  have hT := coefficient_acceleration f.toNewtonianMetricFamily hc hlarge q v 0
  have hS := coefficient_acceleration f.toNewtonianMetricFamily hc hlarge q v k.succ
  rw [sum_coefficient_time_succ, sum_coefficient_time_velocity,
    f.lowerContraction_metricDerivative hc0 q.property, lowerContraction_leading_zero] at hT
  rw [sum_coefficient_space_succ, sum_coefficient_space_velocity,
    f.lowerContraction_metricDerivative hc0 q.property, lowerContraction_leading_succ] at hS
  have h := core_identity (F00 := -coordinatePartial f.potential q 0 -
      2 * ∑ j, v j * coordinatePartial f.potential q j.succ)
    (R0 := lowerContraction (f.firstArray q) (timeVelocity v) 0 +
      epsilon c * lowerContraction (f.secondArray c q) (timeVelocity v) 0) hε hT hS (by ring) rfl
  rw [accelerationRemainder, ← h, postNewtonianAcceleration, postNewtonianCorrection_eq]

end PostNewtonianMetricFamily

/-! ### Uniform bounds -/

/-- A real function bounded on a set. -/
private def BoundedOn {α : Type} (T : Set α) (F : α → ℝ) : Prop :=
  ∃ C, 0 ≤ C ∧ ∀ x ∈ T, |F x| ≤ C

section BoundedOn

variable {α : Type} {T : Set α} {F G : α → ℝ}

private theorem BoundedOn.const (a : ℝ) : BoundedOn T (fun _ => a) :=
  ⟨|a|, abs_nonneg a, fun _ _ => le_rfl⟩

private theorem BoundedOn.add (hF : BoundedOn T F) (hG : BoundedOn T G) :
    BoundedOn T (fun x => F x + G x) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  exact ⟨C + D, by positivity, fun x hx => (abs_add_le _ _).trans (add_le_add (hF x hx) (hG x hx))⟩

private theorem BoundedOn.sub (hF : BoundedOn T F) (hG : BoundedOn T G) :
    BoundedOn T (fun x => F x - G x) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  exact ⟨C + D, by positivity, fun x hx => (abs_sub _ _).trans (add_le_add (hF x hx) (hG x hx))⟩

private theorem BoundedOn.mul (hF : BoundedOn T F) (hG : BoundedOn T G) :
    BoundedOn T (fun x => F x * G x) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C * D, by positivity, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hF x hx) (hG x hx) (abs_nonneg _) hC

private theorem BoundedOn.neg (hF : BoundedOn T F) : BoundedOn T (fun x => -F x) := by
  obtain ⟨C, hC, hF⟩ := hF
  exact ⟨C, hC, fun x hx => by rw [abs_neg]; exact hF x hx⟩

private theorem BoundedOn.div_const (hF : BoundedOn T F) (a : ℝ) :
    BoundedOn T (fun x => F x / a) := by
  simpa only [div_eq_mul_inv] using hF.mul (BoundedOn.const a⁻¹)

private theorem BoundedOn.pow (hF : BoundedOn T F) (n : ℕ) : BoundedOn T (fun x => F x ^ n) := by
  induction n with
  | zero => simpa using BoundedOn.const (T := T) 1
  | succ n ih => simpa only [pow_succ] using ih.mul hF

private theorem BoundedOn.sum {ι : Type} [Fintype ι] {H : ι → α → ℝ}
    (hH : ∀ i, BoundedOn T (H i)) : BoundedOn T (fun x => ∑ i, H i x) := by
  choose C hC hb using hH
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC i, fun x hx => ?_⟩
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hb i x hx)

private theorem BoundedOn.of_le {C : ℝ} (h : ∀ x ∈ T, |F x| ≤ C) : BoundedOn T F :=
  ⟨max C 0, le_max_right _ _, fun x hx => (h x hx).trans (le_max_left _ _)⟩

end BoundedOn

/-- Decompose a bound on a polynomial expression into bounds on its atoms. -/
local macro "bounded_on" : tactic => `(tactic| repeat' first
  | intro _
  | with_reducible apply BoundedOn.const
  | with_reducible apply_assumption
  | with_reducible apply BoundedOn.add
  | with_reducible apply BoundedOn.sub
  | with_reducible apply BoundedOn.mul
  | with_reducible apply BoundedOn.neg
  | with_reducible apply BoundedOn.div_const
  | with_reducible apply BoundedOn.pow
  | with_reducible apply BoundedOn.sum)

private theorem BoundedOn.lowerContr {α : Type} {T : Set α}
    {D : α → Fin 4 → Fin 4 → Fin 4 → ℝ} {u : α → E}
    (hD : ∀ m a b, BoundedOn T (fun x => D x m a b)) (hu : ∀ i, BoundedOn T (fun x => u x i))
    (l : Fin 4) : BoundedOn T (fun x => lowerContraction (D x) (u x) l) := by
  unfold lowerContraction
  bounded_on

private theorem BoundedOn.core {α : Type} {T : Set α}
    {ε Φ ψ A ak Φk vk Bk β γ η θ F00 R0 F1k Rk : α → ℝ}
    (h₁ : BoundedOn T ε) (h₂ : BoundedOn T Φ) (h₃ : BoundedOn T ψ) (h₄ : BoundedOn T A)
    (h₅ : BoundedOn T ak) (h₆ : BoundedOn T Φk) (h₇ : BoundedOn T vk) (h₈ : BoundedOn T Bk)
    (h₉ : BoundedOn T β) (h₁₀ : BoundedOn T γ) (h₁₁ : BoundedOn T η) (h₁₂ : BoundedOn T θ)
    (h₁₃ : BoundedOn T F00) (h₁₄ : BoundedOn T R0) (h₁₅ : BoundedOn T F1k)
    (h₁₆ : BoundedOn T Rk) :
    BoundedOn T (fun x => PostNewtonianMetricFamily.coreError (ε x) (Φ x) (ψ x) (A x) (ak x)
      (Φk x) (vk x) (Bk x) (β x) (γ x) (η x) (θ x) (F00 x) (R0 x) (F1k x) (Rk x)) := by
  unfold PostNewtonianMetricFamily.coreError
  bounded_on

private theorem BoundedOn.block {α : Type} {T : Set α} {p : α → Fin 4 → ℝ}
    {b : α → Fin 4 → S} {h : α → Fin 4 → NewtonianSpatialMatrix}
    (hp : ∀ m, BoundedOn T (fun x => p x m)) (hb : ∀ m j, BoundedOn T (fun x => b x m j))
    (hh : ∀ m i j, BoundedOn T (fun x => h x m i j)) (m a c : Fin 4) :
    BoundedOn T (fun x => blockArray (p x) (b x) (h x) m a c) := by
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) c
  · exact hp m
  · exact hb m j
  · exact hb m i
  · exact hh m i j

private theorem BoundedOn.timeVel {α : Type} {T : Set α} {v : α → S}
    (hv : ∀ j, BoundedOn T (fun x => v x j)) (i : Fin 4) :
    BoundedOn T (fun x => timeVelocity (v x) i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact BoundedOn.const 1
  · exact hv j

private theorem abs_coordinatePartial_le {g : E → ℝ} {q : E} {K : ℝ} (hg : ‖fderiv ℝ g q‖ ≤ K)
    (m : Fin 4) : |coordinatePartial g q m| ≤ K := by
  rw [coordinatePartial, ← Real.norm_eq_abs]
  exact ((fderiv ℝ g q).le_opNorm _).trans (by simpa [Pi.norm_single] using hg)

private theorem coordinatePartial_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → Fin 3 → F} {q : E} (hg : DifferentiableAt ℝ g q) (j : Fin 3) (m : Fin 4) :
    fderiv ℝ (fun x => g x j) q (Pi.single m 1) = fderiv ℝ g q (Pi.single m 1) j := by
  have h := ((proj j : (Fin 3 → F) →L[ℝ] F).hasFDerivAt.comp q hg.hasFDerivAt).fderiv
  change fderiv ℝ ((proj j : (Fin 3 → F) →L[ℝ] F) ∘ g) q (Pi.single m 1) = _
  rw [h]
  rfl

private theorem norm_fderiv_apply_le {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {q : E} {K : ℝ} (hg : ‖fderiv ℝ g q‖ ≤ K) (m : Fin 4) :
    ‖fderiv ℝ g q (Pi.single m 1)‖ ≤ K :=
  ((fderiv ℝ g q).le_opNorm _).trans (by simpa [Pi.norm_single] using hg)

namespace PostNewtonianMetricFamily

variable {U : Opens E} (f : PostNewtonianMetricFamily U)

/-- **The acceleration of a test body in the second approximation (§106).** On the whole
coordinate domain and for velocities `‖v‖ ≤ V`, the coordinate-time acceleration of the
geodesics of a post-Newtonian family is the Euler–Lagrange acceleration
`−∇Φ + a₁/c²` of the test-body Lagrangian up to `C/c⁴`, with one constant `C` for all
`c ≥ 24K + 2`. -/
theorem acceleration_error {V : ℝ} (hV : 0 ≤ V) :
    ∃ C, 0 ≤ C ∧ ∀ c, 24 * f.bound + 2 ≤ c → ∀ q ∈ U, ∀ v : S, ‖v‖ ≤ V →
      ‖f.acceleration c q v - f.postNewtonianAcceleration c q v‖ ≤ C / c ^ 4 := by
  have hK := f.bound_nonneg
  set T : Set (ℝ × E × S) := {p | 24 * f.bound + 2 ≤ p.1 ∧ p.2.1 ∈ U ∧ ‖p.2.2‖ ≤ V}
  have hT1 {p : ℝ × E × S} (hp : p ∈ T) : 1 ≤ p.1 := by linarith [hp.1]
  have hT2 {p : ℝ × E × S} (hp : p ∈ T) : 24 * f.bound < p.1 ^ 2 := by
    nlinarith [hp.1, sq_nonneg (p.1 - 1)]
  have hd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {q : E}
      (hg : ContDiffOn ℝ ∞ g U) (hq : q ∈ U) : DifferentiableAt ℝ g q :=
    (hg.contDiffAt (U.isOpen.mem_nhds hq)).differentiableAt (by simp)
  -- the atoms
  have hε : BoundedOn T (fun p => epsilon p.1) := BoundedOn.of_le fun p hp => by
    rw [abs_of_nonneg (epsilon_nonneg _)]
    exact epsilon_le_one (hT1 hp)
  have hv (j : Fin 3) : BoundedOn T (fun p => p.2.2 j) :=
    BoundedOn.of_le fun p hp => spaceComponent_abs_le hp.2.2 j
  have hΦ : BoundedOn T (fun p => f.potential p.2.1) := BoundedOn.of_le fun p hp => by
    simpa only [Real.norm_eq_abs] using f.potential_bound.value _ hp.2.1
  have hψ : BoundedOn T (fun p => f.scalarPotential p.2.1) := BoundedOn.of_le fun p hp => by
    simpa only [Real.norm_eq_abs] using f.scalar_bound.value _ hp.2.1
  have hA : BoundedOn T (fun p => f.timeRemainder p.1 p.2.1) := BoundedOn.of_le fun p hp => by
    simpa only [Real.norm_eq_abs] using (f.timeRemainder_bound _ (hT1 hp)).value _ hp.2.1
  have hB (j : Fin 3) : BoundedOn T (fun p => f.vectorPotential p.2.1 j) :=
    BoundedOn.of_le fun p hp => spaceComponent_abs_le (f.vector_bound.value _ hp.2.1) j
  have hB' (j : Fin 3) : BoundedOn T (fun p => f.mixedRemainder p.1 p.2.1 j) :=
    BoundedOn.of_le fun p hp =>
      spaceComponent_abs_le ((f.mixedRemainder_bound _ (hT1 hp)).value _ hp.2.1) j
  have hH (i j : Fin 3) : BoundedOn T (fun p => f.spatialRemainder p.1 p.2.1 i j) :=
    BoundedOn.of_le fun p hp =>
      spatialComponent_abs_le ((f.spatialRemainder_bound _ (hT1 hp)).value _ hp.2.1) i j
  have hΦm (m : Fin 4) : BoundedOn T (fun p => coordinatePartial f.potential p.2.1 m) :=
    BoundedOn.of_le fun p hp => abs_coordinatePartial_le (f.potential_bound.first _ hp.2.1) m
  have hψm (m : Fin 4) : BoundedOn T (fun p => coordinatePartial f.scalarPotential p.2.1 m) :=
    BoundedOn.of_le fun p hp => abs_coordinatePartial_le (f.scalar_bound.first _ hp.2.1) m
  have hAm (m : Fin 4) : BoundedOn T (fun p => coordinatePartial (f.timeRemainder p.1) p.2.1 m) :=
    BoundedOn.of_le fun p hp =>
      abs_coordinatePartial_le ((f.timeRemainder_bound _ (hT1 hp)).first _ hp.2.1) m
  have hBm (m : Fin 4) (j : Fin 3) :
      BoundedOn T (fun p => coordinatePartial (fun x => f.vectorPotential x j) p.2.1 m) :=
    BoundedOn.of_le fun p hp => by
      rw [coordinatePartial, coordinatePartial_apply (hd f.vector_smooth hp.2.1),
        ← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ j).trans
        (norm_fderiv_apply_le (f.vector_bound.first _ hp.2.1) m)
  have hB'm (m : Fin 4) (j : Fin 3) :
      BoundedOn T (fun p => coordinatePartial (fun x => f.mixedRemainder p.1 x j) p.2.1 m) :=
    BoundedOn.of_le fun p hp => by
      rw [coordinatePartial, coordinatePartial_apply
        (hd (f.mixedRemainder_smooth p.1 (by linarith [hT1 hp])) hp.2.1), ← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ j).trans
        (norm_fderiv_apply_le ((f.mixedRemainder_bound _ (hT1 hp)).first _ hp.2.1) m)
  have hHm (m : Fin 4) (i j : Fin 3) :
      BoundedOn T (fun p => coordinatePartial (fun x => f.spatialRemainder p.1 x i j) p.2.1 m) :=
    BoundedOn.of_le fun p hp => by
      have hs := hd (f.spatialRemainder_smooth p.1 (by linarith [hT1 hp])) hp.2.1
      rw [coordinatePartial, coordinatePartial_apply (differentiableAt_pi.mp hs i),
        coordinatePartial_apply hs, ← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans
        (norm_fderiv_apply_le ((f.spatialRemainder_bound _ (hT1 hp)).first _ hp.2.1) m))
  have ha (j : Fin 3) : BoundedOn T (fun p => f.acceleration p.1 p.2.1 p.2.2 j) := by
    refine BoundedOn.of_le (C := f.accelerationErrorConstant V + f.bound) fun p hp => ?_
    have h := f.toNewtonianMetricFamily.acceleration_error (hT1 hp) (hT2 hp) ⟨p.2.1, hp.2.1⟩ hV
      hp.2.2
    have he := mul_le_mul_of_nonneg_left (epsilon_le_one (hT1 hp))
      (f.accelerationErrorConstant_nonneg hV)
    have hj := (norm_le_pi_norm _ j).trans (h.trans (he.trans_eq (mul_one _)))
    have hg : |f.spatialGradient p.2.1 j| ≤ f.bound :=
      abs_coordinatePartial_le (f.potential_bound.first _ hp.2.1) j.succ
    rw [Pi.add_apply, Real.norm_eq_abs] at hj
    calc |f.acceleration p.1 p.2.1 p.2.2 j|
        = |(f.acceleration p.1 p.2.1 p.2.2 j + f.spatialGradient p.2.1 j) -
            f.spatialGradient p.2.1 j| := by ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add hj hg)
  have hu (i : Fin 4) : BoundedOn T (fun p => timeVelocity p.2.2 i) := BoundedOn.timeVel hv i
  have h1 (l : Fin 4) : BoundedOn T
      (fun p => lowerContraction (f.firstArray p.2.1) (timeVelocity p.2.2) l) := by
    refine BoundedOn.lowerContr (fun m a b => ?_) hu l
    refine BoundedOn.block (fun m => ?_) (fun m j => hBm m j) (fun m i j => ?_) m a b
    · exact (BoundedOn.const (-2)).mul ((((BoundedOn.const 2).mul hΦ).mul (hΦm m)).add (hψm m))
    · exact ((BoundedOn.const (-2)).mul (hΦm m)).mul (BoundedOn.const _)
  have h2 (l : Fin 4) : BoundedOn T
      (fun p => lowerContraction (f.secondArray p.1 p.2.1) (timeVelocity p.2.2) l) := by
    refine BoundedOn.lowerContr (fun m a b => ?_) hu l
    exact BoundedOn.block hAm hB'm hHm m a b
  have hX (k : Fin 3) : BoundedOn T (fun p => f.accelerationRemainder p.1 p.2.1 p.2.2 k) := by
    have hBk (j : Fin 3) : BoundedOn T
        (fun p => f.vectorPotential p.2.1 j + epsilon p.1 * f.mixedRemainder p.1 p.2.1 j) :=
      (hB j).add (hε.mul (hB' j))
    exact BoundedOn.core hε hΦ hψ hA (ha k) (hΦm k.succ) (hv k) (hBk k)
      (BoundedOn.sum fun j => (hBk j).mul (ha j)) (BoundedOn.sum fun j => (hBk j).mul (hv j))
      (BoundedOn.sum fun j => (hH k j).mul (ha j)) (BoundedOn.sum fun j => (hH k j).mul (hv j))
      ((hΦm 0).neg.sub ((BoundedOn.const 2).mul (BoundedOn.sum fun j => (hv j).mul (hΦm j.succ))))
      ((h1 0).add (hε.mul (h2 0))) (h1 k.succ) (h2 k.succ)
  choose C hC0 hC using hX
  refine ⟨∑ k, C k, Finset.sum_nonneg fun k _ => hC0 k, fun c hc q hq v hv' => ?_⟩
  have hp : ((c, q, v) : ℝ × E × S) ∈ T := ⟨hc, hq, hv'⟩
  have hc1 := hT1 hp
  have hc4 : epsilon c ^ 2 = 1 / c ^ 4 := by
    rw [epsilon, inv_pow, ← pow_mul, one_div]
  refine (pi_norm_le_iff_of_nonneg
    (div_nonneg (Finset.sum_nonneg fun k _ => hC0 k) (by positivity))).mpr fun k => ?_
  rw [Pi.sub_apply, f.acceleration_sub_eq hc1 (by linarith [hT2 hp]) ⟨q, hq⟩ v k,
    Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg _), hc4]
  have hk := (hC k (c, q, v) hp).trans
    (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ k))
  rw [one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right hk (by positivity)

/-- The same estimate for the acceleration extracted from the Levi-Civita connection of the
native Lorentz metric of the family. -/
theorem native_acceleration_error {V : ℝ} (hV : 0 ≤ V) :
    ∃ C, 0 ≤ C ∧ ∀ c (hc : 24 * f.bound + 2 ≤ c), ∀ x q : U, ∀ v : S, ‖v‖ ≤ V →
      ‖coordinateTimeAcceleration (f.lorentzMetric c (by linarith [f.bound_nonneg])
          (by nlinarith [f.bound_nonneg, sq_nonneg (c - 1)])) (physicalChart x) q v -
        f.postNewtonianAcceleration c q v‖ ≤ C / c ^ 4 := by
  obtain ⟨C, hC, h⟩ := f.acceleration_error hV
  refine ⟨C, hC, fun c hc x q v hv => ?_⟩
  rw [← f.acceleration_eq_native]
  exact h c hc q q.property v hv

/-- **Geodesics in the second approximation.** An affine geodesic of the native metric of a
member with `c ≥ 24K + 2`, reparametrized by the physical time coordinate and with coordinate
speed at most `V`, has the coordinate acceleration `−∇Φ + a₁/c²` up to `C/c⁴`. -/
theorem geodesic_acceleration_error {V : ℝ} (hV : 0 ≤ V) :
    ∃ C, 0 ≤ C ∧ ∀ c (hc : 24 * f.bound + 2 ≤ c) (x : U) {γ : ℝ → U} {r : ℝ → ℝ} {t : ℝ},
      ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) 2 γ (r t) → ContDiffAt ℝ 2 r t → deriv r t ≠ 0 →
      (f.lorentzMetric c (by linarith [f.bound_nonneg])
          (by nlinarith [f.bound_nonneg, sq_nonneg (c - 1)])).covariantAlong
        (SmoothGeometry.LorentzMetric.curveVelocity γ) (r t) = 0 →
      (fun s => physicalChart x (γ (r s)) 0) =ᶠ[𝓝 t] id →
      ‖(fun j : Fin 3 => deriv (physicalChart x ∘ γ ∘ r) t j.succ)‖ ≤ V →
      ‖(fun k : Fin 3 => deriv (deriv (physicalChart x ∘ γ ∘ r)) t k.succ) -
        f.postNewtonianAcceleration c (γ (r t))
          (fun j : Fin 3 => deriv (physicalChart x ∘ γ ∘ r) t j.succ)‖ ≤ C / c ^ 4 := by
  obtain ⟨C, hC, h⟩ := f.native_acceleration_error hV
  refine ⟨C, hC, fun c hc x γ r t hγ hr hn hgeo hclock hv => ?_⟩
  have hk := coordinateTime_of_affine_reparam _ (physicalChart_mem x) (by simp) hγ hr hn hgeo
    hclock
  rw [show (fun k : Fin 3 => deriv (deriv (physicalChart x ∘ γ ∘ r)) t k.succ) = _ from
    funext hk]
  simpa only [physicalChart_apply] using h c hc x (γ (r t)) _ hv

end PostNewtonianMetricFamily

/-! ### The test-body Lagrangian -/

/-- The inclusion `w ↦ (0, w)` of space into the coordinate model. -/
private def spaceInclusion : S →L[ℝ] E :=
  ContinuousLinearMap.pi fun i => Fin.cases (motive := fun _ => S →L[ℝ] ℝ) 0 (fun j => proj j) i

private theorem spaceInclusion_apply (w : S) : spaceInclusion w = (Fin.cons 0 w : E) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [spaceInclusion]

/-- A linear form on the coordinate model on a spatial vector `(0, w)`. -/
private theorem apply_cons_zero (ℓ : E →L[ℝ] ℝ) (w : S) :
    ℓ (Fin.cons 0 w) = ∑ j, w j * ℓ (Pi.single j.succ 1) := by
  have h : (Fin.cons 0 w : E) = ∑ j, w j • (Pi.single j.succ 1 : E) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.sum_apply, Fin.succ_ne_zero]
    · simp [Finset.sum_apply, Pi.single_apply, Fin.succ_inj]
  rw [h, map_sum]
  simp [map_smul]

/-- A linear form on the coordinate model on `u = (1, v)`. -/
private theorem apply_timeVelocity (ℓ : E →L[ℝ] ℝ) (v : S) :
    ℓ (timeVelocity v) = ℓ (Pi.single 0 1) + ∑ j, v j * ℓ (Pi.single j.succ 1) := by
  have h : timeVelocity v = (Pi.single 0 1 : E) + Fin.cons 0 v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [timeVelocity, Fin.succ_ne_zero]
  rw [h, map_add, apply_cons_zero]

private theorem hasFDerivAt_slice {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → F}
    {t : ℝ} {z : S × S} (hΦ : DifferentiableAt ℝ Φ (Fin.cons t z.1)) :
    HasFDerivAt (fun y : S × S => Φ (Fin.cons t y.1))
      ((fderiv ℝ Φ (Fin.cons t z.1)).comp (spaceInclusion.comp (fst ℝ S S))) z := by
  have hι : HasFDerivAt (fun y : S × S => (Fin.cons t y.1 : E))
      (spaceInclusion.comp (fst ℝ S S)) z := by
    have h : (fun y : S × S => (Fin.cons t y.1 : E)) =
        fun y => (Fin.cons t 0 : E) + (spaceInclusion.comp (fst ℝ S S)) y := by
      funext y i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [spaceInclusion_apply]
    rw [h]
    exact ((spaceInclusion.comp (fst ℝ S S)).hasFDerivAt).const_add _
  exact hΦ.hasFDerivAt.comp z hι

private theorem hasDerivAt_path {x : ℝ → S} {t : ℝ} (hx : DifferentiableAt ℝ x t) :
    HasDerivAt (fun s => (Fin.cons s (x s) : E)) (timeVelocity (deriv x t)) t := by
  refine hasDerivAt_pi.mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [timeVelocity] using hasDerivAt_id' t
  · simpa [timeVelocity] using hasDerivAt_pi.mp hx.hasDerivAt j

namespace PostNewtonianMetricFamily

variable {U : Opens E} (f : PostNewtonianMetricFamily U)

/-- The test-body Lagrangian of §106 in coordinate time, for a body of mass `m`:
`L = −mc² + mv²/2 − mΦ + (m/c²)(v⁴/8 − (3/2)Φv² − Φ²/2 − ψ + B·v)`, the expansion of
`−mc √(−g(u, u))`, `u = (1, v)`, to order `c⁻²`. -/
def lagrangian (m c : ℝ) : Mechanics.Lagrangian S := fun t z =>
  -m * c ^ 2 + m * ((∑ j, z.2 j ^ 2) / 2 - f.potential (Fin.cons t z.1) +
    epsilon c * ((∑ j, z.2 j ^ 2) ^ 2 / 8 -
      3 / 2 * f.potential (Fin.cons t z.1) * ∑ j, z.2 j ^ 2 -
      f.potential (Fin.cons t z.1) ^ 2 / 2 - f.scalarPotential (Fin.cons t z.1) +
      ∑ j, f.vectorPotential (Fin.cons t z.1) j * z.2 j))

/-- The force `∂L/∂x` of the test-body Lagrangian per unit mass. -/
def lagrangianForce (c : ℝ) (q : E) (v : S) : S := fun k =>
  -coordinatePartial f.potential q k.succ + epsilon c *
    (-(3 / 2) * coordinatePartial f.potential q k.succ * ∑ j, v j ^ 2 -
      f.potential q * coordinatePartial f.potential q k.succ -
      coordinatePartial f.scalarPotential q k.succ +
      ∑ j, coordinatePartial (fun y => f.vectorPotential y j) q k.succ * v j)

/-- The momentum `∂L/∂v` of the test-body Lagrangian per unit mass. -/
def lagrangianMomentum (c : ℝ) (q : E) (v : S) : S := fun k =>
  v k + epsilon c *
    ((∑ j, v j ^ 2) * v k / 2 - 3 * f.potential q * v k + f.vectorPotential q k)

theorem fderiv_lagrangian (m c t : ℝ) {z : S × S} (hz : (Fin.cons t z.1 : E) ∈ U)
    (w : S × S) :
    fderiv ℝ (f.lagrangian m c t) z w =
      m * (∑ k, f.lagrangianForce c (Fin.cons t z.1) z.2 k * w.1 k +
        ∑ k, f.lagrangianMomentum c (Fin.cons t z.1) z.2 k * w.2 k) := by
  have hd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
      (hg : ContDiffOn ℝ ∞ g U) : DifferentiableAt ℝ g (Fin.cons t z.1) :=
    (hg.contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hΦ := hasFDerivAt_slice (hd f.potential_smooth)
  have hψ := hasFDerivAt_slice (hd f.scalar_smooth)
  have hB (j : Fin 3) := hasFDerivAt_slice (Φ := fun y => f.vectorPotential y j)
    (differentiableAt_pi.mp (hd f.vector_smooth) j)
  have hdΦ := hΦ.differentiableAt
  have hdψ := hψ.differentiableAt
  have hdB (j : Fin 3) := (hB j).differentiableAt
  have hBf (j : Fin 3) := (hB j).fderiv
  have hs (j : Fin 3) : fderiv ℝ (fun y : S × S => y.2 j) z = (proj j).comp (snd ℝ S S) :=
    ((proj j).comp (snd ℝ S S)).fderiv
  unfold lagrangian
  simp only [pow_two, div_eq_mul_inv]
  simp (disch := (intros; fun_prop)) only [fderiv_const_add, fderiv_const_mul, fderiv_fun_add,
    fderiv_fun_sub, fderiv_fun_mul, fderiv_fun_sum, fderiv_const_apply, hΦ.fderiv, hψ.fderiv,
    hBf, hs]
  simp only [add_apply, sub_apply, smul_apply, coe_comp, Function.comp_apply, FunLike.coe_sum,
    Finset.sum_apply, smul_eq_mul, proj_apply, coe_snd', coe_fst', spaceInclusion_apply,
    apply_cons_zero, zero_apply]
  simp only [lagrangianForce, lagrangianMomentum, coordinatePartial, Fin.sum_univ_three]
  ring

theorem force_lagrangian (m c : ℝ) (x : ℝ → S) {t : ℝ} (ht : (Fin.cons t (x t) : E) ∈ U)
    (k : Fin 3) :
    Mechanics.force (f.lagrangian m c) x t (Pi.single k 1) =
      m * f.lagrangianForce c (Fin.cons t (x t)) (deriv x t) k := by
  rw [Mechanics.force, comp_apply, inl_apply, f.fderiv_lagrangian m c t ht]
  simp [Pi.single_apply]

theorem momentum_lagrangian (m c : ℝ) (x : ℝ → S) {t : ℝ} (ht : (Fin.cons t (x t) : E) ∈ U) :
    Mechanics.momentum (f.lagrangian m c) x t =
      ∑ k, (m * f.lagrangianMomentum c (Fin.cons t (x t)) (deriv x t) k) • proj k := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [Mechanics.momentum, comp_apply, inr_apply, f.fderiv_lagrangian m c t ht]
  simp [Finset.mul_sum, mul_assoc]

/-- The time derivative of the momentum per unit mass along a path with position `q`, velocity
`v` and acceleration `a`: `a + ((v·a) v + v² a/2 − 3 (u·∂Φ) v − 3Φ a + u·∂B)/c²`, `u = (1, v)`. -/
def momentumRate (c : ℝ) (q : E) (v a : S) : S := fun k =>
  a k + epsilon c * ((∑ j, v j * a j) * v k + (∑ j, v j ^ 2) * a k / 2 -
    3 * fderiv ℝ f.potential q (timeVelocity v) * v k - 3 * f.potential q * a k +
    fderiv ℝ (fun y => f.vectorPotential y k) q (timeVelocity v))

theorem hasDerivAt_lagrangianMomentum (c : ℝ) {x : ℝ → S} (hx : ContDiff ℝ 2 x) {t : ℝ}
    (ht : (Fin.cons t (x t) : E) ∈ U) (k : Fin 3) :
    HasDerivAt (fun s => f.lagrangianMomentum c (Fin.cons s (x s)) (deriv x s) k)
      (f.momentumRate c (Fin.cons t (x t)) (deriv x t) (deriv (deriv x) t) k) t := by
  have hd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
      (hg : ContDiffOn ℝ ∞ g U) : DifferentiableAt ℝ g (Fin.cons t (x t)) :=
    (hg.contDiffAt (U.isOpen.mem_nhds ht)).differentiableAt (by simp)
  have hγ := hasDerivAt_path ((hx.differentiable (by norm_num)) t)
  have hΦ := (hd f.potential_smooth).hasFDerivAt.comp_hasDerivAt t hγ
  have hB (j : Fin 3) := (differentiableAt_pi.mp (hd f.vector_smooth) j).hasFDerivAt.comp_hasDerivAt
    t hγ
  have hv (j : Fin 3) : HasDerivAt (fun s => deriv x s j) (deriv (deriv x) t j) t :=
    hasDerivAt_pi.mp (hx.differentiable_deriv_two t).hasDerivAt j
  have hdΦ := hΦ.differentiableAt
  have hdB (j : Fin 3) := (hB j).differentiableAt
  have hdv (j : Fin 3) := (hv j).differentiableAt
  have hΦd := hΦ.deriv
  have hBd (j : Fin 3) := (hB j).deriv
  have hvd (j : Fin 3) := (hv j).deriv
  simp only [Function.comp_def] at hdΦ hdB hΦd hBd
  have hdiff : DifferentiableAt ℝ
      (fun s => f.lagrangianMomentum c (Fin.cons s (x s)) (deriv x s) k) t := by
    unfold lagrangianMomentum
    fun_prop
  have hval : deriv (fun s => f.lagrangianMomentum c (Fin.cons s (x s)) (deriv x s) k) t =
      f.momentumRate c (Fin.cons t (x t)) (deriv x t) (deriv (deriv x) t) k := by
    unfold lagrangianMomentum momentumRate
    simp only [pow_two, div_eq_mul_inv]
    simp (disch := (intros; fun_prop)) only [deriv_fun_add, deriv_fun_sub, deriv_fun_mul,
      deriv_fun_sum, deriv_const, hΦd, hBd, hvd]
    simp only [Fin.sum_univ_three]
    ring
  exact hval ▸ hdiff.hasDerivAt

/-- **The Euler–Lagrange equations of the test-body Lagrangian**, along a `C²` path in the
domain: the residual `∂L/∂x − d/dt ∂L/∂v` is `m (F − ṗ)` with the force `F`
(`lagrangianForce`) and the rate of the momentum per unit mass (`momentumRate`). -/
theorem eulerLagrange_lagrangian (m c : ℝ) {x : ℝ → S} (hx : ContDiff ℝ 2 x) {t : ℝ}
    (ht : (Fin.cons t (x t) : E) ∈ U) (k : Fin 3) :
    Mechanics.eulerLagrange (f.lagrangian m c) x t (Pi.single k 1) =
      m * (f.lagrangianForce c (Fin.cons t (x t)) (deriv x t) k -
        f.momentumRate c (Fin.cons t (x t)) (deriv x t) (deriv (deriv x) t) k) := by
  have hγ := (hasDerivAt_path ((hx.differentiable (by norm_num)) t)).continuousAt
  have hev : ∀ᶠ s in 𝓝 t, (Fin.cons s (x s) : E) ∈ U :=
    hγ.preimage_mem_nhds (U.isOpen.mem_nhds ht)
  have hmom : Mechanics.momentum (f.lagrangian m c) x =ᶠ[𝓝 t] fun s =>
      ∑ k, (m * f.lagrangianMomentum c (Fin.cons s (x s)) (deriv x s) k) • proj k :=
    hev.mono fun s hs => f.momentum_lagrangian m c x hs
  have hD : HasDerivAt (fun s =>
      ∑ k, (m * f.lagrangianMomentum c (Fin.cons s (x s)) (deriv x s) k) • proj k)
      (∑ k, (m * f.momentumRate c (Fin.cons t (x t)) (deriv x t) (deriv (deriv x) t) k) •
        (proj k : S →L[ℝ] ℝ)) t :=
    HasDerivAt.fun_sum fun k _ =>
      ((f.hasDerivAt_lagrangianMomentum c hx ht k).const_mul m).smul_const
        (proj k : S →L[ℝ] ℝ)
  rw [Mechanics.eulerLagrange, sub_apply, f.force_lagrangian m c x ht, hmom.deriv_eq, hD.deriv]
  simp [Pi.single_apply]
  ring

end PostNewtonianMetricFamily

/-- The velocity form `Q_v(w) = (v·w) v + v² w/2 − 3Φ w` of the rate of the momentum. -/
private def velocityForm (Φ : ℝ) (v w : S) : S := fun k =>
  (∑ j, v j * w j) * v k + (∑ j, v j ^ 2) * w k / 2 - 3 * Φ * w k

private theorem velocityForm_sub (Φ : ℝ) (v w w' : S) (k : Fin 3) :
    velocityForm Φ v w k - velocityForm Φ v w' k = velocityForm Φ v (w - w') k := by
  simp only [velocityForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

private theorem velocityForm_smul (Φ r : ℝ) (v w : S) (k : Fin 3) :
    velocityForm Φ v (r • w) k = r * velocityForm Φ v w k := by
  simp only [velocityForm, Pi.smul_apply, smul_eq_mul, mul_left_comm _ r, ← Finset.mul_sum]
  ring

private theorem abs_velocityForm_le {Φ K V : ℝ} {v w : S} (hΦ : |Φ| ≤ K) (hv : ‖v‖ ≤ V)
    (hV : 0 ≤ V) (k : Fin 3) :
    |velocityForm Φ v w k| ≤ (9 / 2 * V ^ 2 + 3 * K) * ‖w‖ := by
  have h1 := mixedPairing_abs_le (B := v) (v := w) hv le_rfl hV
  have h2 := spatialSquare_le hv hV
  have h3 : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hvk := spaceComponent_abs_le hv k
  have hwk := spaceComponent_abs_le (le_refl ‖w‖) k
  have hw := norm_nonneg w
  have e1 : |(∑ j, v j * w j) * v k| ≤ 3 * V * ‖w‖ * V := by
    rw [abs_mul]
    exact mul_le_mul h1 hvk (abs_nonneg _) (by positivity)
  have e2 : |(∑ j, v j ^ 2) * w k / 2| ≤ 3 * V ^ 2 * ‖w‖ / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg h3, abs_two]
    exact div_le_div_of_nonneg_right (mul_le_mul h2 hwk (abs_nonneg _) (by positivity))
      (by norm_num)
  have e3 : |3 * Φ * w k| ≤ 3 * K * ‖w‖ := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul (by linarith) hwk (abs_nonneg _) (by linarith [abs_nonneg Φ])
  unfold velocityForm
  calc _ ≤ |(∑ j, v j * w j) * v k + (∑ j, v j ^ 2) * w k / 2| + |3 * Φ * w k| := abs_sub _ _
    _ ≤ |(∑ j, v j * w j) * v k| + |(∑ j, v j ^ 2) * w k / 2| + |3 * Φ * w k| :=
      add_le_add_left (abs_add_le _ _) _
    _ ≤ _ := by nlinarith

/-- The velocity-dependent residual of the Euler–Lagrange equations at order `c⁻²`, in terms of
the potential `Φ`, the derivatives `g = ∂Φ`, `ψ' = ∂ψ`, `b = ∂B` and the velocity. -/
private def elResidual (Φ : ℝ) (g ψ : Fin 4 → ℝ) (b : Fin 4 → Fin 3 → ℝ) (v : S) (k : Fin 3) :
    ℝ :=
  -(3 / 2) * g k.succ * (∑ j, v j ^ 2) - Φ * g k.succ - ψ k.succ + ∑ j, b k.succ j * v j +
    3 * (g 0 + ∑ j, v j * g j.succ) * v k - (b 0 k + ∑ j, v j * b j.succ k)

private theorem BoundedOn.elResidual {α : Type} {T : Set α} {Φ : α → ℝ} {g ψ : α → Fin 4 → ℝ}
    {b : α → Fin 4 → Fin 3 → ℝ} {v : α → S} (hΦ : BoundedOn T Φ)
    (hg : ∀ m, BoundedOn T (fun x => g x m)) (hψ : ∀ m, BoundedOn T (fun x => ψ x m))
    (hb : ∀ m j, BoundedOn T (fun x => b x m j)) (hv : ∀ j, BoundedOn T (fun x => v x j))
    (k : Fin 3) : BoundedOn T (fun x => elResidual (Φ x) (g x) (ψ x) (b x) (v x) k) := by
  unfold PostNewtonian.elResidual
  bounded_on

namespace PostNewtonianMetricFamily

variable {U : Opens E} (f : PostNewtonianMetricFamily U)

private theorem force_sub_momentumRate (c : ℝ) (q : E) (v a : S) (k : Fin 3) :
    f.lagrangianForce c q v k - f.momentumRate c q v a k =
      -(a k + coordinatePartial f.potential q k.succ) + epsilon c *
        (elResidual (f.potential q) (fun m => coordinatePartial f.potential q m)
          (fun m => coordinatePartial f.scalarPotential q m)
          (fun m j => coordinatePartial (fun y => f.vectorPotential y j) q m) v k -
        velocityForm (f.potential q) v a k) := by
  simp only [lagrangianForce, momentumRate, elResidual, velocityForm, apply_timeVelocity,
    coordinatePartial]
  ring

private theorem postNewtonianCorrection_eq_residual (q : E) (v : S) (k : Fin 3) :
    f.postNewtonianCorrection q v k =
      elResidual (f.potential q) (fun m => coordinatePartial f.potential q m)
          (fun m => coordinatePartial f.scalarPotential q m)
          (fun m j => coordinatePartial (fun y => f.vectorPotential y j) q m) v k -
        velocityForm (f.potential q) v (fun j => -coordinatePartial f.potential q j.succ) k := by
  simp only [postNewtonianCorrection, elResidual, velocityForm, Fin.sum_univ_three]
  ring

/-- **The Euler–Lagrange acceleration of the test-body Lagrangian (§106).** For a body of mass
`m ≠ 0` on a `C²` path that satisfies the Euler–Lagrange equations of `lagrangian m c` at time
`t`, with `‖ẋ(t)‖ ≤ V`, the acceleration is `−∇Φ + a₁/c²` up to `C/c⁴`, with one constant for
all `c ≥ c₁`. -/
theorem eulerLagrange_acceleration_error {V : ℝ} (hV : 0 ≤ V) :
    ∃ C c₁, 0 ≤ C ∧ 1 ≤ c₁ ∧ ∀ m c, m ≠ 0 → c₁ ≤ c → ∀ x : ℝ → S, ContDiff ℝ 2 x → ∀ t,
      (Fin.cons t (x t) : E) ∈ U → ‖deriv x t‖ ≤ V →
      Mechanics.eulerLagrange (f.lagrangian m c) x t = 0 →
      ‖deriv (deriv x) t - f.postNewtonianAcceleration c (Fin.cons t (x t)) (deriv x t)‖ ≤
        C / c ^ 4 := by
  have hK := f.bound_nonneg
  set K := f.bound
  set M := 9 / 2 * V ^ 2 + 3 * K
  have hM : 0 ≤ M := by positivity
  set T : Set (E × S) := {p | p.1 ∈ U ∧ ‖p.2‖ ≤ V}
  have hd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {q : E}
      (hg : ContDiffOn ℝ ∞ g U) (hq : q ∈ U) : DifferentiableAt ℝ g q :=
    (hg.contDiffAt (U.isOpen.mem_nhds hq)).differentiableAt (by simp)
  have hR (k : Fin 3) : BoundedOn T (fun p => elResidual (f.potential p.1)
      (fun m => coordinatePartial f.potential p.1 m)
      (fun m => coordinatePartial f.scalarPotential p.1 m)
      (fun m j => coordinatePartial (fun y => f.vectorPotential y j) p.1 m) p.2 k) := by
    refine BoundedOn.elResidual ?_ (fun m => ?_) (fun m => ?_) (fun m j => ?_) (fun j => ?_) k
    · exact BoundedOn.of_le fun p hp => by
        simpa only [Real.norm_eq_abs] using f.potential_bound.value _ hp.1
    · exact BoundedOn.of_le fun p hp =>
        abs_coordinatePartial_le (f.potential_bound.first _ hp.1) m
    · exact BoundedOn.of_le fun p hp =>
        abs_coordinatePartial_le (f.scalar_bound.first _ hp.1) m
    · exact BoundedOn.of_le fun p hp => by
        rw [coordinatePartial, coordinatePartial_apply (hd f.vector_smooth hp.1),
          ← Real.norm_eq_abs]
        exact (norm_le_pi_norm _ j).trans
          (norm_fderiv_apply_le (f.vector_bound.first _ hp.1) m)
    · exact BoundedOn.of_le fun p hp => spaceComponent_abs_le hp.2 j
  choose Rk hRk0 hRk using hR
  set R := ∑ k, Rk k
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun k _ => hRk0 k
  have hRle (k : Fin 3) : Rk k ≤ R := Finset.single_le_sum (fun j _ => hRk0 j) (Finset.mem_univ k)
  refine ⟨M * (R + 2 * M * (K + R)), 2 * M + 1, by positivity, by linarith, ?_⟩
  intro m c hm hc x hx t ht hv hEL
  set q : E := Fin.cons t (x t)
  set v := deriv x t
  set a := deriv (deriv x) t
  have hc1 : 1 ≤ c := by linarith
  have hε0 := epsilon_nonneg c
  have hε1 := epsilon_le_one hc1
  have hεM : epsilon c * M ≤ 1 / 2 := by
    have hc2 : 2 * M < c ^ 2 := by nlinarith [sq_nonneg (c - 1)]
    have h : M / c ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    simpa only [epsilon, div_eq_mul_inv, mul_comm] using h
  obtain ⟨r, hr_def⟩ : ∃ r : S, r = fun k => elResidual (f.potential q)
      (fun m => coordinatePartial f.potential q m)
      (fun m => coordinatePartial f.scalarPotential q m)
      (fun m j => coordinatePartial (fun y => f.vectorPotential y j) q m) v k := ⟨_, rfl⟩
  have hr : ‖r‖ ≤ R := (pi_norm_le_iff_of_nonneg hR0).mpr fun k => by
    rw [Real.norm_eq_abs, hr_def]
    exact (hRk k (q, v) ⟨ht, hv⟩).trans (hRle k)
  have hΦ : |f.potential q| ≤ K := by
    simpa only [Real.norm_eq_abs] using f.potential_bound.value _ ht
  have hg (k : Fin 3) : |coordinatePartial f.potential q k.succ| ≤ K :=
    abs_coordinatePartial_le (f.potential_bound.first _ ht) k.succ
  have hQ (w : S) : ‖velocityForm (f.potential q) v w‖ ≤ M * ‖w‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => by
      rw [Real.norm_eq_abs]
      exact abs_velocityForm_le hΦ hv hV k
  -- the Euler–Lagrange equations
  have hkey (k : Fin 3) : a k + coordinatePartial f.potential q k.succ =
      epsilon c * (r k - velocityForm (f.potential q) v a k) := by
    have h := f.eulerLagrange_lagrangian m c hx ht k
    rw [hEL, zero_apply, eq_comm, mul_eq_zero, or_iff_right hm, sub_eq_zero] at h
    have h' := f.force_sub_momentumRate c q v a k
    rw [h, sub_self] at h'
    rw [hr_def]
    linear_combination h'
  obtain ⟨w, hw_def⟩ : ∃ w : S, w = fun k => r k - velocityForm (f.potential q) v a k :=
    ⟨_, rfl⟩
  -- a priori bound on the acceleration
  have ha : ‖a‖ ≤ 2 * (K + R) := by
    have hw : ‖w‖ ≤ R + M * ‖a‖ :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => by
        rw [Real.norm_eq_abs, hw_def]
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · exact (spaceComponent_abs_le hr k)
        · exact (spaceComponent_abs_le (hQ a) k)
    have hak : ‖a‖ ≤ K + R + epsilon c * M * ‖a‖ :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => by
        rw [Real.norm_eq_abs]
        have h := hkey k
        have hwk := spaceComponent_abs_le hw k
        calc |a k| = |-coordinatePartial f.potential q k.succ + epsilon c * w k| := by
              rw [hw_def, ← h]; ring_nf
          _ ≤ K + epsilon c * (R + M * ‖a‖) := by
              refine (abs_add_le _ _).trans (add_le_add (by rw [abs_neg]; exact hg k) ?_)
              rw [abs_mul, abs_of_nonneg hε0]
              exact mul_le_mul_of_nonneg_left hwk hε0
          _ ≤ K + R + epsilon c * M * ‖a‖ := by nlinarith
    nlinarith [norm_nonneg a]
  have hw : ‖w‖ ≤ R + M * (2 * (K + R)) :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => by
      rw [Real.norm_eq_abs, hw_def]
      refine (abs_sub _ _).trans (add_le_add (spaceComponent_abs_le hr k) ?_)
      exact (spaceComponent_abs_le (hQ a) k).trans (mul_le_mul_of_nonneg_left ha hM)
  -- the exact identity
  have hsum : (fun j => a j - -coordinatePartial f.potential q j.succ) = epsilon c • w := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, hw_def]
    linear_combination hkey j
  have hc4 : epsilon c ^ 2 = 1 / c ^ 4 := by
    rw [epsilon, inv_pow, ← pow_mul, one_div]
  refine (pi_norm_le_iff_of_nonneg (div_nonneg (by positivity) (by positivity))).mpr fun k => ?_
  have hid : a k - f.postNewtonianAcceleration c q v k =
      -(epsilon c ^ 2 * velocityForm (f.potential q) v w k) := by
    have h1 := velocityForm_sub (f.potential q) v a
      (fun j => -coordinatePartial f.potential q j.succ) k
    rw [show a - (fun j => -coordinatePartial f.potential q j.succ) =
      (fun j => a j - -coordinatePartial f.potential q j.succ) from rfl, hsum,
      velocityForm_smul] at h1
    have hrk := congrFun hr_def k
    rw [postNewtonianAcceleration, f.postNewtonianCorrection_eq_residual]
    linear_combination hkey k + epsilon c * hrk - epsilon c * h1
  rw [Pi.sub_apply, Real.norm_eq_abs, hid, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg _), hc4,
    one_div_mul_eq_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc |velocityForm (f.potential q) v w k| ≤ M * ‖w‖ := (spaceComponent_abs_le (hQ w) k)
    _ ≤ M * (R + 2 * M * (K + R)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      linarith

/-- **The Euler–Lagrange hypothesis is satisfiable.** At every point of the domain and for
`3K < c²`, `c ≥ 1`, the quadratic path through `x₀` at rest at time `t` with the acceleration
`a = (−∇Φ − (Φ∇Φ + ∇ψ + ∂_t B)/c²)/(1 − 3Φ/c²)` satisfies the Euler–Lagrange equations of the
test-body Lagrangian at `t`. -/
theorem exists_eulerLagrange_rest (m c : ℝ) (hc : 1 ≤ c) (hsmall : 3 * f.bound < c ^ 2)
    {t : ℝ} {x₀ : S} (h₀ : (Fin.cons t x₀ : E) ∈ U) :
    ∃ x : ℝ → S, ContDiff ℝ 2 x ∧ x t = x₀ ∧ deriv x t = 0 ∧
      Mechanics.eulerLagrange (f.lagrangian m c) x t = 0 := by
  set q : E := Fin.cons t x₀
  have hc0 : 0 < c := by linarith
  have hΦ : |f.potential q| ≤ f.bound := by
    simpa only [Real.norm_eq_abs] using f.potential_bound.value _ h₀
  have hN : 0 < 1 - 3 * epsilon c * f.potential q := by
    have hε : 0 < epsilon c := inv_pos.mpr (by positivity)
    have hεc : epsilon c * c ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
    have h1 : 3 * epsilon c * f.potential q ≤ 3 * epsilon c * f.bound :=
      mul_le_mul_of_nonneg_left (abs_le.mp hΦ).2 (by positivity)
    have h2 := mul_lt_mul_of_pos_left hsmall hε
    linarith
  set a : S := fun k => (-coordinatePartial f.potential q k.succ + epsilon c *
    (-(f.potential q * coordinatePartial f.potential q k.succ) -
      coordinatePartial f.scalarPotential q k.succ -
      coordinatePartial (fun y => f.vectorPotential y k) q 0)) /
    (1 - 3 * epsilon c * f.potential q)
  set x : ℝ → S := fun s => x₀ + ((s - t) ^ 2 / 2) • a
  have hx' (s : ℝ) : HasDerivAt x ((s - t) • a) s := by
    have h1 : HasDerivAt (fun s : ℝ => (s - t) ^ 2 / 2) (s - t) s := by
      have h := (((hasDerivAt_id' s).sub_const t).pow 2).div_const 2
      convert h using 1
      ring
    exact (h1.smul_const a).const_add x₀
  have hdx : deriv x = fun s => (s - t) • a := funext fun s => (hx' s).deriv
  have hddx : deriv (deriv x) t = a := by
    rw [hdx]
    have h := ((hasDerivAt_id' t).sub_const t).smul_const a
    simpa using h.deriv
  have hxt : x t = x₀ := by simp [x]
  have hvt : deriv x t = 0 := by simp [hdx]
  have hxs : ContDiff ℝ 2 x := by
    simp only [x]
    fun_prop
  refine ⟨x, hxs, hxt, hvt, ContinuousLinearMap.ext fun w => ?_⟩
  have hw : w = ∑ k, w k • (Pi.single k 1 : S) := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one]
    exact (Finset.univ_sum_single w).symm
  rw [hw, map_sum, zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, smul_eq_zero]
  right
  rw [f.eulerLagrange_lagrangian m c hxs (by rwa [hxt]) k, hxt, hvt, hddx]
  have hak : (1 - 3 * epsilon c * f.potential q) * a k =
      -coordinatePartial f.potential q k.succ + epsilon c *
        (-(f.potential q * coordinatePartial f.potential q k.succ) -
          coordinatePartial f.scalarPotential q k.succ -
          coordinatePartial (fun y => f.vectorPotential y k) q 0) := by
    simp only [a]
    field_simp
  have hF : f.lagrangianForce c q 0 k = -coordinatePartial f.potential q k.succ + epsilon c *
      (-(f.potential q * coordinatePartial f.potential q k.succ) -
        coordinatePartial f.scalarPotential q k.succ) := by
    simp [lagrangianForce]
  have hP : f.momentumRate c q 0 a k = a k + epsilon c * (-(3 * f.potential q * a k) +
      coordinatePartial (fun y => f.vectorPotential y k) q 0) := by
    simp [momentumRate, apply_timeVelocity, coordinatePartial]
  show m * (f.lagrangianForce c q 0 k - f.momentumRate c q 0 a k) = 0
  rw [hF, hP]
  linear_combination (-m) * hak

/-- **Geodesics and the test-body Lagrangian agree to `c⁻⁴`.** For a path satisfying the
Euler–Lagrange equations of the test-body Lagrangian at `t`, its acceleration differs from the
coordinate-time geodesic acceleration of the family at the same position and velocity by at most
`C/c⁴`, uniformly for `c ≥ c₁`. -/
theorem eulerLagrange_sub_acceleration {V : ℝ} (hV : 0 ≤ V) :
    ∃ C c₁, 0 ≤ C ∧ 1 ≤ c₁ ∧ ∀ m c, m ≠ 0 → c₁ ≤ c → ∀ x : ℝ → S, ContDiff ℝ 2 x → ∀ t,
      (Fin.cons t (x t) : E) ∈ U → ‖deriv x t‖ ≤ V →
      Mechanics.eulerLagrange (f.lagrangian m c) x t = 0 →
      ‖deriv (deriv x) t - f.acceleration c (Fin.cons t (x t)) (deriv x t)‖ ≤ C / c ^ 4 := by
  obtain ⟨C₁, hC₁, h₁⟩ := f.acceleration_error hV
  obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := f.eulerLagrange_acceleration_error hV
  refine ⟨C₁ + C₂, max c₂ (24 * f.bound + 2), by positivity, le_max_of_le_left hc₂, ?_⟩
  intro m c hm hc x hx t ht hv hEL
  have e₁ := h₁ c (le_of_max_le_right hc) _ ht _ hv
  have e₂ := h₂ m c hm (le_of_max_le_left hc) x hx t ht hv hEL
  calc _ = ‖(deriv (deriv x) t - f.postNewtonianAcceleration c (Fin.cons t (x t)) (deriv x t)) -
        (f.acceleration c (Fin.cons t (x t)) (deriv x t) -
          f.postNewtonianAcceleration c (Fin.cons t (x t)) (deriv x t))‖ := by
        congr 1
        abel
    _ ≤ _ := norm_sub_le _ _
    _ ≤ C₂ / c ^ 4 + C₁ / c ^ 4 := add_le_add e₂ e₁
    _ = (C₁ + C₂) / c ^ 4 := by ring

end PostNewtonianMetricFamily

end ProjectAinos.GeneralRelativity.PostNewtonian
