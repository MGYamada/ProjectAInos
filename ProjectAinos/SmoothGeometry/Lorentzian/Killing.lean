/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Geodesic
public import ProjectAinos.SmoothGeometry.Lorentzian.Curvature
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.AlongCurveReparam

/-!
# Killing fields, conserved pairings and the red shift

A vector field `K` of a Lorentz manifold is a Killing field when it satisfies the Killing
equation `g(∇_v K, w) + g(v, ∇_w K) = 0` at every event (`IsKillingField`).

* `IsKillingField.pairing_eq`: along an affinely parametrized geodesic, on any convex set of
  parameters, the pairing `g(K, γ̇)` is constant.
* `killingNorm`, `stationaryVelocity`, `observedFrequency`: where `K` is timelike, the observer
  that moves along `K` has the unit velocity `u = K/N` with `N = √(−g(K, K))`, and measures the
  frequency `ω = −g(u, γ̇)` of a ray `γ`. `killingNorm_mul_observedFrequency_eq` is the red shift
  `N(γ(a)) ω(a) = N(γ(b)) ω(b)` along a given geodesic segment (Landau–Lifshitz, §88).
* `killing_chartField_of`: in a chart, the co-ordinate field `∂_k` satisfies the Killing
  equation at an event where the components of the metric do not change along `∂_k`;
  `CoordinateMetric.isKillingField_chartField`, `CoordinateMetric.isKillingField_of_invariant`:
  for a metric given by coefficients, `∂_k` is a Killing field when the coefficients do not
  depend on `x^k`, for instance when the form is invariant under the translations along `x^k`.

The geodesic is given, on an interval or any convex set of parameters; nothing is assumed about
its completeness, and it need not be null.
-/

@[expose] public section

noncomputable section

open Bundle Set TopologicalSpace VectorField
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

namespace LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The Killing equation `g(∇_v K, w) + g(v, ∇_w K) = 0` at every event. -/
def IsKillingField (g : LorentzMetric σ d M) (K : ∀ x : M, TangentSpace I x) : Prop :=
  ∀ x (v w : TangentSpace I x),
    g.form x (g.leviCivita K x v) w + g.form x v (g.leviCivita K x w) = 0

/-- A Killing field is orthogonal to its own derivative along any direction:
`g(∇_v K, v) = 0`. -/
theorem IsKillingField.form_leviCivita_self {g : LorentzMetric σ d M}
    {K : ∀ x : M, TangentSpace I x} (hK : g.IsKillingField K) (x : M) (v : TangentSpace I x) :
    g.form x (g.leviCivita K x v) v = 0 := by
  have h := hK x v v
  rw [g.symmetric x v] at h
  linarith

/-- Along a geodesic the pairing `g(K, γ̇)` has zero derivative. -/
theorem IsKillingField.hasDerivAt_pairing {g : LorentzMetric σ d M}
    {K : ∀ x : M, TangentSpace I x} (hK : g.IsKillingField K)
    (hKd : ∀ x, MDifferentiableAt I ((I).prod I) (T% K) x) {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn s γ) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (fun r => g.form (γ r) (K (γ r)) (curveVelocity γ r)) 0 t := by
  have hγt : MDifferentiableAt 𝓘(ℝ) I γ t := (hγ t ht).1.mdifferentiableAt (by norm_num)
  have hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun r => TotalSpace.mk' E (γ r) (K (γ r))) t := (hKd (γ t)).comp t hγt
  have hW : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun r => TotalSpace.mk' E (γ r) (curveVelocity γ r)) t :=
    (curveVelocity_contMDiffAt (n := 1) (hγ t ht).1).mdifferentiableAt (by norm_num)
  have h := g.hasDerivAt_pairing_along hγt hV hW
  rw [g.covariantAlong_ambient hγt (hKd (γ t)), (hγ t ht).2, map_zero,
    hK.form_leviCivita_self, zero_add] at h
  exact h

/-- **Conservation of the Killing pairing.** Along a geodesic, on any convex set of parameters,
`g(K, γ̇)` is constant. -/
theorem IsKillingField.pairing_eq {g : LorentzMetric σ d M} {K : ∀ x : M, TangentSpace I x}
    (hK : g.IsKillingField K) (hKd : ∀ x, MDifferentiableAt I ((I).prod I) (T% K) x)
    {γ : ℝ → M} {s : Set ℝ} (hγ : g.IsGeodesicOn s γ) (hs : Convex ℝ s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) :
    g.form (γ a) (K (γ a)) (curveVelocity γ a) = g.form (γ b) (K (γ b)) (curveVelocity γ b) := by
  let f : ℝ → ℝ := fun t => g.form (γ t) (K (γ t)) (curveVelocity γ t)
  have hd (t : ℝ) (ht : t ∈ s) : HasDerivAt f 0 t := hK.hasDerivAt_pairing hKd hγ ht
  apply hs.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (f := f)
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt) _ ha hb
  intro t ht
  by_cases hu : UniqueDiffWithinAt ℝ s t
  · have hf : HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) t := by
      rw [hasFDerivAt_iff_hasDerivAt]
      exact hd t ht
    exact hf.hasFDerivWithinAt.fderivWithin hu
  · exact fderivWithin_zero_of_not_uniqueDiffWithinAt hu

/-! ### Stationary observers and the red shift -/

/-- The norm `N = √(−g(K, K))` of a vector field at an event. -/
def killingNorm (g : LorentzMetric .timeNegative d M) (K : ∀ x : M, TangentSpace I x) (x : M) :
    ℝ :=
  Real.sqrt (-g.form x (K x) (K x))

/-- The velocity `K/N` of the observer that moves along `K`. -/
def stationaryVelocity (g : LorentzMetric .timeNegative d M) (K : ∀ x : M, TangentSpace I x)
    (x : M) : TangentSpace I x :=
  (g.killingNorm K x)⁻¹ • K x

/-- The frequency `ω = −g(u, γ̇)` of the ray `γ` measured at `γ(t)` by the observer with the
velocity `u = K/N`. -/
def observedFrequency (g : LorentzMetric .timeNegative d M) (K : ∀ x : M, TangentSpace I x)
    (γ : ℝ → M) (t : ℝ) : ℝ :=
  -g.form (γ t) (g.stationaryVelocity K (γ t)) (curveVelocity γ t)

theorem killingNorm_pos {g : LorentzMetric .timeNegative d M}
    {K : ∀ x : M, TangentSpace I x} {x : M} (hx : g.form x (K x) (K x) < 0) :
    0 < g.killingNorm K x :=
  Real.sqrt_pos.mpr (neg_pos.mpr hx)

/-- Where `K` is timelike, the observer that moves along `K` has a unit velocity. -/
theorem form_stationaryVelocity {g : LorentzMetric .timeNegative d M}
    {K : ∀ x : M, TangentSpace I x}
    {x : M} (hx : g.form x (K x) (K x) < 0) :
    g.form x (g.stationaryVelocity K x) (g.stationaryVelocity K x) = -1 := by
  have hN := killingNorm_pos (g := g) hx
  have hsq : g.killingNorm K x ^ 2 = -g.form x (K x) (K x) :=
    Real.sq_sqrt (neg_nonneg.mpr hx.le)
  simp only [stationaryVelocity, map_smul, smul_apply, smul_eq_mul]
  field_simp
  linarith

theorem killingNorm_mul_observedFrequency {g : LorentzMetric .timeNegative d M}
    {K : ∀ x : M, TangentSpace I x}
    {γ : ℝ → M} {t : ℝ}
    (ht : g.form (γ t) (K (γ t)) (K (γ t)) < 0) :
    g.killingNorm K (γ t) * g.observedFrequency K γ t =
      -g.form (γ t) (K (γ t)) (curveVelocity γ t) := by
  have hN := (killingNorm_pos (g := g) ht).ne'
  simp only [observedFrequency, stationaryVelocity, map_smul, smul_apply,
    smul_eq_mul]
  field_simp

/-- **The red shift** (Landau–Lifshitz, §88). Let `K` be a Killing field and `γ` a geodesic,
given on a convex set of parameters, and let `K` be timelike at the events `γ(a)` and `γ(b)`.
The frequencies that the observers along `K` measure at these events satisfy
`N(γ(a)) ω(a) = N(γ(b)) ω(b)`. -/
theorem killingNorm_mul_observedFrequency_eq {g : LorentzMetric .timeNegative d M}
    {K : ∀ x : M, TangentSpace I x}
    (hK : g.IsKillingField K)
    (hKd : ∀ x, MDifferentiableAt I ((I).prod I) (T% K) x) {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn s γ) (hs : Convex ℝ s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hta : g.form (γ a) (K (γ a)) (K (γ a)) < 0) (htb : g.form (γ b) (K (γ b)) (K (γ b)) < 0) :
    g.killingNorm K (γ a) * g.observedFrequency K γ a =
      g.killingNorm K (γ b) * g.observedFrequency K γ b := by
  rw [killingNorm_mul_observedFrequency hta, killingNorm_mul_observedFrequency htb,
    hK.pairing_eq hKd hγ hs ha hb]

/-! ### Co-ordinate Killing fields -/

variable {σ' : LorentzConvention}

/-- In a chart, the co-ordinate field `∂_k` satisfies the Killing equation at an event where the
components of the metric do not change along `∂_k`: then `L_{∂_k} g = ∂_k g_{ij} = 0`. -/
theorem killing_chartField_of (g : LorentzMetric σ' d M) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (k : Fin (d + 1))
    (h : ∀ i j, mvfderiv I (fun y => g.chartComponent e y i j) x
      (chartField e (Pi.single k 1) x) = 0) (v w : TangentSpace I x) :
    g.form x (g.leviCivita (chartField e (Pi.single k 1)) x v) w +
      g.form x v (g.leviCivita (chartField e (Pi.single k 1)) x w) = 0 := by
  set K := chartField e (Pi.single k 1)
  have hd (i : Fin (d + 1)) := chartField_mdifferentiableAt he hx (Pi.single i 1)
  have hcomm (i : Fin (d + 1)) :
      g.leviCivita (chartField e (Pi.single i 1)) x (K x) =
        g.leviCivita K x (chartField e (Pi.single i 1) x) := by
    have h := g.covariantField_commutator (hd k) (hd i)
    rw [chartField_bracket he hx] at h
    exact sub_eq_zero.mp h
  have hbasis (i j : Fin (d + 1)) :
      g.form x (g.leviCivita K x (chartField e (Pi.single i 1) x))
          (chartField e (Pi.single j 1) x) +
        g.form x (chartField e (Pi.single i 1) x)
          (g.leviCivita K x (chartField e (Pi.single j 1) x)) = 0 := by
    have hc := g.leviCivita_metricCompatible (K x) (hd i) (hd j)
    rw [← hcomm i, ← hcomm j, ← hc]
    exact h i j
  have hv : v = ∑ i, chartTangentMap e x v i • chartField e (Pi.single i 1) x := by
    conv_lhs => rw [← chartField_tangentMap he hx v]
    exact chartField_eq_sum e x _
  have hw : w = ∑ j, chartTangentMap e x w j • chartField e (Pi.single j 1) x := by
    conv_lhs => rw [← chartField_tangentMap he hx w]
    exact chartField_eq_sum e x _
  rw [hv, hw]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := hbasis j i
  linear_combination (chartTangentMap e x w i * chartTangentMap e x v j) * this

end LorentzMetric

namespace CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-- For a metric given by coefficients on `U`, the co-ordinate field `∂_k` is a Killing field
when the coefficients do not depend on `x^k`. -/
theorem isKillingField_chartField (g : CoordinateMetric σ d U) (x₀ : U) (k : Fin (d + 1))
    (h : ∀ y ∈ U, ∀ i j, fderiv ℝ (fun z => g.coefficient z i j) y (Pi.single k 1) = 0) :
    g.toLorentzMetric.IsKillingField (chartField (physicalChart x₀) (Pi.single k 1)) := by
  intro y v w
  refine g.toLorentzMetric.killing_chartField_of (physicalChart_mem x₀) (by simp) k
    (fun i j => ?_) v w
  rw [toLorentzMetric_component_derivative]
  exact h y y.property i j

/-- A function that is invariant under the translations along `v` has zero derivative along
`v`. -/
theorem fderiv_eq_zero_of_invariant {f : MinkowskiModel d → ℝ} {y v : MinkowskiModel d}
    (hf : DifferentiableAt ℝ f y) (h : ∀ t : ℝ, f (y + t • v) = f y) : fderiv ℝ f y v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h1 : HasDerivAt (fun t : ℝ => f (y + t • v)) (fderiv ℝ f y v) 0 :=
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun t : ℝ => f (y + t • v)) 0 0 := by
    simp only [h]
    exact hasDerivAt_const _ _
  exact h1.unique h2

/-- **A stationary metric.** If the form does not change under the translations along `x^k`,
the co-ordinate field `∂_k` is a Killing field. -/
theorem isKillingField_of_invariant (g : CoordinateMetric σ d U) (x₀ : U) (k : Fin (d + 1))
    (h : ∀ (y : MinkowskiModel d) (t : ℝ), g.form (y + t • Pi.single k 1) = g.form y) :
    g.toLorentzMetric.IsKillingField (chartField (physicalChart x₀) (Pi.single k 1)) := by
  refine g.isKillingField_chartField x₀ k fun y hy i j => ?_
  have hd : DifferentiableAt ℝ (fun z => g.coefficient z i j) y :=
    ((g.coefficient_contDiffOn i j).differentiableOn (by simp) y hy).differentiableAt
      (U.isOpen.mem_nhds hy)
  refine fderiv_eq_zero_of_invariant hd fun t => ?_
  simp only [coefficient, Matrix.of_apply, h]

/-- The co-ordinate fields of `U` are smooth. -/
theorem chartField_mdifferentiableAt (x₀ y : U) (v : MinkowskiModel d) :
    MDifferentiableAt 𝓘(ℝ, MinkowskiModel d) ((𝓘(ℝ, MinkowskiModel d)).prod 𝓘(ℝ, MinkowskiModel d))
      (T% (chartField (physicalChart x₀) v)) y :=
  LorentzMetric.chartField_mdifferentiableAt (physicalChart_mem x₀) (by simp) v

end CoordinateMetric

end ProjectAinos.SmoothGeometry
