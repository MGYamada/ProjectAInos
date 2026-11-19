/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateCurvature
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateTangent
public import ProjectAinos.SmoothGeometry.Lorentzian.Geodesic

/-!
# The geodesic equation of a coordinate metric

For a coordinate metric `g` on an open set `U` of the model space, a curve `γ` in `U` is read
through its coordinates `x(t) = (γ t : MinkowskiModel d)`. The derivatives are the ordinary
derivatives `ẋ = deriv x` and `ẍ = deriv (deriv x)` of the coordinates as a function of the
parameter, and the Christoffel symbols are the classical `christoffelOf g.coefficient`. This
compares the native geodesics of `g.toLorentzMetric` with the chart geodesics of the
coefficients (Landau–Lifshitz §87, equation (87.3)):

* `isGeodesicOn_iff`: on an open parameter set where the coordinates are `C²`, `γ` is a
  native geodesic exactly when `ẍ^k + Γ^k_{ij} ẋ^i ẋ^j = 0`;
* `form_curveVelocity`, `pairing_curveVelocity`: the native squared velocity is
  `g_{ij} ẋ^i ẋ^j`, and its pairing with a co-ordinate vector `v` is `g_{ij} v^i ẋ^j`;
* `minkowski_isGeodesicOn_line`: for the Minkowski coordinate metric the affine lines are
  geodesics, since its Christoffel symbols vanish (its coefficients are constant).
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-- A map into `U` is differentiable exactly when its coordinates are. -/
theorem mdifferentiableAt_iff_differentiableAt_val {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : F → U} {p₀ : F} :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, MinkowskiModel d) f p₀ ↔
      DifferentiableAt ℝ (fun p => (f p : MinkowskiModel d)) p₀ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact mdifferentiableAt_iff_differentiableAt.mp
      ((((contMDiff_subtype_val (n := 1) (U := U)) (f p₀)).mdifferentiableAt
        one_ne_zero).comp p₀ h)
  · rw [mdifferentiableAt_iff_target]
    refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr h.continuousAt, ?_⟩
    have he : (extChartAt 𝓘(ℝ, MinkowskiModel d) (f p₀) ∘ f) =
        fun p => (f p : MinkowskiModel d) := by
      funext p
      rw [Function.comp_apply, extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply]
      exact physicalChart_apply (f p₀) (f p)
    rw [he, mdifferentiableAt_iff_differentiableAt]
    exact h

variable (g : CoordinateMetric σ d U)

/-- At a parameter where the curve is `C²`, its covariant acceleration vanishes exactly when
the coordinates satisfy `ẍ^k + Γ^k_{ij} ẋ^i ẋ^j = 0`. -/
theorem covariantAlong_curveVelocity_eq_zero_iff {γ : ℝ → U} {t : ℝ}
    (hγ : ContDiffAt ℝ 2 (fun t => (γ t : MinkowskiModel d)) t) :
    g.toLorentzMetric.covariantAlong (curveVelocity γ) t = 0 ↔ ∀ k : Fin (d + 1),
      deriv (deriv (fun t => (γ t : MinkowskiModel d))) t k +
        ∑ i, ∑ j, christoffelOf g.coefficient (γ t) k i j *
          deriv (fun t => (γ t : MinkowskiModel d)) t i *
            deriv (fun t => (γ t : MinkowskiModel d)) t j = 0 := by
  have he := physicalChart_mem (γ t)
  have hx : γ t ∈ (physicalChart (γ t)).source := by simp
  have hcomp : (physicalChart (γ t) ∘ γ) = fun t' => (γ t' : MinkowskiModel d) :=
    funext fun t' => physicalChart_apply (γ t) (γ t')
  rw [g.toLorentzMetric.geodesic_equation_iff_coordinates he hx
    (contMDiffAt_iff_contDiffAt_val.mpr hγ), hcomp]
  simp only [g.toLorentzMetric_chartChristoffel]

/-- The geodesic equation in the co-ordinates of a coordinate metric (Landau–Lifshitz (87.3)).
On an open parameter set `s` where the coordinates `x(t)` of `γ` are `C²`, `γ` is a native
affine geodesic of `g` exactly when `ẍ^k + Γ^k_{ij} ẋ^i ẋ^j = 0` on `s`, with `ẋ = deriv x`,
`ẍ = deriv (deriv x)` and `Γ = christoffelOf g.coefficient`. -/
theorem isGeodesicOn_iff {γ : ℝ → U} {s : Set ℝ} (hs : IsOpen s)
    (hγ : ContDiffOn ℝ 2 (fun t => (γ t : MinkowskiModel d)) s) :
    g.toLorentzMetric.IsGeodesicOn s γ ↔ ∀ t ∈ s, ∀ k : Fin (d + 1),
      deriv (deriv (fun t => (γ t : MinkowskiModel d))) t k +
        ∑ i, ∑ j, christoffelOf g.coefficient (γ t) k i j *
          deriv (fun t => (γ t : MinkowskiModel d)) t i *
            deriv (fun t => (γ t : MinkowskiModel d)) t j = 0 := by
  have hc (t : ℝ) (ht : t ∈ s) : ContDiffAt ℝ 2 (fun t => (γ t : MinkowskiModel d)) t :=
    hγ.contDiffAt (hs.mem_nhds ht)
  constructor
  · intro h t ht
    exact (g.covariantAlong_curveVelocity_eq_zero_iff (hc t ht)).mp (h t ht).2
  · intro h t ht
    exact ⟨contMDiffAt_iff_contDiffAt_val.mpr (hc t ht),
      (g.covariantAlong_curveVelocity_eq_zero_iff (hc t ht)).mpr (h t ht)⟩

/-- The native squared velocity of a curve is `g_{ij} ẋ^i ẋ^j`, with `ẋ` the derivative of the
coordinates. -/
theorem form_curveVelocity {γ : ℝ → U} {t : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel d)) t) :
    g.toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) =
      ∑ i, ∑ j, g.coefficient (γ t) i j * deriv (fun t => (γ t : MinkowskiModel d)) t i *
        deriv (fun t => (γ t : MinkowskiModel d)) t j := by
  refine (g.form_apply (γ t) (curveVelocity γ t) (curveVelocity γ t)).trans ?_
  rw [curveVelocity_val (mdifferentiableAt_iff_differentiableAt_val.mpr hγ)]

/-- The native pairing `g(v, γ̇)` of a co-ordinate vector `v` with the velocity of a curve is
`g_{ij} v^i ẋ^j`. -/
theorem pairing_curveVelocity {γ : ℝ → U} {t : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel d)) t) (x : U)
    (v : MinkowskiModel d) :
    g.toLorentzMetric.form (γ t) (chartField (physicalChart x) v (γ t)) (curveVelocity γ t) =
      ∑ i, ∑ j, g.coefficient (γ t) i j * v i *
        deriv (fun t => (γ t : MinkowskiModel d)) t j := by
  refine (g.form_apply (γ t) (chartField (physicalChart x) v (γ t)) (curveVelocity γ t)).trans ?_
  rw [physicalChart_chartField,
    curveVelocity_val (mdifferentiableAt_iff_differentiableAt_val.mpr hγ)]

/-- For the Minkowski coordinate metric on any open set `U`, a curve whose coordinates are the
affine line `a + t • b` on an open parameter set `s` is a geodesic on `s`. -/
theorem minkowski_isGeodesicOn_line {γ : ℝ → U} {s : Set ℝ} (hs : IsOpen s)
    (a b : MinkowskiModel d) (hγ : ∀ t ∈ s, (γ t : MinkowskiModel d) = a + t • b) :
    (minkowski σ d U).toLorentzMetric.IsGeodesicOn s γ := by
  have hev (t : ℝ) (ht : t ∈ s) :
      (fun t' => (γ t' : MinkowskiModel d)) =ᶠ[𝓝 t] fun t' => a + t' • b :=
    eventually_of_mem (hs.mem_nhds ht) hγ
  have hline : ContDiff ℝ 2 (fun t : ℝ => a + t • b) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hc : ContDiffOn ℝ 2 (fun t => (γ t : MinkowskiModel d)) s :=
    fun t ht => (hline.contDiffAt.congr_of_eventuallyEq (hev t ht)).contDiffWithinAt
  have hderiv (t : ℝ) (ht : t ∈ s) : deriv (fun t' => (γ t' : MinkowskiModel d)) t = b := by
    rw [(hev t ht).deriv_eq]
    simpa using (((hasDerivAt_id t).smul_const b).const_add a).deriv
  have hΓ (y : MinkowskiModel d) (k i j : Fin (d + 1)) :
      christoffelOf (minkowski σ d U).coefficient y k i j = 0 := by
    simp [christoffelOf, coefficient, minkowski]
  rw [(minkowski σ d U).isGeodesicOn_iff hs hc]
  intro t ht k
  have hdd : deriv (deriv (fun t' => (γ t' : MinkowskiModel d))) t = 0 := by
    have h : deriv (fun t' => (γ t' : MinkowskiModel d)) =ᶠ[𝓝 t] fun _ => b :=
      eventually_of_mem (hs.mem_nhds ht) hderiv
    rw [h.deriv_eq, deriv_const]
  simp only [hdd, hΓ, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero]

/- The hypotheses of `minkowski_isGeodesicOn_line` are satisfiable: on the whole model space
every affine line is a curve in `U`. -/
example (a b : MinkowskiModel d) :
    (minkowski σ d ⊤).toLorentzMetric.IsGeodesicOn univ
      (fun t => (⟨a + t • b, trivial⟩ : (⊤ : Opens (MinkowskiModel d)))) :=
  minkowski_isGeodesicOn_line isOpen_univ a b fun _ _ => rfl

end ProjectAinos.SmoothGeometry.CoordinateMetric
