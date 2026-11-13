/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianMetric
public import ProjectAInos.GeneralRelativity.ProperTimeParameter
public import ProjectAInos.SmoothGeometry.Lorentzian.Geodesic

/-! # Coordinate-time acceleration from the actual Lorentz connection

Using physical time as parameter introduces a non-affine correction. The
coefficient below is extracted from the native connection; it is not an
independently assumed Newtonian equation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open ContinuousLinearMap Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity
open SmoothGeometry LorentzMetric NewtonianMetricFamily

local notation "E" => NewtonianCoordinates
local notation "I" => 𝓘(ℝ, E)

/-- Local physical-time parametrization fixes both time derivatives. -/
theorem coordinateTime_derivatives {q : ℝ → E} {t : ℝ} (hq : ContDiffAt ℝ 2 q t)
    (hclock : (fun s => q s 0) =ᶠ[𝓝 t] id) :
    deriv q t 0 = 1 ∧ deriv (deriv q) t 0 = 0 := by
  have hd : (fun s => deriv q s 0) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [hq.eventually (by norm_num), hclock.deriv] with s hs hc
    have hp := (proj 0 : E →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s
      (hs.differentiableAt (by norm_num)).hasDerivAt
    simpa only [deriv_id'', Function.id_def, ContinuousLinearMap.proj_apply] using hp.deriv.symm.trans hc
  refine ⟨hd.self_of_nhds, ?_⟩
  have hp := (proj 0 : E →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
    ((hq.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  simpa only [deriv_const, ContinuousLinearMap.proj_apply] using hp.deriv.symm.trans hd.deriv_eq

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]
  (g : LorentzMetric .timeNegative 3 M)

/-- `-Γⁱ(w,w) + vⁱ Γᵗ(w,w)`, where `w=(1,v)`. The second term is essential
when a non-affine coordinate time replaces the affine geodesic parameter. -/
def coordinateTimeAcceleration (e : OpenPartialHomeomorph M E) (q : E)
    (v : NewtonianSpace) : NewtonianSpace := fun k =>
  -(∑ i : Fin 4, ∑ j : Fin 4, g.chartChristoffel e (e.symm q) k.succ i j *
    timeVelocity v i * timeVelocity v j) +
  v k * (∑ i : Fin 4, ∑ j : Fin 4, g.chartChristoffel e (e.symm q) 0 i j *
    timeVelocity v i * timeVelocity v j)

/-- The coordinate-time ODE is equivalent to tangential native acceleration.
The time equation determines its tangential factor, so none is postulated. -/
theorem tangential_iff_coordinateTime {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {γ : ℝ → M} {t : ℝ}
    (hx : γ t ∈ e.source) (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hclock : (fun s => e (γ s) 0) =ᶠ[𝓝 t] id) :
    (∃ a : ℝ, g.covariantAlong (curveVelocity γ) t = a • curveVelocity γ t) ↔
      ∀ k : Fin 3, deriv (deriv (e ∘ γ)) t k.succ =
        coordinateTimeAcceleration g e (e (γ t)) (fun j => deriv (e ∘ γ) t j.succ) k := by
  have hq : ContDiffAt ℝ 2 (e ∘ γ) t :=
    (((contMDiffAt_of_mem_maximalAtlas he hx).of_le (by norm_num)).comp t hγ).contDiffAt
  obtain ⟨hv, ha⟩ := coordinateTime_derivatives hq hclock
  have hw : timeVelocity (fun j => deriv (e ∘ γ) t j.succ) = deriv (e ∘ γ) t := by
    ext i
    refine Fin.cases ?_ (fun _ => rfl) i
    exact hv.symm
  have hvel := chartTangentMap_curveVelocity he hx (hγ.mdifferentiableAt (by norm_num))
  let T := ∑ i : Fin 4, ∑ j : Fin 4, g.chartChristoffel e (γ t) 0 i j *
    deriv (e ∘ γ) t i * deriv (e ∘ γ) t j
  constructor
  · rintro ⟨a, h⟩ k
    have hh (l : Fin 4) := congrArg (fun z => chartTangentMap e (γ t) z l) h
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, hvel,
      g.covariantAcceleration_coordinates he hx hγ] at hh
    have ht : T = a := by simpa only [ha, hv, zero_add, mul_one] using hh 0
    simp only [coordinateTimeAcceleration, e.left_inv hx, hw]
    have hs := hh k.succ
    change _ + _ = a * _ at hs
    dsimp only [T] at ht
    rw [ht]
    linarith
  · intro h
    refine ⟨T, ?_⟩
    apply (chartTangentEquiv he hx).injective
    ext l
    simp only [chartTangentEquiv_apply, map_smul, Pi.smul_apply, smul_eq_mul, hvel,
      g.covariantAcceleration_coordinates he hx hγ]
    refine Fin.cases ?_ (fun k => ?_) l
    · simp only [ha, hv, zero_add, mul_one]
      rfl
    · have hk := h k
      simp only [coordinateTimeAcceleration, e.left_inv hx, hw] at hk
      dsimp only [T]
      linarith

/-- An affine geodesic reparametrized by a regular physical-time clock obeys
the coordinate-time equation, including its non-affine correction. -/
theorem coordinateTime_of_affine_reparam {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {γ : ℝ → M} {r : ℝ → ℝ} {t : ℝ}
    (hx : γ (r t) ∈ e.source) (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (r t))
    (hr : ContDiffAt ℝ 2 r t) (hn : deriv r t ≠ 0)
    (hgeo : g.covariantAlong (curveVelocity γ) (r t) = 0)
    (hclock : (fun s => e (γ (r s)) 0) =ᶠ[𝓝 t] id) :
    ∀ k : Fin 3, deriv (deriv (e ∘ γ ∘ r)) t k.succ =
      coordinateTimeAcceleration g e (e (γ (r t)))
        (fun j => deriv (e ∘ γ ∘ r) t j.succ) k := by
  apply (tangential_iff_coordinateTime (γ := γ ∘ r) (t := t) g he hx
    (hγ.comp t hr.contMDiffAt) hclock).mp
  refine ⟨deriv (deriv r) t / deriv r t, ?_⟩
  rw [g.covariantAcceleration_reparam hγ hr, hgeo, smul_zero, add_zero,
    curveVelocity_comp (hγ.mdifferentiableAt (by norm_num)) (hr.differentiableAt (by norm_num)),
    smul_smul, div_mul_cancel₀ _ hn]

/-- Local regularity of the actual coordinate-time acceleration follows
from the smooth native connection. Uniform Lipschitz constants need the
additional quantitative metric-family estimates. -/
theorem coordinateTimeAcceleration_contDiffAt {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {z : E × NewtonianSpace}
    (hz : z.1 ∈ e.target) :
    ContDiffAt ℝ ∞ (fun y : E × NewtonianSpace => coordinateTimeAcceleration g e y.1 y.2) z := by
  have hc (k i j : Fin 4) :
      ContDiffAt ℝ ∞ (fun y : E × NewtonianSpace =>
        g.chartChristoffel e (e.symm y.1) k i j) z :=
    (((g.chartChristoffel_contMDiffAt he (e.map_target hz) k i j).comp z.1
      (contMDiffAt_symm_of_mem_maximalAtlas he hz)).contDiffAt).comp z contDiffAt_fst
  have hw (i : Fin 4) :
      ContDiffAt ℝ ∞ (fun y : E × NewtonianSpace => timeVelocity y.2 i) z := by
    refine Fin.cases contDiffAt_const (fun j => ?_) i
    change ContDiffAt ℝ ∞ (fun y : E × NewtonianSpace => y.2 j) z
    fun_prop
  have hsum (k : Fin 4) := ContDiffAt.sum (fun i (_ : i ∈ Finset.univ) =>
    ContDiffAt.sum (fun j (_ : j ∈ Finset.univ) => ((hc k i j).mul (hw i)).mul (hw j)))
  apply contDiffAt_pi.mpr
  intro k
  have hv : ContDiffAt ℝ ∞ (fun y : E × NewtonianSpace => y.2 k) z := by fun_prop
  exact (hsum k.succ).neg.add (hv.mul (hsum 0))

end ProjectAInos.GeneralRelativity
