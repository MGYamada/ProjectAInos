module

public import ProjectAInos.Thermodynamics.BoundaryGraph
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Differentiability of the adiabat graph

Two supporting inequalities bound the first-order remainder by the change in
the pressure covector. Continuity of pressure therefore gives the full Fréchet
derivative, with no assumption that pressure itself is differentiable.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical

/-- The work-coordinate derivative prescribed by the pressure: `−Σ Pᵢ dVᵢ`. -/
noncomputable def pressureDerivative {n : ℕ} (p : WorkCoordinates n) :
    WorkCoordinates n →L[ℝ] ℝ :=
  ((-pressureForm p).comp (LinearMap.inr ℝ ℝ (WorkCoordinates n))).toContinuousLinearMap

@[simp] theorem pressureDerivative_apply {n : ℕ} (p v : WorkCoordinates n) :
    pressureDerivative p v = -∑ i, p i * v i := by
  simp [pressureDerivative, pressureForm]

/-- The pressure covector depends linearly, and therefore continuously, on the
finite-dimensional pressure vector. -/
noncomputable def pressureDerivativeLinear {n : ℕ} :
    WorkCoordinates n →ₗ[ℝ] (WorkCoordinates n →L[ℝ] ℝ) where
  toFun := pressureDerivative
  map_add' p q := by
    apply ContinuousLinearMap.ext
    intro v
    simp [add_mul, Finset.sum_add_distrib, add_comm]
  map_smul' a p := by
    apply ContinuousLinearMap.ext
    intro v
    simp [mul_assoc, ← Finset.mul_sum]

namespace SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- The derivative covector along the chosen boundary graph. -/
noncomputable def boundaryDerivative (S : SimpleSystem P n) (x : SimpleCoordinates n)
    (v : WorkCoordinates n) : WorkCoordinates n →L[ℝ] ℝ :=
  pressureDerivative (S.pressure (S.boundaryEnergy x v, v))

theorem boundaryDerivative_continuousOn (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) :
    ContinuousOn (S.boundaryDerivative x) (S.boundaryDomain x) := by
  have hgraph : ContinuousOn (fun v => (S.boundaryEnergy x v, v)) (S.boundaryDomain x) :=
    (S.boundaryEnergy_continuousOn hpositive hx).prodMk continuousOn_id
  have hp := S.pressure_locallyLipschitz.continuousOn.comp hgraph
    (fun v hv => (S.boundaryEnergy_mem hv).1)
  exact pressureDerivativeLinear.continuous_of_finiteDimensional.continuousOn.comp hp
    (fun _ _ => mem_univ _)

/-- The lower supporting inequality for the graph. -/
theorem boundaryDerivative_le_sub (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain)
    {v w : WorkCoordinates n} (hv : v ∈ S.boundaryDomain x) (hw : w ∈ S.boundaryDomain x) :
    S.boundaryDerivative x v (w - v) ≤ S.boundaryEnergy x w - S.boundaryEnergy x v := by
  have h := (S.pressure_support_at_boundary hpositive hx (S.boundaryEnergy_mem hv)).2 _
    (S.boundary_subset_sector hx (S.boundaryEnergy_mem hw))
  simp only [LinearMap.neg_apply, pressureForm, LinearMap.coe_mk, AddHom.coe_mk] at h
  simp only [boundaryDerivative, pressureDerivative_apply, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]
  linarith

/-- The upper supporting inequality, using the pressure at the other point. -/
theorem boundaryEnergy_sub_le_derivative (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain)
    {v w : WorkCoordinates n} (hv : v ∈ S.boundaryDomain x) (hw : w ∈ S.boundaryDomain x) :
    S.boundaryEnergy x w - S.boundaryEnergy x v ≤ S.boundaryDerivative x w (w - v) := by
  have h := S.boundaryDerivative_le_sub hpositive hx hw hv
  rw [show v - w = -(w - v) by abel, map_neg] at h
  linarith

/-- LY 3.5(iv): the boundary graph has derivative `−P` at every work coordinate
in its open domain. -/
theorem boundaryEnergy_hasFDerivAt (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain)
    {v : WorkCoordinates n} (hv : v ∈ S.boundaryDomain x) :
    HasFDerivAt (S.boundaryEnergy x) (S.boundaryDerivative x v) v := by
  have hcontinuous := (S.boundaryDerivative_continuousOn hpositive hx).continuousAt
    ((S.boundaryDomain_isOpen hpositive hx).mem_nhds hv)
  have hnorm : Tendsto (fun w => ‖S.boundaryDerivative x w - S.boundaryDerivative x v‖)
      (𝓝 v) (𝓝 0) := by
    have hc : ContinuousAt (fun w => ‖S.boundaryDerivative x w - S.boundaryDerivative x v‖) v :=
      (hcontinuous.sub continuousAt_const).norm
    simpa only [sub_self, norm_zero] using hc.tendsto
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hsmall := hnorm.eventually (gt_mem_nhds hε)
  filter_upwards [(S.boundaryDomain_isOpen hpositive hx).mem_nhds hv, hsmall] with w hw hnormw
  have hlo := S.boundaryDerivative_le_sub hpositive hx hv hw
  have hhi := S.boundaryEnergy_sub_le_derivative hpositive hx hv hw
  have hnonneg : 0 ≤ S.boundaryEnergy x w - S.boundaryEnergy x v -
      S.boundaryDerivative x v (w - v) := by linarith
  calc
    ‖S.boundaryEnergy x w - S.boundaryEnergy x v - S.boundaryDerivative x v (w - v)‖ =
        S.boundaryEnergy x w - S.boundaryEnergy x v - S.boundaryDerivative x v (w - v) :=
      Real.norm_of_nonneg hnonneg
    _ ≤ (S.boundaryDerivative x w - S.boundaryDerivative x v) (w - v) := by
      simp only [sub_apply]
      linarith
    _ ≤ ‖(S.boundaryDerivative x w - S.boundaryDerivative x v) (w - v)‖ := le_abs_self _
    _ ≤ ‖S.boundaryDerivative x w - S.boundaryDerivative x v‖ * ‖w - v‖ :=
      (S.boundaryDerivative x w - S.boundaryDerivative x v).le_opNorm _
    _ ≤ ε * ‖w - v‖ := mul_le_mul_of_nonneg_right hnormw.le (norm_nonneg _)

/-- LY 3.5(iv), regularity of the derivative: the pressure's local Lipschitz
bound composes with the locally Lipschitz graph and the linear covector map. -/
theorem boundaryDerivative_locallyLipschitzOn (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) :
    LocallyLipschitzOn (S.boundaryDomain x) (S.boundaryDerivative x) := by
  intro v hv
  let g : WorkCoordinates n → SimpleCoordinates n := fun w => (S.boundaryEnergy x w, w)
  have hgv : g v ∈ S.domain := (S.boundaryEnergy_mem hv).1
  have hgc : ContinuousAt g v :=
    ((S.boundaryEnergy_continuousOn hpositive hx).continuousAt
      ((S.boundaryDomain_isOpen hpositive hx).mem_nhds hv)).prodMk continuousAt_id
  obtain ⟨K, T, hT, hLip⟩ := S.boundaryEnergy_locallyLipschitzOn hpositive hx hv
  rw [nhdsWithin_eq_nhds.mpr ((S.boundaryDomain_isOpen hpositive hx).mem_nhds hv)] at hT
  obtain ⟨L, U, hU, hPLip⟩ := S.pressure_locallyLipschitz hgv
  rw [nhdsWithin_eq_nhds.mpr (S.isOpen_domain.mem_nhds hgv)] at hU
  have hgLip : LipschitzOnWith (max K 1) g T :=
    hLip.prodMk LipschitzWith.id.lipschitzOnWith
  let D : WorkCoordinates n →L[ℝ] (WorkCoordinates n →L[ℝ] ℝ) :=
    pressureDerivativeLinear.toContinuousLinearMap
  refine ⟨‖D‖₊ * (L * max K 1), T ∩ g ⁻¹' U,
    mem_nhdsWithin_of_mem_nhds (inter_mem hT (hgc.tendsto hU)), ?_⟩
  have hcomp : LipschitzOnWith (L * max K 1) (S.pressure ∘ g) (T ∩ g ⁻¹' U) :=
    hPLip.comp (hgLip.mono inter_subset_left)
      ((mapsTo_preimage g U).mono_left inter_subset_right)
  exact D.lipschitzWith.comp_lipschitzOnWith hcomp

end SimpleSystem

end ProjectAInos.Thermodynamics.Physical
