module

public import ProjectAInos.Thermodynamics.BoundaryDifferentiability
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Local uniqueness of adiabat graphs

Along a straight segment of work coordinates, the difference between two
graphs satisfies a Grönwall estimate. Local Lipschitz continuity of pressure
therefore makes coincident boundary graphs agree in a neighborhood.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical

/-- A differential bound by the difference itself forces equality along a
segment, when the two graph values agree at its first endpoint. -/
theorem eq_of_segment_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (f' g' : E → E →L[ℝ] ℝ) (a b : E) (K : ℝ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt f (f' (a + t • (b - a))) (a + t • (b - a)))
    (hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt g (g' (a + t • (b - a))) (a + t • (b - a)))
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖f' (a + t • (b - a)) - g' (a + t • (b - a))‖ ≤
        K * ‖f (a + t • (b - a)) - g (a + t • (b - a))‖)
    (ha : f a = g a) : f b = g b := by
  let γ : ℝ → E := fun t => a + t • (b - a)
  let h : ℝ → ℝ := fun t => f (γ t) - g (γ t)
  let h' : ℝ → ℝ := fun t => (f' (γ t) - g' (γ t)) (b - a)
  have hγ' (t : ℝ) : HasDerivAt γ (b - a) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (b - a)).const_add a
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt h (h' t) t := by
    exact ((hf t ht).comp_hasDerivAt t (hγ' t)).sub
      ((hg t ht).comp_hasDerivAt t (hγ' t))
  have hcontinuous : ContinuousOn h (Icc (0 : ℝ) 1) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hderivwithin : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt h (h' t) (Ici t) t :=
    fun t ht => (hderiv t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt
  have hzero : h 0 = 0 := by simp [h, γ, ha]
  have hnorm (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖h' t‖ ≤ (K * ‖b - a‖) * ‖h t‖ := by
    calc
      ‖h' t‖ ≤ ‖f' (γ t) - g' (γ t)‖ * ‖b - a‖ :=
        (f' (γ t) - g' (γ t)).le_opNorm _
      _ ≤ (K * ‖h t‖) * ‖b - a‖ :=
        mul_le_mul_of_nonneg_right (hbound t ⟨ht.1, ht.2.le⟩) (norm_nonneg _)
      _ = _ := by ring
  have hfinal := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hcontinuous hderivwithin hzero hnorm 1 (by norm_num)
  simpa [h, γ, sub_eq_zero] using hfinal

/-- Local uniqueness for scalar graphs whose derivative is a locally Lipschitz
function of the graph point. The range is not assumed to have a global bound. -/
theorem eventually_eq_of_graph_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (Q : ℝ × E → E →L[ℝ] ℝ) (Ω : Set (ℝ × E))
    (hopen : IsOpen Ω) (hQ : LocallyLipschitzOn Ω Q)
    (a : E) (haΩ : (f a, a) ∈ Ω) (ha : f a = g a)
    (U : Set E) (hU : U ∈ 𝓝 a)
    (hf : ∀ w ∈ U, HasFDerivAt f (Q (f w, w)) w)
    (hg : ∀ w ∈ U, HasFDerivAt g (Q (g w, w)) w) :
    ∀ᶠ w in 𝓝 a, f w = g w := by
  obtain ⟨K, T, hT, hLip⟩ := hQ haΩ
  rw [hopen.nhdsWithin_eq haΩ] at hT
  have hfc : ContinuousAt (fun w => (f w, w)) a :=
    (hf a (mem_of_mem_nhds hU)).continuousAt.prodMk continuousAt_id
  have hgc : ContinuousAt (fun w => (g w, w)) a :=
    (hg a (mem_of_mem_nhds hU)).continuousAt.prodMk continuousAt_id
  have hfT : {w | (f w, w) ∈ T} ∈ 𝓝 a := hfc.tendsto.eventually_mem hT
  have hgT : {w | (g w, w) ∈ T} ∈ 𝓝 a :=
    hgc.tendsto.eventually_mem (by simpa only [ha] using hT)
  have hN : U ∩ {w | (f w, w) ∈ T} ∩ {w | (g w, w) ∈ T} ∈ 𝓝 a :=
    inter_mem (inter_mem hU hfT) hgT
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
  filter_upwards [Metric.ball_mem_nhds a hε] with b hb
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      a + t • (b - a) ∈ Metric.ball a ε := by
    have h := convex_ball a ε (Metric.mem_ball_self hε) hb
      (sub_nonneg.mpr ht.2) ht.1 (show 1 - t + t = (1 : ℝ) by ring)
    convert h using 1
    module
  apply eq_of_segment_derivative_bound f g
    (fun w => Q (f w, w)) (fun w => Q (g w, w)) a b (K : ℝ)
  · intro t ht
    exact hf _ (hball (hseg t ht)).1.1
  · intro t ht
    exact hg _ (hball (hseg t ht)).1.1
  · intro t ht
    have hmem := hball (hseg t ht)
    have h := hLip.dist_le_mul _ hmem.1.2 _ hmem.2
    simpa [dist_eq_norm, Prod.norm_def] using h
  · exact ha

namespace SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- LY 3.6, local uniqueness: two adiabat graphs that meet coincide on a
neighborhood of the meeting work coordinate. -/
theorem boundaryEnergy_eventually_eq (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain)
    {v : WorkCoordinates n} (hvx : v ∈ S.boundaryDomain x) (hvy : v ∈ S.boundaryDomain y)
    (heq : S.boundaryEnergy x v = S.boundaryEnergy y v) :
    ∀ᶠ w in 𝓝 v, S.boundaryEnergy x w = S.boundaryEnergy y w := by
  let Q : SimpleCoordinates n → WorkCoordinates n →L[ℝ] ℝ :=
    fun z => pressureDerivative (S.pressure z)
  have hQ : LocallyLipschitzOn S.domain Q := by
    intro z hz
    obtain ⟨K, T, hT, hLip⟩ := S.pressure_locallyLipschitz hz
    let D : WorkCoordinates n →L[ℝ] (WorkCoordinates n →L[ℝ] ℝ) :=
      pressureDerivativeLinear.toContinuousLinearMap
    exact ⟨‖D‖₊ * K, T, hT, D.lipschitzWith.comp_lipschitzOnWith hLip⟩
  apply eventually_eq_of_graph_derivative (S.boundaryEnergy x) (S.boundaryEnergy y)
    Q S.domain S.isOpen_domain hQ v (S.boundaryEnergy_mem hvx).1 heq
    (S.boundaryDomain x ∩ S.boundaryDomain y)
    (inter_mem ((S.boundaryDomain_isOpen hpositive hx).mem_nhds hvx)
      ((S.boundaryDomain_isOpen hpositive hy).mem_nhds hvy))
  · intro w hw
    exact S.boundaryEnergy_hasFDerivAt hpositive hx hw.1
  · intro w hw
    exact S.boundaryEnergy_hasFDerivAt hpositive hy hw.2

end SimpleSystem

end ProjectAInos.Thermodynamics.Physical
