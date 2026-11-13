/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Fixed-endpoint manifold variations and localized chart constructions

Only joint C² regularity near the reference segment is required. A smooth
coordinate perturbation supported in one chart is extended by the original
curve outside that chart's parameter region.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Topology

namespace ProjectAInos.Variational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

local notation "I" => 𝓘(ℝ, E)
local notation "J" => 𝓘(ℝ, ℝ × ℝ)

/-- An actual two-parameter family through a fixed reference curve, fixing
both endpoints for nearby variation parameters. -/
structure ManifoldCurveVariation (γ : ℝ → M) (a b : ℝ) where
  family : ℝ × ℝ → M
  reference : ∀ t, family (0, t) = γ t
  regular : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 family (0, t)
  left_fixed : ∀ᶠ ε in 𝓝 (0 : ℝ), family (ε, a) = γ a
  right_fixed : ∀ᶠ ε in 𝓝 (0 : ℝ), family (ε, b) = γ b

/-- A chart perturbation, extended by the reference curve in parameter time. -/
def chartCurveFamily (e : OpenPartialHomeomorph M E) (U : Set ℝ)
    (γ : ℝ → M) (η : ℝ → E) (p : ℝ × ℝ) : M := by
  classical
  exact if p.2 ∈ U then e.symm (e (γ p.2) + p.1 • η p.2) else γ p.2

omit [ChartedSpace E M] in
theorem chartCurveFamily_reference {e : OpenPartialHomeomorph M E} {U : Set ℝ}
    {γ : ℝ → M} (hstay : MapsTo γ U e.source) (η : ℝ → E) (t : ℝ) :
    chartCurveFamily e U γ η (0, t) = γ t := by
  by_cases ht : t ∈ U
  · simp only [chartCurveFamily, ht, ite_true, zero_smul, add_zero, e.left_inv (hstay ht)]
  · simp only [chartCurveFamily, ht, ite_false]

omit [ChartedSpace E M] in
theorem chartCurveFamily_of_zero {e : OpenPartialHomeomorph M E} {U : Set ℝ}
    {γ : ℝ → M} {η : ℝ → E} (hstay : MapsTo γ U e.source) {t : ℝ}
    (hη : η t = 0) (ε : ℝ) : chartCurveFamily e U γ η (ε, t) = γ t := by
  by_cases ht : t ∈ U
  · simp only [chartCurveFamily, ht, ite_true, hη, smul_zero, add_zero, e.left_inv (hstay ht)]
  · simp only [chartCurveFamily, ht, ite_false]

/-- Local regularity at a reference point is enough for the piecewise family.
The support condition provides a neighborhood where the pieces agree. -/
theorem chartCurveFamily_contMDiffAt {e : OpenPartialHomeomorph M E} {U : Set ℝ}
    {γ : ℝ → M} {η : ℝ → E} {t : ℝ}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (hU : IsOpen U)
    (hstay : MapsTo γ U e.source) (hsupport : tsupport η ⊆ U)
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) (hη : ContDiff ℝ 2 η) :
    ContMDiffAt J I 2 (chartCurveFamily e U γ η) (0, t) := by
  by_cases ht : t ∈ U
  · have hx := hstay ht
    have hq : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => e (γ p.2) + p.1 • η p.2) (0, t) :=
      ((((contMDiffAt_of_mem_maximalAtlas he hx).of_le (by simp)).comp t hγ).contDiffAt.comp
        (0, t) contDiffAt_snd).add
          (contDiffAt_fst.smul (hη.contDiffAt.comp (0, t) contDiffAt_snd))
    have hinv : ContMDiffAt I I 2 e.symm (e (γ t) + (0 : ℝ) • η t) := by
      simpa only [zero_smul, add_zero] using
        (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx)).of_le (by simp)
    apply (hinv.comp (0, t) hq.contMDiffAt).congr_of_eventuallyEq
    filter_upwards [(continuous_snd.continuousAt : ContinuousAt (Prod.snd : ℝ × ℝ → ℝ) (0, t))
      (hU.mem_nhds ht)] with p hp
    change p.2 ∈ U at hp
    simp only [chartCurveFamily, hp, ite_true, Function.comp_apply]
  · have hnot : t ∉ tsupport η := fun hs => ht (hsupport hs)
    have hzero : ∀ᶠ s in 𝓝 t, η s = 0 :=
      eventually_of_mem ((isClosed_tsupport η).isOpen_compl.mem_nhds hnot)
        (fun _ hs => image_eq_zero_of_notMem_tsupport hs)
    apply (hγ.comp (0, t) contDiffAt_snd.contMDiffAt).congr_of_eventuallyEq
    filter_upwards [(continuous_snd.continuousAt : ContinuousAt (Prod.snd : ℝ × ℝ → ℝ) (0, t)) hzero] with p hp
    exact chartCurveFamily_of_zero hstay hp p.1

omit [ChartedSpace E M] in
/-- Coordinate velocity in the variation parameter is the prescribed test
vector. The coordinate identity is used only near the reference point. -/
theorem chartCurveFamily_coordinate_hasDerivAt {e : OpenPartialHomeomorph M E} {U : Set ℝ}
    {γ : ℝ → M} (η : ℝ → E) (hstay : MapsTo γ U e.source) {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun ε => e (chartCurveFamily e U γ η (ε, t))) (η t) 0 := by
  have hd : HasDerivAt (fun ε : ℝ => e (γ t) + ε • η t) (η t) 0 := by
    simpa only [zero_add, one_smul, Pi.add_apply, id_eq] using!
      (hasDerivAt_const (0 : ℝ) (e (γ t))).add
        ((hasDerivAt_id (0 : ℝ)).smul_const (η t))
  apply hd.congr_of_eventuallyEq
  have htarget : e (γ t) + (0 : ℝ) • η t ∈ e.target := by
    simpa only [zero_smul, add_zero] using e.map_source (hstay ht)
  filter_upwards [hd.continuousAt (e.open_target.mem_nhds htarget)] with ε hε
  simp only [chartCurveFamily, ht, ite_true, e.right_inv hε]

/-- Construct an admissible manifold variation rather than assuming that
coordinate test fields are realizable by actual curves. -/
def chartCurveVariation {e : OpenPartialHomeomorph M E} {U : Set ℝ}
    {γ : ℝ → M} {η : ℝ → E} {a b : ℝ}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (hU : IsOpen U)
    (hUI : U ⊆ Ioo a b) (hstay : MapsTo γ U e.source) (hsupport : tsupport η ⊆ U)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t) (hη : ContDiff ℝ 2 η) :
    ManifoldCurveVariation (E := E) γ a b where
  family := chartCurveFamily e U γ η
  reference := chartCurveFamily_reference hstay η
  regular := fun t ht => chartCurveFamily_contMDiffAt he hU hstay hsupport (hγ t ht) hη
  left_fixed := Eventually.of_forall fun ε => by
    have ha : a ∉ U := fun ha => (lt_irrefl a) (hUI ha).1
    simp only [chartCurveFamily, ha, ite_false]
  right_fixed := Eventually.of_forall fun ε => by
    have hb : b ∉ U := fun hb => (lt_irrefl b) (hUI hb).2
    simp only [chartCurveFamily, hb, ite_false]

end ProjectAInos.Variational
