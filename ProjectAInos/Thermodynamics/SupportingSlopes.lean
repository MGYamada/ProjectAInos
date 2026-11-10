module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic.Linarith

/-!
# Supporting slopes of concave energy functions

At an interior point of a concave function, the supporting slopes form the
closed interval from the right derivative to the left derivative. Two concave
energy functions attain their constrained sum maximum exactly when those
intervals intersect. No differentiability premise is imposed: concavity gives
the required one-sided derivatives.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace ProjectAInos.Thermodynamics

/-- A line of slope `b` through the graph at `x` bounds the function above. -/
def SupportsSlope (f : ℝ → ℝ) (D : Set ℝ) (x b : ℝ) : Prop :=
  ∀ y ∈ D, f y ≤ f x + b * (y - x)

/-- All supporting slopes at a fixed energy. -/
def supportingSlopes (f : ℝ → ℝ) (D : Set ℝ) (x : ℝ) : Set ℝ :=
  {b | SupportsSlope f D x b}

noncomputable def rightSlope (f : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin f (Ioi x) x
noncomputable def leftSlope (f : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin f (Iio x) x

/-- Concavity supplies the right derivative at every interior point. -/
theorem concave_hasDerivWithinAt_rightSlope {f : ℝ → ℝ} {D : Set ℝ}
    (hf : ConcaveOn ℝ D f) {x : ℝ} (hx : x ∈ interior D) :
    HasDerivWithinAt f (rightSlope f x) (Ioi x) x := by
  have h := (hf.neg.differentiableWithinAt_Ioi_of_mem_interior hx).neg
  have hd : DifferentiableWithinAt ℝ f (Ioi x) x := by simpa only [neg_neg] using h
  exact hd.hasDerivWithinAt

/-- Concavity supplies the left derivative at every interior point. -/
theorem concave_hasDerivWithinAt_leftSlope {f : ℝ → ℝ} {D : Set ℝ}
    (hf : ConcaveOn ℝ D f) {x : ℝ} (hx : x ∈ interior D) :
    HasDerivWithinAt f (leftSlope f x) (Iio x) x := by
  have h := (hf.neg.differentiableWithinAt_Iio_of_mem_interior hx).neg
  have hd : DifferentiableWithinAt ℝ f (Iio x) x := by simpa only [neg_neg] using h
  exact hd.hasDerivWithinAt

theorem concave_rightSlope_le_leftSlope {f : ℝ → ℝ} {D : Set ℝ}
    (hf : ConcaveOn ℝ D f) {x : ℝ} (hx : x ∈ interior D) :
    rightSlope f x ≤ leftSlope f x := by
  have h := hf.neg.leftDeriv_le_rightDeriv_of_mem_interior hx
  simpa only [derivWithin.neg, neg_le_neg_iff, rightSlope, leftSlope] using h

/-- A right derivative is bounded above by every supporting slope. -/
theorem SupportsSlope.right_derivative_le {f : ℝ → ℝ} {D : Set ℝ} {x b d : ℝ}
    (h : SupportsSlope f D x b) (hx : x ∈ interior D)
    (hd : HasDerivWithinAt f d (Ioi x) x) : d ≤ b := by
  apply le_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hd)
  have hD : D ∈ 𝓝[>] x := nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hx)
  filter_upwards [hD, self_mem_nhdsWithin] with y hy (hxy : x < y)
  rw [slope_def_field]
  apply (div_le_iff₀ (sub_pos.mpr hxy)).mpr
  linarith [h y hy]

/-- Every supporting slope is bounded above by the left derivative. -/
theorem SupportsSlope.le_left_derivative {f : ℝ → ℝ} {D : Set ℝ} {x b d : ℝ}
    (h : SupportsSlope f D x b) (hx : x ∈ interior D)
    (hd : HasDerivWithinAt f d (Iio x) x) : b ≤ d := by
  apply ge_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp hd)
  have hD : D ∈ 𝓝[<] x := nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hx)
  filter_upwards [hD, self_mem_nhdsWithin] with y hy (hyx : y < x)
  rw [slope_def_field]
  apply (le_div_iff_of_neg (sub_neg.mpr hyx)).mpr
  linarith [h y hy]

/-- The complete supporting interval is bounded by the one-sided derivatives. -/
theorem supportsSlope_iff {f : ℝ → ℝ} {D : Set ℝ}
    (hf : ConcaveOn ℝ D f) {x b : ℝ} (hx : x ∈ interior D) :
    SupportsSlope f D x b ↔ rightSlope f x ≤ b ∧ b ≤ leftSlope f x := by
  constructor
  · intro h
    exact ⟨h.right_derivative_le hx (concave_hasDerivWithinAt_rightSlope hf hx),
      h.le_left_derivative hx (concave_hasDerivWithinAt_leftSlope hf hx)⟩
  · rintro ⟨hr, hl⟩ y hy
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · have h := (hf.slope_le_of_hasDerivWithinAt_Ioi (interior_subset hx) hy hxy
        (concave_hasDerivWithinAt_rightSlope hf hx)).trans hr
      rw [slope_def_field] at h
      have h' := (div_le_iff₀ (sub_pos.mpr hxy)).mp h
      linarith
    · simp
    · have h := hl.trans (hf.le_slope_of_hasDerivWithinAt_Iio hy (interior_subset hx) hyx
        (concave_hasDerivWithinAt_leftSlope hf hx))
      rw [slope_comm f y x, slope_def_field] at h
      have h' := (le_div_iff_of_neg (sub_neg.mpr hyx)).mp h
      linarith

theorem supportingSlopes_eq_Icc {f : ℝ → ℝ} {D : Set ℝ}
    (hf : ConcaveOn ℝ D f) {x : ℝ} (hx : x ∈ interior D) :
    supportingSlopes f D x = Icc (rightSlope f x) (leftSlope f x) := by
  ext b
  exact supportsSlope_iff hf hx

/-- Interior points always have at least one supporting slope. -/
theorem supportingSlopes_nonempty {f : ℝ → ℝ} {D : Set ℝ}
    (hf : ConcaveOn ℝ D f) {x : ℝ} (hx : x ∈ interior D) :
    (supportingSlopes f D x).Nonempty := by
  rw [supportingSlopes_eq_Icc hf hx]
  exact nonempty_Icc.mpr (concave_rightSlope_le_leftSlope hf hx)

/-- At a larger energy, every supporting slope is no greater than any slope
at a smaller energy. This order fact does not itself require concavity. -/
theorem SupportsSlope.antitone {f : ℝ → ℝ} {D : Set ℝ} {x y b c : ℝ}
    (hb : SupportsSlope f D x b) (hc : SupportsSlope f D y c)
    (hx : x ∈ D) (hy : y ∈ D) (hxy : x < y) : c ≤ b := by
  by_contra h
  have hpos := mul_pos (sub_pos.mpr (lt_of_not_ge h)) (sub_pos.mpr hxy)
  have h₁ := hb y hy
  have h₂ := hc x hx
  nlinarith

/-- A common supporting slope makes the entropy sum maximal at fixed total
energy, even without a concavity hypothesis. -/
theorem isMaxOn_add_reflection_of_common_support
    {f g : ℝ → ℝ} {D₁ D₂ : Set ℝ} {E x b : ℝ}
    (hf : SupportsSlope f D₁ x b) (hg : SupportsSlope g D₂ (E - x) b) :
    IsMaxOn (fun u => f u + g (E - u))
      (D₁ ∩ (fun u => E - u) ⁻¹' D₂) x := by
  intro u hu
  change f u + g (E - u) ≤ f x + g (E - x)
  have h₁ := hf u hu.1
  have h₂ := hg (E - u) hu.2
  nlinarith

/-- A maximum of the fixed-total-energy sum forces the two supporting
intervals to intersect. One-sided differentiability follows from concavity. -/
theorem common_support_of_isMaxOn_add_reflection
    {f g : ℝ → ℝ} {D₁ D₂ : Set ℝ}
    (hf : ConcaveOn ℝ D₁ f) (hg : ConcaveOn ℝ D₂ g)
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) {E x : ℝ}
    (hx : x ∈ D₁) (hy : E - x ∈ D₂)
    (hmax : IsMaxOn (fun u => f u + g (E - u))
      (D₁ ∩ (fun u => E - u) ⁻¹' D₂) x) :
    ∃ b, SupportsSlope f D₁ x b ∧ SupportsSlope g D₂ (E - x) b := by
  have hx' : x ∈ interior D₁ := by rw [hD₁.interior_eq]; exact hx
  have hy' : E - x ∈ interior D₂ := by rw [hD₂.interior_eq]; exact hy
  have hopen : IsOpen (D₁ ∩ (fun u => E - u) ⁻¹' D₂) :=
    hD₁.inter (hD₂.preimage (continuous_const.sub continuous_id))
  have hxin : x ∈ interior (D₁ ∩ (fun u => E - u) ⁻¹' D₂) := by
    rw [hopen.interior_eq]
    exact ⟨hx, hy⟩
  have hsupport : SupportsSlope (fun u => f u + g (E - u))
      (D₁ ∩ (fun u => E - u) ⁻¹' D₂) x 0 := by
    intro u hu
    have h := hmax hu
    change f u + g (E - u) ≤ f x + g (E - x) at h
    simpa only [zero_mul, add_zero] using h
  have hright : HasDerivWithinAt (fun u => f u + g (E - u))
      (rightSlope f x - leftSlope g (E - x)) (Ioi x) x := by
    have hreflect : HasDerivWithinAt (fun u : ℝ => E - u) (-1) (Ioi x) x :=
      ((hasDerivAt_id x).const_sub E).hasDerivWithinAt
    have hcomp := (concave_hasDerivWithinAt_leftSlope hg hy').comp x hreflect
      (show MapsTo (fun u : ℝ => E - u) (Ioi x) (Iio (E - x)) from
        fun u hu => by change x < u at hu; change E - u < E - x; linarith)
    simpa only [Pi.add_def, Function.comp_def, mul_neg_one, sub_eq_add_neg] using
      (concave_hasDerivWithinAt_rightSlope hf hx').add hcomp
  have hleft : HasDerivWithinAt (fun u => f u + g (E - u))
      (leftSlope f x - rightSlope g (E - x)) (Iio x) x := by
    have hreflect : HasDerivWithinAt (fun u : ℝ => E - u) (-1) (Iio x) x :=
      ((hasDerivAt_id x).const_sub E).hasDerivWithinAt
    have hcomp := (concave_hasDerivWithinAt_rightSlope hg hy').comp x hreflect
      (show MapsTo (fun u : ℝ => E - u) (Iio x) (Ioi (E - x)) from
        fun u hu => by change u < x at hu; change E - x < E - u; linarith)
    simpa only [Pi.add_def, Function.comp_def, mul_neg_one, sub_eq_add_neg] using
      (concave_hasDerivWithinAt_leftSlope hf hx').add hcomp
  have hcross₁ : rightSlope f x ≤ leftSlope g (E - x) :=
    sub_nonpos.mp (hsupport.right_derivative_le hxin hright)
  have hcross₂ : rightSlope g (E - x) ≤ leftSlope f x :=
    sub_nonneg.mp (hsupport.le_left_derivative hxin hleft)
  refine ⟨max (rightSlope f x) (rightSlope g (E - x)),
    (supportsSlope_iff hf hx').mpr ⟨le_max_left _ _, ?_⟩,
    (supportsSlope_iff hg hy').mpr ⟨le_max_right _ _, ?_⟩⟩
  · exact max_le (concave_rightSlope_le_leftSlope hf hx') hcross₂
  · exact max_le hcross₁ (concave_rightSlope_le_leftSlope hg hy')

/-- Thermal maximization for two concave energy functions is exactly existence
of a common supporting inverse-temperature slope. -/
theorem isMaxOn_add_reflection_iff_common_support
    {f g : ℝ → ℝ} {D₁ D₂ : Set ℝ}
    (hf : ConcaveOn ℝ D₁ f) (hg : ConcaveOn ℝ D₂ g)
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) {E x : ℝ}
    (hx : x ∈ D₁) (hy : E - x ∈ D₂) :
    IsMaxOn (fun u => f u + g (E - u))
      (D₁ ∩ (fun u => E - u) ⁻¹' D₂) x ↔
        ∃ b, SupportsSlope f D₁ x b ∧ SupportsSlope g D₂ (E - x) b := by
  constructor
  · exact common_support_of_isMaxOn_add_reflection hf hg hD₁ hD₂ hx hy
  · rintro ⟨b, hf', hg'⟩
    exact isMaxOn_add_reflection_of_common_support hf' hg'

/-- Equivalent interval-intersection form, allowing nondifferentiable entropy
functions and nonunique supporting slopes. -/
theorem isMaxOn_add_reflection_iff_inter_supportingSlopes
    {f g : ℝ → ℝ} {D₁ D₂ : Set ℝ}
    (hf : ConcaveOn ℝ D₁ f) (hg : ConcaveOn ℝ D₂ g)
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) {E x : ℝ}
    (hx : x ∈ D₁) (hy : E - x ∈ D₂) :
    IsMaxOn (fun u => f u + g (E - u))
      (D₁ ∩ (fun u => E - u) ⁻¹' D₂) x ↔
        (supportingSlopes f D₁ x ∩ supportingSlopes g D₂ (E - x)).Nonempty :=
  isMaxOn_add_reflection_iff_common_support hf hg hD₁ hD₂ hx hy

end ProjectAInos.Thermodynamics
