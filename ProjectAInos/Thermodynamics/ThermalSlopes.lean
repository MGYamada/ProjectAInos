module

public import ProjectAInos.Thermodynamics.ThermalMaximizers
public import ProjectAInos.Thermodynamics.SupportingSlopes

/-!
# Supporting entropy slopes and thermal equilibrium

Concavity gives a nonempty closed interval of supporting slopes on every
energy fiber. Thermal equilibrium of two copies of one simple system is
equivalent to intersection of these intervals. No differentiability or unique
temperature is assumed: those are later consequences of the thermal axioms.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

namespace SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- Supporting slopes of the entropy as a function of energy at a physical state. -/
def entropySlopes (S : SimpleSystem P n) (s : SimpleCoordinates n → ℝ)
    (x : S.domain) : Set ℝ :=
  supportingSlopes (energyEntropy s x.val.2) (S.energyDomain x.val.2) x.val.1

theorem entropySlopes_eq_Icc (S : SimpleSystem P n)
    {s : SimpleCoordinates n → ℝ} (hs : ConcaveOn ℝ S.domain s) (x : S.domain) :
    S.entropySlopes s x = Icc (rightSlope (energyEntropy s x.val.2) x.val.1)
      (leftSlope (energyEntropy s x.val.2) x.val.1) := by
  apply supportingSlopes_eq_Icc (S.energyEntropy_concave hs x.val.2)
  rw [(S.energyDomain_isOpen x.val.2).interior_eq]
  exact x.property

theorem entropySlopes_nonempty (S : SimpleSystem P n)
    {s : SimpleCoordinates n → ℝ} (hs : ConcaveOn ℝ S.domain s) (x : S.domain) :
    (S.entropySlopes s x).Nonempty := by
  apply supportingSlopes_nonempty (S.energyEntropy_concave hs x.val.2)
  rw [(S.energyDomain_isOpen x.val.2).interior_eq]
  exact x.property

theorem entropySlopes_isClosed (S : SimpleSystem P n)
    {s : SimpleCoordinates n → ℝ} (hs : ConcaveOn ℝ S.domain s) (x : S.domain) :
    IsClosed (S.entropySlopes s x) := by
  rw [S.entropySlopes_eq_Icc hs x]
  exact isClosed_Icc

theorem entropySlopes_antitone (S : SimpleSystem P n) (s : SimpleCoordinates n → ℝ)
    {x y : S.domain} (hwork : x.val.2 = y.val.2) (henergy : x.val.1 < y.val.1)
    {b c : ℝ} (hb : b ∈ S.entropySlopes s x) (hc : c ∈ S.entropySlopes s y) : c ≤ b := by
  change SupportsSlope (energyEntropy s x.val.2) (S.energyDomain x.val.2) x.val.1 b at hb
  change SupportsSlope (energyEntropy s y.val.2) (S.energyDomain y.val.2) y.val.1 c at hc
  rw [hwork] at hb
  apply hb.antitone hc _ y.property henergy
  simpa only [energyDomain, mem_ofPred_eq, ← hwork, Prod.mk.eta] using x.property

end SimpleSystem

namespace ThermalFamily

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} (F : ThermalFamily P) {n : ℕ}

/-- Thermal equilibrium is intersection of supporting entropy-slope intervals,
derived from concavity and the proved maximum-entropy criterion. -/
theorem thermal_iff_entropySlopes_inter (S : SimpleSystem P n) (hS : F.admitted S)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀)) (x y : S.domain) :
    F.thermal (S.represent x) (S.represent y) ↔
      (S.entropySlopes (S.referenceEntropy hlocal x₀ x₁ hstrict) x ∩
        S.entropySlopes (S.referenceEntropy hlocal x₀ x₁ hstrict) y).Nonempty := by
  rw [F.thermal_iff_allocationEntropy_max S hS hlocal x₀ x₁ hstrict]
  have hs := S.referenceEntropy_concave hlocal x₀ x₁ hstrict
  have hy : x.val.1 + y.val.1 - x.val.1 ∈ S.energyDomain y.val.2 := by
    simpa only [SimpleSystem.energyDomain, mem_ofPred_eq, add_sub_cancel_left, Prod.mk.eta]
      using y.property
  have h := isMaxOn_add_reflection_iff_inter_supportingSlopes
    (S.energyEntropy_concave hs x.val.2) (S.energyEntropy_concave hs y.val.2)
    (S.energyDomain_isOpen x.val.2) (S.energyDomain_isOpen y.val.2) x.property hy
  have hfun : SimpleSystem.allocationEntropy (S.referenceEntropy hlocal x₀ x₁ hstrict)
      (x.val.1 + y.val.1) x.val.2 y.val.2 =
      fun u => SimpleSystem.energyEntropy (S.referenceEntropy hlocal x₀ x₁ hstrict) x.val.2 u +
        SimpleSystem.energyEntropy (S.referenceEntropy hlocal x₀ x₁ hstrict) y.val.2
          (x.val.1 + y.val.1 - u) := rfl
  have hdomain : S.allocationDomain (x.val.1 + y.val.1) x.val.2 y.val.2 =
      S.energyDomain x.val.2 ∩ (fun u => x.val.1 + y.val.1 - u) ⁻¹' S.energyDomain y.val.2 := rfl
  rw [hfun, hdomain]
  simpa only [SimpleSystem.entropySlopes, add_sub_cancel_left] using h

/-- Along a fixed work coordinate, distinct thermal classes have strictly
ordered supporting slopes. -/
theorem entropySlope_lt_of_not_thermal (S : SimpleSystem P n) (hS : F.admitted S)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀)) {x y : S.domain}
    (hwork : x.val.2 = y.val.2) (henergy : x.val.1 < y.val.1)
    (hnot : ¬ F.thermal (S.represent x) (S.represent y)) {b c : ℝ}
    (hb : b ∈ S.entropySlopes (S.referenceEntropy hlocal x₀ x₁ hstrict) x)
    (hc : c ∈ S.entropySlopes (S.referenceEntropy hlocal x₀ x₁ hstrict) y) : c < b := by
  have hle := S.entropySlopes_antitone _ hwork henergy hb hc
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hnot
  apply (F.thermal_iff_entropySlopes_inter S hS hlocal x₀ x₁ hstrict x y).mpr
  exact ⟨b, hb, by simpa only [heq] using hc⟩

end ThermalFamily

end ProjectAInos.Thermodynamics.Physical
