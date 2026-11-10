module

public import ProjectAInos.Thermodynamics.CalibratorDirections
public import ProjectAInos.Thermodynamics.ThermalJoinCoherence

/-!
# Calibration from cross-equilibrium reference pairs

Three cross-equilibrium pairs identify two independent component differences
with differences of states in one simple thermal join. The join's proved
affine-line representation makes the component directions collinear. Their
strictness then realizes a crossed entropy calibrator in the original systems.
No universality of a thermal class or product comparison is assumed here.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X}

namespace SimpleThermalJoin

/-- At equilibrium the joined completed state is the sum of the component
completed states. This uses adiabatic equivalence, not thermal invariance under
arbitrary adiabatic transformations. -/
theorem completedState_eq_sum_of_equilibrium
    {n m : ℕ} {S : SimpleSystem P n} {T : SimpleSystem P m}
    (J : SimpleThermalJoin S T) (x : S.domain) (y : T.domain)
    (h : J.thermalJoin.Equilibrium x y) :
    P.completedState (J.system.represent (J.point (joinedState x y))) =
      P.completedState (S.represent x) + P.completedState (T.represent y) := by
  simp only [Accessibility.completedState_apply,
    J.stateClass_eq_sum_of_equilibrium x y h, map_add]

end SimpleThermalJoin

namespace ThermalFamily

variable (F : ThermalFamily P)

/-- Three thermal cross pairs of strict references are sufficient to produce
an entropy calibrator; the fourth corner is not needed. -/
theorem calibrator_of_three_cross_thermal_reference_pairs
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (a₀ a₁ : S.domain) (b₀ b₁ : T.domain)
    (ha : P.relation (S.represent a₀) (S.represent a₁) ∧
      ¬ P.relation (S.represent a₁) (S.represent a₀))
    (hb : P.relation (T.represent b₀) (T.represent b₁) ∧
      ¬ P.relation (T.represent b₁) (T.represent b₀))
    (h₀₀ : F.thermal (S.represent a₀) (T.represent b₀))
    (h₁₀ : F.thermal (S.represent a₁) (T.represent b₀))
    (h₀₁ : F.thermal (S.represent a₀) (T.represent b₁)) :
    ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d) := by
  let J := F.join S T hS hT
  let z₀ := J.point (joinedState a₀ b₀)
  let z₁ := J.point (joinedState a₀ b₁)
  let z := J.point (joinedState a₁ b₀)
  have hc₀ := J.completedState_eq_sum_of_equilibrium a₀ b₀
    ((F.thermal_iff S T hS hT a₀ b₀).mp h₀₀)
  have hc₁ := J.completedState_eq_sum_of_equilibrium a₀ b₁
    ((F.thermal_iff S T hS hT a₀ b₁).mp h₀₁)
  have hc := J.completedState_eq_sum_of_equilibrium a₁ b₀
    ((F.thermal_iff S T hS hT a₁ b₀).mp h₁₀)
  have hd₁ : P.completedState (J.system.represent z₁) - P.completedState (J.system.represent z₀) =
      P.completedState (T.represent b₁) - P.completedState (T.represent b₀) := by
    rw [hc₁, hc₀]
    abel
  have hd : P.completedState (J.system.represent z) - P.completedState (J.system.represent z₀) =
      P.completedState (S.represent a₁) - P.completedState (S.represent a₀) := by
    rw [hc, hc₀]
    abel
  have hstrictJ := P.strict_reference_of_crossed hb
    ((P.crossed_equivalence_iff_directions_eq (T.represent b₀) (T.represent b₁)
      (J.system.represent z₀) (J.system.represent z₁)).mpr hd₁.symm)
  obtain ⟨r, hr⟩ := J.system.exists_coordinate_of_local_intervals
    (F.localMixtureIntervals_of_axioms J.system (F.join_admitted S T hS hT))
    z₀ z₁ hstrictJ z
  rw [hd, hd₁] at hr
  by_contra hno
  exact F.reference_direction_ne_smul_of_no_calibrator S T hS hT hno a₀ a₁ b₀ b₁ ha hb r hr

/-- Four cross-equilibrium reference pairs give calibrators. This convenient
rectangle formulation exposes the hypothesis produced by universal-isotherm
arguments; the proof only needs three of its corners. -/
theorem calibrator_of_cross_thermal_reference_pairs
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (a₀ a₁ : S.domain) (b₀ b₁ : T.domain)
    (ha : P.relation (S.represent a₀) (S.represent a₁) ∧
      ¬ P.relation (S.represent a₁) (S.represent a₀))
    (hb : P.relation (T.represent b₀) (T.represent b₁) ∧
      ¬ P.relation (T.represent b₁) (T.represent b₀))
    (hcross : ∀ a ∈ ({a₀, a₁} : Set S.domain), ∀ b ∈ ({b₀, b₁} : Set T.domain),
      F.thermal (S.represent a) (T.represent b)) :
    ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d) :=
  F.calibrator_of_three_cross_thermal_reference_pairs S T hS hT a₀ a₁ b₀ b₁ ha hb
    (hcross a₀ (by simp) b₀ (by simp)) (hcross a₁ (by simp) b₀ (by simp))
    (hcross a₀ (by simp) b₁ (by simp))

end ThermalFamily

end ProjectAInos.Thermodynamics.Physical
