module

public import ProjectAInos.Thermodynamics.FamilyCalibration
public import ProjectAInos.Thermodynamics.UniqueThermalSplit
public import ProjectAInos.Thermodynamics.UniversalThermalClass
public import ProjectAInos.Thermodynamics.UniversalJoinCalibration

/-!
# Entropy calibrators from the simple-system and thermal axioms

The no-calibrator alternative makes each joined adiabat a thermal class, hence
makes the whole join one isotherm. Coordinate-preserving splitting makes each
component class meet every work fiber. Transversality prevents either class
from being one adiabat; the resulting cross-equilibrium strict pairs yield a
calibrator through the joined system's affine entropy line.

This includes the universal-isotherm branch without identifying thermal and
adiabatic equivalence, or assuming continuity of a selected thermal splitting.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical.ThermalFamily

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} (F : ThermalFamily P)

/-- A universal joined isotherm also yields calibrators. Universality alone
does not imply nonunique splitting; the proof uses transversality in both
component systems and the common affine direction in the joined system. -/
theorem exists_calibrator_of_universal_join
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T) (x : S.domain) (y : T.domain)
    (huniversal : ∀ z w : (F.join S T hS hT).system.domain,
      F.thermal ((F.join S T hS hT).system.represent z)
        ((F.join S T hS hT).system.represent w)) :
    ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d) := by
  obtain ⟨a₀, a₁, b₀, b₁, ha, hb, h₀₀, h₁₀, h₀₁, _⟩ :=
    F.exists_cross_thermal_strict_pairs_of_universal_join S T hS hT x y huniversal
  exact F.calibrator_of_three_cross_thermal_reference_pairs S T hS hT
    a₀ a₁ b₀ b₁ ha hb h₀₀ h₁₀ h₀₁

/-- LY 4.7: every two nonempty admitted simple systems admit a crossed strict
entropy calibrator. All geometric and thermal premises are fields of `F`. -/
theorem hasCalibrators_of_axioms : F.HasCalibrators := by
  intro n m S T hS hT hSne hTne
  obtain ⟨x, hx⟩ := hSne
  obtain ⟨y, hy⟩ := hTne
  by_contra hno
  exact hno (F.exists_calibrator_of_universal_join S T hS hT ⟨x, hx⟩ ⟨y, hy⟩
    (F.joined_all_thermal_of_no_calibrator S T hS hT hno))

end ProjectAInos.Thermodynamics.Physical.ThermalFamily
