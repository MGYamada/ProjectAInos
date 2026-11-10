module

public import ProjectAInos.Thermodynamics.SimpleComparison
public import ProjectAInos.Thermodynamics.CalibratorExistence
public import ProjectAInos.Thermodynamics.CommonProducts

/-!
# Calibration of a family of simple systems

Pairwise crossed calibrators need not use a common reference pair. The affine
representation within one anchor system identifies all their directions with
one positive direction in the completion. This supplies comparison on every
finite scaled product, including zero weights and the empty product.

Calibrator existence remains an explicit physical obligation in this module.
It is not replaced by a product comparison hypothesis.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical.ThermalFamily

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} (F : ThermalFamily P)

/-- Every pair of nonempty admitted systems has crossed strict reference pairs.
Empty coordinate domains do not assert the existence of physical states. -/
def HasCalibrators : Prop :=
  ∀ {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m),
    F.admitted S → F.admitted T → S.domain.Nonempty → T.domain.Nonempty →
      ∃ a b : S.domain, ∃ c d : T.domain,
        IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d)

/-- Calibrators to one anchor align all reference directions. Each system is
free to use its own reference states in the calibrator with that anchor. -/
theorem exists_common_coordinates (hcal : F.HasCalibrators)
    {Γ : Type*} (n : Γ → ℕ) (S : ∀ g, SimpleSystem P (n g))
    (hS : ∀ g, F.admitted (S g)) (hnonempty : ∀ g, (S g).domain.Nonempty)
    (anchor : Γ) :
    ∃ e : Completion P.StateSpace, e ∈ processCone P.StateSpace ∧ e ≠ 0 ∧
      ∃ (reference : ∀ g, (S g).domain) (coordinate : ∀ g, (S g).domain → ℝ),
        ∀ g (z : (S g).domain), P.completedState ((S g).represent z) -
          P.completedState ((S g).represent (reference g)) = coordinate g z • e := by
  classical
  obtain ⟨a₀, a₁, _, _, hanchor, _⟩ :=
    hcal (S anchor) (S anchor) (hS anchor) (hS anchor) (hnonempty anchor) (hnonempty anchor)
  let e := P.completedState ((S anchor).represent a₁) -
    P.completedState ((S anchor).represent a₀)
  obtain ⟨he, hne⟩ := P.strict_reference_direction hanchor
  have hpairs (g : Γ) :=
    hcal (S g) (S anchor) (hS g) (hS anchor) (hnonempty g) (hnonempty anchor)
  choose lower upper anchorLower anchorUpper hpairs using hpairs
  have hanchorCoord (z : (S anchor).domain) :=
    (S anchor).exists_coordinate_of_local_intervals
      (F.localMixtureIntervals_of_axioms (S anchor) (hS anchor)) a₀ a₁ hanchor z
  have hdir (g : Γ) : ∃ r : ℝ,
      P.completedState ((S g).represent (upper g)) -
        P.completedState ((S g).represent (lower g)) = r • e := by
    obtain ⟨u, hu⟩ := hanchorCoord (anchorLower g)
    obtain ⟨v, hv⟩ := hanchorCoord (anchorUpper g)
    refine ⟨v - u, ?_⟩
    rw [(P.crossed_equivalence_iff_directions_eq _ _ _ _).mp (hpairs g).2.2]
    rw [sub_smul, ← hv, ← hu]
    abel
  have hcoords (g : Γ) (z : (S g).domain) : ∃ r : ℝ,
      P.completedState ((S g).represent z) -
        P.completedState ((S g).represent (lower g)) = r • e := by
    obtain ⟨u, hu⟩ := (S g).exists_coordinate_of_local_intervals
      (F.localMixtureIntervals_of_axioms (S g) (hS g)) (lower g) (upper g) (hpairs g).1 z
    obtain ⟨r, hr⟩ := hdir g
    exact ⟨u * r, by rw [hu, hr, mul_smul]⟩
  choose coordinate hcoordinate using hcoords
  exact ⟨e, he, hne, lower, coordinate, hcoordinate⟩

/-- Pairwise calibrators and the proved single-system geometry give comparison
on every finite scaled product. No common choice of calibrating pairs is assumed. -/
theorem scaled_products_comparable (hcal : F.HasCalibrators)
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (S : ∀ i, SimpleSystem P (n i))
    (hS : ∀ i, F.admitted (S i)) (weight : ι → ℝ≥0)
    (x y : ∀ i, (S i).domain) :
    P.relation (∑ i, weight i • (S i).represent (x i))
        (∑ i, weight i • (S i).represent (y i)) ∨
      P.relation (∑ i, weight i • (S i).represent (y i))
        (∑ i, weight i • (S i).represent (x i)) := by
  classical
  rcases isEmpty_or_nonempty ι with hi | hi
  · let := hi
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact Or.inl (P.refl 0)
  · let := hi
    obtain ⟨anchor⟩ := hi
    obtain ⟨e, he, hne, reference, coordinate, hcoordinate⟩ :=
      F.exists_common_coordinates hcal n S hS (fun i => ⟨x i, (x i).property⟩) anchor
    apply P.finite_products_comparable weight weight
      (fun i => (S i).represent (x i)) (fun i => (S i).represent (reference i))
      (fun i => (S i).represent (y i)) (fun i => (S i).represent (reference i))
      (fun i => coordinate i (x i)) (fun i => coordinate i (y i)) he hne
    · exact fun i => hcoordinate i (x i)
    · exact fun i => hcoordinate i (y i)
    · rfl

end ProjectAInos.Thermodynamics.Physical.ThermalFamily
