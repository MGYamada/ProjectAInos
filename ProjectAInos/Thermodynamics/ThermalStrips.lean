module

public import ProjectAInos.Thermodynamics.ReferenceIntervals
public import ProjectAInos.Thermodynamics.LocalLines
public import ProjectAInos.Thermodynamics.Calibration
public import ProjectAInos.Thermodynamics.SectorGeometry

/-!
# Local reference intervals and global single-system representation

Mixture comparison produces local affine coordinates in the state completion.
Connectedness joins these local lines into one line. The required local
intervals are explicit inputs to this intermediate theorem; the thermal-axiom
derivation of those intervals is separate.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical

namespace Accessibility

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]

/-- Comparison with all mixtures gives a real affine coordinate for a raw
state, using the stable adiabatic quotient. -/
theorem reference_coordinate_of_mixture_comparison (P : Accessibility X)
    {x₀ x₁ x : X} (hstrict : P.relation x₀ x₁ ∧ ¬ P.relation x₁ x₀)
    (hlower : P.relation x₀ x) (hupper : P.relation x x₁)
    (hcompare : ∀ t : ℝ≥0, t ≤ 1 →
      P.relation ((1 - t) • x₀ + t • x₁) x ∨
        P.relation x ((1 - t) • x₀ + t • x₁)) :
    ∃ r ∈ Icc (0 : ℝ) 1, P.completedState x - P.completedState x₀ =
      r • (P.completedState x₁ - P.completedState x₀) := by
  apply exists_reference_coordinate_of_comparable P.stability
    (lt_iff_le_not_ge.mpr hstrict) hlower hupper
  exact hcompare

end Accessibility

namespace SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- An interior point of a sector is not adiabatically equivalent to its
anchor. This does not require simple-system comparison. -/
theorem completedState_ne_of_mem_interior (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain)
    (hy : y ∈ interior (S.sector x)) :
    P.completedState (S.represent x) ≠ P.completedState (S.represent y) := by
  intro heq
  have hxy := (P.completedState_eq_iff _ _).mp heq
  have hyD := (interior_subset hy).1
  apply S.self_not_mem_interior hyD
  exact interior_mono (S.sector_subset_of_mem ⟨hx, hxy.2⟩) hy

/-- Every neighborhood of a simple-system state contains a state with a
different adiabatic class, by local vertical interior. -/
theorem completedState_varies_in_neighborhood (S : SimpleSystem P n)
    (x : S.domain) (U : Set S.domain) (hU : U ∈ 𝓝 x) :
    ∃ y ∈ U, P.completedState (S.represent x) ≠ P.completedState (S.represent y) := by
  obtain ⟨O, hO, hOU⟩ := (mem_nhds_subtype S.domain x U).mp hU
  obtain ⟨u, hu, _⟩ := S.exists_vertical_interior x.property
  let γ : ℝ → SimpleCoordinates n := fun t => ((1 - t) * x.val.1 + t * u, x.val.2)
  have hγ : Tendsto γ (𝓝 0) (𝓝 (x : SimpleCoordinates n)) := by
    have hc : Continuous γ := by dsimp [γ]; fun_prop
    simpa [γ] using hc.tendsto (0 : ℝ)
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ O ∧ t < 1 :=
    (hγ.eventually_mem hO).and (Iio_mem_nhds (by norm_num))
  obtain ⟨t, ht, htO, ht1⟩ := hevent.exists_gt
  have hint : γ t ∈ interior (S.sector x) :=
    S.vertical_between_mem_interior x.property hu ht ht1
  let y : S.domain := ⟨γ t, (interior_subset hint).1⟩
  exact ⟨y, hOU htO, S.completedState_ne_of_mem_interior x.property hint⟩

/-- Each state has an open neighborhood between strict references whose
mixtures can be compared with every state of that neighborhood. -/
def LocalMixtureIntervals (S : SimpleSystem P n) : Prop :=
    ∀ x : S.domain, ∃ a b : S.domain,
      (P.relation (S.represent a) (S.represent b) ∧
        ¬ P.relation (S.represent b) (S.represent a)) ∧
      ∃ U : Set S.domain, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
        P.relation (S.represent a) (S.represent y) ∧
        P.relation (S.represent y) (S.represent b) ∧
        ∀ t : ℝ≥0, t ≤ 1 →
          P.relation ((1 - t) • S.represent a + t • S.represent b) (S.represent y) ∨
          P.relation (S.represent y) ((1 - t) • S.represent a + t • S.represent b)

/-- Open locally comparable reference intervals determine one affine line for
all states of a simple system. The local interval premise will be supplied by
thermal transversality, thermal splitting, and simple-system comparison. -/
theorem completedState_mem_line_of_local_intervals (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals)
    (x₀ x₁ : S.domain)
    (hne : P.completedState (S.represent x₀) ≠ P.completedState (S.represent x₁))
    (x : S.domain) :
    P.completedState (S.represent x) ∈
      line[ℝ, P.completedState (S.represent x₀), P.completedState (S.represent x₁)] := by
  let : PreconnectedSpace S.domain :=
    isPreconnected_iff_preconnectedSpace.mp S.convex_domain.isPreconnected
  apply mem_affineSpan_pair_of_locally_line
    (fun y : S.domain => P.completedState (S.represent y))
    S.completedState_varies_in_neighborhood ?_ x₀ x₁ hne x
  intro y
  obtain ⟨a, b, hab, U, hU, hyU, hinterval⟩ := hlocal y
  refine ⟨P.completedState (S.represent a), P.completedState (S.represent b),
    U, hU, hyU, ?_⟩
  intro z hz
  obtain ⟨haz, hzb, hcompare⟩ := hinterval z hz
  obtain ⟨r, _, hr⟩ := P.reference_coordinate_of_mixture_comparison hab haz hzb hcompare
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨r, ?_⟩
  rw [AffineMap.lineMap_apply_module]
  have heq := eq_add_of_sub_eq hr
  rw [heq]
  module

/-- Local thermal reference intervals give an affine coordinate relative to
any strict reference pair of the simple system. -/
theorem exists_coordinate_of_local_intervals (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀)) (x : S.domain) :
    ∃ r : ℝ, P.completedState (S.represent x) - P.completedState (S.represent x₀) =
      r • (P.completedState (S.represent x₁) - P.completedState (S.represent x₀)) := by
  have hne : P.completedState (S.represent x₀) ≠ P.completedState (S.represent x₁) := by
    intro h
    exact hstrict.2 ((P.completedState_eq_iff _ _).mp h).2
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (S.completedState_mem_line_of_local_intervals hlocal x₀ x₁ hne x)
  refine ⟨r, ?_⟩
  rw [← hr, AffineMap.lineMap_apply_module]
  module

/-- Equal-total-amount products of one simple system are comparable once its
local thermal intervals have been established. No product CH is assumed. -/
theorem scaled_products_comparable_of_local_intervals (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀))
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ≥0) (b : κ → ℝ≥0) (hbalance : ∑ i, a i = ∑ j, b j)
    (x : ι → S.domain) (y : κ → S.domain) :
    P.relation (∑ i, a i • S.represent (x i)) (∑ j, b j • S.represent (y j)) ∨
      P.relation (∑ j, b j • S.represent (y j)) (∑ i, a i • S.represent (x i)) := by
  classical
  have hx := fun i => S.exists_coordinate_of_local_intervals hlocal x₀ x₁ hstrict (x i)
  have hy := fun j => S.exists_coordinate_of_local_intervals hlocal x₀ x₁ hstrict (y j)
  obtain ⟨he, hne⟩ := P.strict_reference_direction hstrict
  apply P.finite_products_comparable a b (fun i => S.represent (x i))
    (fun _ => S.represent x₀) (fun j => S.represent (y j)) (fun _ => S.represent x₀)
    (fun i => (hx i).choose) (fun j => (hy j).choose) he hne
    (fun i => (hx i).choose_spec) (fun j => (hy j).choose_spec)
  simp only [← Finset.sum_smul, ← NNReal.coe_sum, hbalance]

end SimpleSystem

end ProjectAInos.Thermodynamics.Physical
