module

public import ProjectAInos.Thermodynamics.SimpleEntropy
public import ProjectAInos.Thermodynamics.ThermalFamily

/-!
# Entropy maximizers under energy exchange

At fixed total energy and work coordinates, the entropy of two copies is a
concave function of their energy allocation. Its maximizers form a convex set.
The single-system entropy criterion identifies these maximizers with thermal
equilibrium, without assuming comparison between different systems.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

/-- Maximizers of a concave real-valued function form a convex set. -/
theorem convex_maximizers_of_concave {E : Type*} [AddCommGroup E] [Module ℝ E]
    {D : Set E} {s : E → ℝ} (hs : ConcaveOn ℝ D s) :
    Convex ℝ {x | x ∈ D ∧ IsMaxOn s D x} := by
  by_cases h : ({x | x ∈ D ∧ IsMaxOn s D x} : Set E).Nonempty
  · obtain ⟨u, hu, hmax⟩ := h
    have hset : {x | x ∈ D ∧ IsMaxOn s D x} = {x ∈ D | s u ≤ s x} := by
      ext x
      constructor
      · rintro ⟨hx, hmx⟩
        exact ⟨hx, hmx hu⟩
      · rintro ⟨hx, hux⟩
        exact ⟨hx, fun y hy => (hmax hy).trans hux⟩
    rw [hset]
    exact hs.convex_ge (s u)
  · simpa only [Set.not_nonempty_iff_eq_empty.mp h] using (convex_empty : Convex ℝ (∅ : Set E))

namespace SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- The admissible energies at a fixed work coordinate. -/
def energyDomain (S : SimpleSystem P n) (V : WorkCoordinates n) : Set ℝ :=
  {u | (u, V) ∈ S.domain}

/-- Entropy restricted to an energy fiber. -/
def energyEntropy (s : SimpleCoordinates n → ℝ) (V : WorkCoordinates n) (u : ℝ) : ℝ :=
  s (u, V)

theorem energyDomain_isOpen (S : SimpleSystem P n) (V : WorkCoordinates n) :
    IsOpen (S.energyDomain V) :=
  S.isOpen_domain.preimage (continuous_id.prodMk continuous_const)

/-- Allowed energy allocations at fixed total energy and fixed work coordinates. -/
def allocationDomain (S : SimpleSystem P n) (U : ℝ) (V W : WorkCoordinates n) : Set ℝ :=
  {u | (u, V) ∈ S.domain ∧ (U - u, W) ∈ S.domain}

/-- Total entropy as a function of the first subsystem's energy. -/
def allocationEntropy (s : SimpleCoordinates n → ℝ) (U : ℝ) (V W : WorkCoordinates n)
    (u : ℝ) : ℝ := s (u, V) + s (U - u, W)

private theorem allocation_left_mix (u v a b : ℝ) (V : WorkCoordinates n) (hab : a + b = 1) :
    a • (u, V) + b • (v, V) = (a * u + b * v, V) := by
  apply Prod.ext
  · rfl
  · change a • V + b • V = V
    rw [← add_smul, hab, one_smul]

private theorem allocation_right_mix (U u v a b : ℝ) (W : WorkCoordinates n)
    (hab : a + b = 1) :
    a • (U - u, W) + b • (U - v, W) = (U - (a * u + b * v), W) := by
  apply Prod.ext
  · change a * (U - u) + b * (U - v) = U - (a * u + b * v)
    calc
      _ = (a + b) * U - (a * u + b * v) := by ring
      _ = _ := by rw [hab, one_mul]
  · change a • W + b • W = W
    rw [← add_smul, hab, one_smul]

theorem energyDomain_convex (S : SimpleSystem P n) (V : WorkCoordinates n) :
    Convex ℝ (S.energyDomain V) := by
  intro u hu v hv a b ha hb hab
  simpa only [energyDomain, Set.mem_ofPred_eq, smul_eq_mul, allocation_left_mix u v a b V hab] using
    S.convex_domain hu hv ha hb hab

theorem energyEntropy_concave (S : SimpleSystem P n)
    {s : SimpleCoordinates n → ℝ} (hs : ConcaveOn ℝ S.domain s) (V : WorkCoordinates n) :
    ConcaveOn ℝ (S.energyDomain V) (energyEntropy s V) := by
  refine ⟨S.energyDomain_convex V, ?_⟩
  intro u hu v hv a b ha hb hab
  simpa only [energyEntropy, smul_eq_mul, allocation_left_mix u v a b V hab] using
    hs.2 hu hv ha hb hab

theorem allocationDomain_convex (S : SimpleSystem P n) (U : ℝ) (V W : WorkCoordinates n) :
    Convex ℝ (S.allocationDomain U V W) := by
  intro u hu v hv a b ha hb hab
  exact ⟨by simpa only [smul_eq_mul, allocation_left_mix u v a b V hab] using
      S.convex_domain hu.1 hv.1 ha hb hab,
    by simpa only [smul_eq_mul, allocation_right_mix U u v a b W hab] using
      S.convex_domain hu.2 hv.2 ha hb hab⟩

/-- Concavity survives restriction to energy exchange with fixed total energy. -/
theorem allocationEntropy_concave (S : SimpleSystem P n)
    {s : SimpleCoordinates n → ℝ} (hs : ConcaveOn ℝ S.domain s)
    (U : ℝ) (V W : WorkCoordinates n) :
    ConcaveOn ℝ (S.allocationDomain U V W) (allocationEntropy s U V W) := by
  refine ⟨S.allocationDomain_convex U V W, ?_⟩
  intro u hu v hv a b ha hb hab
  have hl := hs.2 hu.1 hv.1 ha hb hab
  have hr := hs.2 hu.2 hv.2 ha hb hab
  rw [allocation_left_mix u v a b V hab] at hl
  rw [allocation_right_mix U u v a b W hab] at hr
  simp only [smul_eq_mul] at hl hr ⊢
  dsimp only [allocationEntropy]
  linarith

def allocationLeft (S : SimpleSystem P n) {U : ℝ} {V W : WorkCoordinates n}
    (u : S.allocationDomain U V W) : S.domain := ⟨(u.val, V), u.property.1⟩

def allocationRight (S : SimpleSystem P n) {U : ℝ} {V W : WorkCoordinates n}
    (u : S.allocationDomain U V W) : S.domain := ⟨(U - u.val, W), u.property.2⟩

theorem joinedState_allocation_eq (S : SimpleSystem P n)
    {U : ℝ} {V W : WorkCoordinates n} (u v : S.allocationDomain U V W) :
    joinedState (S.allocationLeft u) (S.allocationRight u) =
      joinedState (S.allocationLeft v) (S.allocationRight v) := by
  apply Subtype.ext
  simp only [joinedState, allocationLeft, allocationRight, add_sub_cancel]

/-- The thermal maximum criterion expressed directly in the energy allocation
coordinate, rather than quantified over typed pairs of subsystem states. -/
theorem equilibrium_iff_allocationEntropy_max (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀))
    (J : ThermalJoin P S.domain S.domain (fun x => S.represent x) (fun y => S.represent y))
    {U : ℝ} {V W : WorkCoordinates n} (u : S.allocationDomain U V W) :
    J.Equilibrium (S.allocationLeft u) (S.allocationRight u) ↔
      IsMaxOn (allocationEntropy (S.referenceEntropy hlocal x₀ x₁ hstrict) U V W)
        (S.allocationDomain U V W) u := by
  rw [S.equilibrium_iff_referenceEntropy_maximum hlocal x₀ x₁ hstrict]
  constructor
  · intro hmax v hv
    exact hmax (S.allocationLeft ⟨v, hv⟩) (S.allocationRight ⟨v, hv⟩)
      (S.joinedState_allocation_eq ⟨v, hv⟩ u)
  · intro hmax a b hab
    have hsum : a.val.1 + b.val.1 = U := by
      have h := congrArg (fun z : joinedDomain S.domain S.domain => z.val.1) hab
      simpa only [joinedState, allocationLeft, allocationRight, add_sub_cancel] using h
    have hV : a.val.2 = V := congrArg (fun z : joinedDomain S.domain S.domain => z.val.2.1) hab
    have hW : b.val.2 = W := congrArg (fun z : joinedDomain S.domain S.domain => z.val.2.2) hab
    have hb : U - a.val.1 = b.val.1 := by linarith
    have haD : a.val.1 ∈ S.allocationDomain U V W := by
      constructor
      · simpa only [← hV, Prod.mk.eta] using a.property
      · simpa only [hb, ← hW, Prod.mk.eta] using b.property
    have h := hmax haD
    change allocationEntropy (S.referenceEntropy hlocal x₀ x₁ hstrict) U V W a.val.1 ≤
      allocationEntropy (S.referenceEntropy hlocal x₀ x₁ hstrict) U V W u at h
    simpa only [allocationEntropy, allocationLeft, allocationRight, hb, ← hV, ← hW,
      Prod.mk.eta] using h

/-- The allocations that give equilibrium form a convex set. This allows
multiple maximizing splits and does not assume unique thermal splitting. -/
theorem equilibrium_allocations_convex (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀))
    (J : ThermalJoin P S.domain S.domain (fun x => S.represent x) (fun y => S.represent y))
    (U : ℝ) (V W : WorkCoordinates n) :
    Convex ℝ {u | ∃ hu : u ∈ S.allocationDomain U V W,
      J.Equilibrium (S.allocationLeft ⟨u, hu⟩) (S.allocationRight ⟨u, hu⟩)} := by
  have hset : {u | ∃ hu : u ∈ S.allocationDomain U V W,
      J.Equilibrium (S.allocationLeft ⟨u, hu⟩) (S.allocationRight ⟨u, hu⟩)} =
      {u | u ∈ S.allocationDomain U V W ∧
        IsMaxOn (allocationEntropy (S.referenceEntropy hlocal x₀ x₁ hstrict) U V W)
          (S.allocationDomain U V W) u} := by
    ext u
    constructor
    · rintro ⟨hu, heq⟩
      exact ⟨hu, (S.equilibrium_iff_allocationEntropy_max hlocal x₀ x₁ hstrict J ⟨u, hu⟩).mp heq⟩
    · rintro ⟨hu, hmax⟩
      exact ⟨hu, (S.equilibrium_iff_allocationEntropy_max hlocal x₀ x₁ hstrict J ⟨u, hu⟩).mpr hmax⟩
  rw [hset]
  exact convex_maximizers_of_concave
    (S.allocationEntropy_concave (S.referenceEntropy_concave hlocal x₀ x₁ hstrict) U V W)

end SimpleSystem

namespace ThermalFamily

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} (F : ThermalFamily P) {n : ℕ}

/-- The raw thermal relation, restricted to a simple member, is exactly the
maximum-entropy condition for energy exchange between two copies. -/
theorem thermal_iff_allocationEntropy_max (S : SimpleSystem P n) (hS : F.admitted S)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀)) (x y : S.domain) :
    F.thermal (S.represent x) (S.represent y) ↔
      IsMaxOn (SimpleSystem.allocationEntropy (S.referenceEntropy hlocal x₀ x₁ hstrict)
        (x.val.1 + y.val.1) x.val.2 y.val.2)
        (S.allocationDomain (x.val.1 + y.val.1) x.val.2 y.val.2) x.val.1 := by
  let u : S.allocationDomain (x.val.1 + y.val.1) x.val.2 y.val.2 :=
    ⟨x.val.1, x.property, by simpa only [add_sub_cancel_left, Prod.mk.eta] using y.property⟩
  have hx : S.allocationLeft u = x := Subtype.ext Prod.mk.eta
  have hy : S.allocationRight u = y := by
    apply Subtype.ext
    simp only [SimpleSystem.allocationRight, u, add_sub_cancel_left, Prod.mk.eta]
  have h := S.equilibrium_iff_allocationEntropy_max hlocal x₀ x₁ hstrict
    (F.join S S hS hS).thermalJoin u
  rw [hx, hy] at h
  exact (F.thermal_iff S S hS hS x y).trans h

end ThermalFamily

end ProjectAInos.Thermodynamics.Physical
