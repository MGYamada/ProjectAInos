module

public import ProjectAInos.Thermodynamics.Completion
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.EReal.Operations
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso

/-!
# Transition costs and weak entropy

Direct transitions, finite chains, and catalysts define extended-real costs.
Catalytic invariance descends the cost to the completion of system types.
Scaling and cycle consistency give sublinearity, and absence of sinks makes
the finite-cost domain a vector space. Hahn–Banach then selects compatible
entropy constants. The state-model bridges keep entropy calibration,
composition, and invertible scaling as explicit premises.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Reactions

/-- Positive real multiplication as an order isomorphism of extended costs. -/
def costScale (r : ℝ) (hr : 0 < r) : EReal ≃o EReal :=
  (OrderIso.mulLeft₀ r hr).withTopCongr.withBotCongr

theorem costScale_apply (r : ℝ) (hr : 0 < r) (x : EReal) :
    costScale r hr x = (r : EReal) * x := by
  induction x with
  | bot => rw [EReal.coe_mul_bot_of_pos hr]; rfl
  | coe x => rfl
  | top => rw [EReal.coe_mul_top_of_pos hr]; rfl

@[simp] theorem costScale_zero (r : ℝ) (hr : 0 < r) : costScale r hr 0 = 0 := by
  rw [costScale_apply, mul_zero]

theorem costScale_add (r : ℝ) (hr : 0 < r) (x y : EReal) :
    costScale r hr (x + y) = costScale r hr x + costScale r hr y := by
  simp only [costScale_apply]
  exact EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hr.le)
    (EReal.coe_ne_top r) x y

@[simp] theorem costScale_inv (r : ℝ) (hr : 0 < r) (x : EReal) :
    costScale r hr (costScale r⁻¹ (inv_pos.mpr hr) x) = x := by
  induction x with
  | bot => rfl
  | top => rfl
  | coe x =>
    change ((r * (r⁻¹ * x) : ℝ) : EReal) = (x : EReal)
    rw [mul_inv_cancel_left₀ hr.ne']

section TransitionCosts

variable {Γ : Type*} (State : Γ → Type*) (entropy : ∀ g, State g → ℝ)
  (accessible : (Σ g, State g) → (Σ g, State g) → Prop)

/-- The infimum of calibrated entropy changes of direct transformations. -/
def directCost (a b : Γ) : EReal :=
  sInf {c | ∃ (x : State a) (y : State b), accessible ⟨a, x⟩ ⟨b, y⟩ ∧
    c = ((entropy b y - entropy a x : ℝ) : EReal)}

theorem directCost_le {a b : Γ} {x : State a} {y : State b}
    (h : accessible ⟨a, x⟩ ⟨b, y⟩) :
    directCost State entropy accessible a b ≤ ((entropy b y - entropy a x : ℝ) : EReal) :=
  sInf_le ⟨x, y, h, rfl⟩

/-- Finite-above direct cost is exactly existence of an admissible transition. -/
theorem directCost_lt_top_iff (a b : Γ) :
    directCost State entropy accessible a b < ⊤ ↔
      ∃ (x : State a) (y : State b), accessible ⟨a, x⟩ ⟨b, y⟩ := by
  constructor
  · intro h
    obtain ⟨_, ⟨x, y, hxy, _⟩, _⟩ := sInf_lt_iff.mp h
    exact ⟨x, y, hxy⟩
  · rintro ⟨x, y, hxy⟩
    exact (directCost_le State entropy accessible hxy).trans_lt (EReal.coe_lt_top _)

theorem directCost_self (a : Γ) [Nonempty (State a)]
    (hrefl : ∀ x : State a, accessible ⟨a, x⟩ ⟨a, x⟩)
    (hmono : ∀ x y : State a, accessible ⟨a, x⟩ ⟨a, y⟩ → entropy a x ≤ entropy a y) :
    directCost State entropy accessible a a = 0 := by
  apply le_antisymm
  · obtain ⟨x⟩ := ‹Nonempty (State a)›
    simpa using directCost_le State entropy accessible (hrefl x)
  · apply le_sInf
    rintro r ⟨x, y, hxy, rfl⟩
    exact EReal.coe_nonneg.mpr (sub_nonneg.mpr (hmono x y hxy))

/-- Returning an unchanged ancillary state can only lower the direct cost. -/
theorem directCost_add_same [AddCommMonoid Γ] [∀ a, Nonempty (State a)]
    (compose : ∀ {a b}, State a → State b → State (a + b))
    (hentropy : ∀ {a b} (x : State a) (y : State b),
      entropy (a + b) (compose x y) = entropy a x + entropy b y)
    (hcompose : ∀ {a b z} (x : State a) (y : State b) (w : State z),
      accessible ⟨a, x⟩ ⟨b, y⟩ →
      accessible ⟨a + z, compose x w⟩ ⟨b + z, compose y w⟩) (a b z : Γ) :
    directCost State entropy accessible (a + z) (b + z) ≤
      directCost State entropy accessible a b := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (State z))
  apply le_sInf
  rintro r ⟨x, y, hxy, rfl⟩
  simpa only [hentropy, add_sub_add_right_eq_sub] using
    directCost_le State entropy accessible (hcompose x y w hxy)

/-- Parallel composition makes direct costs subadditive. Unreachable inputs
may have cost `+∞`; only `-∞` is excluded, as supplied below by cycle consistency
and absence of sinks. This avoids the indeterminate mixed-infinity case. -/
theorem directCost_subadditive [AddCommMonoid Γ]
    (compose : ∀ {a b}, State a → State b → State (a + b))
    (hentropy : ∀ {a b} (x : State a) (y : State b),
      entropy (a + b) (compose x y) = entropy a x + entropy b y)
    (hcompose : ∀ {a b c d} (x : State a) (y : State b) (u : State c) (v : State d),
      accessible ⟨a, x⟩ ⟨b, y⟩ → accessible ⟨c, u⟩ ⟨d, v⟩ →
      accessible ⟨a + c, compose x u⟩ ⟨b + d, compose y v⟩)
    (a b c d : Γ)
    (hab : directCost State entropy accessible a b ≠ ⊥)
    (hcd : directCost State entropy accessible c d ≠ ⊥) :
    directCost State entropy accessible (a + c) (b + d) ≤
      directCost State entropy accessible a b + directCost State entropy accessible c d := by
  apply EReal.le_add_of_forall_gt (.inl hab) (.inr hcd)
  intro r hr s hs
  obtain ⟨r', ⟨x, y, hxy, rfl⟩, hrr⟩ := sInf_lt_iff.mp hr
  obtain ⟨s', ⟨u, v, huv, rfl⟩, hss⟩ := sInf_lt_iff.mp hs
  have hsum := directCost_le State entropy accessible (hcompose x y u v hxy huv)
  have heq : entropy (b + d) (compose y v) - entropy (a + c) (compose x u) =
      (entropy b y - entropy a x) + (entropy d v - entropy c u) := by
    rw [hentropy, hentropy]
    abel
  rw [heq, EReal.coe_add] at hsum
  exact hsum.trans (add_le_add hrr.le hss.le)

/-- Reversible state scaling carries the infimum of transition costs to its scaled value. -/
theorem directCost_scale_equiv {a b a' b' : Γ} (r : ℝ) (hr : 0 < r)
    (ea : State a ≃ State a') (eb : State b ≃ State b')
    (haccess : ∀ x y, accessible ⟨a', ea x⟩ ⟨b', eb y⟩ ↔ accessible ⟨a, x⟩ ⟨b, y⟩)
    (hentropy : ∀ x y, entropy b' (eb y) - entropy a' (ea x) =
      r * (entropy b y - entropy a x)) :
    directCost State entropy accessible a' b' =
      costScale r hr (directCost State entropy accessible a b) := by
  apply le_antisymm
  · change directCost State entropy accessible a' b' ≤ costScale r hr (sInf _)
    rw [(costScale r hr).map_sInf]
    apply le_iInf₂
    rintro c ⟨x, y, hxy, rfl⟩
    simpa only [hentropy, costScale_apply, EReal.coe_mul] using
      directCost_le State entropy accessible ((haccess x y).mpr hxy)
  · apply le_sInf
    rintro c ⟨x, y, hxy, rfl⟩
    have hxy' : accessible ⟨a, ea.symm x⟩ ⟨b, eb.symm y⟩ :=
      (haccess (ea.symm x) (eb.symm y)).mp (by simpa using hxy)
    have h := (costScale r hr).monotone (directCost_le State entropy accessible hxy')
    have heq := hentropy (ea.symm x) (eb.symm y)
    simpa only [costScale_apply, ← EReal.coe_mul, ← heq, Equiv.apply_symm_apply] using h

/-- Extensivity and invertible scaling of accessibility imply direct-cost homogeneity. -/
theorem directCost_smul [AddCommMonoid Γ] [Module ℝ≥0 Γ]
    (scale : ∀ (r : ℝ≥0), 0 < r → ∀ a, State a ≃ State (r • a))
    (hentropy : ∀ (r : ℝ≥0) (hr : 0 < r) a (x : State a),
      entropy (r • a) (scale r hr a x) = (r : ℝ) * entropy a x)
    (haccess : ∀ (r : ℝ≥0) (hr : 0 < r) a b (x : State a) (y : State b),
      accessible ⟨r • a, scale r hr a x⟩ ⟨r • b, scale r hr b y⟩ ↔
        accessible ⟨a, x⟩ ⟨b, y⟩)
    (r : ℝ≥0) (hr : 0 < r) (a b : Γ) :
    directCost State entropy accessible (r • a) (r • b) =
      costScale r (NNReal.coe_pos.mpr hr) (directCost State entropy accessible a b) := by
  apply directCost_scale_equiv State entropy accessible r (NNReal.coe_pos.mpr hr)
    (scale r hr a) (scale r hr b) (haccess r hr a b)
  intro x y
  rw [hentropy, hentropy, mul_sub]

/-- A finite chain with its total transition cost. Each edge is available. -/
inductive CostChain (D : Γ → Γ → EReal) (a : Γ) : Γ → EReal → Prop
  | nil : CostChain D a a 0
  | step {b c : Γ} {r : EReal} : CostChain D a b r → D b c < ⊤ →
      CostChain D a c (r + D b c)

theorem CostChain.finite {D : Γ → Γ → EReal} {a b : Γ} {r : EReal}
    (h : CostChain D a b r) : r < ⊤ := by
  induction h with
  | nil => exact EReal.coe_lt_top 0
  | step _ hstep ih => exact lt_top_iff_ne_top.mpr (EReal.add_ne_top ih.ne hstep.ne)

theorem CostChain.append {D : Γ → Γ → EReal} {a b c : Γ} {r s : EReal}
    (h : CostChain D a b r) (k : CostChain D b c s) : CostChain D a c (r + s) := by
  induction k with
  | nil => simpa only [add_zero] using h
  | step _ hstep ih => simpa only [add_assoc] using CostChain.step ih hstep

theorem CostChain.map_le {D : Γ → Γ → EReal} (f : Γ → Γ)
    (hf : ∀ a b, D (f a) (f b) ≤ D a b) {a b : Γ} {r : EReal}
    (h : CostChain D a b r) : ∃ s, CostChain D (f a) (f b) s ∧ s ≤ r := by
  induction h with
  | nil => exact ⟨0, CostChain.nil, le_rfl⟩
  | step _ hstep ih =>
    obtain ⟨s, hs, hsr⟩ := ih
    exact ⟨_, CostChain.step hs ((hf _ _).trans_lt hstep), add_le_add hsr (hf _ _)⟩

theorem CostChain.smul [AddCommMonoid Γ] [Module ℝ≥0 Γ]
    {D : Γ → Γ → EReal} (r : ℝ≥0) (hr : 0 < r)
    (hscale : ∀ a b, D (r • a) (r • b) = costScale r (NNReal.coe_pos.mpr hr) (D a b))
    {a b : Γ} {c : EReal} (h : CostChain D a b c) :
    CostChain D (r • a) (r • b) (costScale r (NNReal.coe_pos.mpr hr) c) := by
  induction h with
  | nil => simpa only [costScale_zero] using CostChain.nil
  | @step b c t _ hstep ih =>
    have htop : costScale r (NNReal.coe_pos.mpr hr) ⊤ = ⊤ := rfl
    have hedge : D (r • b) (r • c) < ⊤ := by
      rw [hscale, ← htop]
      exact (costScale r (NNReal.coe_pos.mpr hr)).strictMono hstep
    simpa only [hscale, costScale_add] using CostChain.step ih hedge

/-- The least cost of a finite chain of available transformations. -/
def chainCost (D : Γ → Γ → EReal) (a b : Γ) : EReal :=
  sInf {r | CostChain D a b r}

/-- Cycle consistency normalizes the infimum over self-chains to zero. -/
theorem chainCost_self (D : Γ → Γ → EReal)
    (hcycle : ∀ a r, CostChain D a a r → 0 ≤ r) (a : Γ) :
    chainCost D a a = 0 := by
  apply le_antisymm (sInf_le CostChain.nil)
  exact le_sInf fun r hr => hcycle a r hr

theorem chainCost_map_le (D : Γ → Γ → EReal) (f : Γ → Γ)
    (hf : ∀ a b, D (f a) (f b) ≤ D a b) (a b : Γ) :
    chainCost D (f a) (f b) ≤ chainCost D a b := by
  apply le_sInf
  intro r hr
  obtain ⟨s, hs, hsr⟩ := hr.map_le f hf
  exact (sInf_le hs).trans hsr

theorem chainCost_triangle (D : Γ → Γ → EReal) (a b c : Γ)
    (hab : chainCost D a b < ⊤) (hbc : chainCost D b c < ⊤) :
    chainCost D a c ≤ chainCost D a b + chainCost D b c := by
  apply EReal.le_add_of_forall_gt (.inr hbc.ne) (.inl hab.ne)
  intro r hr s hs
  obtain ⟨r', hr', hrr⟩ := sInf_lt_iff.mp hr
  obtain ⟨s', hs', hss⟩ := sInf_lt_iff.mp hs
  exact (sInf_le (CostChain.append hr' hs')).trans (add_le_add hrr.le hss.le)

/-- Chain costs are subadditive under composition. A common spectator may
lower the direct cost, which suffices to compose two chains successively.
The statement includes unreachable `+∞` inputs. -/
theorem chainCost_subadditive [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b) (a b c d : Γ)
    (hab : chainCost D a b ≠ ⊥) (hcd : chainCost D c d ≠ ⊥) :
    chainCost D (a + c) (b + d) ≤ chainCost D a b + chainCost D c d := by
  by_cases hatop : chainCost D a b = ⊤
  · rw [hatop, EReal.top_add_of_ne_bot hcd]
    exact le_top
  by_cases hctop : chainCost D c d = ⊤
  · rw [hctop, EReal.add_top_of_ne_bot hab]
    exact le_top
  have hleft : chainCost D (a + c) (b + c) ≤ chainCost D a b :=
    chainCost_map_le D (fun x => x + c) (fun x y => hshift x y c) a b
  have hright : chainCost D (b + c) (b + d) ≤ chainCost D c d := by
    simpa only [add_comm b] using
      chainCost_map_le D (fun x => x + b) (fun x y => hshift x y b) c d
  exact (chainCost_triangle D (a + c) (b + c) (b + d)
    (hleft.trans_lt (lt_top_iff_ne_top.mpr hatop))
    (hright.trans_lt (lt_top_iff_ne_top.mpr hctop))).trans (add_le_add hleft hright)

theorem chainCost_smul_le [AddCommMonoid Γ] [Module ℝ≥0 Γ]
    (D : Γ → Γ → EReal) (r : ℝ≥0) (hr : 0 < r)
    (hscale : ∀ a b, D (r • a) (r • b) = costScale r (NNReal.coe_pos.mpr hr) (D a b)) (a b : Γ) :
    chainCost D (r • a) (r • b) ≤ costScale r (NNReal.coe_pos.mpr hr) (chainCost D a b) := by
  simp only [chainCost]
  rw [(costScale r (NNReal.coe_pos.mpr hr)).map_sInf]
  apply le_iInf₂
  intro c hc
  exact sInf_le (hc.smul r hr hscale)

/-- Invertible positive scaling preserves the full chain infimum, including
unreachable costs and costs that have not yet been shown bounded below. -/
theorem chainCost_smul [AddCommMonoid Γ] [Module ℝ≥0 Γ]
    (D : Γ → Γ → EReal)
    (hscale : ∀ (r : ℝ≥0) (hr : 0 < r) a b,
      D (r • a) (r • b) = costScale r (NNReal.coe_pos.mpr hr) (D a b))
    (r : ℝ≥0) (hr : 0 < r) (a b : Γ) :
    chainCost D (r • a) (r • b) =
      costScale r (NNReal.coe_pos.mpr hr) (chainCost D a b) := by
  apply le_antisymm (chainCost_smul_le D r hr (hscale r hr) a b)
  have h := (costScale r (NNReal.coe_pos.mpr hr)).monotone
    (chainCost_smul_le D r⁻¹ (inv_pos.mpr hr) (hscale r⁻¹ (inv_pos.mpr hr))
      (r • a) (r • b))
  simpa only [inv_smul_smul₀ hr.ne', NNReal.coe_inv, costScale_inv] using h

theorem chainCost_le_direct (D : Γ → Γ → EReal) (a b : Γ) :
    chainCost D a b ≤ D a b := by
  by_cases h : D a b = ⊤
  · simp [h]
  · apply sInf_le
    change CostChain D a b (D a b)
    simpa only [zero_add] using CostChain.step (CostChain.nil (D := D) (a := a))
      (lt_top_iff_ne_top.mpr h)

/-- The least chain cost after adjoining the same catalyst to both systems. -/
def catalystCost [AddCommMonoid Γ] (D : Γ → Γ → EReal) (a b : Γ) : EReal :=
  ⨅ z, chainCost D (a + z) (b + z)

/-- System reachability through finitely many transformations and a catalyst. -/
def Connected [AddCommMonoid Γ] (D : Γ → Γ → EReal) (a b : Γ) : Prop :=
  ∃ z r, CostChain D (a + z) (b + z) r

/-- Absence of sinks is symmetry of system reachability. -/
def NoSinks [AddCommMonoid Γ] (D : Γ → Γ → EReal) : Prop :=
  ∀ a b, Connected D a b → Connected D b a

theorem catalystCost_lt_top_iff_connected [AddCommMonoid Γ]
    (D : Γ → Γ → EReal) (a b : Γ) : catalystCost D a b < ⊤ ↔ Connected D a b := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := iInf_lt_iff.mp h
    obtain ⟨r, hr, _⟩ := sInf_lt_iff.mp hz
    exact ⟨z, r, hr⟩
  · rintro ⟨z, r, hr⟩
    exact ((iInf_le (fun z => chainCost D (a + z) (b + z)) z).trans
      (sInf_le hr)).trans_lt hr.finite

theorem NoSinks.cost_symmetry [AddCommMonoid Γ] {D : Γ → Γ → EReal} (hM : NoSinks D)
    (a b : Γ) (h : catalystCost D a b < ⊤) : catalystCost D b a < ⊤ :=
  (catalystCost_lt_top_iff_connected D b a).mpr
    (hM a b ((catalystCost_lt_top_iff_connected D a b).mp h))

theorem catalystCost_le_chain [AddCommMonoid Γ] (D : Γ → Γ → EReal) (a b : Γ) :
    catalystCost D a b ≤ chainCost D a b := by
  change (⨅ z, chainCost D (a + z) (b + z)) ≤ chainCost D a b
  simpa only [add_zero] using iInf_le (fun z => chainCost D (a + z) (b + z)) 0

theorem catalystCost_le_direct [AddCommMonoid Γ] (D : Γ → Γ → EReal) (a b : Γ) :
    catalystCost D a b ≤ D a b :=
  (catalystCost_le_chain D a b).trans (chainCost_le_direct D a b)

theorem catalystCost_add_same [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b) (a b z : Γ) :
    catalystCost D (a + z) (b + z) = catalystCost D a b := by
  apply le_antisymm
  · apply le_iInf
    intro w
    refine (iInf_le (fun c => chainCost D (a + z + c) (b + z + c)) w).trans ?_
    simpa only [add_right_comm a z w, add_right_comm b z w] using
      chainCost_map_le D (fun c => c + z) (fun a b => hshift a b z) (a + w) (b + w)
  · apply le_iInf
    intro w
    change (⨅ c, chainCost D (a + c) (b + c)) ≤ _
    simpa only [add_assoc] using
      iInf_le (fun c => chainCost D (a + c) (b + c)) (z + w)

theorem catalystCost_triangle [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b) (a b c : Γ)
    (hab : catalystCost D a b < ⊤) (hbc : catalystCost D b c < ⊤) :
    catalystCost D a c ≤ catalystCost D a b + catalystCost D b c := by
  apply EReal.le_add_of_forall_gt (.inr hbc.ne) (.inl hab.ne)
  intro r hr s hs
  obtain ⟨z, hz⟩ := iInf_lt_iff.mp hr
  obtain ⟨w, hw⟩ := iInf_lt_iff.mp hs
  obtain ⟨r', hr', hrr⟩ := sInf_lt_iff.mp hz
  obtain ⟨s', hs', hss⟩ := sInf_lt_iff.mp hw
  obtain ⟨u, hu, hur⟩ := hr'.map_le (fun d => d + w) (fun a b => hshift a b w)
  obtain ⟨v, hv, hvs⟩ := hs'.map_le (fun d => d + z) (fun a b => hshift a b z)
  have hv' : CostChain D (b + z + w) (c + z + w) v := by
    simpa only [add_right_comm b w z, add_right_comm c w z] using hv
  have hchain : chainCost D (a + (z + w)) (c + (z + w)) ≤ u + v := by
    apply sInf_le
    change CostChain D (a + (z + w)) (c + (z + w)) (u + v)
    simpa only [add_assoc] using hu.append hv'
  exact (iInf_le (fun t => chainCost D (a + t) (c + t)) (z + w)).trans
    (hchain.trans (add_le_add (hur.trans hrr.le) (hvs.trans hss.le)))

theorem catalystCost_subadditive [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b) (a b c d : Γ)
    (hab : catalystCost D a b < ⊤) (hcd : catalystCost D c d < ⊤) :
    catalystCost D (a + c) (b + d) ≤ catalystCost D a b + catalystCost D c d := by
  have hleft := catalystCost_add_same D hshift a b c
  have hright : catalystCost D (b + c) (b + d) = catalystCost D c d := by
    simpa only [add_comm b] using catalystCost_add_same D hshift c d b
  simpa only [hleft, hright] using catalystCost_triangle D hshift (a + c) (b + c)
    (b + d) (hleft ▸ hab) (hright ▸ hcd)

theorem catalystCost_self [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hcycle : ∀ a r, CostChain D a a r → 0 ≤ r) (a : Γ) :
    catalystCost D a a = 0 := by
  apply le_antisymm
  · exact (catalystCost_le_chain D a a).trans (sInf_le CostChain.nil)
  · apply le_iInf
    intro z
    exact le_sInf fun r hr => hcycle (a + z) r hr

/-- Cycles and absence of sinks exclude negative infinity for catalytic cost,
without assuming that every pair of labels is reachable. -/
theorem catalystCost_ne_bot_of_noSinks [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b)
    (hcycle : ∀ a r, CostChain D a a r → 0 ≤ r) (hM : NoSinks D) (a b : Γ) :
    catalystCost D a b ≠ ⊥ := by
  intro hbot
  have hab : catalystCost D a b < ⊤ := hbot ▸ bot_lt_top
  have hba := hM.cost_symmetry a b hab
  have h := catalystCost_triangle D hshift a b a hab hba
  rw [catalystCost_self D hcycle, hbot, EReal.bot_add] at h
  exact (show ¬ (0 : EReal) ≤ ⊥ by simp) h

/-- The lower catalytic bound excludes negative infinity for chain costs too. -/
theorem chainCost_ne_bot_of_noSinks [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b)
    (hcycle : ∀ a r, CostChain D a a r → 0 ≤ r) (hM : NoSinks D) (a b : Γ) :
    chainCost D a b ≠ ⊥ := by
  intro hbot
  apply catalystCost_ne_bot_of_noSinks D hshift hcycle hM a b
  exact bot_unique (hbot ▸ catalystCost_le_chain D a b)

/-- Direct costs also retain `+∞` but cannot equal `-∞` under the physical
cycle and no-sinks premises. -/
theorem directCost_ne_bot_of_noSinks [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b)
    (hcycle : ∀ a r, CostChain D a a r → 0 ≤ r) (hM : NoSinks D) (a b : Γ) :
    D a b ≠ ⊥ := by
  intro hbot
  apply catalystCost_ne_bot_of_noSinks D hshift hcycle hM a b
  exact bot_unique (hbot ▸ catalystCost_le_direct D a b)

/-- Direct composition subadditivity with its lower-bound obligations derived
from cycles and absence of sinks. No reachability or finite-cost assumption is
made on either pair of input labels. -/
theorem directCost_subadditive_of_noSinks [AddCommMonoid Γ]
    (compose : ∀ {a b}, State a → State b → State (a + b))
    (hentropy : ∀ {a b} (x : State a) (y : State b),
      entropy (a + b) (compose x y) = entropy a x + entropy b y)
    (hcompose : ∀ {a b c d} (x : State a) (y : State b) (u : State c) (v : State d),
      accessible ⟨a, x⟩ ⟨b, y⟩ → accessible ⟨c, u⟩ ⟨d, v⟩ →
      accessible ⟨a + c, compose x u⟩ ⟨b + d, compose y v⟩)
    (hshift : ∀ a b z, directCost State entropy accessible (a + z) (b + z) ≤
      directCost State entropy accessible a b)
    (hcycle : ∀ a r, CostChain (directCost State entropy accessible) a a r → 0 ≤ r)
    (hM : NoSinks (directCost State entropy accessible)) (a b c d : Γ) :
    directCost State entropy accessible (a + c) (b + d) ≤
      directCost State entropy accessible a b + directCost State entropy accessible c d :=
  directCost_subadditive State entropy accessible compose hentropy hcompose a b c d
    (directCost_ne_bot_of_noSinks _ hshift hcycle hM a b)
    (directCost_ne_bot_of_noSinks _ hshift hcycle hM c d)

/-- The chain triangle inequality includes unreachable costs once absence of
sinks has excluded negative infinity. -/
theorem chainCost_triangle_of_noSinks [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b)
    (hcycle : ∀ a r, CostChain D a a r → 0 ≤ r) (hM : NoSinks D) (a b c : Γ) :
    chainCost D a c ≤ chainCost D a b + chainCost D b c := by
  by_cases hab : chainCost D a b = ⊤
  · rw [hab, EReal.top_add_of_ne_bot (chainCost_ne_bot_of_noSinks D hshift hcycle hM b c)]
    exact le_top
  by_cases hbc : chainCost D b c = ⊤
  · rw [hbc, EReal.add_top_of_ne_bot (chainCost_ne_bot_of_noSinks D hshift hcycle hM a b)]
    exact le_top
  exact chainCost_triangle D a b c (lt_top_iff_ne_top.mpr hab) (lt_top_iff_ne_top.mpr hbc)

/-- Catalytic triangle inequalities retain the unreachable `+∞` cases. -/
theorem catalystCost_triangle_of_noSinks [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b)
    (hcycle : ∀ a r, CostChain D a a r → 0 ≤ r) (hM : NoSinks D) (a b c : Γ) :
    catalystCost D a c ≤ catalystCost D a b + catalystCost D b c := by
  by_cases hab : catalystCost D a b = ⊤
  · rw [hab, EReal.top_add_of_ne_bot (catalystCost_ne_bot_of_noSinks D hshift hcycle hM b c)]
    exact le_top
  by_cases hbc : catalystCost D b c = ⊤
  · rw [hbc, EReal.add_top_of_ne_bot (catalystCost_ne_bot_of_noSinks D hshift hcycle hM a b)]
    exact le_top
  exact catalystCost_triangle D hshift a b c
    (lt_top_iff_ne_top.mpr hab) (lt_top_iff_ne_top.mpr hbc)

/-- Under absence of sinks, chain subadditivity needs no finite-cost premise. -/
theorem chainCost_subadditive_of_noSinks [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b)
    (hcycle : ∀ a r, CostChain D a a r → 0 ≤ r) (hM : NoSinks D) (a b c d : Γ) :
    chainCost D (a + c) (b + d) ≤ chainCost D a b + chainCost D c d :=
  chainCost_subadditive D hshift a b c d
    (chainCost_ne_bot_of_noSinks D hshift hcycle hM a b)
    (chainCost_ne_bot_of_noSinks D hshift hcycle hM c d)

/-- Catalytic composition subadditivity without finite-reachability premises. -/
theorem catalystCost_subadditive_of_noSinks [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b)
    (hcycle : ∀ a r, CostChain D a a r → 0 ≤ r) (hM : NoSinks D) (a b c d : Γ) :
    catalystCost D (a + c) (b + d) ≤ catalystCost D a b + catalystCost D c d := by
  have hleft := catalystCost_add_same D hshift a b c
  have hright : catalystCost D (b + c) (b + d) = catalystCost D c d := by
    simpa only [add_comm b] using catalystCost_add_same D hshift c d b
  simpa only [hleft, hright] using
    catalystCost_triangle_of_noSinks D hshift hcycle hM (a + c) (b + c) (b + d)

theorem catalystCost_smul_le [AddCommMonoid Γ] [Module ℝ≥0 Γ]
    (D : Γ → Γ → EReal) (r : ℝ≥0) (hr : 0 < r)
    (hscale : ∀ a b, D (r • a) (r • b) = costScale r (NNReal.coe_pos.mpr hr) (D a b)) (a b : Γ) :
    catalystCost D (r • a) (r • b) ≤ costScale r (NNReal.coe_pos.mpr hr) (catalystCost D a b) := by
  simp only [catalystCost]
  rw [(costScale r (NNReal.coe_pos.mpr hr)).map_iInf]
  apply le_iInf
  intro z
  refine (iInf_le (fun c => chainCost D (r • a + c) (r • b + c)) (r • z)).trans ?_
  simpa only [smul_add] using chainCost_smul_le D r hr hscale (a + z) (b + z)

theorem catalystCost_smul [AddCommMonoid Γ] [Module ℝ≥0 Γ]
    (D : Γ → Γ → EReal)
    (hscale : ∀ (r : ℝ≥0) (hr : 0 < r) a b,
      D (r • a) (r • b) = costScale r (NNReal.coe_pos.mpr hr) (D a b))
    (r : ℝ≥0) (hr : 0 < r) (a b : Γ) :
    catalystCost D (r • a) (r • b) = costScale r (NNReal.coe_pos.mpr hr) (catalystCost D a b) := by
  apply le_antisymm (catalystCost_smul_le D r hr (hscale r hr) a b)
  have h := (costScale r (NNReal.coe_pos.mpr hr)).monotone
    (catalystCost_smul_le D r⁻¹ (inv_pos.mpr hr) (hscale r⁻¹ (inv_pos.mpr hr))
      (r • a) (r • b))
  simpa only [inv_smul_smul₀ hr.ne', NNReal.coe_inv, costScale_inv] using h

/-- Catalytic invariance respects the equivalence defining formal differences. -/
theorem catalystCost_eq_of_cross_add [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b)
    {a b c d z : Γ} (h : z + (d + a) = z + (b + c)) :
    catalystCost D a b = catalystCost D c d := by
  have hnum : a + (d + z) = c + (b + z) := by
    simpa only [add_comm, add_left_comm, add_assoc] using h
  calc
    catalystCost D a b = catalystCost D (a + (d + z)) (b + (d + z)) :=
      (catalystCost_add_same D hshift a b (d + z)).symm
    _ = catalystCost D (c + (b + z)) (d + (b + z)) := by
      rw [hnum]
      congr 1
      ac_rfl
    _ = catalystCost D c d := catalystCost_add_same D hshift c d (b + z)

/-- The catalyst cost descended to formal differences of system types. -/
def completedCost [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b) (v : Completion Γ) : EReal :=
  AddLocalization.liftOn v (fun a b => catalystCost D a b.val) (by
    intro a c b d h
    obtain ⟨z, hz⟩ := AddLocalization.r_iff_exists.mp h
    exact catalystCost_eq_of_cross_add D hshift hz)

@[simp] theorem completedCost_of_sub [AddCommMonoid Γ] (D : Γ → Γ → EReal)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b) (a b : Γ) :
    completedCost D hshift (Completion.of a - Completion.of b) = catalystCost D a b := by
  simp [Completion.of, Algebra.GrothendieckAddGroup.of,
    ← AddLocalization.mk_zero_eq_addMonoidOf_mk, Algebra.GrothendieckAddGroup.mk_sub_mk,
    completedCost, AddLocalization.liftOn_mk]

theorem catalystCost_le_entropy_change [AddCommMonoid Γ]
    {a b : Γ} {x : State a} {y : State b} (h : accessible ⟨a, x⟩ ⟨b, y⟩) :
    catalystCost (directCost State entropy accessible) a b ≤
      ((entropy b y - entropy a x : ℝ) : EReal) :=
  (catalystCost_le_direct _ a b).trans (directCost_le State entropy accessible h)

end TransitionCosts

section CorrectedEntropy

variable {Γ : Type*} [AddCommMonoid Γ] [Module ℝ≥0 Γ]
  {State : Γ → Type*} (entropy : ∀ g, State g → ℝ) (B : Γ →ₗ[ℝ≥0] ℝ)

/-- Calibrated state entropy with the selected system-dependent constant. -/
def correctedEntropy (x : Σ g, State g) : ℝ := entropy x.1 x.2 + B x.1

/-- Additive calibrated entropy remains additive after correction. -/
theorem correctedEntropy_compose
    (compose : ∀ {a b}, State a → State b → State (a + b))
    (hentropy : ∀ {a b} (x : State a) (y : State b),
      entropy (a + b) (compose x y) = entropy a x + entropy b y)
    {a b : Γ} (x : State a) (y : State b) :
    correctedEntropy entropy B ⟨a + b, compose x y⟩ =
      correctedEntropy entropy B ⟨a, x⟩ + correctedEntropy entropy B ⟨b, y⟩ := by
  simp only [correctedEntropy, hentropy, map_add]
  ring

/-- Extensive calibrated entropy remains extensive after correction. -/
theorem correctedEntropy_scale
    (scale : ∀ (r : ℝ≥0), 0 < r → ∀ a, State a → State (r • a))
    (hentropy : ∀ (r : ℝ≥0) (hr : 0 < r) a (x : State a),
      entropy (r • a) (scale r hr a x) = (r : ℝ) * entropy a x)
    (r : ℝ≥0) (hr : 0 < r) {a : Γ} (x : State a) :
    correctedEntropy entropy B ⟨r • a, scale r hr a x⟩ =
      (r : ℝ) * correctedEntropy entropy B ⟨a, x⟩ := by
  simp only [correctedEntropy, hentropy, map_smul, NNReal.smul_def, smul_eq_mul]
  ring

end CorrectedEntropy

section HahnBanach

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Sublinearity before excluding negative infinity, and the no-sinks axiom. -/
structure CostLaws (F : V → EReal) : Prop where
  zero : F 0 = 0
  add_le : ∀ x y, F x < ⊤ → F y < ⊤ → F (x + y) ≤ F x + F y
  positive_homogeneous : ∀ (r : ℝ), 0 < r → ∀ x, F (r • x) = (r : EReal) * F x
  no_sinks : ∀ x, F x < ⊤ → F (-x) < ⊤

/-- The chain and catalyst construction supplies the laws needed by Hahn–Banach.
The system model supplies scaling, cycle consistency, and the no-sinks premise. -/
theorem costLaws_of_catalyst {Γ : Type*} [AddCommMonoid Γ] [Module ℝ≥0 Γ]
    (D : Γ → Γ → EReal) (system : Γ →ₗ[ℝ≥0] V) (F : V → EReal)
    (hrep : ∀ v : V, ∃ a b, v = system a - system b)
    (hcost : ∀ a b, F (system a - system b) = catalystCost D a b)
    (hshift : ∀ a b z, D (a + z) (b + z) ≤ D a b)
    (hscale : ∀ (r : ℝ≥0) (hr : 0 < r) a b,
      D (r • a) (r • b) = costScale r (NNReal.coe_pos.mpr hr) (D a b))
    (hcycle : ∀ a r, CostChain D a a r → 0 ≤ r)
    (hsinks : ∀ a b, catalystCost D a b < ⊤ → catalystCost D b a < ⊤) : CostLaws F where
  zero := by
    simpa only [sub_self] using (hcost 0 0).trans (catalystCost_self D hcycle 0)
  add_le v w hv hw := by
    obtain ⟨a, b, rfl⟩ := hrep v
    obtain ⟨c, d, rfl⟩ := hrep w
    have heq : system a - system b + (system c - system d) =
        system (a + c) - system (b + d) := by simp only [map_add]; abel
    rw [heq, hcost, hcost, hcost]
    exact catalystCost_subadditive D hshift a b c d ((hcost a b) ▸ hv) ((hcost c d) ▸ hw)
  positive_homogeneous r hr v := by
    obtain ⟨a, b, rfl⟩ := hrep v
    let t : ℝ≥0 := ⟨r, hr.le⟩
    have ht : 0 < t := hr
    have heq : r • (system a - system b) = system (t • a) - system (t • b) := by
      simp only [map_smul, NNReal.smul_def, smul_sub]
      rfl
    rw [heq, hcost, hcost, catalystCost_smul D hscale t ht, costScale_apply]
    rfl
  no_sinks v hv := by
    obtain ⟨a, b, rfl⟩ := hrep v
    rw [neg_sub, hcost]
    exact hsinks a b ((hcost a b) ▸ hv)

namespace CostLaws

variable {F : V → EReal} (hF : CostLaws F)

include hF

/-- A returning finite-cost chain excludes an unbounded entropy gain. -/
theorem ne_bot (x : V) : F x ≠ ⊥ := by
  intro hx
  have hxt : F x < ⊤ := by rw [hx]; exact bot_lt_top
  have h := hF.add_le x (-x) hxt (hF.no_sinks x hxt)
  rw [add_neg_cancel, hF.zero, hx, EReal.bot_add] at h
  exact (show ¬ (0 : EReal) ≤ ⊥ by simp) h

private theorem finite_smul_nonneg {x : V} (hx : F x < ⊤) {r : ℝ} (hr : 0 ≤ r) :
    F (r • x) < ⊤ := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [hF.zero]
  · rw [hF.positive_homogeneous r hr]
    rw [← EReal.coe_toReal hx.ne (hF.ne_bot x), ← EReal.coe_mul]
    exact EReal.coe_lt_top _

/-- Axiom M makes the finite-cost domain into a real linear subspace. -/
def finiteDomain : Submodule ℝ V where
  carrier := {x | F x < ⊤}
  zero_mem' := by change F 0 < ⊤; rw [hF.zero]; exact EReal.coe_lt_top 0
  add_mem' hx hy := lt_of_le_of_lt (hF.add_le _ _ hx hy)
    (lt_top_iff_ne_top.mpr (EReal.add_ne_top hx.ne hy.ne))
  smul_mem' r x hx := by
    change F (r • x) < ⊤
    by_cases hr : 0 ≤ r
    · exact hF.finite_smul_nonneg hx hr
    · have hr' : 0 ≤ -r := neg_nonneg.mpr (le_of_not_ge hr)
      have h := hF.finite_smul_nonneg (hF.no_sinks x hx) hr'
      simpa only [neg_smul, smul_neg, neg_neg] using h

/-- The cost restricted to its finite domain. -/
def finiteCost (x : hF.finiteDomain) : ℝ := (F x).toReal

theorem finiteCost_homogeneous (r : ℝ) (hr : 0 < r) (x : hF.finiteDomain) :
    hF.finiteCost (r • x) = r * hF.finiteCost x := by
  change (F (r • (x : V))).toReal = _
  rw [hF.positive_homogeneous r hr, EReal.toReal_mul, EReal.toReal_coe]
  rfl

theorem finiteCost_subadditive (x y : hF.finiteDomain) :
    hF.finiteCost (x + y) ≤ hF.finiteCost x + hF.finiteCost y := by
  change (F ((x : V) + (y : V))).toReal ≤ (F x).toReal + (F y).toReal
  have h := EReal.toReal_le_toReal (hF.add_le x y x.property y.property)
    (hF.ne_bot (x + y)) (EReal.add_ne_top x.property.ne y.property.ne)
  simpa only [EReal.toReal_add x.property.ne (hF.ne_bot x) y.property.ne (hF.ne_bot y)] using h

/-- Hahn–Banach chooses compatible additive constants, including infinite costs. -/
theorem exists_linear_bound : ∃ L : V →ₗ[ℝ] ℝ, ∀ x,
    -F (-x) ≤ (L x : EReal) ∧ (L x : EReal) ≤ F x := by
  let p : hF.finiteDomain →ₗ.[ℝ] ℝ := ⟨⊥, 0⟩
  obtain ⟨f, _, hf⟩ := exists_extension_of_le_sublinear p hF.finiteCost
    hF.finiteCost_homogeneous hF.finiteCost_subadditive (by
      intro x
      have hx : x.val = 0 := x.property
      simp [p, hx, finiteCost, hF.zero])
  obtain ⟨L, hL⟩ := f.exists_extend
  have hbound (x : V) : (L x : EReal) ≤ F x := by
    by_cases hx : F x = ⊤
    · simp [hx]
    · let y : hF.finiteDomain := ⟨x, lt_top_iff_ne_top.mpr hx⟩
      have hy : L x = f y := congrArg (fun g : hF.finiteDomain →ₗ[ℝ] ℝ => g y) hL
      rw [hy, ← EReal.coe_toReal hx (hF.ne_bot x)]
      exact EReal.coe_le_coe_iff.mpr (hf y)
  refine ⟨L, fun x => ⟨?_, hbound x⟩⟩
  have h := EReal.neg_le_neg_iff.mpr (hbound (-x))
  simpa only [map_neg, EReal.coe_neg, neg_neg] using h

end CostLaws

/-- Cost-selected constants make every admissible transition entropy-monotone. -/
theorem exists_weak_entropy {Γ : Type*} [AddCommMonoid Γ] [Module ℝ≥0 Γ]
    (State : Γ → Type*) (entropy : ∀ g, State g → ℝ)
    (accessible : (Σ g, State g) → (Σ g, State g) → Prop)
    (system : Γ →ₗ[ℝ≥0] V) (F : V → EReal) (hF : CostLaws F)
    (hcost : ∀ a b, F (system a - system b) =
      catalystCost (directCost State entropy accessible) a b) :
    ∃ B : Γ →ₗ[ℝ≥0] ℝ, ∀ {a b : Γ} {x : State a} {y : State b},
      accessible ⟨a, x⟩ ⟨b, y⟩ → entropy a x + B a ≤ entropy b y + B b := by
  obtain ⟨L, hL⟩ := hF.exists_linear_bound
  refine ⟨(L.restrictScalars ℝ≥0).comp system, ?_⟩
  intro a b x y hxy
  have h := (hL (system a - system b)).2.trans
    ((hcost a b) ▸ catalystCost_le_entropy_change State entropy accessible hxy)
  rw [map_sub, EReal.coe_le_coe_iff] at h
  change entropy a x + L (system a) ≤ entropy b y + L (system b)
  linarith

/-- Weak entropy obtained from actual transition costs with explicit model premises. -/
theorem exists_weak_entropy_of_transition_costs
    {Γ : Type*} [AddCommMonoid Γ] [Module ℝ≥0 Γ]
    (State : Γ → Type*) (entropy : ∀ g, State g → ℝ)
    (accessible : (Σ g, State g) → (Σ g, State g) → Prop)
    (system : Γ →ₗ[ℝ≥0] V) (F : V → EReal)
    (hrep : ∀ v : V, ∃ a b, v = system a - system b)
    (hcost : ∀ a b, F (system a - system b) =
      catalystCost (directCost State entropy accessible) a b)
    (hshift : ∀ a b z, directCost State entropy accessible (a + z) (b + z) ≤
      directCost State entropy accessible a b)
    (hscale : ∀ (r : ℝ≥0) (hr : 0 < r) a b,
      directCost State entropy accessible (r • a) (r • b) =
        costScale r (NNReal.coe_pos.mpr hr) (directCost State entropy accessible a b))
    (hcycle : ∀ a r, CostChain (directCost State entropy accessible) a a r → 0 ≤ r)
    (hsinks : ∀ a b, catalystCost (directCost State entropy accessible) a b < ⊤ →
      catalystCost (directCost State entropy accessible) b a < ⊤) :
    ∃ B : Γ →ₗ[ℝ≥0] ℝ, ∀ {a b : Γ} {x : State a} {y : State b},
      accessible ⟨a, x⟩ ⟨b, y⟩ → entropy a x + B a ≤ entropy b y + B b :=
  exists_weak_entropy State entropy accessible system F
    (costLaws_of_catalyst _ system F hrep hcost hshift hscale hcycle hsinks) hcost

/-- The canonical formal-system completion removes the need to choose a cost descent. -/
theorem exists_weak_entropy_from_cost_model
    {Γ : Type*} [AddCommMonoid Γ] [Module ℝ≥0 Γ]
    (State : Γ → Type*) (entropy : ∀ g, State g → ℝ)
    (accessible : (Σ g, State g) → (Σ g, State g) → Prop)
    (hshift : ∀ a b z, directCost State entropy accessible (a + z) (b + z) ≤
      directCost State entropy accessible a b)
    (hscale : ∀ (r : ℝ≥0) (hr : 0 < r) a b,
      directCost State entropy accessible (r • a) (r • b) =
        costScale r (NNReal.coe_pos.mpr hr) (directCost State entropy accessible a b))
    (hcycle : ∀ a r, CostChain (directCost State entropy accessible) a a r → 0 ≤ r)
    (hsinks : ∀ a b, catalystCost (directCost State entropy accessible) a b < ⊤ →
      catalystCost (directCost State entropy accessible) b a < ⊤) :
    ∃ B : Γ →ₗ[ℝ≥0] ℝ, ∀ {a b : Γ} {x : State a} {y : State b},
      accessible ⟨a, x⟩ ⟨b, y⟩ → entropy a x + B a ≤ entropy b y + B b :=
  exists_weak_entropy_of_transition_costs State entropy accessible Completion.ofLinear
    (completedCost (directCost State entropy accessible) hshift)
    Completion.exists_sub_of (completedCost_of_sub _ hshift) hshift hscale hcycle hsinks

end HahnBanach

end ProjectAInos.Thermodynamics.Reactions
