module

public import ProjectAInos.Thermodynamics.IdealGas
public import ProjectAInos.Thermodynamics.SectorModel
public import ProjectAInos.Thermodynamics.Entropy
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The extensive ideal-gas algebraic consistency model

Composite states are represented by total entropy and positive total amount,
together with the empty state. Its order compares total entropy at equal amount.
The single-box map preserves and reflects accessibility in this algebraic model.
It witnesses stability and exchange comparison, not a `SimpleSystem` or
`ThermalFamily` satisfying the geometric and thermal premises.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.IdealGas

/-- Entropy-amount pairs of nonempty systems, together with the empty system. -/
def extensiveStates : Submodule ℝ≥0 SectorState where
  carrier := {x | x = 0 ∨ 0 < SectorState.amount x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    rcases hx with rfl | hx
    · simpa using hy
    rcases hy with rfl | hy
    · simpa using Or.inr hx
    · exact Or.inr (by simpa using add_pos hx hy)
  smul_mem' := by
    intro a x hx
    rcases hx with rfl | hx
    · exact Or.inl (smul_zero _)
    rcases eq_or_lt_of_le (show 0 ≤ a from bot_le) with ha | ha
    · exact Or.inl (by simp [← ha])
    · exact Or.inr (by simpa using mul_pos (NNReal.coe_pos.mpr ha) hx)

/-- The semimodule of entropy-amount states. -/
abbrev ExtensiveState := extensiveStates

instance : PosSMulMono ℝ≥0 ExtensiveState where
  smul_le_smul_of_nonneg_left {a} ha {x y} h :=
    show a • x.val ≤ a • y.val from smul_le_smul_of_nonneg_left h ha

/-- A box supplies its entropy and positive amount. -/
noncomputable def State.extensive (k c : ℝ) (X : State) : ExtensiveState :=
  ⟨(entropy k c X, X.amount), Or.inr X.amount_pos⟩

/-- Operational accessibility of individual boxes agrees with the model order. -/
theorem accessible_iff_extensive_le {k c : ℝ} (hk : 0 < k) (X Y : State) :
    Accessible X Y ↔ X.extensive k c ≤ Y.extensive k c := accessible_iff hk X Y

/-- Every entropy value occurs at each positive amount. -/
theorem exists_state_of_entropy_amount {k c s n : ℝ} (hk : 0 < k) (hn : 0 < n) :
    ∃ X : State, entropy k c X = s ∧ X.amount = n := by
  let X : State :=
    { energy := n
      volume := n * Real.exp (s / (k * n) - c)
      amount := n
      energy_pos := hn
      volume_pos := mul_pos hn (Real.exp_pos _)
      amount_pos := hn }
  refine ⟨X, ?_, rfl⟩
  dsimp [entropy, entropyValue, X]
  rw [div_self hn.ne', Real.log_one, mul_div_cancel_left₀ _ hn.ne', Real.log_exp]
  field_simp
  ring

/-- A6 descends from coordinatewise limits of entropy and amount. -/
theorem extensive_stability : Stability ExtensiveState := by
  intro x y z₀ z₁ ε hpos hlim h
  exact SectorState.stability x.val y.val z₀.val z₁.val ε hpos hlim h

/-- Equal amounts are comparable, yielding exchange comparison. -/
theorem extensive_exchangeComparison : ExchangeComparison ExtensiveState := by
  intro x y u v hxy huv
  exact SectorState.exchangeComparison x.val y.val u.val v.val hxy huv

/-- Every formal entropy-amount vector is a difference of physical amounts. -/
theorem exists_extensive_difference (v : SectorState) :
    ∃ x y : ExtensiveState, v = (y : SectorState) - (x : SectorState) := by
  let n := max 0 (-SectorState.amount v) + 1
  have hn : 0 < n := by dsimp [n]; linarith [le_max_left (0 : ℝ) (-SectorState.amount v)]
  have hvn : 0 < SectorState.amount v + n := by
    dsimp [n]
    linarith [le_max_right (0 : ℝ) (-SectorState.amount v)]
  refine ⟨⟨(0, n), Or.inr hn⟩,
    ⟨(SectorState.entropy v, SectorState.amount v + n), Or.inr hvn⟩, ?_⟩
  apply Prod.ext
  · change v.1 = v.1 - 0
    simp
  · change v.2 = (v.2 + n) - n
    ring

/-- Completing the positive-amount state cone gives all entropy-amount pairs. -/
noncomputable def extensiveCompletionEquiv : Completion ExtensiveState ≃ₗ[ℝ] SectorState :=
  LinearEquiv.ofBijective (Completion.liftLinear extensiveStates.subtype)
    ⟨Completion.liftLinear_injective _ Subtype.val_injective,
      Completion.liftLinear_surjective _ (fun v => by
        obtain ⟨x, y, h⟩ := exists_extensive_difference v
        exact ⟨y, x, h⟩)⟩

@[simp] theorem extensiveCompletionEquiv_of (x : ExtensiveState) :
    extensiveCompletionEquiv (Completion.of x) = (x : SectorState) :=
  Completion.liftLinear_of _ x

/-- Positive process differences have nonnegative entropy and zero amount. -/
theorem extensive_mem_processCone_iff (v : Completion ExtensiveState) :
    v ∈ processCone ExtensiveState ↔
      SectorState.amount (extensiveCompletionEquiv v) = 0 ∧
        0 ≤ SectorState.entropy (extensiveCompletionEquiv v) := by
  obtain ⟨y, x, rfl⟩ := Completion.exists_sub_of v
  rw [processCone_reflects extensive_stability, map_sub,
    extensiveCompletionEquiv_of, extensiveCompletionEquiv_of]
  change (SectorState.amount x.val = SectorState.amount y.val ∧
      SectorState.entropy x.val ≤ SectorState.entropy y.val) ↔
    (SectorState.amount y.val - SectorState.amount x.val = 0 ∧
      0 ≤ SectorState.entropy y.val - SectorState.entropy x.val)
  rw [sub_eq_zero, sub_nonneg, eq_comm]

/-- The process span is the entropy axis in the completed state space. -/
theorem extensive_mem_processSpan_iff (v : Completion ExtensiveState) :
    v ∈ processSpan ExtensiveState ↔ SectorState.amount (extensiveCompletionEquiv v) = 0 := by
  constructor
  · intro hv
    obtain ⟨p, hp, q, hq, rfl⟩ := (processCone ExtensiveState).mem_span.mp hv
    have hp' := (extensive_mem_processCone_iff p).mp hp
    have hq' := (extensive_mem_processCone_iff q).mp hq
    simp [map_sub, hp'.1, hq'.1]
  · intro hv
    rcases le_total 0 (SectorState.entropy (extensiveCompletionEquiv v)) with hs | hs
    · exact Submodule.subset_span ((extensive_mem_processCone_iff v).mpr ⟨hv, hs⟩)
    · have hneg : -v ∈ processCone ExtensiveState := by
        apply (extensive_mem_processCone_iff (-v)).mpr
        rw [map_neg]
        constructor
        · simpa using congrArg Neg.neg hv
        · change 0 ≤ -SectorState.entropy (extensiveCompletionEquiv v)
          exact neg_nonneg.mpr hs
      simpa using (processSpan ExtensiveState).neg_mem (Submodule.subset_span hneg)

/-- Amount is the universal conserved coordinate in the consistency model. -/
noncomputable def extensiveAmount : Completion ExtensiveState →ₗ[ℝ] ℝ where
  toFun v := SectorState.amount (extensiveCompletionEquiv v)
  map_add' x y := by simp
  map_smul' r v := by
    rw [map_smul]
    rfl

/-- The kernel of amount is exactly the space of accessible process differences. -/
theorem extensiveAmount_ker : LinearMap.ker extensiveAmount = processSpan ExtensiveState := by
  ext v
  exact (extensive_mem_processSpan_iff v).symm

theorem extensiveAmount_surjective : Function.Surjective extensiveAmount := by
  intro n
  let w : SectorState := (0, n)
  refine ⟨extensiveCompletionEquiv.symm w, ?_⟩
  change SectorState.amount (extensiveCompletionEquiv (extensiveCompletionEquiv.symm w)) = n
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The ideal-gas conservation quotient has one coordinate, the amount. -/
noncomputable def extensiveConservationEquiv :
    (Completion ExtensiveState ⧸ processSpan ExtensiveState) ≃ₗ[ℝ] ℝ :=
  (Submodule.quotEquivOfEq _ _ extensiveAmount_ker.symm).trans
    (extensiveAmount.quotKerEquivOfSurjective extensiveAmount_surjective)

end ProjectAInos.Thermodynamics.IdealGas
