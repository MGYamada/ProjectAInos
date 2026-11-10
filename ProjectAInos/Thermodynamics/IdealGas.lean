module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# A macroscopic monatomic ideal gas

The amount of matter is a positive real number. The constant `c` fixes the
entropy reference. A separate collection of boxes has the sum of their
entropies, while mixing into one equilibrium state obeys concavity.
The operational relation uses reversible motion along adiabats and
constant-energy free expansion with equilibration as explicit model inputs.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Thermodynamics.IdealGas

/-- An equilibrium state with positive energy, volume, and amount. -/
structure State where
  energy : ℝ
  volume : ℝ
  amount : ℝ
  energy_pos : 0 < energy
  volume_pos : 0 < volume
  amount_pos : 0 < amount

/-- The extensive entropy formula, with Boltzmann constant `k` and reference `c`. -/
def entropyValue (k c U V N : ℝ) : ℝ :=
  k * N * ((3 / 2 : ℝ) * Real.log (U / N) + Real.log (V / N) + c)

/-- Entropy of one equilibrium box. -/
def entropy (k c : ℝ) (X : State) : ℝ :=
  entropyValue k c X.energy X.volume X.amount

/-- Positive scaling of the entire macroscopic state. -/
def State.scale (X : State) (t : ℝ) (ht : 0 < t) : State where
  energy := t * X.energy
  volume := t * X.volume
  amount := t * X.amount
  energy_pos := mul_pos ht X.energy_pos
  volume_pos := mul_pos ht X.volume_pos
  amount_pos := mul_pos ht X.amount_pos

@[simp] theorem entropy_scale (k c : ℝ) (X : State) (t : ℝ) (ht : 0 < t) :
    entropy k c (X.scale t ht) = t * entropy k c X := by
  simp only [entropy, entropyValue, State.scale, mul_div_mul_left _ _ ht.ne']
  ring

/-- Entropy of a finite collection of separate boxes. -/
def compositeEntropy (k c : ℝ) (boxes : List State) : ℝ :=
  (boxes.map (entropy k c)).sum

@[simp] theorem compositeEntropy_append (k c : ℝ) (xs ys : List State) :
    compositeEntropy k c (xs ++ ys) =
      compositeEntropy k c xs + compositeEntropy k c ys := by
  simp [compositeEntropy]

/-- A logarithmic coordinate for the reversible adiabats. -/
def adiabat (X : State) : ℝ :=
  (3 / 2 : ℝ) * Real.log X.energy + Real.log X.volume

private theorem entropy_expanded (k c : ℝ) (X : State) :
    entropy k c X =
      k * X.amount * (adiabat X - (5 / 2 : ℝ) * Real.log X.amount + c) := by
  simp only [entropy, entropyValue, adiabat,
    Real.log_div X.energy_pos.ne' X.amount_pos.ne',
    Real.log_div X.volume_pos.ne' X.amount_pos.ne']
  ring

theorem entropy_le_iff_adiabat_le {k c : ℝ} (hk : 0 < k) {X Y : State}
    (hN : X.amount = Y.amount) :
    entropy k c X ≤ entropy k c Y ↔ adiabat X ≤ adiabat Y := by
  rw [entropy_expanded, entropy_expanded, ← hN,
    mul_le_mul_iff_right₀ (mul_pos hk X.amount_pos)]
  constructor <;> intro h <;> linarith

theorem entropy_eq_iff_adiabat_eq {k c : ℝ} (hk : 0 < k) {X Y : State}
    (hN : X.amount = Y.amount) :
    entropy k c X = entropy k c Y ↔ adiabat X = adiabat Y := by
  rw [le_antisymm_iff, le_antisymm_iff,
    entropy_le_iff_adiabat_le hk hN, entropy_le_iff_adiabat_le hk hN.symm]

/-- The adiabat can also be expressed without logarithms. -/
theorem adiabat_eq_iff (X Y : State) :
    adiabat X = adiabat Y ↔
      X.energy ^ 3 * X.volume ^ 2 = Y.energy ^ 3 * Y.volume ^ 2 := by
  have hx : 0 < X.energy ^ 3 * X.volume ^ 2 := mul_pos (pow_pos X.energy_pos _) (pow_pos X.volume_pos _)
  have hy : 0 < Y.energy ^ 3 * Y.volume ^ 2 := mul_pos (pow_pos Y.energy_pos _) (pow_pos Y.volume_pos _)
  rw [← Real.log_injOn_pos.eq_iff hx hy]
  simp only [Real.log_mul (pow_ne_zero _ X.energy_pos.ne')
      (pow_ne_zero _ X.volume_pos.ne'),
    Real.log_mul (pow_ne_zero _ Y.energy_pos.ne') (pow_ne_zero _ Y.volume_pos.ne'),
    Real.log_pow]
  dsimp [adiabat]
  constructor <;> intro h <;> linarith

/-- Allowed generating operations on a fixed-amount sector. -/
def Step (X Y : State) : Prop :=
  X.amount = Y.amount ∧
    (adiabat X = adiabat Y ∨ X.energy = Y.energy ∧ X.volume ≤ Y.volume)

/-- A finite sequence of allowed operations, including the empty sequence. -/
def Accessible (X Y : State) : Prop := Relation.ReflTransGen Step X Y

private theorem step_mono {X Y : State} (h : Step X Y) :
    X.amount = Y.amount ∧ adiabat X ≤ adiabat Y := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with h | ⟨hU, hV⟩
  · exact h.le
  · dsimp [adiabat]
    rw [hU]
    linarith [Real.log_le_log X.volume_pos hV]

theorem accessible_iff {k c : ℝ} (hk : 0 < k) (X Y : State) :
    Accessible X Y ↔ X.amount = Y.amount ∧ entropy k c X ≤ entropy k c Y := by
  constructor
  · intro h
    have h' : X.amount = Y.amount ∧ adiabat X ≤ adiabat Y := by
      induction h with
      | refl => exact ⟨rfl, le_rfl⟩
      | @tail Z Y hXY hZY ih =>
        obtain ⟨hN, hS⟩ := step_mono hZY
        exact ⟨ih.1.trans hN, ih.2.trans hS⟩
    exact ⟨h'.1, (entropy_le_iff_adiabat_le hk h'.1).2 h'.2⟩
  · rintro ⟨hN, hS⟩
    let Z : State :=
      { energy := Y.energy
        volume := Real.exp (adiabat X - (3 / 2 : ℝ) * Real.log Y.energy)
        amount := X.amount
        energy_pos := Y.energy_pos
        volume_pos := Real.exp_pos _
        amount_pos := X.amount_pos }
    have hZ : adiabat Z = adiabat X := by
      dsimp [adiabat, Z]
      rw [Real.log_exp]
      ring
    have hV : Z.volume ≤ Y.volume := by
      apply (Real.log_le_log_iff Z.volume_pos Y.volume_pos).1
      have := (entropy_le_iff_adiabat_le hk hN).1 hS
      dsimp [adiabat] at hZ this
      change (3 / 2 : ℝ) * Real.log Y.energy + Real.log Z.volume = _ at hZ
      linarith
    have hXZ : Step X Z := ⟨rfl, Or.inl hZ.symm⟩
    have hZY : Step Z Y := ⟨hN, Or.inr ⟨rfl, hV⟩⟩
    exact (Relation.ReflTransGen.single hXZ).trans (Relation.ReflTransGen.single hZY)


private theorem weighted_positive {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : 0 < x) (hy : 0 < y) : 0 < a * x + b * y := by
  rcases ha.eq_or_lt with ha | ha
  · have hb' : b = 1 := by linarith
    simpa [← ha, hb'] using hy
  · exact add_pos_of_pos_of_nonneg (mul_pos ha hx) (mul_nonneg hb hy.le)

/-- Concavity of the perspective of logarithm. -/
private theorem log_perspective_concave {a b x y n m : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : 0 < x) (hy : 0 < y) (hn : 0 < n) (hm : 0 < m) :
    a * (n * Real.log (x / n)) + b * (m * Real.log (y / m)) ≤
      (a * n + b * m) * Real.log ((a * x + b * y) / (a * n + b * m)) := by
  let N := a * n + b * m
  have hN : 0 < N := weighted_positive ha hb hab hn hm
  have hweights : a * n / N + b * m / N = 1 := by
    rw [← add_div, div_self hN.ne']
  have harg : a * n / N * (x / n) + b * m / N * (y / m) =
      (a * x + b * y) / N := by
    field_simp
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2
    (div_pos hx hn) (div_pos hy hm)
    (div_nonneg (mul_nonneg ha hn.le) hN.le)
    (div_nonneg (mul_nonneg hb hm.le) hN.le) hweights
  simp only [smul_eq_mul] at hlog
  rw [harg] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hN.le
  have hleft : N * (a * n / N * Real.log (x / n) +
      b * m / N * Real.log (y / m)) =
      a * (n * Real.log (x / n)) + b * (m * Real.log (y / m)) := by
    field_simp
  rwa [hleft] at hscaled

/-- Concavity in all three extensive coordinates. -/
theorem entropyValue_concave {k c a b U₁ V₁ N₁ U₂ V₂ N₂ : ℝ}
    (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hU₁ : 0 < U₁) (hV₁ : 0 < V₁) (hN₁ : 0 < N₁)
    (hU₂ : 0 < U₂) (hV₂ : 0 < V₂) (hN₂ : 0 < N₂) :
    a * entropyValue k c U₁ V₁ N₁ + b * entropyValue k c U₂ V₂ N₂ ≤
      entropyValue k c (a * U₁ + b * U₂) (a * V₁ + b * V₂)
        (a * N₁ + b * N₂) := by
  have hU := log_perspective_concave ha hb hab hU₁ hU₂ hN₁ hN₂
  have hV := log_perspective_concave ha hb hab hV₁ hV₂ hN₁ hN₂
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 3 / 2)) hV
  have hscaled := mul_le_mul_of_nonneg_left hsum hk
  dsimp [entropyValue]
  nlinarith


/-- At fixed positive amount, entropy is strictly concave in energy and volume. -/
theorem entropyValue_strictConcave_fixedAmount {k c a b U₁ V₁ U₂ V₂ N : ℝ}
    (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hU₁ : 0 < U₁) (hV₁ : 0 < V₁) (hU₂ : 0 < U₂) (hV₂ : 0 < V₂)
    (hN : 0 < N) (hne : (U₁, V₁) ≠ (U₂, V₂)) :
    a * entropyValue k c U₁ V₁ N + b * entropyValue k c U₂ V₂ N <
      entropyValue k c (a * U₁ + b * U₂) (a * V₁ + b * V₂) N := by
  have hU := strictConcaveOn_log_Ioi.concaveOn.2
    (div_pos hU₁ hN) (div_pos hU₂ hN) ha.le hb.le hab
  have hV := strictConcaveOn_log_Ioi.concaveOn.2
    (div_pos hV₁ hN) (div_pos hV₂ hN) ha.le hb.le hab
  simp only [smul_eq_mul] at hU hV
  have hstrict :
      (3 / 2 : ℝ) * (a * Real.log (U₁ / N) + b * Real.log (U₂ / N)) +
        (a * Real.log (V₁ / N) + b * Real.log (V₂ / N)) <
      (3 / 2 : ℝ) * Real.log (a * (U₁ / N) + b * (U₂ / N)) +
        Real.log (a * (V₁ / N) + b * (V₂ / N)) := by
    by_cases hEq : U₁ = U₂
    · have hneV : V₁ / N ≠ V₂ / N := by
        intro h
        apply hne
        have hv : V₁ = V₂ := (div_left_inj' hN.ne').1 h
        exact Prod.ext hEq hv
      have hs := strictConcaveOn_log_Ioi.2
        (div_pos hV₁ hN) (div_pos hV₂ hN) hneV ha hb hab
      simp only [smul_eq_mul] at hs
      linarith
    · have hneU : U₁ / N ≠ U₂ / N := by
        intro h
        exact hEq ((div_left_inj' hN.ne').1 h)
      have hs := strictConcaveOn_log_Ioi.2
        (div_pos hU₁ hN) (div_pos hU₂ hN) hneU ha hb hab
      simp only [smul_eq_mul] at hs
      linarith
  have hscaled := mul_lt_mul_of_pos_left hstrict (mul_pos hk hN)
  have hconst : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  dsimp [entropyValue]
  rw [add_div, add_div]
  simp only [mul_div_assoc] at *
  nlinarith

end ProjectAInos.Thermodynamics.IdealGas
