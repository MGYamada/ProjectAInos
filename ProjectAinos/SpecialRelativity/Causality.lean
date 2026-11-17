/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Minkowski.Affine
public import ProjectAinos.SmoothGeometry.Minkowski.ReverseCauchySchwarz
import Mathlib.Tactic.Linarith

/-!
# Signals with a finite speed

A relation `R p q` between events says that a signal sent at `p` can be received at `q`
(Landau–Lifshitz, *The Classical Theory of Fields*, §1). That no signal is faster than light is
a physical premise. Here it is the hypothesis `IsCausalRelation R`: the relation is contained in
the causal order, whose cone is the closed future cone.

* `causallyPrecedes_poincare`: an orthochronous Poincaré transformation preserves the causal
  order, and `IsCausalRelation.transform` shows that the hypothesis holds for the transformed
  relation: it does not depend on the inertial frame.
* `IsCausalRelation.not_of_spacelike`: no signal joins two events with a spacelike separation.
* `IsCausalRelation.clock_pos`: for every observer the reception is later than the emission, if
  the two events are different. The order in time of cause and effect is the same in all
  frames.
* `IsCausalRelation.restForm_le_clock_sq`: for every observer the distance covered by the
  signal is at most the time that it takes: its speed is at most one.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ}

/-- A relation between events that is contained in the causal order: a signal from `p` reaches
`q` only if `q − p` is in the closed future cone. -/
def IsCausalRelation (R : MinkowskiModel d → MinkowskiModel d → Prop) : Prop :=
  ∀ p q, R p q → CausallyPrecedes p q

/-- An orthochronous Poincaré transformation preserves the causal order. -/
theorem causallyPrecedes_poincare (f : PoincareGroup d)
    (hf : PoincareGroup.linear f ∈ orthochronousLorentzGroup d) (p q : MinkowskiModel d) :
    CausallyPrecedes (f.val p) (f.val q) ↔ CausallyPrecedes p q := by
  change FutureCausal (f.val q - f.val p) ↔ FutureCausal (q - p)
  rw [PoincareGroup.map_sub]
  exact hf (q - p)

namespace IsCausalRelation

variable {R : MinkowskiModel d → MinkowskiModel d → Prop}

/-- The relation seen in another inertial frame is again contained in the causal order. -/
theorem transform (hR : IsCausalRelation R) (f : PoincareGroup d)
    (hf : PoincareGroup.linear f ∈ orthochronousLorentzGroup d) :
    IsCausalRelation fun p q => R (f.val.symm p) (f.val.symm q) := by
  intro p q h
  have h1 := (causallyPrecedes_poincare f hf _ _).mpr (hR _ _ h)
  simpa using h1

/-- No signal joins two events with a spacelike separation. -/
theorem not_of_spacelike (hR : IsCausalRelation R) {p q : MinkowskiModel d}
    (h : Spacelike (q - p)) : ¬R p q := by
  intro hpq
  have hc : Causal (q - p) := ((futureCausal_iff _).mp (hR p q hpq)).1
  exact absurd h (not_lt.mpr hc)

/-- For every observer the reception is later than the emission. -/
theorem clock_pos (hR : IsCausalRelation R) (u : Observer d) {p q : MinkowskiModel d}
    (h : R p q) (hne : p ≠ q) : 0 < u.clock (q - p) :=
  pair_pos_of_futureTimelike u.futureTimelike (hR p q h) (sub_ne_zero.mpr (Ne.symm hne))

/-- For every observer the distance covered by a signal is at most the time that it takes. -/
theorem restForm_le_clock_sq (hR : IsCausalRelation R) (u : Observer d)
    {p q : MinkowskiModel d} (h : R p q) :
    u.restForm (u.project (q - p)) (u.project (q - p)) ≤ u.clock (q - p) ^ 2 := by
  have hc : 0 ≤ intervalQuadratic (q - p) := ((futureCausal_iff _).mp (hR p q h)).1
  have hsplit := u.intervalQuadratic_eq (q - p)
  linarith

end IsCausalRelation

/-- The causal order itself is a relation of this kind. -/
theorem isCausalRelation_causallyPrecedes :
    IsCausalRelation (fun p q : MinkowskiModel d => CausallyPrecedes p q) :=
  fun _ _ h => h

end ProjectAinos.SpecialRelativity
