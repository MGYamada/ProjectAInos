/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.External.YM.ChallengeSpec

/-! # Additional contracts for interpreting the imported hierarchy

These conditions are explicit premises on a candidate hierarchy. The imported
joint target is preserved, and no existence assertion is made here.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace YangMills.Hierarchy
open Filter MeasureTheory
open scoped Topology

variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

/-- On separated configurations, each fixed degree profile determines a complex
multilinear map of the insertions. Nonzero Wightman labels have a unique degree. -/
structure CorrelatorAlgebra : Prop where
  multilinear (s : Option T.Character) {n : ℕ} (degree : Fin n → ℕ)
      (x : Points n) (hx : x ∈ WilsonFamily.separated n) :
    ∃ F : MultilinearMap ℂ (fun i => T.Field (degree i)) ℂ,
      ∀ v, T.correlation s (fun i => ⟨degree i, v i⟩) x = F v
  uniqueDegree {d e : ℕ} (v : T.Field d) (w : T.Field e) :
    T.toLabel d v = T.toLabel e w → T.toLabel d v ≠ 0 → d = e

/-- Zero insertions vanish in the phase average and in each individual phase. -/
theorem CorrelatorAlgebra.correlation_eq_zero {T : Hierarchy C} (h : T.CorrelatorAlgebra)
    (s : Option T.Character) {n : ℕ} (degree : Fin n → ℕ)
    (x : Points n) (hx : x ∈ WilsonFamily.separated n)
    (v : ∀ i, T.Field (degree i)) (j : Fin n) (hj : v j = 0) :
    T.correlation s (fun i => ⟨degree i, v i⟩) x = 0 := by
  obtain ⟨F, hF⟩ := h.multilinear s degree x hx
  rw [hF, F.map_coord_zero j hj]

/-- The separated correlators depend only on the Wightman labels. A common
zero label forces both evaluations to vanish, regardless of its tagged degree. -/
theorem CorrelatorAlgebra.correlation_eq_of_labels {T : Hierarchy C} (h : T.CorrelatorAlgebra)
    (hreconstructed : T.Reconstructed) (s : Option T.Character) {n : ℕ}
    (a b : Fin n → T.Tag) (x : Points n) (hx : x ∈ WilsonFamily.separated n)
    (heq : ∀ i, T.toLabel (a i).1 (a i).2 = T.toLabel (b i).1 (b i).2) :
    T.correlation s a x = T.correlation s b x := by
  classical
  by_cases hz : ∃ j, T.toLabel (a j).1 (a j).2 = 0
  · obtain ⟨j, hj⟩ := hz
    have ha : (a j).2 = 0 :=
      hreconstructed.injective _ (hj.trans (map_zero _).symm)
    have hb : (b j).2 = 0 :=
      hreconstructed.injective _ ((heq j).symm.trans (hj.trans (map_zero _).symm))
    exact (h.correlation_eq_zero s (fun i => (a i).1) x hx (fun i => (a i).2) j ha).trans
      (h.correlation_eq_zero s (fun i => (b i).1) x hx (fun i => (b i).2) j hb).symm
  · have htags : a = b := by
      funext i
      have hne : T.toLabel (a i).1 (a i).2 ≠ 0 := fun hi => hz ⟨i, hi⟩
      have hi := heq i
      generalize a i = A at hi hne ⊢
      generalize b i = B at hi ⊢
      rcases A with ⟨d, v⟩
      rcases B with ⟨e, w⟩
      have hde : d = e := h.uniqueDegree v w hi hne
      subst e
      exact congrArg (Sigma.mk d) (show v = w from hreconstructed.injective d hi)
    rw [htags]

/-- Nonzero labels determine the same OPE weight in any representative tuple. -/
theorem CorrelatorAlgebra.weight_eq {T : Hierarchy C} (h : T.CorrelatorAlgebra)
    {I : Type} [Fintype I] (a b : I → T.Tag)
    (heq : ∀ i, T.toLabel (a i).1 (a i).2 = T.toLabel (b i).1 (b i).2)
    (hne : ∀ i, T.toLabel (a i).1 (a i).2 ≠ 0) : T.weight a = T.weight b := by
  unfold weight
  exact Finset.sum_congr rfl fun i _ => congrArg (fun d : ℕ => (d : ℝ))
    (h.uniqueDegree (a i).2 (b i).2 (heq i) (hne i))

/-- The original Wilson sequence has the selected-phase limit on the same tests,
with the same order of mesh and volume limits. -/
def SelectedWilsonLimit (order : ℕ → ℕ) : Prop :=
  C.Converges order (fun v => T.correlation (some T.selected) (T.project ∘ v))

/-- Equality of the selected and averaged smeared moments for lattice tokens. -/
def SelectedMomentsAgree : Prop :=
  ∀ (n : ℕ) (v : Fin n → C.Token) (t : WilsonFamily.SeparatedTest n),
    (∫ x, t x * T.correlation none (T.project ∘ v) x) =
      ∫ x, t x * T.correlation (some T.selected) (T.project ∘ v) x

/-- Once the average is a Wilson limit, the same Wilson sequence reaches the
selected phase exactly when its smeared moments agree with the average.
Uniqueness is used first at fixed volume, then along the volume sequence. -/
theorem selectedWilsonLimit_iff (order : ℕ → ℕ)
    (h : C.Converges order (fun v => T.correlation none (T.project ∘ v))) :
    T.SelectedWilsonLimit order ↔ T.SelectedMomentsAgree := by
  constructor
  · intro hs n v t
    obtain ⟨hfit, row, hrow, hlim⟩ := h n v t
    obtain ⟨_, selectedRow, hselectedRow, hselectedLim⟩ := hs n v t
    have hrows : (fun k => row (order k)) =ᶠ[atTop] fun k => selectedRow (order k) := by
      filter_upwards [hfit] with k hk
      exact tendsto_nhds_unique (hrow (order k) hk) (hselectedRow (order k) hk)
    exact tendsto_nhds_unique hlim (hselectedLim.congr' hrows.symm)
  · intro hagree n v t
    obtain ⟨hfit, row, hrow, hlim⟩ := h n v t
    exact ⟨hfit, row, hrow, hagree n v t ▸ hlim⟩

/-- The upstream properties together with the extra correlator and selected-limit
premises needed for the stated interpretation of the same Wilson sequence. -/
structure IntegratedProperties (order : ℕ → ℕ) : Prop extends T.Properties order where
  correlatorAlgebra : T.CorrelatorAlgebra
  selectedMomentsAgree : T.SelectedMomentsAgree

theorem IntegratedProperties.selectedWilson {T : Hierarchy C} {order : ℕ → ℕ}
    (h : T.IntegratedProperties order) : T.SelectedWilsonLimit order :=
  (T.selectedWilsonLimit_iff order h.toProperties.wilson).mpr h.selectedMomentsAgree

end YangMills.Hierarchy
