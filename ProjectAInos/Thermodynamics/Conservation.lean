module

public import ProjectAInos.Thermodynamics.Representation
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Conserved quantities and entropy extensions

The quotient by the process span is universal for linear conserved quantities.
After choosing an entropy coordinate on that span, its linear extensions form
a nonempty affine family parametrized by the dual of the conservation quotient.
-/

@[expose] public section

namespace ProjectAInos.Thermodynamics

variable {V E : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup E] [Module ℝ E]

/-- A linear observable factors through the conservation quotient exactly when
it vanishes on the process span. -/
theorem existsUnique_conservation_factor_iff (W : Submodule ℝ V) (q : V →ₗ[ℝ] E) :
    (∃! φ : (V ⧸ W) →ₗ[ℝ] E, φ.comp W.mkQ = q) ↔ W ≤ LinearMap.ker q := by
  constructor
  · rintro ⟨φ, hφ, _⟩ v hv
    change q v = 0
    rw [← hφ, LinearMap.comp_apply]
    have hzero : W.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hv
    rw [hzero, map_zero]
  · intro hq
    refine ⟨W.liftQ q hq, W.liftQ_mkQ q hq, ?_⟩
    intro φ hφ
    exact Submodule.linearMap_qext W (hφ.trans (W.liftQ_mkQ q hq).symm)

/-- Vanishing on every process is precisely the hypothesis needed for the
universal conservation factorization. -/
theorem existsUnique_process_factor_iff (P : PointedCone ℝ V) (q : V →ₗ[ℝ] E) :
    (∃! φ : (V ⧸ Submodule.span ℝ (P : Set V)) →ₗ[ℝ] E,
      φ.comp (Submodule.span ℝ (P : Set V)).mkQ = q) ↔
    ∀ v ∈ P, q v = 0 := by
  rw [existsUnique_conservation_factor_iff, Submodule.span_le]
  rfl

/-- The process span and its conservation quotient form a short exact sequence. -/
theorem conservation_exact (W : Submodule ℝ V) :
    Function.Injective W.subtype ∧
      LinearMap.range W.subtype = LinearMap.ker W.mkQ ∧
      Function.Surjective W.mkQ := by
  exact ⟨Subtype.val_injective, by simp, W.mkQ_surjective⟩

/-- An entropy on all formal state differences extending a fixed entropy unit
on the process span. -/
abbrev EntropyExtension {W : Submodule ℝ V} (s : W ≃ₗ[ℝ] ℝ) :=
  {S : V →ₗ[ℝ] ℝ // S.comp W.subtype = s.toLinearMap}

theorem entropyExtension_nonempty {W : Submodule ℝ V} (s : W ≃ₗ[ℝ] ℝ) :
    Nonempty (EntropyExtension s) := by
  obtain ⟨S, hS⟩ := s.toLinearMap.exists_extend
  exact ⟨⟨S, hS⟩⟩

theorem EntropyExtension.apply_subtype {W : Submodule ℝ V} {s : W ≃ₗ[ℝ] ℝ}
    (S : EntropyExtension s) (w : W) : S.val w = s w :=
  LinearMap.congr_fun S.property w

/-- Entropy inequalities characterize the cone for differences in the process
span. The membership hypothesis records the matched conservation sector. -/
theorem EntropyExtension.le_iff {W : Submodule ℝ V} {s : W ≃ₗ[ℝ] ℝ}
    (S : EntropyExtension s) (P : PointedCone ℝ V)
    (hs : ∀ w : W, 0 ≤ s w ↔ (w : V) ∈ P)
    {x y : V} (hxy : y - x ∈ W) :
    S.val x ≤ S.val y ↔ y - x ∈ P := by
  rw [← sub_nonneg, ← map_sub]
  change 0 ≤ S.val (⟨y - x, hxy⟩ : W) ↔ y - x ∈ P
  rw [S.apply_subtype]
  exact hs ⟨y - x, hxy⟩

/-- Equality of universal conserved quantities is equivalent to matching
process sectors. -/
theorem conservation_eq_iff (W : Submodule ℝ V) (x y : V) :
    W.mkQ x = W.mkQ y ↔ y - x ∈ W := by
  rw [eq_comm, ← sub_eq_zero, ← map_sub]
  exact Submodule.Quotient.mk_eq_zero W

/-- Once one entropy extension is fixed, every other extension is obtained by
adding one unique linear conserved quantity. -/
theorem EntropyExtension.existsUnique_difference {W : Submodule ℝ V}
    {s : W ≃ₗ[ℝ] ℝ} (S₀ S : EntropyExtension s) :
    ∃! φ : (V ⧸ W) →ₗ[ℝ] ℝ, S.val = S₀.val + φ.comp W.mkQ := by
  have hvanish : W ≤ LinearMap.ker (S.val - S₀.val) := by
    intro w hw
    change S.val w - S₀.val w = 0
    rw [show S.val w = s ⟨w, hw⟩ from S.apply_subtype ⟨w, hw⟩,
      show S₀.val w = s ⟨w, hw⟩ from S₀.apply_subtype ⟨w, hw⟩]
    exact sub_self _
  obtain ⟨φ, hφ, huniq⟩ :=
    (existsUnique_conservation_factor_iff W (S.val - S₀.val)).mpr hvanish
  refine ⟨φ, ?_, ?_⟩
  · change S.val = S₀.val + φ.comp W.mkQ
    rw [hφ]
    abel
  · intro ψ hψ
    apply huniq ψ
    rw [hψ]
    abel

/-- Adding a linear conserved quantity preserves the chosen entropy unit. -/
def EntropyExtension.addConserved {W : Submodule ℝ V} {s : W ≃ₗ[ℝ] ℝ}
    (S : EntropyExtension s) (φ : (V ⧸ W) →ₗ[ℝ] ℝ) : EntropyExtension s :=
  ⟨S.val + φ.comp W.mkQ, by
    ext w
    have hzero : W.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero W).mpr w.property
    simp [hzero, S.apply_subtype]⟩

/-- The dual conservation space parametrizes all extensions after an origin
extension has been chosen. -/
noncomputable def EntropyExtension.equivConserved {W : Submodule ℝ V}
    {s : W ≃ₗ[ℝ] ℝ} (S₀ : EntropyExtension s) :
    ((V ⧸ W) →ₗ[ℝ] ℝ) ≃ EntropyExtension s :=
  Equiv.ofBijective S₀.addConserved ⟨by
    intro φ ψ h
    apply Submodule.linearMap_qext W
    have hval := congrArg Subtype.val h
    exact add_left_cancel hval, by
    intro S
    obtain ⟨φ, hφ, _⟩ := S₀.existsUnique_difference S
    exact ⟨φ, Subtype.ext hφ.symm⟩⟩

end ProjectAInos.Thermodynamics
