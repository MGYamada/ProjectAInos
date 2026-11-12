/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.FiniteHodge
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm

/-! # Hodge transport between distinct finite topological fibres -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower

namespace ProjectAInos.SmoothGeometry.DifferentialForm

section Algebra
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- A metric-preserving linear map preserves the induced exterior-power pairing. -/
theorem exteriorPower_pairing_map (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (L : V →ₗ[ℝ] W) (hL : ∀ v w, C (L v) (L w) = B v w) {k : ℕ} (α β : ⋀[ℝ]^k V) :
    C.exteriorPower k (exteriorPower.map k L α) (exteriorPower.map k L β) =
      B.exteriorPower k α β := by
  suffices h : (C.exteriorPower k).compl₁₂ (exteriorPower.map k L) (exteriorPower.map k L) =
      B.exteriorPower k from congrArg (fun f => f α β) h
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  change C.exteriorPower k (exteriorPower.map k L (ιMulti ℝ k v))
    (exteriorPower.map k L (ιMulti ℝ k w)) = B.exteriorPower k (ιMulti ℝ k v) (ιMulti ℝ k w)
  simp only [exteriorPower.map_apply_ιMulti, LinearMap.BilinForm.bilinForm_ιMulti_ιMulti,
    Function.comp_apply, hL]

/-- Transforming the first input suffices when the inverse metrics are related on that input. -/
theorem exteriorPower_pairing_precomp (B C : LinearMap.BilinForm ℝ V)
    (L : V →ₗ[ℝ] V) (hL : ∀ v w, C (L v) w = B v w) {k : ℕ} (α β : ⋀[ℝ]^k V) :
    C.exteriorPower k (exteriorPower.map k L α) β = B.exteriorPower k α β := by
  suffices h : (C.exteriorPower k).comp (exteriorPower.map k L) = B.exteriorPower k from
    congrArg (fun f => f α β) h
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  change C.exteriorPower k (exteriorPower.map k L (ιMulti ℝ k v)) (ιMulti ℝ k w) =
    B.exteriorPower k (ιMulti ℝ k v) (ιMulti ℝ k w)
  simp only [exteriorPower.map_apply_ιMulti, LinearMap.BilinForm.bilinForm_ιMulti_ιMulti,
    Function.comp_apply, hL]

variable [FiniteDimensional ℝ V]

/-- Changing the inverse metric can be implemented by precomposing covectors before a fixed Hodge. -/
theorem hodge_metric_precomp (B C : LinearMap.BilinForm ℝ V)
    (hB : Function.Bijective B) (hC : Function.Bijective C)
    (vol : ⋀[ℝ]^(Module.finrank ℝ V) V ≃ₗ[ℝ] ℝ) (L : V →ₗ[ℝ] V)
    (hL : ∀ v w, C (L v) w = B v w) {k l : ℕ}
    (hkl : k + l = Module.finrank ℝ V) (α : ⋀[ℝ]^k V) :
    hodge B hB vol hkl α = hodge C hC vol hkl (exteriorPower.map k L α) := by
  symm
  apply hodge_unique
  intro β
  rw [hodge_pairing]
  exact exteriorPower_pairing_precomp B C L hL α β

end Algebra

section Degree
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] {k l : ℕ}

theorem finiteDegreeCast_comp (h : k = l) (L : V →L[ℝ] W) (α : W [⋀^Fin k]→L[ℝ] ℝ) :
    finiteDegreeCast h (α.compContinuousLinearMap L) =
      (finiteDegreeCast h α).compContinuousLinearMap L := by subst l; rfl

end Degree

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
  {n k l : ℕ}

/-- Hodge with a declared top degree, retaining the proof of its actual dimension. -/
def finiteHodgeOfDegree (B : LinearMap.BilinForm ℝ (Dual ℝ V)) (hB : Function.Bijective B)
    (vol : V [⋀^Fin n]→L[ℝ] ℝ) (hv : vol ≠ 0) (hn : n = Module.finrank ℝ (Dual ℝ V))
    (hkl : k + l = n) : (V [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ] (V [⋀^Fin l]→L[ℝ] ℝ) :=
  finiteHodge B hB (finiteDegreeCast hn vol) (finiteDegreeCast_ne_zero hn hv) (hkl.trans hn)

theorem finiteHodgeOfDegree_wedge (B : LinearMap.BilinForm ℝ (Dual ℝ V))
    (hB : Function.Bijective B) (vol : V [⋀^Fin n]→L[ℝ] ℝ) (hv : vol ≠ 0)
    (hn : n = Module.finrank ℝ (Dual ℝ V)) (hkl : k + l = n)
    (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteDegreeCast hkl (finiteWedge α (finiteHodgeOfDegree B hB vol hv hn hkl β)) =
      B.exteriorPower k (finiteToExterior β) (finiteToExterior α) • vol := by
  apply finiteDegreeCast_injective hn
  rw [finiteDegreeCast_trans, finiteDegreeCast_smul]
  exact finiteHodge_wedge _ _ _ _ _ _ _

theorem finiteHodgeOfDegree_unique (B : LinearMap.BilinForm ℝ (Dual ℝ V))
    (hB : Function.Bijective B) (vol : V [⋀^Fin n]→L[ℝ] ℝ) (hv : vol ≠ 0)
    (hn : n = Module.finrank ℝ (Dual ℝ V)) (hkl : k + l = n)
    (β : V [⋀^Fin k]→L[ℝ] ℝ) (γ : V [⋀^Fin l]→L[ℝ] ℝ)
    (h : ∀ α : V [⋀^Fin k]→L[ℝ] ℝ, finiteDegreeCast hkl (finiteWedge α γ) =
      B.exteriorPower k (finiteToExterior β) (finiteToExterior α) • vol) :
    γ = finiteHodgeOfDegree B hB vol hv hn hkl β := by
  apply finiteHodge_unique
  intro α
  have hh := congrArg (finiteDegreeCast hn) (h α)
  rw [finiteDegreeCast_trans, finiteDegreeCast_smul] at hh
  exact hh

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W] [FiniteDimensional ℝ W]

/-- Transport preserves Hodge when it preserves the inverse metric and oriented volume. -/
theorem finiteHodgeOfDegree_natural
    (B : LinearMap.BilinForm ℝ (Dual ℝ V)) (hB : Function.Bijective B)
    (C : LinearMap.BilinForm ℝ (Dual ℝ W)) (hC : Function.Bijective C)
    (volV : V [⋀^Fin n]→L[ℝ] ℝ) (hv : volV ≠ 0) (hnV : n = Module.finrank ℝ (Dual ℝ V))
    (volW : W [⋀^Fin n]→L[ℝ] ℝ) (hw : volW ≠ 0) (hnW : n = Module.finrank ℝ (Dual ℝ W))
    (L : V ≃L[ℝ] W)
    (hmetric : ∀ α β : Dual ℝ W, B (L.toLinearMap.dualMap α) (L.toLinearMap.dualMap β) = C α β)
    (hvolume : volW.compContinuousLinearMap L.toContinuousLinearMap = volV)
    (hkl : k + l = n) (β : W [⋀^Fin k]→L[ℝ] ℝ) :
    (finiteHodgeOfDegree C hC volW hw hnW hkl β).compContinuousLinearMap L.toContinuousLinearMap =
      finiteHodgeOfDegree B hB volV hv hnV hkl (β.compContinuousLinearMap L.toContinuousLinearMap) := by
  apply finiteHodgeOfDegree_unique
  intro α
  let a := α.compContinuousLinearMap L.symm.toContinuousLinearMap
  have ha : a.compContinuousLinearMap L.toContinuousLinearMap = α := by
    ext v
    change α (fun i => L.symm (L (v i))) = α v
    simp
  rw [← ha, finiteWedge_comp, finiteDegreeCast_comp,
    finiteHodgeOfDegree_wedge]
  have hp := exteriorPower_pairing_map C B L.toLinearMap.dualMap hmetric
    (finiteToExterior β) (finiteToExterior a)
  have hp' : B.exteriorPower k
      (finiteToExterior (β.compContinuousLinearMap L.toContinuousLinearMap))
      (finiteToExterior (a.compContinuousLinearMap L.toContinuousLinearMap)) =
        C.exteriorPower k (finiteToExterior β) (finiteToExterior a) := by
    rw [finiteToExterior_comp, finiteToExterior_comp]
    exact hp
  rw [hp']
  ext v
  change _ * volW (fun i => L (v i)) = _ * volV v
  exact congrArg (fun r : ℝ => C.exteriorPower k (finiteToExterior β) (finiteToExterior a) * r)
    (congrArg (fun f => f v) hvolume)

end ProjectAInos.SmoothGeometry.DifferentialForm
