/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ProjectAInos.SmoothGeometry.DifferentialForm.Hodge
public import ProjectAInos.SmoothGeometry.DifferentialForm.Coordinates
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm

/-! # Exterior functoriality and oriented Hodge naturality -/
@[expose] public section
noncomputable section
open Module exteriorPower
namespace ProjectAInos.SmoothGeometry.DifferentialForm
variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
variable {k l : ℕ}

def exteriorEquiv (A : M ≃ₗ[ℝ] M) (k : ℕ) : ⋀[ℝ]^k M ≃ₗ[ℝ] ⋀[ℝ]^k M :=
  LinearEquiv.ofBijective (exteriorPower.map k A.toLinearMap)
    ⟨exteriorPower.map_injective A.symm (by ext; simp), exteriorPower.map_surjective A.surjective⟩

omit [FiniteDimensional ℝ M] in
theorem wedge_map (A : M →ₗ[ℝ] M) (α : ⋀[ℝ]^k M) (β : ⋀[ℝ]^l M) :
    exteriorPower.wedge ℝ M k l (exteriorPower.map k A α) (exteriorPower.map l A β) =
      exteriorPower.map (k+l) A (exteriorPower.wedge ℝ M k l α β) := by
  apply Subtype.ext
  simp only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, coe_map, map_mul]

theorem top_map {n : ℕ} (h : n = Module.finrank ℝ M) (f : ⋀[ℝ]^n M →ₗ[ℝ] ℝ)
    (A : M →ₗ[ℝ] M) (α : ⋀[ℝ]^n M) :
    f (exteriorPower.map n A α) = A.det * f α := by
  subst n
  suffices H : f.comp (exteriorPower.map (Module.finrank ℝ M) A) = A.det • f from
    congrArg (fun g => g α) H
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change f (exteriorPower.map (Module.finrank ℝ M) A (ιMulti ℝ _ v)) = _
  rw [exteriorPower.map_apply_ιMulti]
  let F := f.compAlternatingMap (ιMulti ℝ (Module.finrank ℝ M))
  change F (A ∘ v) = A.det * F v
  rw [F.eq_smul_basis_det (Module.finBasis ℝ M)]
  simp only [smul_apply, Basis.det_comp, smul_eq_mul]
  ring

theorem wedgePairing_map (vol : ⋀[ℝ]^(Module.finrank ℝ M) M ≃ₗ[ℝ] ℝ)
    (hkl : k+l = Module.finrank ℝ M) (A : M →ₗ[ℝ] M) (α : ⋀[ℝ]^k M) (β : ⋀[ℝ]^l M) :
    wedgePairing vol hkl (exteriorPower.map k A α) (exteriorPower.map l A β) =
      A.det * wedgePairing vol hkl α β := by
  change (hkl.symm ▸ vol.toLinearMap) (exteriorPower.wedge ℝ M k l _ _) = _
  rw [wedge_map, top_map hkl]
  rfl

omit [FiniteDimensional ℝ M] in
theorem exteriorPower_isometry (B : LinearMap.BilinForm ℝ M) (A : M →ₗ[ℝ] M)
    (hA : ∀ v w, B (A v) (A w) = B v w) (α β : ⋀[ℝ]^k M) :
    B.exteriorPower k (exteriorPower.map k A α) (exteriorPower.map k A β) = B.exteriorPower k α β := by
  suffices H : (B.exteriorPower k).compl₁₂ (exteriorPower.map k A) (exteriorPower.map k A) =
      B.exteriorPower k from congrArg (fun f => f α β) H
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  change B.exteriorPower k (exteriorPower.map k A (ιMulti ℝ k v))
    (exteriorPower.map k A (ιMulti ℝ k w)) = B.exteriorPower k (ιMulti ℝ k v) (ιMulti ℝ k w)
  simp only [exteriorPower.map_apply_ιMulti,
    LinearMap.BilinForm.bilinForm_ιMulti_ιMulti, Function.comp_apply, hA]

theorem hodge_isometry (B : LinearMap.BilinForm ℝ M) (hB : Function.Bijective B)
    (vol : ⋀[ℝ]^(Module.finrank ℝ M) M ≃ₗ[ℝ] ℝ) (hkl : k+l = Module.finrank ℝ M)
    (A : M ≃ₗ[ℝ] M) (hA : ∀ v w, B (A v) (A w) = B v w)
    (hd : A.toLinearMap.det = 1) (α : ⋀[ℝ]^k M) :
    hodge B hB vol hkl (exteriorPower.map k A.toLinearMap α) =
      exteriorPower.map l A.toLinearMap (hodge B hB vol hkl α) := by
  exact hodge_natural B hB vol hkl (exteriorEquiv A k) (exteriorEquiv A l)
    (exteriorPower_isometry B A.toLinearMap hA)
    (fun a b => by
      change wedgePairing vol hkl (exteriorPower.map k A.toLinearMap a)
        (exteriorPower.map l A.toLinearMap b) = _
      rw [wedgePairing_map, hd, one_mul]) α

theorem fromExterior_map_dual {n k : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (α : ExteriorCovector n k) :
    toExterior.symm (exteriorPower.map k L.toLinearMap.dualMap α) =
      (toExterior.symm α).compContinuousLinearMap L := by
  ext v
  rw [fromExterior_apply]
  change pairingDual ℝ (Fin n → ℝ) k (exteriorPower.map k L.toLinearMap.dualMap α) (ιMulti ℝ k v) =
    toExterior.symm α (L ∘ v)
  rw [fromExterior_apply]
  suffices H : ((pairingDual ℝ (Fin n → ℝ) k).flip (ιMulti ℝ k v)).comp
      (exteriorPower.map k L.toLinearMap.dualMap) =
      (pairingDual ℝ (Fin n → ℝ) k).flip (ιMulti ℝ k (L ∘ v)) from congrArg (fun f => f α) H
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change pairingDual ℝ (Fin n → ℝ) k (exteriorPower.map k L.toLinearMap.dualMap (ιMulti ℝ k a))
    (ιMulti ℝ k v) = pairingDual ℝ (Fin n → ℝ) k (ιMulti ℝ k a) (ιMulti ℝ k (L ∘ v))
  rw [exteriorPower.map_apply_ιMulti, pairingDual_ιMulti_ιMulti, pairingDual_ιMulti_ιMulti]
  rfl

theorem toExterior_comp {n k : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (ω : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) :
    toExterior (ω.compContinuousLinearMap L) = exteriorPower.map k L.toLinearMap.dualMap (toExterior ω) := by
  apply toExterior.symm.injective
  rw [LinearEquiv.symm_apply_apply, fromExterior_map_dual, LinearEquiv.symm_apply_apply]

theorem pullback_wedge {n k l : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (α : Form (Fin n → ℝ) k) (β : Form (Fin n → ℝ) l) :
    pullback f (wedge α β) = wedge (pullback f α) (pullback f β) := by
  funext x
  apply toExterior.injective
  simp only [pullback, wedge, toExterior_comp, toExterior_wedgeFiber]
  exact (wedge_map (fderiv ℝ f x).toLinearMap.dualMap _ _).symm

end ProjectAInos.SmoothGeometry.DifferentialForm
