/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Isometry
public import ProjectAInos.SmoothGeometry.Lorentzian

/-! # Affine Minkowski isometries and their C∞ scheme maps -/

@[expose] public section
noncomputable section
open scoped Manifold ContDiff
namespace ProjectAInos.SmoothGeometry.Minkowski

def PoincareGroup (d : ℕ) : Subgroup (MinkowskiModel d ≃ᵃ[ℝ] MinkowskiModel d) :=
  (LorentzGroup d).comap AffineEquiv.linearHom

namespace PoincareGroup
variable {d : ℕ}

/-- A Lorentz map followed by translation, with an explicit affine origin. -/
def ofLinearTranslation (L : LorentzGroup d) (a : MinkowskiModel d) : PoincareGroup d :=
  ⟨AffineEquiv.ofLinearEquiv L.val 0 a, by
    change (AffineEquiv.ofLinearEquiv L.val 0 a).linear ∈ LorentzGroup d
    simp⟩

@[simp] theorem ofLinearTranslation_apply (L : LorentzGroup d) (a v : MinkowskiModel d) :
    (ofLinearTranslation L a).val v = L.val v + a := by
  simp [ofLinearTranslation]

def translation (a : MinkowskiModel d) : PoincareGroup d := ofLinearTranslation 1 a

@[simp] theorem translation_apply (a v : MinkowskiModel d) :
    (translation a).val v = v+a := by
  simp [translation]

def linear (f : PoincareGroup d) : LorentzGroup d := ⟨f.val.linear, f.property⟩

theorem apply_eq (f : PoincareGroup d) (v : MinkowskiModel d) :
    f.val v = f.val.linear v + f.val 0 := by
  simpa using f.val.map_vadd 0 v

theorem map_sub (f : PoincareGroup d) (v w : MinkowskiModel d) :
    f.val v - f.val w = f.val.linear (v-w) := by
  rw [apply_eq f v, apply_eq f w, _root_.map_sub]; abel

theorem preserves_interval (f : PoincareGroup d) (σ : LorentzConvention)
    (v w : MinkowskiModel d) : intervalSq σ (f.val v) (f.val w) = intervalSq σ v w := by
  change minkowskiForm σ d (f.val w - f.val v) (f.val w - f.val v) = _
  rw [map_sub]
  exact LorentzGroup.preserves_metric (linear f) σ _ _

theorem contDiff (f : PoincareGroup d) : ContDiff ℝ ∞ f.val := by
  have h := (LorentzGroup.toContinuousLinearEquiv (linear f)).contDiff (n := ∞) |>.add
    (contDiff_const (c := f.val 0))
  convert h using 1
  funext x; exact apply_eq f x

def toSchemeMap (f : PoincareGroup d) :
    Manifold.scheme (d+1) (MinkowskiModel d) ⟶ Manifold.scheme (d+1) (MinkowskiModel d) :=
  Manifold.schemeMap f.val (contDiff f).contMDiff

def toSchemeIso (f : PoincareGroup d) :
    Manifold.scheme (d+1) (MinkowskiModel d) ≅ Manifold.scheme (d+1) (MinkowskiModel d) where
  hom := toSchemeMap f
  inv := toSchemeMap f⁻¹
  hom_inv_id := by
    rw [toSchemeMap, toSchemeMap, ← Manifold.schemeMap_comp]
    have h : (fun x => (f⁻¹).val (f.val x)) = id := funext f.val.symm_apply_apply
    simpa only [Function.comp_def, h] using
      (Manifold.schemeMap_id (M := MinkowskiModel d) (n := d+1))
  inv_hom_id := by
    rw [toSchemeMap, toSchemeMap, ← Manifold.schemeMap_comp]
    have h : (fun x => f.val ((f⁻¹).val x)) = id := funext f.val.apply_symm_apply
    simpa only [Function.comp_def, h] using
      (Manifold.schemeMap_id (M := MinkowskiModel d) (n := d+1))

end PoincareGroup
end ProjectAInos.SmoothGeometry.Minkowski
