/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Hodge
public import ProjectAInos.SmoothGeometry.DifferentialForm.FiniteDual

/-! # The volume functional determined by a nonzero top form

An oriented top form is a vector in the top exterior power of the dual.
The functional used in Hodge duality divides by that volume vector. This
construction records the reciprocal normalization explicitly.
-/

@[expose] public section
noncomputable section
open Module exteriorPower

namespace ProjectAInos.SmoothGeometry.DifferentialForm

section OneDimension
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A nonzero vector in a one-dimensional space identifies scalars with its multiples. -/
def volumeMultiples (hdim : Module.finrank ℝ V = 1) (v : V) (hv : v ≠ 0) : ℝ ≃ₗ[ℝ] V :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℝ V v)
    ⟨fun _ _ h => (smul_left_injective ℝ hv) h,
      fun w => exists_smul_eq_of_finrank_eq_one hdim hv w⟩

/-- Evaluate a vector as a scalar multiple of the specified nonzero volume. -/
def volumeNormalizer (hdim : Module.finrank ℝ V = 1) (v : V) (hv : v ≠ 0) : V ≃ₗ[ℝ] ℝ :=
  (volumeMultiples hdim v hv).symm

theorem volumeNormalizer_smul (hdim : Module.finrank ℝ V = 1) (v : V) (hv : v ≠ 0) (r : ℝ) :
    volumeNormalizer hdim v hv (r • v) = r :=
  (volumeMultiples hdim v hv).symm_apply_apply r

theorem volumeNormalizer_self (hdim : Module.finrank ℝ V = 1) (v : V) (hv : v ≠ 0) :
    volumeNormalizer hdim v hv v = 1 := by
  simpa only [one_smul] using volumeNormalizer_smul hdim v hv 1

theorem volumeNormalizer_spec (hdim : Module.finrank ℝ V = 1) (v : V) (hv : v ≠ 0) (w : V) :
    volumeNormalizer hdim v hv w • v = w :=
  (volumeMultiples hdim v hv).apply_symm_apply w

theorem volumeNormalizer_unique (hdim : Module.finrank ℝ V = 1) (v : V) (hv : v ≠ 0)
    (f : V →ₗ[ℝ] ℝ) (hf : f v = 1) : f = (volumeNormalizer hdim v hv).toLinearMap := by
  ext w
  obtain ⟨r, rfl⟩ := exists_smul_eq_of_finrank_eq_one hdim hv w
  rw [map_smul, hf, smul_eq_mul, mul_one]
  exact (volumeNormalizer_smul hdim v hv r).symm

/-- Scaling the volume vector scales its evaluating functional reciprocally. -/
theorem volumeNormalizer_scale (hdim : Module.finrank ℝ V = 1) (v : V) (hv : v ≠ 0)
    (r : ℝ) (hr : r ≠ 0) (w : V) :
    volumeNormalizer hdim (r • v) (smul_ne_zero hr hv) w = r⁻¹ * volumeNormalizer hdim v hv w := by
  have h := volumeNormalizer_unique hdim (r • v) (smul_ne_zero hr hv)
    (r⁻¹ • (volumeNormalizer hdim v hv).toLinearMap) (by
      simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, volumeNormalizer_smul, smul_eq_mul]
      exact inv_mul_cancel₀ hr)
  exact (congrArg (fun f : V →ₗ[ℝ] ℝ => f w) h).symm

end OneDimension

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Hodge depends only on the metric and volume maps, not on their invertibility proofs. -/
theorem hodge_congr_data (B C : LinearMap.BilinForm ℝ V)
    (hB : Function.Bijective B) (hC : Function.Bijective C) (hBC : B = C)
    (vol vol' : ⋀[ℝ]^(Module.finrank ℝ V) V ≃ₗ[ℝ] ℝ) (hvol : vol = vol')
    {k l : ℕ} (hkl : k + l = Module.finrank ℝ V) :
    hodge B hB vol hkl = hodge C hC vol' hkl := by
  subst C
  subst vol'
  rfl

omit [FiniteDimensional ℝ V] in
private theorem cast_volume_apply {i j : ℕ} (h : i = j)
    (f : ⋀[ℝ]^j V →ₗ[ℝ] ℝ) (x : ⋀[ℝ]^i V) :
    (h.symm ▸ f) x = f (h ▸ x) := by subst j; rfl

/-- A nonzero top exterior covector canonically defines the Hodge volume functional. -/
def exteriorVolume (v : ⋀[ℝ]^(Module.finrank ℝ V) V) (hv : v ≠ 0) :
    ⋀[ℝ]^(Module.finrank ℝ V) V ≃ₗ[ℝ] ℝ :=
  volumeNormalizer (by simp) v hv

theorem exteriorVolume_self (v : ⋀[ℝ]^(Module.finrank ℝ V) V) (hv : v ≠ 0) :
    exteriorVolume v hv v = 1 := volumeNormalizer_self _ _ _

theorem exteriorVolume_spec (v : ⋀[ℝ]^(Module.finrank ℝ V) V) (hv : v ≠ 0)
    (w : ⋀[ℝ]^(Module.finrank ℝ V) V) : exteriorVolume v hv w • v = w :=
  volumeNormalizer_spec _ _ _ _

/-- A normalized top functional is uniquely fixed by its value on the chosen volume. -/
theorem exteriorVolume_unique (v : ⋀[ℝ]^(Module.finrank ℝ V) V) (hv : v ≠ 0)
    (f : ⋀[ℝ]^(Module.finrank ℝ V) V →ₗ[ℝ] ℝ) (hf : f v = 1) :
    f = (exteriorVolume v hv).toLinearMap := volumeNormalizer_unique _ _ _ _ hf

/-- Hodge's defining scalar equation is exactly equality with a multiple of the volume vector. -/
theorem hodge_wedge_volume (B : LinearMap.BilinForm ℝ V) (hB : Function.Bijective B)
    (v : ⋀[ℝ]^(Module.finrank ℝ V) V) (hv : v ≠ 0)
    {k l : ℕ} (hkl : k + l = Module.finrank ℝ V) (α β : ⋀[ℝ]^k V) :
    (hkl ▸ exteriorPower.wedge ℝ V k l α (hodge B hB (exteriorVolume v hv) hkl β)) =
      B.exteriorPower k β α • v := by
  have h := hodge_pairing B hB (exteriorVolume v hv) hkl α β
  change (hkl.symm ▸ (exteriorVolume v hv).toLinearMap)
    (exteriorPower.wedge ℝ V k l α (hodge B hB (exteriorVolume v hv) hkl β)) = _ at h
  rw [cast_volume_apply hkl] at h
  calc
    _ = exteriorVolume v hv
        (hkl ▸ exteriorPower.wedge ℝ V k l α (hodge B hB (exteriorVolume v hv) hkl β)) • v :=
      (exteriorVolume_spec v hv _).symm
    _ = _ := congrArg (fun r : ℝ => r • v) h

/-- Rescaling oriented volume by `r` rescales Hodge by `r`. -/
theorem hodge_scale_volume (B : LinearMap.BilinForm ℝ V) (hB : Function.Bijective B)
    (v : ⋀[ℝ]^(Module.finrank ℝ V) V) (hv : v ≠ 0) (r : ℝ) (hr : r ≠ 0)
    {k l : ℕ} (hkl : k + l = Module.finrank ℝ V) (α : ⋀[ℝ]^k V) :
    hodge B hB (exteriorVolume (r • v) (smul_ne_zero hr hv)) hkl α =
      r • hodge B hB (exteriorVolume v hv) hkl α := by
  symm
  apply hodge_unique
  intro β
  rw [map_smul]
  have hh : ∀ (γ : ⋀[ℝ]^k V) (δ : ⋀[ℝ]^l V),
      wedgePairing (exteriorVolume (r • v) (smul_ne_zero hr hv)) hkl γ δ =
        r⁻¹ * wedgePairing (exteriorVolume v hv) hkl γ δ := by
    intro γ δ
    change (hkl.symm ▸ (exteriorVolume (r • v) (smul_ne_zero hr hv)).toLinearMap)
      (exteriorPower.wedge ℝ V k l γ δ) =
      r⁻¹ * (hkl.symm ▸ (exteriorVolume v hv).toLinearMap)
        (exteriorPower.wedge ℝ V k l γ δ)
    rw [cast_volume_apply hkl, cast_volume_apply hkl]
    exact volumeNormalizer_scale _ v hv r hr _
  rw [hh, hodge_pairing]
  change r * (r⁻¹ * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]

end ProjectAInos.SmoothGeometry.DifferentialForm
