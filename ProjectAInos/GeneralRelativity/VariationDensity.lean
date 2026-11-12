/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.ParticleAction
public import ProjectAInos.SmoothGeometry.Lorentzian.CurveFamily

/-! # Intrinsic first variations of particle densities

A genuine C² manifold-valued family is varied. The interchange of native
parameter derivatives and metric compatibility identify its density
derivative without choosing a chart in the theorem statement.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity

open SmoothGeometry LorentzMetric

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "J" => 𝓘(ℝ, ℝ × ℝ)

/-- Differentiate the actual curve-velocity density of a manifold family.
The variation field is the native derivative in the first parameter. -/
theorem quadraticDensity_hasDerivAt (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {a t : ℝ} (hΓ : ContMDiffAt J I 2 Γ (a, t)) :
    HasDerivAt (fun ε => (1 / 2 : ℝ) * g.form (Γ (ε, t))
      (curveVelocity (fun s => Γ (ε, s)) t) (curveVelocity (fun s => Γ (ε, s)) t))
      (g.form (Γ (a, t))
        (g.covariantAlong (γ := fun s => Γ (a, s))
          (fun s => familyVelocity Γ (1, 0) (a, s)) t)
        (curveVelocity (fun s => Γ (a, s)) t)) a := by
  have hslice : ContDiff ℝ ∞ (fun ε : ℝ => (ε, t)) := contDiff_id.prodMk contDiff_const
  have hγ : MDifferentiableAt 𝓘(ℝ) I (fun ε => Γ (ε, t)) a :=
    (hΓ.mdifferentiableAt (by norm_num)).comp a
      (hslice.contMDiff.mdifferentiable (by simp) a)
  have hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun ε => TotalSpace.mk' E (Γ (ε, t)) (familyVelocity (d := d) Γ (0, 1) (ε, t))) a :=
    ((familyVelocity_contMDiffAt (0, 1) hΓ).mdifferentiableAt (by norm_num)).comp a
      (hslice.contMDiff.mdifferentiable (by simp) a)
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hΓ.of_le (by norm_num))
  have heq : (fun ε => (1 / 2 : ℝ) * g.form (Γ (ε, t))
      (curveVelocity (fun s => Γ (ε, s)) t) (curveVelocity (fun s => Γ (ε, s)) t)) =ᶠ[𝓝 a]
      (fun ε => (1 / 2 : ℝ) * g.form (Γ (ε, t))
        (familyVelocity Γ (0, 1) (ε, t)) (familyVelocity Γ (0, 1) (ε, t))) := by
    filter_upwards [hslice.continuous.continuousAt hn] with ε hε
    have hpath : HasDerivAt (fun s : ℝ => (ε, s)) (0, 1) t :=
      (hasDerivAt_const t ε).prodMk (hasDerivAt_id t)
    have hv : curveVelocity (d := d) (fun s => Γ (ε, s)) t = familyVelocity Γ (0, 1) (ε, t) := by
      simpa only [Function.comp_def] using!
        (curveVelocity_family (ρ := fun s => (ε, s)) (hε.mdifferentiableAt (by norm_num))
          hpath)
    rw [hv]
  have hp := ((g.hasDerivAt_pairing_along hγ hV hV).const_mul (1 / 2 : ℝ)).congr_of_eventuallyEq heq
  have hpath : HasDerivAt (fun s : ℝ => (a, s)) (0, 1) t :=
    (hasDerivAt_const t a).prodMk (hasDerivAt_id t)
  have ht : curveVelocity (d := d) (fun s => Γ (a, s)) t = familyVelocity Γ (0, 1) (a, t) := by
    simpa only [Function.comp_def] using!
      (curveVelocity_family (ρ := fun s => (a, s)) (hΓ.mdifferentiableAt (by norm_num))
        hpath)
  apply hp.congr_deriv
  rw [g.covariantAlong_family_interchange hΓ, ht, g.symmetric (Γ (a, t))]
  ring

/-- The massive density has a native first variation at a timelike family
velocity. Timelikeness is needed only at the point of differentiation. -/
theorem freeDensity_hasDerivAt (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {a t : ℝ} (hΓ : ContMDiffAt J I 2 Γ (a, t))
    (hv : Timelike g (curveVelocity (fun s => Γ (a, s)) t)) :
    HasDerivAt (fun ε => -m * speedAlong g (fun s => Γ (ε, s)) t)
      ((m / speedAlong g (fun s => Γ (a, s)) t) * g.form (Γ (a, t))
        (g.covariantAlong (γ := fun s => Γ (a, s))
          (fun s => familyVelocity Γ (1, 0) (a, s)) t)
        (curveVelocity (fun s => Γ (a, s)) t)) a := by
  have hq : HasDerivAt (fun ε => g.form (Γ (ε, t))
      (curveVelocity (fun s => Γ (ε, s)) t) (curveVelocity (fun s => Γ (ε, s)) t))
      (2 * g.form (Γ (a, t))
        (g.covariantAlong (γ := fun s => Γ (a, s))
          (fun s => familyVelocity Γ (1, 0) (a, s)) t)
        (curveVelocity (fun s => Γ (a, s)) t)) a := by
    convert (quadraticDensity_hasDerivAt g hΓ).const_mul 2 using 1
    ext ε
    ring
  have hn : -g.form (Γ (a, t)) (curveVelocity (fun s => Γ (a, s)) t)
      (curveVelocity (fun s => Γ (a, s)) t) ≠ 0 := ne_of_gt (neg_pos.mpr hv)
  apply ((hq.neg.sqrt hn).const_mul (-m)).congr_deriv
  dsimp only [speedAlong, properSpeed, Pi.neg_apply]
  ring

end ProjectAInos.GeneralRelativity
