/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ProjectAInos.SmoothGeometry.Minkowski.HodgeFour
public import ProjectAInos.SmoothGeometry.Minkowski.Observer
public import ProjectAInos.SmoothGeometry.DifferentialForm.Calculus

/-! # Two-form coordinates and reconstruction by an observer -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ProjectAInos.SmoothGeometry.Minkowski
open DifferentialForm
abbrev TwoForm := MinkowskiModel 3 [⋀^Fin 2]→L[ℝ] ℝ

theorem twoForm_swap (F : TwoForm) (v w : MinkowskiModel 3) : F ![v,w] = -F ![w,v] := by
  have h := F.toAlternatingMap.map_swap ![w,v] (show (0 : Fin 2) ≠ 1 by decide)
  have hv : ![w,v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v,w] := by ext i; fin_cases i <;> rfl
  rw [hv] at h
  exact h

def component (F : TwoForm) (i j : Fin 4) : ℝ := F ![Pi.single i 1, Pi.single j 1]

def twoFormExpansion (F : TwoForm) : TwoForm :=
  component F 0 1 • coordinateForm ![0,1] + component F 0 2 • coordinateForm ![0,2] +
  component F 0 3 • coordinateForm ![0,3] + component F 1 2 • coordinateForm ![1,2] +
  component F 1 3 • coordinateForm ![1,3] + component F 2 3 • coordinateForm ![2,3]

theorem twoForm_expansion (F : TwoForm) : F = twoFormExpansion F := by
  have h10 := twoForm_swap F (Pi.single 1 1) (Pi.single 0 1)
  have h20 := twoForm_swap F (Pi.single 2 1) (Pi.single 0 1)
  have h21 := twoForm_swap F (Pi.single 2 1) (Pi.single 1 1)
  have h30 := twoForm_swap F (Pi.single 3 1) (Pi.single 0 1)
  have h31 := twoForm_swap F (Pi.single 3 1) (Pi.single 1 1)
  have h32 := twoForm_swap F (Pi.single 3 1) (Pi.single 2 1)
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply (Module.Basis.ext_alternating (Pi.basisFun ℝ (Fin 4)))
  intro f hf
  have h : f = ![f 0, f 1] := by ext i; fin_cases i <;> rfl
  rw [h]
  have hne : f 0 ≠ f 1 := fun he => (by norm_num : (0 : Fin 2) ≠ 1) (hf he)
  generalize h0 : f 0 = i at *
  generalize h1 : f 1 = j at *
  have htuple (i j : Fin 4) : (fun r : Fin 2 => Pi.single (![i,j] r) (1 : ℝ)) =
      ![Pi.single i 1, Pi.single j 1] := by ext r; fin_cases r <;> rfl
  fin_cases i <;> fin_cases j <;>
    simp_all [twoFormExpansion, component, coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply]

theorem hodgeTwo_expansion (σ : LorentzConvention) (F : TwoForm) :
    hodgeFiber σ .standard (by decide : 2+2=3+1) F =
      component F 0 1 • (-coordinateForm ![2,3]) + component F 0 2 • coordinateForm ![1,3] +
      component F 0 3 • (-coordinateForm ![1,2]) + component F 1 2 • coordinateForm ![0,3] +
      component F 1 3 • (-coordinateForm ![0,2]) + component F 2 3 • coordinateForm ![0,1] := by
  conv_lhs => rw [twoForm_expansion F]
  simp only [twoFormExpansion, map_add, map_smul, hodge_dt_dx, hodge_dt_dy, hodge_dt_dz,
    hodge_dx_dy, hodge_dx_dz, hodge_dy_dz]

theorem hodgeTwo_apply (σ : LorentzConvention) (F : TwoForm) (v w : MinkowskiModel 3) :
    hodgeFiber σ .standard (by decide : 2+2=3+1) F ![v,w] =
      -component F 0 1 * (v 2*w 3-v 3*w 2) + component F 0 2 * (v 1*w 3-v 3*w 1) -
      component F 0 3 * (v 1*w 2-v 2*w 1) + component F 1 2 * (v 0*w 3-v 3*w 0) -
      component F 1 3 * (v 0*w 2-v 2*w 0) + component F 2 3 * (v 0*w 1-v 1*w 0) := by
  rw [hodgeTwo_expansion]
  simp [coordinateForm_apply, Matrix.det_fin_two]
  ring

/-- The temporal part of a two-form relative to a timelike direction. -/
def temporalPart (u : MinkowskiModel 3) (F : TwoForm) : TwoForm :=
  wedgeLeft (pair u) (F.curryLeft u)

theorem temporalPart_apply (u : MinkowskiModel 3) (F : TwoForm) (v w : MinkowskiModel 3) :
    temporalPart u F ![v,w] = pair u v * F ![u,w] - pair u w * F ![u,v] := by
  have hr : Fin.removeNth (1 : Fin 2) ![v,w] = ![v] := by
    ext i
    fin_cases i
    rfl
  simp [temporalPart, wedgeLeft, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ, hr, sub_eq_add_neg]

theorem pair_four (u v : MinkowskiModel 3) :
    pair u v = u 0*v 0-u 1*v 1-u 2*v 2-u 3*v 3 := by
  simp [pair, minkowskiForm_apply, Fin.sum_univ_succ, lorentzSign]
  ring

/-- Algebraic reconstruction, valid before imposing the observer normalization. -/
theorem twoForm_reconstruction_scaled (σ : LorentzConvention) (u : MinkowskiModel 3) (F : TwoForm) :
    temporalPart u F - hodgeFiber σ .standard (by decide : 2+2=3+1)
      (temporalPart u (hodgeFiber σ .standard (by decide) F)) = intervalQuadratic u • F := by
  rw [twoForm_expansion F]
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  simp [hodgeTwo_apply, component, temporalPart_apply, twoFormExpansion,
    hodge_dt_dx, hodge_dt_dy, hodge_dt_dz, hodge_dx_dy, hodge_dx_dz, hodge_dy_dz,
    coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply, pair_four,
    intervalQuadratic_apply]
  ring

/-- An arbitrary observer recovers a two-form from its two contractions. -/
theorem observer_twoForm_reconstruction (σ : LorentzConvention) (u : Observer 3) (F : TwoForm) :
    temporalPart u.velocity F - hodgeFiber σ .standard (by decide : 2+2=3+1)
      (temporalPart u.velocity (hodgeFiber σ .standard (by decide) F)) = F := by
  rw [twoForm_reconstruction_scaled, u.unit, one_smul]

/-- Electric/magnetic contraction data reconstruct the field for either orientation. -/
def reconstructTwoForm (σ : LorentzConvention) (o : SpacetimeOrientation) (u : Observer 3)
    (E B : MinkowskiModel 3 [⋀^Fin 1]→L[ℝ] ℝ) : TwoForm :=
  wedgeLeft u.clock E - hodgeFiber σ o (by decide : 2+2=3+1) (wedgeLeft u.clock B)

theorem reconstructTwoForm_contractions (σ : LorentzConvention) (o : SpacetimeOrientation)
    (u : Observer 3) (F : TwoForm) :
    reconstructTwoForm σ o u (F.curryLeft u.velocity)
      ((hodgeFiber σ o (by decide : 2+2=3+1) F).curryLeft u.velocity) = F := by
  cases o with
  | standard => exact observer_twoForm_reconstruction σ u F
  | reversed =>
    unfold reconstructTwoForm
    have hc (G : TwoForm) : (-G).curryLeft u.velocity = -(G.curryLeft u.velocity) := by
      ext v
      simp
    have hw (G : MinkowskiModel 3 [⋀^Fin 1]→L[ℝ] ℝ) :
        wedgeLeft u.clock (-G) = -wedgeLeft u.clock G := (wedgeLeftL u.clock).map_neg G
    simp only [hodgeFiber_reverse, hc, hw, map_neg, neg_neg]
    exact observer_twoForm_reconstruction σ u F

end ProjectAInos.SmoothGeometry.Minkowski
