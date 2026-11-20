/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.ThreePlusOne
public import ProjectAinos.SmoothGeometry.DifferentialForm.BivectorVolume
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The transport of the equations with sources by a proper Lorentz map

A proper Lorentz map `L` (`det L = 1`) carries a solution of the equations of the field with a
matter current to a solution with the transported current (Landau–Lifshitz, *The Classical
Theory of Fields*, §§23, 28, 30, 38).

* `coordinateVolume_comp`: the pullback of the volume `dt ∧ dx ∧ dy ∧ dz` by a linear map is its
  determinant times the volume.
* `matterCurrentForm_lorentz`: `L^*(−ι_k vol) = −ι_{k′} vol` with `k′(y) = L⁻¹ k(L y)`.
* `star_eq_hodgeForm`: the pointwise star of `Field.lean` is `hodgeForm .timeNegative .standard`.
* `excitation_lorentz`: `d(−⋆F) = J` on a set `U` gives `d(−⋆L^*F) = L^*J` on `L⁻¹ U`.
* `excitation_pullback`: for a `C²` potential on an open set `U` with `d(−⋆dA) = −ι_k vol`, the
  potential `L^*A` solves the equation with the current `k′` on `L⁻¹ U`.
* `excitation_of_inhomogeneous`: the converse of `inhomogeneous_of_excitation`. At a point where
  `div E = k⁰` and `curl B − ∂_t E = 𝐤`, the excitation satisfies `dH = −ι_k vol`. With it the
  four equations in the frame of the co-ordinates are equivalent to the equation of the forms.

Improper maps are excluded: the Hodge star commutes only with the pullback by a proper map
(`hodgeForm_pullback`).
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-! ### The volume and the current -/

/-- The pullback of the volume `dt ∧ dx ∧ dy ∧ dz` by a linear map is its determinant times the
volume. -/
theorem coordinateVolume_comp (L : Spacetime →L[ℝ] Spacetime) :
    (coordinateForm (n := 4) id).compContinuousLinearMap L =
      LinearMap.det (L : Spacetime →ₗ[ℝ] Spacetime) • coordinateForm (n := 4) id := by
  have h1 (v : Fin 4 → Spacetime) :
      coordinateForm (n := 4) id v = (Pi.basisFun ℝ (Fin 4)).det v := by
    rw [coordinateForm_apply, Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
  apply topForm_ext_basis (Pi.basisFun ℝ (Fin 4))
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply,
    h1, h1]
  change (Pi.basisFun ℝ (Fin 4)).det ((L : Spacetime →ₗ[ℝ] Spacetime) ∘ _) = _
  rw [Module.Basis.det_comp, smul_eq_mul]

/-- The derivative of a Lorentz map is the map itself. -/
theorem fderiv_lorentz (L : LorentzGroup 3) (x : Spacetime) :
    fderiv ℝ L.val x = (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap :=
  (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap.fderiv

/-- A proper Lorentz map has the determinant `1`. -/
theorem det_properLorentz (L : properLorentzGroup 3) :
    LinearMap.det ((LorentzGroup.toContinuousLinearEquiv L.val).toContinuousLinearMap :
      Spacetime →ₗ[ℝ] Spacetime) = 1 := by
  change LinearMap.det L.val.val.toLinearMap = 1
  have h := L.property
  change L.val.val.det = 1 at h
  simpa only [LinearEquiv.coe_det, Units.val_one] using congrArg Units.val h

/-- The pullback of the current form of a matter current by a proper Lorentz map is the current
form of the transported current `y ↦ L⁻¹ k(L y)`. -/
theorem matterCurrentForm_lorentz (L : properLorentzGroup 3) (k : Spacetime → Spacetime) :
    pullback L.val.val (SourcedAction.matterCurrentForm k) =
      SourcedAction.matterCurrentForm (fun y => L.val.val.symm (k (L.val.val y))) := by
  funext x
  set Lc := (LorentzGroup.toContinuousLinearEquiv L.val).toContinuousLinearMap
  have hvol : (coordinateForm (n := 4) id).compContinuousLinearMap Lc =
      coordinateForm (n := 4) id := by
    rw [coordinateVolume_comp, det_properLorentz, one_smul]
  have hLv : Lc (L.val.val.symm (k (L.val.val x))) = k (L.val.val x) :=
    L.val.val.apply_symm_apply _
  have hi := interior_comp Lc (L.val.val.symm (k (L.val.val x))) (coordinateForm (n := 4) id)
  rw [hvol, hLv] at hi
  simp only [pullback, SourcedAction.matterCurrentForm, fderiv_lorentz]
  rw [hi]
  ext w
  rfl

/-! ### The excitation -/

/-- The pointwise star of `Field.lean` is the Hodge operation on forms with the convention
`timeNegative` and the standard orientation. -/
theorem star_eq_hodgeForm (F : Field) :
    (fun y => star (F y)) = hodgeForm .timeNegative .standard (by decide) F :=
  rfl

/-- The pullback commutes with the excitation `H = −⋆F` for a proper Lorentz map. -/
theorem neg_star_pullback (L : properLorentzGroup 3) (F : Field) :
    (fun y => -star (pullback L.val.val F y)) =
      pullback L.val.val (fun y => -star (F y)) := by
  have h := hodgeForm_pullback .timeNegative .standard (by decide : 2 + 2 = 3 + 1) L F
  rw [← star_eq_hodgeForm, ← star_eq_hodgeForm] at h
  funext y
  have hy := congrFun h y
  rw [hy]
  ext w
  rfl

/-- The equation `d(−⋆F) = J` of the excitation on a set `U` is carried by a proper Lorentz map
`L` to the equation `d(−⋆L^*F) = L^*J` on `L⁻¹ U`. -/
theorem excitation_lorentz (L : properLorentzGroup 3) {F : Field} {J : Form Spacetime 3}
    {U : Set Spacetime} (hF : ∀ x ∈ U, DifferentiableAt ℝ F x)
    (h : ∀ x ∈ U, exteriorDerivative (fun y => -star (F y)) x = J x) :
    ∀ x ∈ L.val.val ⁻¹' U,
      exteriorDerivative (fun y => -star (pullback L.val.val F y)) x = pullback L.val.val J x := by
  intro x hx
  have hH : DifferentiableAt ℝ (fun y => -star (F y)) (L.val.val x) :=
    (star.toContinuousLinearMap.differentiableAt.comp _ (hF _ hx)).neg
  have hL : ContDiffAt ℝ 2 L.val.val x :=
    (LorentzGroup.toContinuousLinearEquiv L.val).contDiff.contDiffAt
  rw [neg_star_pullback]
  have hd := exteriorDerivative_pullback_on (U := {x}) L.val.val (fun y => -star (F y))
    (fun _ hy => hy ▸ hL) (fun _ hy => hy ▸ hH) rfl
  rw [hd]
  simp only [pullback]
  rw [h _ hx]

/-- The field of a `C²` potential on an open set is differentiable there. -/
theorem differentiableAt_fieldTensor {A : Potential} {U : Set Spacetime} (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) {x : Spacetime} (hx : x ∈ U) :
    DifferentiableAt ℝ (fieldTensor A) x := by
  have hAx := (hA x hx).contDiffAt (hU.mem_nhds hx)
  change DifferentiableAt ℝ (extDeriv A) x
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Spacetime ℝ).differentiableAt.comp x
    ((hAx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

/-- The pullback of a `C²` potential on an open set `U` by a Lorentz map is `C²` on `L⁻¹ U`. -/
theorem contDiffOn_pullback_lorentz (L : LorentzGroup 3) {A : Potential} {U : Set Spacetime}
    (hA : ContDiffOn ℝ 2 A U) : ContDiffOn ℝ 2 (pullback L.val A) (L.val ⁻¹' U) := by
  have hL : ContDiff ℝ 2 L.val := (LorentzGroup.toContinuousLinearEquiv L).contDiff
  have hfun : pullback L.val A = fun y =>
      ContinuousAlternatingMap.compContinuousLinearMapCLM
        (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap (A (L.val y)) := by
    funext y
    simp only [pullback, fderiv_lorentz]
    rfl
  rw [hfun]
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM
    (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap :
      (Spacetime [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] (Spacetime [⋀^Fin 1]→L[ℝ] ℝ)).contDiff.comp_contDiffOn
    (hA.comp hL.contDiffOn (fun _ hy => hy))

/-- A `C²` potential with `d(−⋆dA) = −ι_k vol` on an open set `U` is carried by a proper Lorentz
map `L` to the potential `L^*A`, which solves the equation with the transported current
`y ↦ L⁻¹ k(L y)` on `L⁻¹ U`. -/
theorem excitation_pullback (L : properLorentzGroup 3) {A : Potential}
    {k : Spacetime → Spacetime} {U : Set Spacetime} (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U)
    (h : ∀ x ∈ U, exteriorDerivative (fun y => -star (fieldTensor A y)) x =
      SourcedAction.matterCurrentForm k x) :
    ∀ x ∈ L.val.val ⁻¹' U,
      exteriorDerivative (fun y => -star (fieldTensor (pullback L.val.val A) y)) x =
        SourcedAction.matterCurrentForm (fun y => L.val.val.symm (k (L.val.val y))) x := by
  intro x hx
  have hU' : IsOpen (L.val.val ⁻¹' U) :=
    hU.preimage (LorentzGroup.toContinuousLinearEquiv L.val).continuous
  have hpull := fieldTensor_pullback_on L.val.val A (U := L.val.val ⁻¹' U)
    (fun _ _ => (LorentzGroup.toContinuousLinearEquiv L.val).contDiff.contDiffAt)
    (fun y hy => (((hA _ hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)))
  have hloc := exteriorDerivative_local hU'
    (ω := fun y => -star (fieldTensor (pullback L.val.val A) y))
    (η := fun y => -star (pullback L.val.val (fieldTensor A) y))
    (fun y hy => by simp only [hpull hy])
  rw [hloc hx, excitation_lorentz L (fun y hy => differentiableAt_fieldTensor hU hA hy) h x hx,
    matterCurrentForm_lorentz]

/-! ### The equations with sources from the three-dimensional equations -/

/-- The sign `−1` of the time and `1` of space, by which the components of a two-form are raised
with the metric of the signature `(-+++)`. -/
def raiseSign (μ : Fin 4) : ℝ := if μ = 0 then -1 else 1

/-- The contravariant components `F^{μν} = raiseSign μ · raiseSign ν · F_{μν}` of a two-form. -/
def raisedComponents : TwoForm →L[ℝ] (Fin 4 → Fin 4 → ℝ) :=
  ContinuousLinearMap.pi fun μ => ContinuousLinearMap.pi fun ν =>
    (raiseSign μ * raiseSign ν) •
      ContinuousAlternatingMap.apply ℝ Spacetime ℝ ![Pi.single μ 1, Pi.single ν 1]

/-- The components of `raisedComponents`. -/
theorem raisedComponents_apply (F : TwoForm) (μ ν : Fin 4) :
    raisedComponents F μ ν = raiseSign μ * raiseSign ν * component F μ ν :=
  rfl

/-- The excitation `−⋆F` is the volume dual of the contravariant components of `F`. -/
theorem neg_star_eq_bivectorVolume (F : TwoForm) :
    -star F = bivectorVolume (raisedComponents F) := by
  rw [bivectorVolume_apply]
  change -hodgeFiber .timeNegative .standard (by decide) F = _
  rw [hodgeTwo_expansion]
  ext v
  simp [raisedComponents_apply, raiseSign, coordinateForm_apply, Matrix.det_fin_two]
  ring

/-- The exterior derivative of the excitation is the contraction of the volume with the
divergence `∂_μ F^{μν}`. -/
theorem exteriorDerivative_neg_star {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x) :
    exteriorDerivative (fun y => -star (F y)) x =
      interior (fun ν => ∑ μ : Fin 4, raisedComponents (fderiv ℝ F x (Pi.single μ 1)) μ ν)
        (coordinateForm id) := by
  have hfun : (fun y => -star (F y)) = fun y => bivectorVolume (raisedComponents (F y)) :=
    funext fun y => neg_star_eq_bivectorVolume (F y)
  have hB : DifferentiableAt ℝ (fun y => raisedComponents (F y)) x :=
    raisedComponents.differentiableAt.comp x hF
  have hd : fderiv ℝ (fun y => raisedComponents (F y)) x = raisedComponents.comp (fderiv ℝ F x) :=
    (raisedComponents.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  have hskew : ∀ᶠ y in 𝓝 x, ∀ i j,
      raisedComponents (F y) i j = -raisedComponents (F y) j i :=
    Filter.Eventually.of_forall fun y i j => by
      rw [raisedComponents_apply, raisedComponents_apply, component_swap (F y) i j]
      ring
  rw [exteriorDerivative, hfun, extDeriv_bivectorVolume hB hskew, hd]
  rfl

/-- The converse of `inhomogeneous_of_excitation`: at a point where `div E = k⁰` and
`curl B − ∂_t E = 𝐤`, the excitation satisfies `dH = −ι_k vol`. -/
theorem excitation_of_inhomogeneous {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime} (hdiv : divergence3 (electricField F) x = k x 0)
    (hcurl : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ) :
    exteriorDerivative (fun y => -star (F y)) x = SourcedAction.matterCurrentForm k x := by
  rw [exteriorDerivative_neg_star hF]
  have hk : SourcedAction.matterCurrentForm k x = interior (-k x) (coordinateForm id) := by
    have h := SourcedAction.matterCurrentForm_neg (fun y => -k y) x
    simp only [neg_neg] at h
    exact h
  rw [hk]
  congr 1
  have he (i : Fin 3) (μ : Fin 4) := partialAt_electricField hF i μ
  have hb (μ : Fin 4) := partialAt_magneticField hF μ
  have hsw (μ a b : Fin 4) := twoForm_swap (fderiv ℝ F x (Pi.single μ 1)) (Pi.single a 1)
    (Pi.single b 1)
  have hdg (μ a : Fin 4) : fderiv ℝ F x (Pi.single μ 1) ![Pi.single a 1, Pi.single a 1] = 0 := by
    linarith [hsw μ a a]
  have hc0 := hcurl 0
  have hc1 := hcurl 1
  have hc2 := hcurl 2
  simp only [divergence3, Fin.sum_univ_three, curl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hdiv hc0 hc1 hc2
  obtain ⟨hb01, hb11, hb21⟩ := hb 1
  obtain ⟨hb02, hb12, hb22⟩ := hb 2
  obtain ⟨hb03, hb13, hb23⟩ := hb 3
  have h3 : (Fin.succ 2 : Fin 4) = 3 := rfl
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, h3] at hdiv hc0 hc1 hc2
  rw [he 0 1, he 1 2, he 2 3] at hdiv
  rw [hb22, hb13, he 0 0] at hc0
  rw [hb03, hb21, he 1 0] at hc1
  rw [hb11, hb02, he 2 0] at hc2
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, h3] at hdiv hc0 hc1 hc2
  funext ν
  fin_cases ν <;>
    simp [Fin.sum_univ_four, raisedComponents_apply, raiseSign, component, hdg] <;>
    linarith [hsw 0 1 0, hsw 0 2 0, hsw 0 3 0, hsw 1 0 1, hsw 2 0 2, hsw 3 0 3,
      hsw 1 2 1, hsw 1 3 1, hsw 2 1 2, hsw 2 3 2, hsw 3 1 3, hsw 3 2 3]

end ProjectAinos.Electrodynamics
