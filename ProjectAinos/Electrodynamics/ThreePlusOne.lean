/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.FieldTransformation
public import ProjectAinos.Electrodynamics.MatterCurrent
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The equations of Maxwell for the electric and the magnetic field

For a field `G` on flat space-time, `electricField G i` and `magneticField G i` are the
functions `x ↦ Eᵢ(x)` and `x ↦ Bᵢ(x)` of the frame of the co-ordinates
(Landau–Lifshitz, *The Classical Theory of Fields*, §§26, 30). `partialAt f μ x` is the
derivative of `f` along the co-ordinate `x^μ`, `divergence3` the divergence in space and `curl`
the curl.

* `exteriorDerivative_spatial`, `exteriorDerivative_temporal`: the four components of `dG` are
  `div B` and `∂_t B + curl E`.
* `homogeneous_of_closed`: `dF = 0` gives `div B = 0` and `∂_t B + curl E = 0`, and
  `homogeneous_fieldTensor`: these hold for the field of a `C²` potential.
* `electricVector_excitation`, `magneticVector_excitation`: the excitation `H = −⋆F` has the
  electric part `B` and the magnetic part `−E`.
* `inhomogeneous_of_excitation`: `dH = −ι_k vol` for a matter current `k` gives
  `div E = k⁰` and `curl B − ∂_t E = 𝐤`.
* `maxwell_of_stationary`: on the set where the action with the current of the matter is
  stationary, the field of the potential satisfies the four equations.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-! ### The fields and their derivatives -/

/-- The electric field `x ↦ Eᵢ(x)` of a field. -/
def electricField (G : Field) (i : Fin 3) : Spacetime → ℝ := fun y => electricVector (G y) i

/-- The magnetic field `x ↦ Bᵢ(x)` of a field. -/
def magneticField (G : Field) (i : Fin 3) : Spacetime → ℝ := fun y => magneticVector (G y) i

/-- The derivative of a function along the co-ordinate `x^μ`. -/
def partialAt (f : Spacetime → ℝ) (μ : Fin 4) (x : Spacetime) : ℝ :=
  fderiv ℝ f x (Pi.single μ 1)

/-- The divergence `Σᵢ ∂ᵢ fᵢ` in space. -/
def divergence3 (f : Fin 3 → Spacetime → ℝ) (x : Spacetime) : ℝ :=
  ∑ i : Fin 3, partialAt (f i) i.succ x

/-- The curl `∇ × f` in space. -/
def curl (f : Fin 3 → Spacetime → ℝ) (x : Spacetime) : Fin 3 → ℝ :=
  ![partialAt (f 2) 2 x - partialAt (f 1) 3 x, partialAt (f 0) 3 x - partialAt (f 2) 1 x,
    partialAt (f 1) 1 x - partialAt (f 0) 2 x]

/-- The derivative of a component of a field is the component of its derivative. -/
theorem partialAt_component {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x)
    (μ a b : Fin 4) :
    partialAt (fun y => component (G y) a b) μ x =
      fderiv ℝ G x (Pi.single μ 1) ![Pi.single a 1, Pi.single b 1] := by
  let ev : TwoForm →L[ℝ] ℝ :=
    ContinuousAlternatingMap.apply ℝ Spacetime ℝ ![Pi.single a 1, Pi.single b 1]
  have hd : HasFDerivAt (fun y => component (G y) a b) (ev.comp (fderiv ℝ G x)) x :=
    ev.hasFDerivAt.comp x hG.hasFDerivAt
  rw [partialAt, hd.fderiv]
  rfl

theorem partialAt_electricField {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x)
    (i : Fin 3) (μ : Fin 4) :
    partialAt (electricField G i) μ x =
      fderiv ℝ G x (Pi.single μ 1) ![Pi.single i.succ 1, Pi.single 0 1] := by
  rw [← partialAt_component hG]
  congr 1
  funext y
  exact electricVector_apply (G y) i

theorem partialAt_magneticField {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x)
    (μ : Fin 4) :
    partialAt (magneticField G 0) μ x =
        fderiv ℝ G x (Pi.single μ 1) ![Pi.single 2 1, Pi.single 3 1] ∧
      partialAt (magneticField G 1) μ x =
        fderiv ℝ G x (Pi.single μ 1) ![Pi.single 3 1, Pi.single 1 1] ∧
      partialAt (magneticField G 2) μ x =
        fderiv ℝ G x (Pi.single μ 1) ![Pi.single 1 1, Pi.single 2 1] :=
  ⟨partialAt_component hG μ 2 3, partialAt_component hG μ 3 1, partialAt_component hG μ 1 2⟩

/-- The exterior derivative of a field on three vectors. -/
theorem exteriorDerivative_three (G : Field) (x u v w : Spacetime) :
    exteriorDerivative G x ![u, v, w] =
      fderiv ℝ G x u ![v, w] - fderiv ℝ G x v ![u, w] + fderiv ℝ G x w ![u, v] := by
  have h0 : Fin.removeNth (0 : Fin 3) ![u, v, w] = ![v, w] := by
    ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 3) ![u, v, w] = ![u, w] := by
    ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 3) ![u, v, w] = ![u, v] := by
    ext i; fin_cases i <;> rfl
  simp only [exteriorDerivative, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  rw [Fin.sum_univ_three, h0, h1, h2]
  norm_num
  ring

/-! ### The four components of the exterior derivative -/

/-- The spatial component of `dG` is the divergence of the magnetic field. -/
theorem exteriorDerivative_spatial {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x) :
    exteriorDerivative G x ![Pi.single 1 1, Pi.single 2 1, Pi.single 3 1] =
      divergence3 (magneticField G) x := by
  obtain ⟨h1, -, -⟩ := partialAt_magneticField hG 1
  obtain ⟨-, h2, -⟩ := partialAt_magneticField hG 2
  obtain ⟨-, -, h3⟩ := partialAt_magneticField hG 3
  have hs := twoForm_swap (fderiv ℝ G x (Pi.single 2 1)) (Pi.single 1 1) (Pi.single 3 1)
  rw [exteriorDerivative_three, divergence3, Fin.sum_univ_three]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  change _ = partialAt (magneticField G 0) 1 x + partialAt (magneticField G 1) 2 x +
    partialAt (magneticField G 2) 3 x
  rw [h1, h2, h3]
  linarith

/-- The components `(0, j, k)` of `dG` are `∂_t B + curl E`. -/
theorem exteriorDerivative_temporal {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x) :
    exteriorDerivative G x ![Pi.single 0 1, Pi.single 2 1, Pi.single 3 1] =
        partialAt (magneticField G 0) 0 x + curl (electricField G) x 0 ∧
      exteriorDerivative G x ![Pi.single 0 1, Pi.single 3 1, Pi.single 1 1] =
        partialAt (magneticField G 1) 0 x + curl (electricField G) x 1 ∧
      exteriorDerivative G x ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] =
        partialAt (magneticField G 2) 0 x + curl (electricField G) x 2 := by
  obtain ⟨hb0, hb1, hb2⟩ := partialAt_magneticField hG 0
  have he (i : Fin 3) (μ : Fin 4) := partialAt_electricField hG i μ
  have hsw (μ a b : Fin 4) := twoForm_swap (fderiv ℝ G x (Pi.single μ 1)) (Pi.single a 1)
    (Pi.single b 1)
  simp only [curl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · rw [exteriorDerivative_three, hb0, he 2 2, he 1 3]
    simp only [Fin.succ_one_eq_two]
    change _ = _ + (fderiv ℝ G x (Pi.single 2 1) ![Pi.single 3 1, Pi.single 0 1] -
      fderiv ℝ G x (Pi.single 3 1) ![Pi.single 2 1, Pi.single 0 1])
    linarith [hsw 2 0 3, hsw 3 0 2]
  · rw [exteriorDerivative_three, hb1, he 0 3, he 2 1]
    change _ = _ + (fderiv ℝ G x (Pi.single 3 1) ![Pi.single 1 1, Pi.single 0 1] -
      fderiv ℝ G x (Pi.single 1 1) ![Pi.single 3 1, Pi.single 0 1])
    linarith [hsw 3 0 1, hsw 1 0 3]
  · rw [exteriorDerivative_three, hb2, he 1 1, he 0 2]
    change _ = _ + (fderiv ℝ G x (Pi.single 1 1) ![Pi.single 2 1, Pi.single 0 1] -
      fderiv ℝ G x (Pi.single 2 1) ![Pi.single 1 1, Pi.single 0 1])
    linarith [hsw 1 0 2, hsw 2 0 1]

/-! ### The homogeneous equations -/

/-- A closed field satisfies `div B = 0` and `∂_t B + curl E = 0`. -/
theorem homogeneous_of_closed {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    (h : exteriorDerivative F x = 0) :
    divergence3 (magneticField F) x = 0 ∧
      ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0 := by
  obtain ⟨t0, t1, t2⟩ := exteriorDerivative_temporal hF
  refine ⟨?_, fun i => ?_⟩
  · rw [← exteriorDerivative_spatial hF, h]
    rfl
  · fin_cases i
    · exact t0.symm.trans (by rw [h]; rfl)
    · exact t1.symm.trans (by rw [h]; rfl)
    · exact t2.symm.trans (by rw [h]; rfl)

/-- The field of a `C²` potential satisfies the homogeneous equations on its domain. -/
theorem homogeneous_fieldTensor {A : Potential} {U : Set Spacetime} (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) {x : Spacetime} (hx : x ∈ U) :
    divergence3 (magneticField (fieldTensor A)) x = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor A) i) 0 x +
        curl (electricField (fieldTensor A)) x i = 0 := by
  have hAx := (hA x hx).contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fieldTensor A) x := by
    change DifferentiableAt ℝ (extDeriv A) x
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Spacetime ℝ).differentiableAt.comp x
      ((hAx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  exact homogeneous_of_closed hd (bianchi_on A hU hA hx)

/-! ### The excitation and the inhomogeneous equations -/

theorem electricVector_neg (G : TwoForm) : electricVector (-G) = -electricVector G := by
  funext i
  fin_cases i <;> simp [electricVector, component]

theorem magneticVector_neg (G : TwoForm) : magneticVector (-G) = -magneticVector G := by
  funext i
  fin_cases i <;> simp [magneticVector, component]

/-- The electric part of the Hodge dual is minus the magnetic part. -/
theorem electricVector_star (G : TwoForm) : electricVector (star G) = -magneticVector G := by
  funext i
  rw [electricVector_apply, component_swap, component_star_zero_succ]
  rfl

/-- The magnetic part of the Hodge dual is the electric part. -/
theorem magneticVector_star (G : TwoForm) : magneticVector (star G) = electricVector G := by
  have h1 := component_swap G 1 0
  have h2 := component_swap G 2 0
  have h3 := component_swap G 3 0
  funext i
  fin_cases i <;> simp [magneticVector, electricVector, component_star] <;> linarith

/-- The excitation `H = −⋆F` has the electric part `B`. -/
theorem electricVector_excitation (G : TwoForm) : electricVector (-star G) = magneticVector G := by
  rw [electricVector_neg, electricVector_star, neg_neg]

/-- The excitation `H = −⋆F` has the magnetic part `−E`. -/
theorem magneticVector_excitation (G : TwoForm) :
    magneticVector (-star G) = -electricVector G := by
  rw [magneticVector_neg, magneticVector_star]

theorem partialAt_neg (f : Spacetime → ℝ) (μ : Fin 4) (x : Spacetime) :
    partialAt (fun y => -f y) μ x = -partialAt f μ x := by
  rw [partialAt, partialAt, fderiv_fun_neg, neg_apply]

/-- The spatial component of the current form of the matter: `−ρ`. -/
theorem matterCurrentForm_spatial (k : Spacetime → Spacetime) (x : Spacetime) :
    SourcedAction.matterCurrentForm k x ![Pi.single 1 1, Pi.single 2 1, Pi.single 3 1] =
      -k x 0 := by
  simp only [SourcedAction.matterCurrentForm, ContinuousAlternatingMap.neg_apply, interior_apply,
    coordinateForm_apply]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove]

/-- The temporal components of the current form of the matter: the current density. -/
theorem matterCurrentForm_temporal (k : Spacetime → Spacetime) (x : Spacetime) :
    SourcedAction.matterCurrentForm k x ![Pi.single 0 1, Pi.single 2 1, Pi.single 3 1] = k x 1 ∧
      SourcedAction.matterCurrentForm k x ![Pi.single 0 1, Pi.single 3 1, Pi.single 1 1] =
        k x 2 ∧
      SourcedAction.matterCurrentForm k x ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] =
        k x 3 := by
  simp only [SourcedAction.matterCurrentForm, ContinuousAlternatingMap.neg_apply, interior_apply,
    coordinateForm_apply]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove]
  ring

/-- With the matter current `k`, the equation `dH = −ι_k vol` of the excitation gives
`div E = k⁰` and `curl B − ∂_t E = 𝐤`. -/
theorem inhomogeneous_of_excitation {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime}
    (h : exteriorDerivative (fun y => -star (F y)) x = SourcedAction.matterCurrentForm k x) :
    divergence3 (electricField F) x = k x 0 ∧
      ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ := by
  let H : Field := fun y => -star (F y)
  have hH : DifferentiableAt ℝ H x :=
    (star.toContinuousLinearMap.differentiableAt.comp x hF).neg
  have hE : electricField H = magneticField F := by
    funext i y
    exact congrFun (electricVector_excitation (F y)) i
  have hB (i : Fin 3) : magneticField H i = fun y => -electricField F i y := by
    funext y
    exact congrFun (magneticVector_excitation (F y)) i
  have hdiv : divergence3 (magneticField H) x = -divergence3 (electricField F) x := by
    simp only [divergence3, hB, partialAt_neg, Finset.sum_neg_distrib]
  obtain ⟨t0, t1, t2⟩ := exteriorDerivative_temporal hH
  obtain ⟨j1, j2, j3⟩ := matterCurrentForm_temporal k x
  have hs := exteriorDerivative_spatial hH
  change exteriorDerivative H x = _ at h
  rw [h, matterCurrentForm_spatial, hdiv] at hs
  rw [h, j1, hB, partialAt_neg, hE] at t0
  rw [h, j2, hB, partialAt_neg, hE] at t1
  rw [h, j3, hB, partialAt_neg, hE] at t2
  refine ⟨by linarith, fun i => ?_⟩
  fin_cases i
  · show curl (magneticField F) x 0 - partialAt (electricField F 0) 0 x = k x 1
    linarith
  · show curl (magneticField F) x 1 - partialAt (electricField F 1) 0 x = k x 2
    linarith
  · show curl (magneticField F) x 2 - partialAt (electricField F 2) 0 x = k x 3
    linarith

/-- On the set where the action with the current of the matter `k` is stationary, the field of
the potential satisfies the four equations of Maxwell in the frame of the co-ordinates. -/
theorem maxwell_of_stationary {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiff ℝ 2 A) {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    (hfin : Integrable (Variational.density
      (SourcedAction.lagrangian (SourcedAction.matterCurrentForm k)) A) (volume.restrict U))
    (hs : Variational.Stationary volume U
      (SourcedAction.lagrangian (SourcedAction.matterCurrentForm k)) A)
    {x : Spacetime} (hx : x ∈ U) :
    (divergence3 (magneticField (fieldTensor A)) x = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor A) i) 0 x +
        curl (electricField (fieldTensor A)) x i = 0) ∧
    (divergence3 (electricField (fieldTensor A)) x = k x 0 ∧
      ∀ i, curl (magneticField (fieldTensor A)) x i -
        partialAt (electricField (fieldTensor A) i) 0 x = k x i.succ) := by
  have hd : DifferentiableAt ℝ (fieldTensor A) x := by
    change DifferentiableAt ℝ (extDeriv A) x
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Spacetime ℝ).differentiableAt.comp x
      ((hA.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  exact ⟨homogeneous_fieldTensor hU hA.contDiffOn hx, inhomogeneous_of_excitation hd
    ((SourcedAction.stationary_iff_matterCurrent hU hA hk hfin).mp hs x hx)⟩

end ProjectAinos.Electrodynamics
