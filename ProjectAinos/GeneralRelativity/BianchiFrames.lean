/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.HomogeneousSpace
public import ProjectAinos.GeneralRelativity.StructureConstants
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Invariant frames of the Bianchi types I, II, V and IX

Landau–Lifshitz, §116, in 0-based indices and the spatial co-ordinates `s = (s₀, s₁, s₂)`, with
`e_α = Pi.single α 1`. Each instance of `InvariantFrame` below has as its structure constants the
canonical ones of `StructureConstants`, with the bracket `[X, Y]^α = X^β ∂_β Y^α − Y^β ∂_β X^α`.

* `InvariantFrame.bianchiI`: the co-ordinate frame `X_a = e_a`, `ω^a = e_a` of `ℝ³`;
  `C = StructureConstants.bianchiI` (abelian).
* `InvariantFrame.bianchiII` (the Heisenberg group): `X₀ = e₀`, `X₁ = e₁`, `X₂ = e₂ + s₁ e₀` on
  `ℝ³`, with `[X₁, X₂] = X₀` and the other brackets zero; `C = StructureConstants.bianchiII`.
* `InvariantFrame.bianchiV`: `X₀ = e₀`, `X₁ = exp(s₀) e₁`, `X₂ = exp(s₀) e₂` on `ℝ³`, with
  `[X₀, X₁] = X₁`, `[X₀, X₂] = X₂` and `[X₁, X₂] = 0`; `C = StructureConstants.bianchiV`.
* `InvariantFrame.bianchiIX`: the left-invariant frame of `SU(2)` in the Euler angles on
  `domainIX = {0 < s₀ < π}`, dual to the one-forms `ω⁰ = (sin s₂, −sin s₀ cos s₂, 0)`,
  `ω¹ = (cos s₂, sin s₀ sin s₂, 0)`, `ω² = (0, cos s₀, 1)`, with `[X₀, X₁] = X₂`, `[X₁, X₂] = X₀`
  and `[X₂, X₀] = X₁`; `C = StructureConstants.bianchiIX`, `C^c_{ab} = ε_{abc}`.

The components are `fieldII`, `coframeII`, … (`fieldI`, …, `coframeIX`); the duality and the
brackets are `coframe_fieldII`, `bracket_fieldII`, …, and the simp lemmas
`InvariantFrame.bianchiII_field_zero`, …, `InvariantFrame.bianchiIX_coframe_two` and
`InvariantFrame.bianchiII_C`, … give the components and the structure constants of the instances.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set
open scoped ContDiff Real

namespace ProjectAinos.GeneralRelativity.HomogeneousSpace

open StructureConstants (levi)

/-! ### Derivatives of components -/

/-- The component `α` of the derivative of a map differentiable at `s` is the derivative of the
component `α`. -/
private theorem fderiv_apply_apply {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {s : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ f s) (v : Fin 3 → ℝ) (α : Fin 3) :
    fderiv ℝ f s v α = fderiv ℝ (fun s => f s α) s v := by
  rw [fderiv_apply hf]
  rfl

/-- The derivative of a scalar function, read off from a derivative of an equal function. -/
private theorem fderiv_apply_of_eq {g g' : (Fin 3 → ℝ) → ℝ} {L : (Fin 3 → ℝ) →L[ℝ] ℝ}
    {s : Fin 3 → ℝ} (hg : g = g') (h : HasFDerivAt g' L s) (v : Fin 3 → ℝ) :
    fderiv ℝ g s v = L v := by
  rw [hg, h.fderiv]

/-- The derivative of `s ↦ (sin s₀)⁻¹` where `sin s₀ ≠ 0`. -/
private theorem hasFDerivAt_inv_sin {s : Fin 3 → ℝ} (hs : Real.sin (s 0) ≠ 0) :
    HasFDerivAt (fun s : Fin 3 → ℝ => (Real.sin (s 0))⁻¹)
      (-(Real.cos (s 0) / Real.sin (s 0) ^ 2) • (proj 0 : (Fin 3 → ℝ) →L[ℝ] ℝ)) s := by
  have h := (hasDerivAt_inv hs).comp_hasFDerivAt s (hasFDerivAt_apply (𝕜 := ℝ) 0 s).sin
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [smul_apply, smul_eq_mul, proj_apply]
  field_simp

/-! ### Type I -/

/-- The frame of type I: the co-ordinate vectors `X_a = e_a`. -/
def fieldI : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun a _ => Pi.single a 1

/-- The coframe of type I: the co-ordinate one-forms `ω^a = e_a`. -/
def coframeI : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun a _ => Pi.single a 1

/-- The frame and the coframe of type I are dual. -/
theorem coframe_fieldI (s : Fin 3 → ℝ) (a b : Fin 3) :
    ∑ α, coframeI a s α * fieldI b s α = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [coframeI, fieldI, Fin.sum_univ_three]

/-- The brackets of type I vanish: the co-ordinate vectors are constant. -/
theorem bracket_fieldI (s : Fin 3 → ℝ) (a b : Fin 3) :
    fderiv ℝ (fieldI b) s (fieldI a s) - fderiv ℝ (fieldI a) s (fieldI b s) =
      ∑ c, StructureConstants.bianchiI c a b • fieldI c s := by
  have h (b : Fin 3) : fderiv ℝ (fieldI b) s = 0 := fderiv_const_apply _
  simp [h]

/-- **Type I**: the co-ordinate frame `X_a = e_a`, `ω^a = e_a` of `ℝ³`, with vanishing brackets
(`C = StructureConstants.bianchiI`). -/
def InvariantFrame.bianchiI : InvariantFrame where
  V := univ
  isOpen := isOpen_univ
  nonempty := univ_nonempty
  field := fieldI
  coframe := coframeI
  C := StructureConstants.bianchiI
  smooth_field _ := contDiffOn_const
  smooth_coframe _ := contDiffOn_const
  coframe_field s _ := coframe_fieldI s
  bracket s _ := bracket_fieldI s

/-- The structure constants of type I. -/
@[simp] theorem InvariantFrame.bianchiI_C :
    InvariantFrame.bianchiI.C = StructureConstants.bianchiI := rfl

/-- The domain of type I is `ℝ³`. -/
@[simp] theorem InvariantFrame.bianchiI_V : InvariantFrame.bianchiI.V = univ := rfl

/-- The frame of type I: `X_a = e_a`. -/
@[simp] theorem InvariantFrame.bianchiI_field (a : Fin 3) (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiI.field a s = Pi.single a 1 := rfl

/-- The coframe of type I: `ω^a = e_a`. -/
@[simp] theorem InvariantFrame.bianchiI_coframe (a : Fin 3) (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiI.coframe a s = Pi.single a 1 := rfl

/-! ### Type II -/

/-- The frame of type II (the Heisenberg group): `X₀ = e₀`, `X₁ = e₁`, `X₂ = e₂ + s₁ e₀`. -/
def fieldII : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  ![fun _ => ![1, 0, 0], fun _ => ![0, 1, 0], fun s => ![s 1, 0, 1]]

/-- The coframe of type II: `ω⁰ = (1, 0, −s₁)`, `ω¹ = (0, 1, 0)`, `ω² = (0, 0, 1)`. -/
def coframeII : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  ![fun s => ![1, 0, -s 1], fun _ => ![0, 1, 0], fun _ => ![0, 0, 1]]

/-- The frame of type II is smooth. -/
theorem contDiff_fieldII (a : Fin 3) : ContDiff ℝ ∞ (fieldII a) := by
  refine contDiff_pi.2 fun α => ?_
  fin_cases a <;> fin_cases α <;> simp [fieldII] <;> fun_prop

/-- The coframe of type II is smooth. -/
theorem contDiff_coframeII (a : Fin 3) : ContDiff ℝ ∞ (coframeII a) := by
  refine contDiff_pi.2 fun α => ?_
  fin_cases a <;> fin_cases α <;> simp [coframeII] <;> fun_prop

/-- The frame and the coframe of type II are dual. -/
theorem coframe_fieldII (s : Fin 3 → ℝ) (a b : Fin 3) :
    ∑ α, coframeII a s α * fieldII b s α = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [coframeII, fieldII, Fin.sum_univ_three]

/-- The derivatives `Σ_β v^β ∂_β X_a` of the frame of type II. -/
private theorem fderiv_fieldII (a : Fin 3) (s v : Fin 3 → ℝ) :
    fderiv ℝ (fieldII a) s v = ![0, 0, ![v 1, 0, 0]] a := by
  have hd := (contDiff_fieldII a).differentiable (by simp) s
  funext α
  rw [fderiv_apply_apply hd]
  fin_cases a <;> fin_cases α <;>
    simp [fieldII, (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) s).fderiv]

/-- The brackets of type II: `[X₁, X₂] = X₀`, and the others vanish. -/
theorem bracket_fieldII (s : Fin 3 → ℝ) (a b : Fin 3) :
    fderiv ℝ (fieldII b) s (fieldII a s) - fderiv ℝ (fieldII a) s (fieldII b s) =
      ∑ c, StructureConstants.bianchiII c a b • fieldII c s := by
  rw [fderiv_fieldII, fderiv_fieldII]
  funext α
  fin_cases a <;> fin_cases b <;> fin_cases α <;>
    simp [fieldII, Fin.sum_univ_three, levi]

/-- **Type II**: the invariant frame of the Heisenberg group on `ℝ³`, with
`C = StructureConstants.bianchiII`. -/
def InvariantFrame.bianchiII : InvariantFrame where
  V := univ
  isOpen := isOpen_univ
  nonempty := univ_nonempty
  field := fieldII
  coframe := coframeII
  C := StructureConstants.bianchiII
  smooth_field a := (contDiff_fieldII a).contDiffOn
  smooth_coframe a := (contDiff_coframeII a).contDiffOn
  coframe_field s _ := coframe_fieldII s
  bracket s _ := bracket_fieldII s

/-- The structure constants of type II. -/
@[simp] theorem InvariantFrame.bianchiII_C :
    InvariantFrame.bianchiII.C = StructureConstants.bianchiII := rfl

/-- The domain of type II is `ℝ³`. -/
@[simp] theorem InvariantFrame.bianchiII_V : InvariantFrame.bianchiII.V = univ := rfl

/-- The frame of type II: `X₀ = e₀`. -/
@[simp] theorem InvariantFrame.bianchiII_field_zero (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.field 0 s = ![1, 0, 0] := rfl

/-- The frame of type II: `X₁ = e₁`. -/
@[simp] theorem InvariantFrame.bianchiII_field_one (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.field 1 s = ![0, 1, 0] := rfl

/-- The frame of type II: `X₂ = e₂ + s₁ e₀`. -/
@[simp] theorem InvariantFrame.bianchiII_field_two (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.field 2 s = ![s 1, 0, 1] := rfl

/-- The coframe of type II: `ω⁰ = (1, 0, −s₁)`. -/
@[simp] theorem InvariantFrame.bianchiII_coframe_zero (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.coframe 0 s = ![1, 0, -s 1] := rfl

/-- The coframe of type II: `ω¹ = (0, 1, 0)`. -/
@[simp] theorem InvariantFrame.bianchiII_coframe_one (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.coframe 1 s = ![0, 1, 0] := rfl

/-- The coframe of type II: `ω² = (0, 0, 1)`. -/
@[simp] theorem InvariantFrame.bianchiII_coframe_two (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.coframe 2 s = ![0, 0, 1] := rfl

/-! ### Type V -/

/-- The frame of type V: `X₀ = e₀`, `X₁ = exp(s₀) e₁`, `X₂ = exp(s₀) e₂`. -/
def fieldV : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  ![fun _ => ![1, 0, 0], fun s => ![0, Real.exp (s 0), 0], fun s => ![0, 0, Real.exp (s 0)]]

/-- The coframe of type V: `ω⁰ = (1, 0, 0)`, `ω¹ = (0, exp(−s₀), 0)`,
`ω² = (0, 0, exp(−s₀))`. -/
def coframeV : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  ![fun _ => ![1, 0, 0], fun s => ![0, Real.exp (-s 0), 0], fun s => ![0, 0, Real.exp (-s 0)]]

/-- The frame of type V is smooth. -/
theorem contDiff_fieldV (a : Fin 3) : ContDiff ℝ ∞ (fieldV a) := by
  refine contDiff_pi.2 fun α => ?_
  fin_cases a <;> fin_cases α <;> simp [fieldV] <;> fun_prop

/-- The coframe of type V is smooth. -/
theorem contDiff_coframeV (a : Fin 3) : ContDiff ℝ ∞ (coframeV a) := by
  refine contDiff_pi.2 fun α => ?_
  fin_cases a <;> fin_cases α <;> simp [coframeV] <;> fun_prop

/-- The frame and the coframe of type V are dual. -/
theorem coframe_fieldV (s : Fin 3 → ℝ) (a b : Fin 3) :
    ∑ α, coframeV a s α * fieldV b s α = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [coframeV, fieldV, Fin.sum_univ_three, Real.exp_neg]

/-- The derivatives `Σ_β v^β ∂_β X_a` of the frame of type V. -/
private theorem fderiv_fieldV (a : Fin 3) (s v : Fin 3 → ℝ) :
    fderiv ℝ (fieldV a) s v =
      ![0, ![0, Real.exp (s 0) * v 0, 0], ![0, 0, Real.exp (s 0) * v 0]] a := by
  have hd := (contDiff_fieldV a).differentiable (by simp) s
  funext α
  rw [fderiv_apply_apply hd]
  fin_cases a <;> fin_cases α <;>
    simp [fieldV, ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) s).exp).fderiv]

/-- The brackets of type V: `[X₀, X₁] = X₁`, `[X₀, X₂] = X₂` and `[X₁, X₂] = 0`. -/
theorem bracket_fieldV (s : Fin 3 → ℝ) (a b : Fin 3) :
    fderiv ℝ (fieldV b) s (fieldV a s) - fderiv ℝ (fieldV a) s (fieldV b s) =
      ∑ c, StructureConstants.bianchiV c a b • fieldV c s := by
  rw [fderiv_fieldV, fderiv_fieldV]
  funext α
  fin_cases a <;> fin_cases b <;> fin_cases α <;>
    simp [fieldV, Fin.sum_univ_three]

/-- **Type V**: an invariant frame on `ℝ³` with `C = StructureConstants.bianchiV`. -/
def InvariantFrame.bianchiV : InvariantFrame where
  V := univ
  isOpen := isOpen_univ
  nonempty := univ_nonempty
  field := fieldV
  coframe := coframeV
  C := StructureConstants.bianchiV
  smooth_field a := (contDiff_fieldV a).contDiffOn
  smooth_coframe a := (contDiff_coframeV a).contDiffOn
  coframe_field s _ := coframe_fieldV s
  bracket s _ := bracket_fieldV s

/-- The structure constants of type V. -/
@[simp] theorem InvariantFrame.bianchiV_C :
    InvariantFrame.bianchiV.C = StructureConstants.bianchiV := rfl

/-- The domain of type V is `ℝ³`. -/
@[simp] theorem InvariantFrame.bianchiV_V : InvariantFrame.bianchiV.V = univ := rfl

/-- The frame of type V: `X₀ = e₀`. -/
@[simp] theorem InvariantFrame.bianchiV_field_zero (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.field 0 s = ![1, 0, 0] := rfl

/-- The frame of type V: `X₁ = exp(s₀) e₁`. -/
@[simp] theorem InvariantFrame.bianchiV_field_one (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.field 1 s = ![0, Real.exp (s 0), 0] := rfl

/-- The frame of type V: `X₂ = exp(s₀) e₂`. -/
@[simp] theorem InvariantFrame.bianchiV_field_two (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.field 2 s = ![0, 0, Real.exp (s 0)] := rfl

/-- The coframe of type V: `ω⁰ = (1, 0, 0)`. -/
@[simp] theorem InvariantFrame.bianchiV_coframe_zero (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.coframe 0 s = ![1, 0, 0] := rfl

/-- The coframe of type V: `ω¹ = (0, exp(−s₀), 0)`. -/
@[simp] theorem InvariantFrame.bianchiV_coframe_one (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.coframe 1 s = ![0, Real.exp (-s 0), 0] := rfl

/-- The coframe of type V: `ω² = (0, 0, exp(−s₀))`. -/
@[simp] theorem InvariantFrame.bianchiV_coframe_two (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.coframe 2 s = ![0, 0, Real.exp (-s 0)] := rfl

/-! ### Type IX -/

/-- The domain `0 < s₀ < π` of the Euler angles `(θ, φ, ψ) = (s₀, s₁, s₂)` of type IX. -/
def domainIX : Set (Fin 3 → ℝ) := {s | 0 < s 0 ∧ s 0 < π}

/-- The domain of type IX is open. -/
theorem isOpen_domainIX : IsOpen domainIX :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) continuous_const)

/-- The domain of type IX is nonempty: it contains `(π/2, 0, 0)`. -/
theorem nonempty_domainIX : domainIX.Nonempty :=
  ⟨![π / 2, 0, 0], show 0 < π / 2 ∧ π / 2 < π from
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩

/-- `sin s₀ > 0` on the domain of type IX. -/
theorem sin_pos_of_mem_domainIX {s : Fin 3 → ℝ} (hs : s ∈ domainIX) : 0 < Real.sin (s 0) :=
  Real.sin_pos_of_pos_of_lt_pi hs.1 hs.2

/-- The frame of type IX, the left-invariant frame of `SU(2)` in the Euler angles:
`X₀ = (sin s₂, −cos s₂ / sin s₀, cos s₀ cos s₂ / sin s₀)`,
`X₁ = (cos s₂, sin s₂ / sin s₀, −cos s₀ sin s₂ / sin s₀)` and `X₂ = (0, 0, 1)`. -/
def fieldIX : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  ![fun s => ![Real.sin (s 2), -Real.cos (s 2) / Real.sin (s 0),
      Real.cos (s 0) * Real.cos (s 2) / Real.sin (s 0)],
    fun s => ![Real.cos (s 2), Real.sin (s 2) / Real.sin (s 0),
      -Real.cos (s 0) * Real.sin (s 2) / Real.sin (s 0)],
    fun _ => ![0, 0, 1]]

/-- The coframe of type IX: `ω⁰ = (sin s₂, −sin s₀ cos s₂, 0)`, `ω¹ = (cos s₂, sin s₀ sin s₂, 0)`
and `ω² = (0, cos s₀, 1)` (L&L, §116). -/
def coframeIX : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  ![fun s => ![Real.sin (s 2), -(Real.sin (s 0) * Real.cos (s 2)), 0],
    fun s => ![Real.cos (s 2), Real.sin (s 0) * Real.sin (s 2), 0],
    fun s => ![0, Real.cos (s 0), 1]]

/-- The frame of type IX is smooth on its domain. -/
theorem contDiffOn_fieldIX (a : Fin 3) : ContDiffOn ℝ ∞ (fieldIX a) domainIX := by
  have h0 : ∀ x ∈ domainIX, Real.sin (x 0) ≠ 0 := fun x hx => (sin_pos_of_mem_domainIX hx).ne'
  refine contDiffOn_pi.2 fun α => ?_
  fin_cases a <;> fin_cases α <;> simp [fieldIX] <;> fun_prop (disch := assumption)

/-- The coframe of type IX is smooth. -/
theorem contDiff_coframeIX (a : Fin 3) : ContDiff ℝ ∞ (coframeIX a) := by
  refine contDiff_pi.2 fun α => ?_
  fin_cases a <;> fin_cases α <;> simp [coframeIX] <;> fun_prop

/-- The frame and the coframe of type IX are dual. -/
theorem coframe_fieldIX {s : Fin 3 → ℝ} (hs : s ∈ domainIX) (a b : Fin 3) :
    ∑ α, coframeIX a s α * fieldIX b s α = if a = b then 1 else 0 := by
  have h := (sin_pos_of_mem_domainIX hs).ne'
  have h2 := Real.sin_sq_add_cos_sq (s 2)
  fin_cases a <;> fin_cases b <;> simp [coframeIX, fieldIX, Fin.sum_univ_three] <;> field_simp <;>
    first | linear_combination h2 | ring

/-- The derivatives `Σ_β v^β ∂_β X_a` of the frame of type IX, as a table in `a`. -/
private def derivFieldIX (s v : Fin 3 → ℝ) : Fin 3 → (Fin 3 → ℝ) :=
  ![![Real.cos (s 2) * v 2,
      Real.cos (s 0) * Real.cos (s 2) / Real.sin (s 0) ^ 2 * v 0 +
        Real.sin (s 2) / Real.sin (s 0) * v 2,
      -(Real.cos (s 2) / Real.sin (s 0) ^ 2) * v 0 -
        Real.cos (s 0) * Real.sin (s 2) / Real.sin (s 0) * v 2],
    ![-(Real.sin (s 2) * v 2),
      -(Real.cos (s 0) * Real.sin (s 2) / Real.sin (s 0) ^ 2) * v 0 +
        Real.cos (s 2) / Real.sin (s 0) * v 2,
      Real.sin (s 2) / Real.sin (s 0) ^ 2 * v 0 -
        Real.cos (s 0) * Real.cos (s 2) / Real.sin (s 0) * v 2],
    0]

/-- The derivatives of the frame of type IX on its domain. -/
private theorem fderiv_fieldIX {s : Fin 3 → ℝ} (hs : s ∈ domainIX) (a : Fin 3)
    (v : Fin 3 → ℝ) : fderiv ℝ (fieldIX a) s v = derivFieldIX s v a := by
  have h := (sin_pos_of_mem_domainIX hs).ne'
  have hd := ((contDiffOn_fieldIX a).contDiffAt (isOpen_domainIX.mem_nhds hs)).differentiableAt
    (by simp)
  have p0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) s
  have p2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) s
  have hi := hasFDerivAt_inv_sin h
  have h0 := Real.sin_sq_add_cos_sq (s 0)
  funext α
  rw [fderiv_apply_apply hd]
  fin_cases a <;> fin_cases α
  · exact (fderiv_apply_of_eq rfl p2.sin v).trans (by simp [derivFieldIX])
  · refine (fderiv_apply_of_eq ?_ (p2.cos.fun_neg.fun_mul hi) v).trans ?_
    · funext x; simp [fieldIX, div_eq_mul_inv]
    · simp [derivFieldIX]; field_simp
  · refine (fderiv_apply_of_eq ?_ ((p0.cos.fun_mul p2.cos).fun_mul hi) v).trans ?_
    · funext x; simp [fieldIX, div_eq_mul_inv]
    · simp [derivFieldIX]; field_simp; linear_combination (-(Real.cos (s 2) * v 0)) * h0
  · exact (fderiv_apply_of_eq rfl p2.cos v).trans (by simp [derivFieldIX])
  · refine (fderiv_apply_of_eq ?_ (p2.sin.fun_mul hi) v).trans ?_
    · funext x; simp [fieldIX, div_eq_mul_inv]
    · simp [derivFieldIX]; field_simp
  · refine (fderiv_apply_of_eq ?_ ((p0.cos.fun_neg.fun_mul p2.sin).fun_mul hi) v).trans ?_
    · funext x; simp [fieldIX, div_eq_mul_inv]
    · simp [derivFieldIX]; field_simp; linear_combination (Real.sin (s 2) * v 0) * h0
  all_goals simp [fieldIX, derivFieldIX]

/-- The brackets of type IX: `[X_a, X_b] = Σ_c ε_{abc} X_c`, that is `[X₀, X₁] = X₂`,
`[X₁, X₂] = X₀` and `[X₂, X₀] = X₁`. -/
theorem bracket_fieldIX {s : Fin 3 → ℝ} (hs : s ∈ domainIX) (a b : Fin 3) :
    fderiv ℝ (fieldIX b) s (fieldIX a s) - fderiv ℝ (fieldIX a) s (fieldIX b s) =
      ∑ c, StructureConstants.bianchiIX c a b • fieldIX c s := by
  have h := (sin_pos_of_mem_domainIX hs).ne'
  have h0 := Real.sin_sq_add_cos_sq (s 0)
  have h2 := Real.sin_sq_add_cos_sq (s 2)
  rw [fderiv_fieldIX hs, fderiv_fieldIX hs]
  funext α
  fin_cases a <;> fin_cases b <;> fin_cases α <;>
    simp [fieldIX, derivFieldIX, Fin.sum_univ_three, levi] <;> field_simp <;>
    first
    | ring1
    | linear_combination (1 - Real.cos (s 0) ^ 2) * h2 - h0
    | linear_combination (Real.cos (s 0) ^ 2 - 1) * h2 + h0

/-- **Type IX**: the left-invariant frame of `SU(2)` in the Euler angles on `0 < s₀ < π`
(L&L, §116), with `C = StructureConstants.bianchiIX`, `C^c_{ab} = ε_{abc}`. -/
def InvariantFrame.bianchiIX : InvariantFrame where
  V := domainIX
  isOpen := isOpen_domainIX
  nonempty := nonempty_domainIX
  field := fieldIX
  coframe := coframeIX
  C := StructureConstants.bianchiIX
  smooth_field := contDiffOn_fieldIX
  smooth_coframe a := (contDiff_coframeIX a).contDiffOn
  coframe_field _ hs := coframe_fieldIX hs
  bracket _ hs := bracket_fieldIX hs

/-- The structure constants of type IX. -/
@[simp] theorem InvariantFrame.bianchiIX_C :
    InvariantFrame.bianchiIX.C = StructureConstants.bianchiIX := rfl

/-- The domain of type IX is `0 < s₀ < π`. -/
@[simp] theorem InvariantFrame.bianchiIX_V : InvariantFrame.bianchiIX.V = domainIX := rfl

/-- The frame of type IX: `X₀ = (sin s₂, −cos s₂ / sin s₀, cos s₀ cos s₂ / sin s₀)`. -/
@[simp] theorem InvariantFrame.bianchiIX_field_zero (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.field 0 s = ![Real.sin (s 2), -Real.cos (s 2) / Real.sin (s 0),
      Real.cos (s 0) * Real.cos (s 2) / Real.sin (s 0)] := rfl

/-- The frame of type IX: `X₁ = (cos s₂, sin s₂ / sin s₀, −cos s₀ sin s₂ / sin s₀)`. -/
@[simp] theorem InvariantFrame.bianchiIX_field_one (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.field 1 s = ![Real.cos (s 2), Real.sin (s 2) / Real.sin (s 0),
      -Real.cos (s 0) * Real.sin (s 2) / Real.sin (s 0)] := rfl

/-- The frame of type IX: `X₂ = (0, 0, 1)`. -/
@[simp] theorem InvariantFrame.bianchiIX_field_two (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.field 2 s = ![0, 0, 1] := rfl

/-- The coframe of type IX: `ω⁰ = (sin s₂, −sin s₀ cos s₂, 0)`. -/
@[simp] theorem InvariantFrame.bianchiIX_coframe_zero (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.coframe 0 s =
      ![Real.sin (s 2), -(Real.sin (s 0) * Real.cos (s 2)), 0] := rfl

/-- The coframe of type IX: `ω¹ = (cos s₂, sin s₀ sin s₂, 0)`. -/
@[simp] theorem InvariantFrame.bianchiIX_coframe_one (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.coframe 1 s =
      ![Real.cos (s 2), Real.sin (s 0) * Real.sin (s 2), 0] := rfl

/-- The coframe of type IX: `ω² = (0, cos s₀, 1)`. -/
@[simp] theorem InvariantFrame.bianchiIX_coframe_two (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.coframe 2 s = ![0, Real.cos (s 0), 1] := rfl

end ProjectAinos.GeneralRelativity.HomogeneousSpace
