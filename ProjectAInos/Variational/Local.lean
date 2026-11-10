module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# First variation in a fixed trivialization

An experimental, theory-independent local API for issue #7. The base point is
held fixed under variation. This is a coordinate model for first jets, not a
construction of the geometric jet bundle. No metric is used.

`jet` uses the total function `fderiv`; every analytic interpretation below
therefore carries explicit differentiability assumptions. In particular, the
definition alone does not certify that a field is differentiable.
-/

@[expose] public section

namespace ProjectAInos.Variational

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Value and first derivative in a fixed trivialization of `E × F → E`. -/
abbrev JetFiber (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] := F × (E →L[ℝ] F)

/-- A scalar Lagrangian relative to a separately chosen integration measure. -/
abbrev Lagrangian (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] := E → JetFiber E F → ℝ

/-- The first jet in this chart, omitting the separately supplied base point. -/
noncomputable def jet (u : E → F) (x : E) : JetFiber E F :=
  (u x, fderiv ℝ u x)

/-- Vertical affine variation; the base coordinates do not move. -/
def perturb (u η : E → F) (ε : ℝ) : E → F := fun x => u x + ε • η x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem perturb_zero (u η : E → F) : perturb u η 0 = u := by
  funext x
  simp [perturb]

theorem jet_add {η ζ : E → F} {x : E}
    (hη : DifferentiableAt ℝ η x) (hζ : DifferentiableAt ℝ ζ x) :
    jet (η + ζ) x = jet η x + jet ζ x := by
  simp only [jet, fderiv_add hη hζ, Pi.add_apply, Prod.mk_add_mk]

theorem jet_const_smul {η : E → F} {x : E}
    (hη : DifferentiableAt ℝ η x) (c : ℝ) :
    jet (c • η) x = c • jet η x := by
  simp only [jet, fderiv_const_smul hη c, Pi.smul_apply, Prod.smul_mk]

/-- Holonomic jets respect affine variations at differentiability points. -/
theorem jet_perturb {u η : E → F} {x : E}
    (hu : DifferentiableAt ℝ u x) (hη : DifferentiableAt ℝ η x) (ε : ℝ) :
    jet (perturb u η ε) x = jet u x + ε • jet η x := by
  change jet (u + ε • η) x = _
  rw [jet_add hu (hη.const_smul ε), jet_const_smul hη ε]

/-- The action integrand before choosing a measure or region. -/
noncomputable def density (L : Lagrangian E F) (u : E → F) (x : E) : ℝ :=
  L x (jet u x)

/-- Candidate first-variation density; its derivative meaning is proved below. -/
noncomputable def firstVariationDensity (L : Lagrangian E F) (u η : E → F)
    (x : E) : ℝ :=
  fderiv ℝ (L x) (jet u x) (jet η x)

/-- Chain rule along the affine jet path, at an arbitrary parameter value. -/
theorem hasDerivAt_density_perturb {L : Lagrangian E F} {u η : E → F}
    {x : E} (ε : ℝ) (hu : DifferentiableAt ℝ u x)
    (hη : DifferentiableAt ℝ η x)
    (hL : DifferentiableAt ℝ (L x) (jet (perturb u η ε) x)) :
    HasDerivAt (fun t => density L (perturb u η t) x)
      (firstVariationDensity L (perturb u η ε) η x) ε := by
  have hp : HasDerivAt (fun t : ℝ => jet u x + t • jet η x) (jet η x) ε := by
    simpa using ((hasDerivAt_id ε).smul_const (jet η x)).const_add (jet u x)
  rw [jet_perturb hu hη ε] at hL
  simpa only [Function.comp_def, density, firstVariationDensity, jet_perturb hu hη]
    using hL.hasFDerivAt.comp_hasDerivAt ε hp

/-- Pointwise first variation at zero; no integration or boundary assumptions. -/
theorem hasDerivAt_density {L : Lagrangian E F} {u η : E → F} {x : E}
    (hu : DifferentiableAt ℝ u x) (hη : DifferentiableAt ℝ η x)
    (hL : DifferentiableAt ℝ (L x) (jet u x)) :
    HasDerivAt (fun ε => density L (perturb u η ε) x)
      (firstVariationDensity L u η x) 0 := by
  simpa using hasDerivAt_density_perturb (L := L) (u := u) (η := η) 0 hu hη
    (by simpa using hL)

/-- Decomposition into value and derivative contributions, with no inner product. -/
theorem firstVariationDensity_split (L : Lagrangian E F) (u η : E → F) (x : E) :
    firstVariationDensity L u η x =
      fderiv ℝ (L x) (jet u x) (η x, 0) +
      fderiv ℝ (L x) (jet u x) (0, fderiv ℝ η x) := by
  rw [← map_add]
  simp [firstVariationDensity, jet]

theorem firstVariationDensity_add (L : Lagrangian E F) (u : E → F)
    {η ζ : E → F} {x : E} (hη : DifferentiableAt ℝ η x)
    (hζ : DifferentiableAt ℝ ζ x) :
    firstVariationDensity L u (η + ζ) x =
      firstVariationDensity L u η x + firstVariationDensity L u ζ x := by
  simp only [firstVariationDensity, jet_add hη hζ, map_add]

theorem firstVariationDensity_smul (L : Lagrangian E F) (u : E → F)
    {η : E → F} {x : E} (hη : DifferentiableAt ℝ η x) (c : ℝ) :
    firstVariationDensity L u (c • η) x = c * firstVariationDensity L u η x := by
  simp only [firstVariationDensity, jet_const_smul hη c, map_smul, smul_eq_mul]

end ProjectAInos.Variational
