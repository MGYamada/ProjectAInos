module

public import ProjectAInos.Variational.Action
public import ProjectAInos.Variational.EulerLagrange
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Dimension and nonzero-variation checks

These examples check the common API in dimensions one and four. They do not
assert the equations of Mechanics or Maxwell theory. The norm used for
calculus on coordinate spaces does not specify a spacetime metric.
-/

@[expose] public section

namespace ProjectAInos.Variational

/-- The one-coordinate base really is continuously linearly equivalent to time. -/
noncomputable def timeCoordinates : Coordinates 1 ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)

/-- On a real time axis, a derivative map is determined by its velocity at `1`. -/
theorem time_derivative_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ →L[ℝ] F) (t : ℝ) : p t = t • p 1 := by
  simpa using p.map_smul t (1 : ℝ)

/-- One-dimensional specialization with any number of field components. -/
theorem mechanics_firstVariation {m : ℕ} {L : Lagrangian ℝ (Coordinates m)}
    {q η : ℝ → Coordinates m} {t : ℝ}
    (hq : DifferentiableAt ℝ q t) (hη : DifferentiableAt ℝ η t)
    (hL : DifferentiableAt ℝ (L t) (jet q t)) :
    HasDerivAt (fun ε => density L (perturb q η ε) t)
      (firstVariationDensity L q η t) 0 :=
  hasDerivAt_density hq hη hL

/-- Four-dimensional specialization, including `m = 4` potential components. -/
theorem spacetime_firstVariation {m : ℕ}
    {L : Lagrangian (Coordinates 4) (Coordinates m)}
    {u η : Coordinates 4 → Coordinates m} {x : Coordinates 4}
    (hu : DifferentiableAt ℝ u x) (hη : DifferentiableAt ℝ η x)
    (hL : DifferentiableAt ℝ (L x) (jet u x)) :
    HasDerivAt (fun ε => density L (perturb u η ε) x)
      (firstVariationDensity L u η x) 0 :=
  hasDerivAt_density hu hη hL

section Quadratic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A nonlinear diagnostic Lagrangian sensitive to a chosen jet component. -/
def quadratic (ℓ : JetFiber E F →L[ℝ] ℝ) : Lagrangian E F :=
  fun _ j => ℓ j * ℓ j

/-- Its analytic derivative, not a definition of the desired variation. -/
theorem firstVariationDensity_quadratic (ℓ : JetFiber E F →L[ℝ] ℝ)
    (u η : E → F) (x : E) :
    firstVariationDensity (quadratic ℓ) u η x =
      2 * ℓ (jet u x) * ℓ (jet η x) := by
  have h := (ℓ.hasFDerivAt (x := jet u x)).mul ℓ.hasFDerivAt
  have heq := congrArg (fun p : JetFiber E F →L[ℝ] ℝ => p (jet η x)) h.fderiv
  change (fderiv ℝ (⇑ℓ * ⇑ℓ) (jet u x)) (jet η x) = _
  rw [heq]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The nonlinear diagnostic is also the actual derivative of the varied density. -/
theorem hasDerivAt_quadratic (ℓ : JetFiber E F →L[ℝ] ℝ)
    {u η : E → F} {x : E} (hu : DifferentiableAt ℝ u x)
    (hη : DifferentiableAt ℝ η x) :
    HasDerivAt (fun ε => density (quadratic ℓ) (perturb u η ε) x)
      (2 * ℓ (jet u x) * ℓ (jet η x)) 0 := by
  rw [← firstVariationDensity_quadratic]
  apply hasDerivAt_density hu hη
  change DifferentiableAt ℝ (⇑ℓ * ⇑ℓ) (jet u x)
  exact ℓ.differentiableAt.mul ℓ.differentiableAt

end Quadratic

/-- Select a directional derivative component of a scalar field's jet. -/
noncomputable def derivativeComponent {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) : JetFiber E ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ v).comp (ContinuousLinearMap.snd ℝ ℝ (E →L[ℝ] ℝ))

/-- For `L = velocity²` and `q = η = id`, the first variation is nonzero. -/
theorem mechanics_quadratic_nonzero (t : ℝ) :
    firstVariationDensity (quadratic (derivativeComponent (1 : ℝ)))
      (fun s : ℝ => s) (fun s : ℝ => s) t = 2 := by
  rw [firstVariationDensity_quadratic]
  simp [derivativeComponent, jet]

/-- A genuinely four-coordinate input, with two different gradient directions. -/
theorem spacetime_quadratic_mixed (x : Coordinates 4) :
    firstVariationDensity
      (quadratic (derivativeComponent (fun _ : Fin 4 => (1 : ℝ))))
      (ContinuousLinearMap.proj (0 : Fin 4) : Coordinates 4 →L[ℝ] ℝ)
      (ContinuousLinearMap.proj (1 : Fin 4) : Coordinates 4 →L[ℝ] ℝ) x = 2 := by
  rw [firstVariationDensity_quadratic]
  simp [derivativeComponent, jet]

/-- A nonzero derivative check on the real time axis. -/
theorem mechanics_quadratic_hasDerivAt (t : ℝ) :
    HasDerivAt (fun ε => density (quadratic (derivativeComponent (1 : ℝ)))
      (perturb (fun s : ℝ => s) (fun s : ℝ => s) ε) t) 2 0 := by
  simpa [derivativeComponent, jet] using
    hasDerivAt_quadratic (derivativeComponent (1 : ℝ))
      (u := fun s : ℝ => s) (η := fun s : ℝ => s) (x := t)
      (differentiableAt_id) (differentiableAt_id)

/-- A nonzero derivative check using different field and variation directions in four dimensions. -/
theorem spacetime_quadratic_hasDerivAt (x : Coordinates 4) :
    HasDerivAt (fun ε => density
      (quadratic (derivativeComponent (fun _ : Fin 4 => (1 : ℝ))))
      (perturb (ContinuousLinearMap.proj (0 : Fin 4) : Coordinates 4 →L[ℝ] ℝ)
        (ContinuousLinearMap.proj (1 : Fin 4) : Coordinates 4 →L[ℝ] ℝ) ε) x) 2 0 := by
  simpa [derivativeComponent, jet] using
    hasDerivAt_quadratic (derivativeComponent (fun _ : Fin 4 => (1 : ℝ)))
      (u := (ContinuousLinearMap.proj (0 : Fin 4) : Coordinates 4 →L[ℝ] ℝ))
      (η := (ContinuousLinearMap.proj (1 : Fin 4) : Coordinates 4 →L[ℝ] ℝ))
      (x := x) (ContinuousLinearMap.differentiableAt _) (ContinuousLinearMap.differentiableAt _)

/-- A scalar model with an explicitly base-dependent momentum. -/
noncomputable def coordinateMomentum {n : ℕ} (i : Fin n) : Lagrangian (Coordinates n) ℝ :=
  fun x j => x i * j.2 (coordinateDirection i)

/-- The divergence term gives a nonzero residual in every dimension with a
coordinate, including the time axis and a four-dimensional base. -/
theorem eulerLagrange_coordinateMomentum {n : ℕ} (i : Fin n) (u : Coordinates n → ℝ)
    (x : Coordinates n) (v : ℝ) : eulerLagrange (coordinateMomentum i) u x v = -v := by
  let M : Coordinates n →L[ℝ] (ℝ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.id ℝ ℝ)
  have hD (y : Coordinates n) : fderiv ℝ (coordinateMomentum i y) (jet u y) =
      y i • derivativeComponent (coordinateDirection i) :=
    (y i • derivativeComponent (coordinateDirection i)).hasFDerivAt.fderiv
  have hA : valueCovector (coordinateMomentum i) u x = 0 := by
    ext
    simp [valueCovector, hD, derivativeComponent]
  have hP (k : Fin n) : momentumCovector (coordinateMomentum i) u k =
      if k = i then (⇑M) else 0 := by
    funext y
    ext
    by_cases hk : k = i
    · subst k
      simp [momentumCovector, hD, M, derivativeComponent, coordinateDirection]
    · simp [momentumCovector, hD, hk, derivativeComponent, coordinateDirection, Pi.single_eq_of_ne]
  rw [eulerLagrange, hA, Finset.sum_eq_single i]
  · simp [hP, M.fderiv, M, coordinateDirection]
  · intro k _ hk
    simp [hP, hk]
  · simp

end ProjectAInos.Variational
