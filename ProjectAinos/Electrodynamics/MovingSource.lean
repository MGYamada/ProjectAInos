/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.MovingCharge
public import ProjectAinos.Electrodynamics.Electrostatics

/-!
# The field of a moving smooth charge

Landau–Lifshitz, §§36 and 38 together. The potential of a smooth charge of compact support
(`SmoothGeometry.Potential.newtonPotential`) is a static solution in the sense of
`MovingCharge.StaticSolution` on the whole of space, and the axis boost carries it to a solution
of Maxwell's equations with the moving charge as source.

* `MovingCharge.spaceLaplacian_eq_coordLaplacian`: the Laplacian of `MovingCharge.lean` is the
  co-ordinate Laplacian of `Potential/Laplacian.lean`.
* `MovingCharge.newtonSolution`: the Newton potential of a `C²` density `ρ` of compact support,
  with `−Δφ = ρ` on all of space.
* `MovingCharge.maxwell_movingNewton`: the boosted Newton potential solves Maxwell's equations
  everywhere, with the density `γρ` at the comoving position and the current `γρ V e₁`.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace ProjectAinos.Electrodynamics.MovingCharge

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Potential SpecialRelativity

/-- The Laplacian `Σᵢ ∂ᵢ∂ᵢ f` of `MovingCharge.lean` is the co-ordinate Laplacian. -/
theorem spaceLaplacian_eq_coordLaplacian (f : Space 3 → ℝ) (p : Space 3) :
    spaceLaplacian f p = coordLaplacian f p := rfl

/-- **The Newton potential is a static solution**: for a `C²` density `ρ` of compact support,
`φ(x) = ∫ ρ(y)/(4π|x − y|) dy` solves `−Δφ = ρ` on the whole of space. -/
def newtonSolution (ρ : Space 3 → ℝ) (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) :
    StaticSolution where
  domain := univ
  isOpen_domain := isOpen_univ
  potential := newtonPotential ρ
  density := ρ
  contDiffOn_potential := (contDiff_two_newtonPotential hcρ hρ).contDiffOn
  poisson p _ := by
    rw [spaceLaplacian_eq_coordLaplacian,
      coordLaplacian_eq_laplacian (contDiff_two_newtonPotential hcρ hρ).contDiffAt]
    exact Electrostatics.neg_laplacian_newtonPotential hcρ hρ p

/-- **The field of a moving smooth charge**: the Newton potential boosted with the velocity `V`
solves Maxwell's equations on the whole of space-time, with the density `γρ` and the current
`γρ V e₁` at the comoving position. -/
theorem maxwell_movingNewton (V : ℝ) (hV : |V| < 1) (ρ : Space 3 → ℝ)
    (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (y : Spacetime) :
    (divergence3 (magneticField (fieldTensor (movingScalar V hV (newtonPotential ρ)))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (movingScalar V hV (newtonPotential ρ))) i) 0 y +
        curl (electricField (fieldTensor (movingScalar V hV (newtonPotential ρ)))) y i = 0) ∧
    divergence3 (electricField (fieldTensor (movingScalar V hV (newtonPotential ρ)))) y =
      (axisVelocity V hV).gamma * ρ (comovingPosition V hV y) ∧
    ∀ i, curl (magneticField (fieldTensor (movingScalar V hV (newtonPotential ρ)))) y i -
        partialAt (electricField (fieldTensor (movingScalar V hV (newtonPotential ρ))) i) 0 y =
      (axisVelocity V hV).gamma * ρ (comovingPosition V hV y) * ![V, 0, 0] i :=
  maxwell_movingScalar V hV (newtonSolution ρ hcρ hρ) (mem_univ _)

end ProjectAinos.Electrodynamics.MovingCharge
