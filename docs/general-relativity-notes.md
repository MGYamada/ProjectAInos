# General Relativity Formalization Notes

These notes record mathematical distinctions and interface decisions in `ProjectAinos/GeneralRelativity` and in the Lorentz geometry that it uses. They complement the [research plan](cinfty-general-relativity.md) with its [ledger](cinfty-general-relativity.md#ledger), the [guide](general-relativity.md) and the [smooth-geometry notes](smooth-geometry-notes.md). Each entry distinguishes proved results from targets. Add an observation that changes an interface, or corrects an earlier judgement, as a numbered entry with a link to the proof.

## GR01. In two dimensions the differential Bianchi identity and the Einstein tensor are empty

**Observation.** The only curved metric with computed curvature is the conformal plane `exp(2x²)(−dt² + dx²)`, of dimension two. The cyclic sum `(∇_X R)(Y, Z) + (∇_Y R)(Z, X) + (∇_Z R)(X, Y)` is antisymmetric in its three vectors, because `(∇_X R)(Y, Z)` is antisymmetric in `Y` and `Z`; in dimension two it is therefore zero for every tensor with this antisymmetry, whatever the connection. In dimension two the Ricci tensor is also `(R/2) g`, so the Einstein tensor is zero: for the conformal plane `ricci_component` gives `diag(2, −2)` and `scalarCurvature_eq` gives `−4 exp(−2x²)`. A regression on this example cannot detect a wrong sign or a missing term in either statement.

**Interface decision.** The differential Bianchi identity, the Einstein tensor and the variation of the Einstein–Hilbert action are tested on a curved metric of dimension four, built from coefficients on a co-ordinate domain. The plan asked for "nonzero-curvature regressions"; the dimension is the additional requirement.

**Proof status.** The four-dimensional example is a target. [Conformal plane](../ProjectAinos/SmoothGeometry/Lorentzian/ConformalExample.lean) · [Curvature](../ProjectAinos/SmoothGeometry/Lorentzian/Curvature.lean)

## GR02. There is no integral of a density on a manifold

**Observation.** The library has the volume density of a metric on the tangent spaces (`volumeDensity`), its expression in a chart (`chartDensity`), the formula of the divergence with it (`divergence_density`), and Stokes' formula for a form with compact support on a co-ordinate space (`integral_exteriorDerivative_basis_zero`). It has integrals along curves. It has no integral of a function or a density over a manifold, and neither has the pinned Mathlib. The action of the gravitational field and the action of the Maxwell field on a curved background are such integrals.

**Interface decision.** The identities of the variation (of the inverse metric, of the density, of the connection, of the scalar curvature) are proved at each point of a manifold. The integrated statement is made first for a metric on the model space and a variation with compact support, where the integral is the Lebesgue integral of the co-ordinates and the existing Stokes formula applies as it stands; then for an open set of the model space; then for a variation supported in a chart of a manifold. The ledger row records how far the statement reaches. An integral that does not depend on the chart, with a partition of unity, is a separate construction.

**Proof status.** Targets. [Volume density](../ProjectAinos/SmoothGeometry/Lorentzian/VolumeDensity.lean) · [Density and divergence](../ProjectAinos/SmoothGeometry/Lorentzian/DensityDerivative.lean) · [Stokes with compact support](../ProjectAinos/SmoothGeometry/DifferentialForm/CompactStokes.lean)
