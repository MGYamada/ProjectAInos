# Physical comparison and reaction entropy

The Lean library derives comparison in finite products of simple systems from
explicit accessibility, geometric, and thermal premises. It then constructs
additive extensive entropy, with a complete accessibility criterion within
each primitive composition label. For mixing and reactions, absence of sinks
allows compatible additive constants to be chosen so that entropy is monotone
for every accessible process.

This document describes the implemented physical and reaction arguments. The
[algebraic development](thermodynamics-algebra.md) covers cancellation,
completion, the process cone, exchange comparison, and the conservation
quotient. The [implementation checklist](thermodynamics-status.md) maps the
whole development to modules; the [formalization notes](thermodynamics-notes.md)
record distinctions that matter when reading the assumptions. The physical
reference is [Lieb–Yngvason, Sections III, IV, and VI](https://arxiv.org/html/cond-mat/9708200v2).

## States, composition, and the two quotients

Write $x\preceq y$ for adiabatic accessibility,
$x\sim_A y$ for accessibility in both directions, and
$x\prec\!\prec y$ for accessibility without the reverse process. Addition
$x+y$ denotes a composite state; $r x$, for $r\geq0$, denotes an
extensively scaled state. The empty system is denoted by $0$.

[Physical.lean](../ProjectAInos/Thermodynamics/Physical.lean) starts with finite
syntax `Composite`: atoms, the empty expression, composition, and nonnegative
scaling. `StructuralEquiv` identifies reassociation, permutation, empty units,
and the scaling coherence laws

$$
1x=x,\qquad r(sx)=(rs)x,\qquad r(x+y)=rx+ry,
\qquad r0=0,\qquad 0x=0.
$$

The structural quotient `CompositeState` has an additive commutative monoid
and a distributive multiplicative action of nonnegative reals. It does **not**
identify $(r+s)x$ with $rx+sx$. The latter is a physical splitting claim.
Consequently the raw state type is not assumed to be a semimodule.

For an accessibility relation `P`, the second quotient
`P.StateSpace` identifies $x\sim_A y$. Splitting supplies scalar-addition
distributivity on these classes, giving an ordered nonnegative-real
semimodule. Stability supplies cancellation, and the real completion and
process cone can then be constructed. Structural equality, adiabatic
equivalence, and thermal equilibrium remain three different notions.

`AtomicDomains` in [AtomicSystems.lean](../ProjectAInos/Thermodynamics/AtomicSystems.lean)
provides a canonical presentation. For primitive system names $g$, first
choose a dimension $n_g$ and a coordinate domain
$\Gamma_g\subseteq\mathbb R\times\mathbb R^{n_g}$. Its atoms are actual
domain points, and

$$
\mathrm{Raw}=\operatorname{CompositeState}
  \left(\coprod_g\Gamma_g\right),\qquad
\ell(x)\in\bigoplus_g\mathbb R_{\geq0}
$$

records the amount of each primitive system. `label_atom` gives one unit of
the corresponding label, and `label_scale` proves extensivity. Domain and
representation equality with an admitted `SimpleSystem` give an equivalence
chart covering its entire domain; `simpleSystem_label` proves the full-domain
label law. Defining the coordinate domains first avoids a recursive atom type
depending on its own accessibility structure. These data construct the
presentation, not the physical axioms of its accessibility relation.

## Accessibility and simple-system assumptions

`Accessibility` in [Physical.lean](../ProjectAInos/Thermodynamics/Physical.lean)
contains the following premises on raw states.

| Premise | Mathematical content |
| --- | --- |
| A1: reflexivity | $x\preceq x$ |
| A2: transitivity | $x\preceq y\preceq z\Rightarrow x\preceq z$ |
| A3: composition | $x\preceq y$ and $z\preceq w\Rightarrow x+z\preceq y+w$ |
| A4: scaling | $x\preceq y\Rightarrow rx\preceq ry$ for $r>0$ |
| A5: splitting | $(a+b)x\sim_A ax+bx$ for $a,b\geq0$ |
| A6: stability | If $\varepsilon_k>0$, $\varepsilon_k\to0$, and $x+\varepsilon_kz_0\preceq y+\varepsilon_kz_1$ for every $k$, then $x\preceq y$ |

A4 is stored also at zero, where reflexivity and the empty-system convention
give the result. `splitting_of_normalized` derives the homogeneous A5 form
from $x\sim_A tx+(1-t)x$, $0<t<1$, together with scaling and the empty
identities. No negative physical amounts are introduced.

A `SimpleSystem` has an open convex domain
$\Gamma\subseteq\mathbb R\times(\operatorname{Fin}n\to\mathbb R)$, an
ambient representation $j$ into raw states, and the following additional
premises. Only values of $j$ on the domain have physical significance.
The implementation also permits $n=0$.

**A7: convex mixing.** For $x,y\in\Gamma$, $a,b\geq0$, and $a+b=1$,

$$
a\,j(x)+b\,j(y)\preceq j(ax+by).
$$

The left side is a composite of scaled physical states; the right side is
the represented coordinate convex combination. Define

$$
A_x=\{y\in\Gamma:j(x)\preceq j(y)\}.
$$

**S1: irreversibility.** Every $x\in\Gamma$ has a $y\in\Gamma$ with
$j(x)\prec\!\prec j(y)$.

**S2: finite-slope unique support and regularity.** There is a pressure field
$P:\Gamma\to\mathbb R^n$, locally Lipschitz on the domain. At each $x$,
the nonzero normalized form

$$
f_x(\delta U,\delta V)=\delta U+\sum_iP_i(x)\delta V_i
$$

or its negative supports $A_x$ at $x$. Every supporting form there has
the same kernel as $f_x$. This asserts uniqueness of the hyperplane, not
equality of arbitrary normal vectors, and does not choose the supporting side.

**S3: boundary path-connectedness.** The set
$\Gamma\cap\operatorname{frontier}(A_x)$ is path-connected. This is the
boundary relative to the open physical domain; the exterior boundary of
$\Gamma$ is excluded. The source states S3 as arcwise connectedness;
mere connectedness, as in the earlier outline's abbreviated wording, is not
the declared premise. [Lieb–Yngvason, Section III, S3](https://arxiv.org/html/cond-mat/9708200v2)

These fields are defined in
[SimpleSystem.lean](../ProjectAInos/Thermodynamics/SimpleSystem.lean).
S1 is kept explicit for the geometric development, although T4 below supplies
irreversible successors in the full thermal family.

## Thermal assumptions and positive scaling

A `ThermalFamily` selects admitted simple systems and is closed under positive
scaling and thermal joining. Scaled systems have the scaled coordinate domain
and the corresponding extensive representation. A join has one energy
coordinate and the concatenated work coordinates. Its domain is exactly

$$
\Delta_{12}=\{(U,V_1,V_2):
  \exists U_1,U_2,\ U=U_1+U_2,
  \ (U_i,V_i)\in\Gamma_i\}.
$$

The following premises are encoded by `ThermalJoin`, `SimpleThermalJoin`, and
`ThermalFamily` in
[PhysicalComparison.lean](../ProjectAInos/Thermodynamics/PhysicalComparison.lean)
and [ThermalFamily.lean](../ProjectAInos/Thermodynamics/ThermalFamily.lean).

- **T1: contact.** The join is an admitted simple system, and
  $j_1(U_1,V_1)+j_2(U_2,V_2)\preceq j_{12}(U_1+U_2,V_1,V_2)$.
- **T2: splitting.** Every joined point has a reverse-accessible split
  preserving its total energy and both work coordinates. Contact supplies the
  other direction. The proportional-copy clause is also retained: for an
  admitted state $x$ and $0<t<1$, $(1-t)x\sim_T tx$.
- **Thermal equilibrium.** For represented member states, $x\sim_T y$
  means that their contact is reversible. Symmetry of unordered contact is
  explicit in the interface.
- **T3: zeroth law.** Thermal equilibrium is transitive on represented member
  states.
- **T4: transversality.** For every member state $x$, there are states
  $a,b$ of that same system with
  $a\sim_T b$ and $a\prec\!\prec x\prec\!\prec b$.

The thermal relation is not required on arbitrary raw composites. In
particular, zero-scale endpoints are handled by A5, not by declaring the empty
system thermally equivalent to every state. Extending the proportional-copy
thermal premise to $t=0$ on the raw type would collapse all represented
thermal classes through $0$.

`ThermalFamily.self_scale` and `scale_iff` prove

$$
x\sim_T y\quad\Longleftrightarrow\quad rx\sim_T sy
\qquad(r,s>0).
$$

`ThermalFamily.common_energy_orientation` in
[ThermalOrientation.lean](../ProjectAInos/Thermodynamics/ThermalOrientation.lean)
proves that all admitted states have the same energy orientation. Opposite
orientations would let an equilibrium contact move both ways in energy at
fixed work coordinates, contradicting the simple join's geometric order.

## From geometry to product comparison

### One simple system

A7 makes forward sectors convex. A6, cancellation, and a collinear
accessibility argument give relative closedness
(`Accessibility.forwardSector_isClosed_relative` in
[ForwardSector.lean](../ProjectAInos/Thermodynamics/ForwardSector.lean)). S1 and
unique finite-slope support imply that each sector has nonempty ambient
interior (`SimpleSystem.forwardSector_interior_nonempty`).

Support at a relative-boundary point is inherited by its own forward sector.
Uniqueness identifies the supporting plane there. The boundary is a graph
$U=u_x(V)$ over an open path-connected work domain; locally it is convex in
the positive orientation and has derivative

$$
Du_x(V)[h]=-\sum_iP_i(u_x(V),V)h_i.
$$

[BoundaryGraph.lean](../ProjectAInos/Thermodynamics/BoundaryGraph.lean) proves
the graph and regularity statements;
`boundaryEnergy_hasFDerivAt` and `boundaryDerivative_locallyLipschitzOn` in
[BoundaryDifferentiability.lean](../ProjectAInos/Thermodynamics/BoundaryDifferentiability.lean)
prove the differential equation and its regularity. Grönwall uniqueness in
[AdiabatUniqueness.lean](../ProjectAInos/Thermodynamics/AdiabatUniqueness.lean)
gives local coincidence of boundary graphs. S3 propagates this to boundary
reversibility, and convex segment crossing gives comparison.

The final results in
[SimpleComparison.lean](../ProjectAInos/Thermodynamics/SimpleComparison.lean)
include `comparison`, `mem_boundary_iff_equivalent`, `sectors_nested`, and
`strict_strips_open`. Energy reflection preserves the premises, so these
results do not assume a preferred orientation.

### One entropy line and its thermal classes

T4 supplies strict thermal reference pairs around every state. Contact with
scaled copies makes each state in the corresponding strip comparable with
every reference mixture. Algebraic cuts give an affine coordinate locally;
connectedness and variation in every neighborhood make these local lines one
line in the completed state space. For a strict pair $x_0,x_1$,

$$
\iota j(x)-\iota j(x_0)
 =s(x)\bigl(\iota j(x_1)-\iota j(x_0)\bigr),
\qquad s(x_0)=0,\quad s(x_1)=1.
$$

Here $\iota$ includes both the adiabatic quotient and its real completion.
`exists_coordinate_of_local_intervals` in
[ThermalStrips.lean](../ProjectAInos/Thermodynamics/ThermalStrips.lean) proves
this representation. In
[SimpleEntropy.lean](../ProjectAInos/Thermodynamics/SimpleEntropy.lean),
`referenceEntropy_relation_iff` characterizes the simple-system order, while
`referenceEntropy_concave` and `referenceEntropy_continuousOn` establish
concavity and continuity. Additivity in the completion already compares
finite products of copies of this one system.

For two copies with fixed total energy and work coordinates, equilibrium is
equivalent to maximizing their entropy sum. Concavity gives a supporting-slope
interval at every interior energy,

$$
\partial^+s(U)=[s'_+(U),s'_-(U)].
$$

The two copies are in thermal equilibrium exactly when these intervals
intersect. This requires neither differentiability of entropy nor a
single-valued temperature. See `equilibrium_iff_referenceEntropy_maximum`,
[SupportingSlopes.lean](../ProjectAInos/Thermodynamics/SupportingSlopes.lean),
and `ThermalFamily.thermal_iff_entropySlopes_inter` in
[ThermalSlopes.lean](../ProjectAInos/Thermodynamics/ThermalSlopes.lean).

The zeroth law and T4 then yield `isotherm_dichotomy`: either the whole simple
system is one thermal class, or one adiabat contains two states that are not
thermally equivalent. The proof uses interval-class ordering and connectedness
in [ThermalClassOrder.lean](../ProjectAInos/Thermodynamics/ThermalClassOrder.lean)
and [ThermalClasses.lean](../ProjectAInos/Thermodynamics/ThermalClasses.lean).

### Calibrators between different systems

A calibrator consists of strict pairs $x_0\prec\!\prec x_1$ and
$y_0\prec\!\prec y_1$ with

$$
x_0+y_1\sim_A x_1+y_0.
$$

Thus their nonzero positive completed differences coincide. The proof of
`ThermalFamily.hasCalibrators_of_axioms` handles both alternatives of the
thermal-class dichotomy:

1. Joined states are proved thermally equivalent to their equilibrium split
   components. The proof splits an iterated join, averages the two copies of
   one component using A7, and closes the accessibility cycle using positive
   thermal scaling. `join_thermal_left`, `join_thermal_right`, and
   `exists_coherent_split` in
   [ThermalJoinCoherence.lean](../ProjectAInos/Thermodynamics/ThermalJoinCoherence.lean)
   establish this without transporting thermal equilibrium across arbitrary
   adiabatic equivalences.
2. Assuming no calibrator, equivalent joined states have adiabatically
   equivalent split components. Graph uniqueness and propagation over the
   joined work domain make each joined adiabat a thermal class. The dichotomy
   therefore makes the whole join one thermal class. This is
   `joined_all_thermal_of_no_calibrator` in
   [UniqueThermalSplit.lean](../ProjectAInos/Thermodynamics/UniqueThermalSplit.lean).
3. A universal joined class gives component classes meeting every nonempty
   work fiber. Such a class cannot be confined to one adiabat: T4 gives
   thermal states straddling it, and the supporting slopes on their two work
   fibers force those states into the same class, a contradiction. Both
   component classes therefore contain strict reference pairs; all their
   cross pairs are in equilibrium. See
   [UniversalThermalClass.lean](../ProjectAInos/Thermodynamics/UniversalThermalClass.lean).
4. Three cross-equilibrium pairs put both component differences on the one
   joined entropy line. Positivity fixes the sign of their scalar ratio;
   continuity along actual coordinate segments realizes equal differences
   and hence a calibrator. This is proved in
   [CalibratorDirections.lean](../ProjectAInos/Thermodynamics/CalibratorDirections.lean)
   and [UniversalJoinCalibration.lean](../ProjectAInos/Thermodynamics/UniversalJoinCalibration.lean).

The endpoint is in
[HasCalibratorsOfAxioms.lean](../ProjectAInos/Thermodynamics/HasCalibratorsOfAxioms.lean).
Neither uniqueness nor continuity of a chosen thermal splitting is assumed.

Calibrators align the entropy lines of different systems with one positive
direction. Consequently `ThermalFamily.product_comparison` compares all
states of any finite scaled product. Empty products and zero weights are
included. The theorem in
[PhysicalEntropyPrinciple.lean](../ProjectAInos/Thermodynamics/PhysicalEntropyPrinciple.lean)
takes no CH, ECH, or calibrator-existence premise; those are conclusions of the
physical assumptions above.

## Composition sectors and the ECH bridge

Product comparison alone does not make all raw states comparable. Primitive
composition labels specify which products should be compared.
`Nonreactive.compositionLabel` is additive and extensive. In
[Nonreactive.lean](../ProjectAInos/Thermodynamics/Nonreactive.lean),
`Generated` closes elementary transformations under A1–A6;
`Generated.label_eq` proves that label conservation survives this closure,
including its stability rule. For elementary changes within a primitive
system, `accessibility_label_eq` supplies the conservation result.

Equal-label raw composites admit a common scaled-product realization. For
positive amounts $a_i,b_j$ of a fixed primitive type with total $M$, use
the refinement weights

$$
c_{ij}=\frac{a_i b_j}{M},\qquad
\sum_jc_{ij}=a_i,\qquad\sum_ic_{ij}=b_j.
$$

Weights between distinct primitive types are zero. Splitting and recombination
identify each original composite adiabatically with its refined product.
Zero terms are removed or handled by the empty identity.
`common_product_of_equal_label` in
[CommonProducts.lean](../ProjectAInos/Thermodynamics/CommonProducts.lean)
constructs these witnesses; common realization is not an additional physical
assumption.

If accessibility preserves labels, the cross sums associated with two
accessible processes have the same label. Common realization and product CH
compare those cross sums, giving exchange comparison on `P.StateSpace`.
`exchangeComparison_of_physical_axioms` exposes this result with label
conservation explicit. It connects the physical proof to the algebraic ECH
criterion and entropy theorem.

There is also a direct calibrated entropy construction. For nonempty
primitive systems, `exists_entropy_of_physical_axioms` returns an additive
extensive function $S_0$ with

$$
\ell(x)=\ell(y)
\quad\Longrightarrow\quad
\bigl(x\preceq y\ \Longleftrightarrow\ S_0(x)\leq S_0(y)\bigr).
$$

This criterion can still be used when reactions allow transitions between
different labels. It does not assert monotonicity of this initial choice
$S_0$ across different labels. The canonical `AtomicDomains` endpoints
derive the chart and label bookkeeping from coordinate atoms; the more
general `ThermalFamily` endpoints accept a matching atomic chart explicitly.

## Mixing and reactions: extended costs

With reactions, different labels may be connected by accessible processes.
ECH on the whole reaction-extended order need not follow, and the process
span need not be one-dimensional. The construction therefore starts with the
already calibrated equal-label entropy $S_0$ and adjusts its additive
constants.

Let $\Lambda$ be the additive monoid of composition labels, and let
$\mathrm{State}(a)=\{x:\ell(x)=a\}$. The three costs in
[Reactions.lean](../ProjectAInos/Thermodynamics/Reactions.lean) are

$$
\begin{aligned}
D(a,b)&=\inf\{S_0(y)-S_0(x):\ell(x)=a,\ \ell(y)=b,\ x\preceq y\},\\
E(a,b)&=\inf\left\{\sum_{i=0}^{k-1}D(a_i,a_{i+1}):
  a_0=a,\ a_k=b,\ D(a_i,a_{i+1})<+\infty\right\},\\
F(a,b)&=\inf_{z\in\Lambda}E(a+z,b+z).
\end{aligned}
$$

Their Lean names are `directCost`, `chainCost`, and `catalystCost`. An empty
chain from a label to itself has cost zero. A chain joins labels, not
necessarily the very same intermediate states: witnesses on consecutive
edges may have different states with the same label. The ancillary label
$z$ is common to both ends, but its input and output states need not be
identical. This is distinct from cancellation of an unchanged spectator
state.

All three costs initially take values in `EReal`:

- $+\infty$ means that there is no available transformation or allowed
  chain in the relevant definition.
- $-\infty$ permits an infimum of available real entropy changes to be
  unbounded below. It must not be confused with unreachability.

`directCost_lt_top_iff` identifies finite-above direct cost with an actual
transition. `CostChain` requires each edge to be less than $+\infty$,
still allowing $-\infty$ at this stage. Because extended-real addition
can combine the two infinities nonclassically, early subadditivity lemmas
state the required finite-above or no-negative-infinity hypotheses.

Composition, positive scaling, and cycle consistency give the cost laws.
For example, adding a common ancillary system cannot raise direct cost;
the catalytic cost is invariant under adding a common label. Positive
homogeneity and composition subadditivity hold in the final physical cost
model, as do the chain and catalytic triangle inequalities.

Cycle consistency is proved, not assumed by the final physical endpoint.
Parallel composition aggregates a finite cycle of actual transitions into
one equal-label process. Additivity of $S_0$ and its equal-label criterion
force a nonnegative total entropy change. Approximation from above then
passes this to chains of infimum costs.
`ActualCostChain.aggregate`, `ActualCostChain.cycle_nonneg`, and
`calibratedDirectCost_cycle_nonneg` in
[ReactionCycles.lean](../ProjectAInos/Thermodynamics/ReactionCycles.lean)
implement the argument. In particular, the physical costs satisfy
$E(a,a)=F(a,a)=0$.

## Absence of sinks and Hahn–Banach constants

**M: absence of sinks.** If there is a finite chain of actual transitions
from $a+z$ to $b+z$ for some ancillary label $z$, there is a finite
chain from $b+w$ to $a+w$ for some ancillary label $w$.

`RawNoSinks` in
[ReactionCalibration.lean](../ProjectAInos/Thermodynamics/ReactionCalibration.lean)
states this solely through the raw accessibility relation and labels, before
choosing costs or entropy constants. It does not demand a single-step reverse
reaction, microscopic reversibility, or restoration of the same ancillary
state. `calibrated_connected_iff_actual` in
[PhysicalReactions.lean](../ProjectAInos/Thermodynamics/PhysicalReactions.lean)
identifies this actual connectivity with $F(a,b)<+\infty$.

Cycles and M exclude $-\infty$: an arbitrarily negative cost followed by
a finite-above returning chain would contradict the zero self-cost. Costs
between disconnected labels remain $+\infty$. The equality-only example
in [ReactionModels.lean](../ProjectAInos/Thermodynamics/ReactionModels.lean)
checks that adjoining ancillary labels does not erase such unreachability.

Catalytic invariance makes $F$ descend to the real completion of the label
monoid. Write

$$
\widehat F(\iota a-\iota b)=F(a,b).
$$

`completedCost` proves this descent, including independence of the formal
difference representative. This completion concerns **system labels**, not
the thermodynamic process span. With M, the set

$$
H=\{v:\widehat F(v)<+\infty\}
$$

is a real linear subspace: no sinks supplies closure under negation. On
$H$, the cost is finite, positively homogeneous, and subadditive.
`CostLaws.finiteDomain` and `finiteCost` express this restriction.

`CostLaws.exists_linear_bound` applies algebraic Hahn–Banach to the real
sublinear cost on $H$, then extends the resulting linear functional to the
whole label completion. Outside $H$, the upper bound is $+\infty$, so
the arbitrary extension still obeys the bounds. The result is

$$
-\widehat F(-v)\leq L(v)\leq\widehat F(v).
$$

Putting $B(a)=L(\iota a)$ gives additive extensive constants satisfying

$$
\boxed{-F(b,a)\leq B(a)-B(b)\leq F(a,b).}
$$

An actual transition has
$F(a,b)\leq D(a,b)\leq S_0(y)-S_0(x)$. Therefore

$$
S(x):=S_0(x)+B(\ell(x))
\quad\text{satisfies}\quad
x\preceq y\Longrightarrow S(x)\leq S(y).
$$

`ThermalFamily.exists_weak_entropy_of_physical_axioms` in
[PhysicalEntropyPrinciple.lean](../ProjectAInos/Thermodynamics/PhysicalEntropyPrinciple.lean)
derives the calibrated $S_0$, all required physical cost laws, and the
corrected $S$. The canonical atomic version is
`AtomicDomains.exists_weak_entropy`. Both entropies are additive and
extensive; the corrected entropy is monotone for every accessible process.
Since the correction cancels when labels agree, it also retains the complete
equal-label criterion. A global converse across different labels, or strict
entropy increase for every irreversible reaction, is not asserted.

## Stoichiometric conservation

For a linear reaction map $N:\mathbb R^r\to\mathbb R^m$, the columns of
$N$ specify composition changes. A linear observable $q$ is conserved
exactly when $q\circ N=0$; equivalently it factors uniquely through
$\mathbb R^m/\operatorname{range}N$. For scalar observables this is the
usual annihilator, represented in coordinates by $\ker N^{\mathsf T}$.
`Stoichiometry.conserved_iff_factors` proves the universal factorization
criterion in [Stoichiometry.lean](../ProjectAInos/Thermodynamics/Stoichiometry.lean).

For species ordered as $(\mathrm H_2,\mathrm O_2,\mathrm H_2\mathrm O)$,
the water reaction direction is $(-2,-1,2)$. The elemental-amount map is

$$
q(h,o,w)=(2h+2w,\ 2o+w).
$$

`waterReaction_range` proves that its kernel is exactly the span of that
reaction, and `waterConservationEquiv` identifies the composition quotient
with $\mathbb R^2$. These are statements about formal linear composition
space. They do not identify the full thermodynamic conservation quotient
with the stoichiometric quotient without a model showing that accessibility
generates exactly those reaction directions. Nor does formal surjectivity
assert physical realizability of negative species amounts.

## Scope and entry points

| Public API | Assumptions and conclusion |
| --- | --- |
| `ThermalFamily.product_comparison` | Admitted simple systems; comparison on every finite scaled product |
| `ThermalFamily.exchangeComparison_of_physical_axioms` | Matching atomic presentation and preserved labels; ECH on adiabatic classes |
| `ThermalFamily.exists_entropy_of_physical_axioms` | Nonempty primitive domains and matching atomic presentation; additive extensive entropy with the equal-label criterion |
| `ThermalFamily.exists_weak_entropy_of_physical_axioms` | The preceding physical calibration data, represented label fibers, and `RawNoSinks`; corrected entropy monotone for all processes |
| `AtomicDomains.exchangeComparison`, `.exists_calibrated_entropy`, `.exists_weak_entropy` | Canonical coordinate atoms supply the chart and full-domain label laws |

All admitted simple systems used in the comparison proof, including the
necessary scaled systems and joins, satisfy the stated geometric and thermal
premises. These hypotheses remain explicit; they are not inferred from bare
coordinate domains. The final endpoints do not take CH, ECH, calibrator
existence, or a preselected globally monotone reaction entropy as inputs.

T5 asserts that every thermal class of one system can be matched at every
admissible work coordinate of another. It is outside the implemented
assumption interface and is unnecessary for the present T4-based product
entropy theorem. Extension to systems without T4, differentiability and
regularity of temperature, and third-law or absolute-zero normalization are
not established here. Supporting entropy-slope intervals are not a proof of
a unique thermodynamic temperature. The later low-temperature assumptions
would also be needed to select additional entropy normalizations.

The constructions use classical choice, quotients, real infima, and algebraic
Hahn–Banach. They are machine-checked existence proofs, not algorithms for
computing reaction costs or choosing entropy constants from experimental
data. Verification and the permitted transitive axioms are documented in the
[implementation checklist](thermodynamics-status.md#verification).
