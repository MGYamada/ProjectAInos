# Thermodynamics Models and Counterexamples

These models test which hypotheses the entropy theorem needs and identify its abstract constructions in concrete coordinates. They preserve the diagnostic examples from the original thermodynamics blueprint and include the later sector, degenerate, and ideal-gas developments. Mathematical calculations and the exact scope of the corresponding Lean results are distinguished below.

Write $M$ for the ordered state semimodule, $V$ for its real Grothendieck completion, $P$ for the cone of accessible differences, $W=\operatorname{span}_{\mathbb R}P$, and $C=V/W$ for the conservation quotient. Exchange comparison, ECH, compares crossed sums of two accessible pairs. Sequential order closedness, SC, means that for positive $\varepsilon_j\to0$,

$$
v+\varepsilon_j w\in P\quad\text{for every }j
\quad\Longrightarrow\quad v\in P.
$$

The distinction between an entropy coordinate on $W$ and an entropy criterion within a conserved sector is explained in [the formalization notes](thermodynamics-notes.md#t02-entropy-order-requires-a-conserved-sector).

## The nonnegative real line

Let $M=\mathbb R_{\ge0}$, with ordinary addition, nonnegative scaling, and order. Taking limits proves A6, and totality proves ECH. The completed model is

$$
V\cong\mathbb R,\qquad P\cong\mathbb R_{\ge0},\qquad W=V,\qquad C=0.
$$

The unit process $e=1$ normalizes the supremum construction to $s_e(w)=w$. The normalized entropy extension is $S(x)=x$; changing the positive entropy unit gives $S(x)=ax$, $a>0$. There is no independent conserved coordinate to add.

[Models.lean](../ProjectAInos/Thermodynamics/Models.lean) proves `nnreal_stability` and `nnreal_exchangeComparison`. [ModelConnections.lean](../ProjectAInos/Thermodynamics/ModelConnections.lean) supplies the explicit linear equivalence `nnrealCompletionEquiv`, the cone criterion `nnreal_mem_processCone_iff`, `nnreal_processSpan_eq_top`, `nnreal_entropyCoordinate_eq`, and the normalized extension. `nnreal_conservation_subsingleton` expresses the vanishing conservation quotient. SC also follows from the general stability-to-cone theorem.

## Two independent monotones: A6 does not imply ECH

Take $M=\mathbb R_{\ge0}^{\,2}$ with coordinatewise order. A6 holds by taking the limit in each coordinate. The accessible pairs

$$
(0,0)\le(1,0),\qquad (0,0)\le(0,1)
$$

would force ECH to compare $(1,0)$ and $(0,1)$, which are incomparable. Thus stability alone does not reduce two independent monotones to one entropy direction.

The concrete completion and cone calculation is

$$
V\cong\mathbb R^2,\qquad P\cong\mathbb R_{\ge0}^{\,2},\qquad W=V.
$$

A real linear functional $S_{a,b}(x,y)=ax+by$ is nonnegative on this cone exactly when $a,b\ge0$: necessity follows by evaluating it on the two coordinate vectors, and sufficiency follows by adding nonnegative terms. The normalization $S_{a,b}(1,1)=1$ therefore leaves the segment

$$
a\ge0,\qquad b\ge0,\qquad a+b=1.
$$

These functionals are monotones; none supplies an order-reflecting scalar description of the coordinatewise order on all states.

The dedicated Lean results in [Models.lean](../ProjectAInos/Thermodynamics/Models.lean) are `Stability.prod`, `nnreal_prod_stability`, and `nnreal_prod_not_exchangeComparison`. SC for its abstract process cone follows from the general theorem. The displayed coordinate identification and classification of the normalized positive functionals are explanatory calculations; this model does not currently have separate named Lean theorems for those identifications or the dual segment.

## Lexicographic order: totality does not imply SC

On $V=\mathbb R^2$, define

$$
P_{\mathrm{lex}}=
\{(a,b):a>0\}\ \cup\ \{(0,b):b\ge0\}.
$$

This is a salient cone, and every vector has a nonnegative or nonpositive lexicographic sign. It fails SC. Indeed,

$$
v=(0,-1)\notin P_{\mathrm{lex}},\qquad
w=(1,0),\qquad
v+\varepsilon w=(\varepsilon,-1)\in P_{\mathrm{lex}}
\quad(\varepsilon>0).
$$

The Lean counterexample uses the explicit sequence $\varepsilon_j=1/(j+1)$. Thus a salient total cone can still fail the stability requirement needed for the real entropy representation. The vector $(0,1)$ also exhibits the familiar non-Archimedean behavior: every positive integer multiple remains lexicographically below $(1,0)$.

[ConeModels.lean](../ProjectAInos/Thermodynamics/ConeModels.lean) proves `lexicographicCone_total`, `lexicographicCone_salient`, and `lexicographicCone_not_sequentialOrderClosed`. The formal counterexample is stated at the cone level; it does not construct a physical thermal family with this order.

## Equality-only accessibility: the degenerate branch

The state space may be nontrivial while admitting no irreversible process. On $M=\mathbb R$, put

$$
x\le_M y\quad\Longleftrightarrow\quad x=y.
$$

This order is compatible with addition and nonnegative scaling. It satisfies A6, and ECH holds because each accessible pair consists of identical states. Nevertheless,

$$
P=\{0\},\qquad W=\{0\}.
$$

There is no nonzero process at which to normalize an entropy coordinate. This is a separate degenerate case, rather than a failure of stability or comparison.

[DegenerateModel.lean](../ProjectAInos/Thermodynamics/DegenerateModel.lean) proves `EqualityState.stability`, `EqualityState.exchangeComparison`, `EqualityState.processCone_eq_bot`, and `EqualityState.processSpan_eq_bot`. [ConeModels.lean](../ProjectAInos/Thermodynamics/ConeModels.lean) also proves the general `zeroCone_span` lemma.

## Entropy and one conserved amount

The sector model has $M=\mathbb R^2$, with coordinates $(s,n)$ and accessibility

$$
(s,n)\le_M(s',n')
\quad\Longleftrightarrow\quad
n=n'\ \text{ and }\ s\le s'.
$$

Here $n$ is an algebraic conserved coordinate and may have either sign. A6 follows by coordinate limits; every fixed-$n$ sector is comparable, so ECH holds. However, $(0,1)$ and $(1,2)$ are incomparable despite their ordered entropy coordinates.

Completion recovers the same real vector space, and

$$
P=\{(s,0):s\ge0\},\qquad
W=\mathbb R\times\{0\},\qquad
C\cong\mathbb R,
$$

where the quotient map is the amount coordinate. On $W$, the entropy unit $(1,0)$ gives the usual coordinate $s$. Every normalized linear extension to $V$ has exactly the form

$$
S_b(s,n)=s+bn,\qquad b\in\mathbb R.
$$

Adding $bn$ does not change entropy differences inside a fixed amount sector. It does not create accessibility between different sectors.

[SectorModel.lean](../ProjectAInos/Thermodynamics/SectorModel.lean) proves stability, ECH, and `different_amounts_incomparable`. [ModelConnections.lean](../ProjectAInos/Thermodynamics/ModelConnections.lean) proves `sector_mem_processCone_iff`, `sector_processSpan_eq_ker`, the quotient equivalence `sectorConservationEquiv`, the process-space equivalence `sectorEntropyEquiv`, and `sector_entropyCoordinate_eq`. `sectorEntropyExtension_classification` establishes existence and uniqueness of the coefficient $b$, rather than merely constructing examples of extensions.

## A populated smooth thermal family

The sector order also supports a concrete family satisfying the geometric and
thermal interfaces. [ReservoirModel.lean](../ProjectAInos/Thermodynamics/ReservoirModel.lean)
defines, for every finite work dimension $n$ and positive amount $r$,

$$
\Gamma_{n,r}=\{(U,V)\in\mathbb R\times\mathbb R^n:U>0\},\qquad
j_{n,r}(U,V)=(U,r),\qquad P(U,V)=0.
$$

Accessibility compares energy at equal amount. Its forward sectors are
halfspaces $U'\ge U$; their relative boundaries are the path-connected
hyperplanes $U'=U$. Supporting forms have the unique energy-normal kernel,
and the constant pressure field is locally Lipschitz. Energy increases give
irreversible processes. Thus these are actual nonempty `SimpleSystem`s.

Scaling by $s>0$ gives amount $sr$, with the exact scaled domain and
representation. Joining amounts $r,q$ gives amount $r+q$, total energy
$U_1+U_2$, and the concatenated work coordinates. Any positive joined energy
splits into two positive energies, and contact and splitting preserve the
represented sector state. Every pair is therefore in thermal equilibrium.
Transversality brackets $U$ by $U/2$ and $2U$ in the same thermal class.

`Reservoir.family_nontrivial` proves `ThermalFamily.Nontrivial`, meaning that
some admitted system has a nonempty domain. `Reservoir.represented_state`
exhibits the represented state $(1,1)$. The general
`ThermalFamily.nontrivial_iff_exists_isState` identifies this witness with
existence of a represented member state. Conditional comparison theorems
retain their original hypotheses; they do not require nonvacuity when it is
mathematically unnecessary.

This model checks populated scaling, joining, support geometry and thermal
equilibrium together. Its thermal relation is universal, so it exercises the
universal-isotherm branch. A varying-temperature example remains separate. The
[join assumption audit](thermodynamics-join-audit.md) records which geometric
facts are explicit inputs in a general family and proved here for reservoirs.

## Canonical atoms with genuine mixing

`AtomicProcesses`, `AtomicReservoir`, and `AtomicObstruction` implement the
canonical `AtomicDomains` realization required by issue #27. The primitive
domain is positive energy with no work coordinates. Raw states are finite
formal composites. Heating, weighted mixing, and reversible separation are
elementary processes, and accessibility is their A1–A6 closure.

`normal_form` constructs reversible equilibration of every finite composite
to one weighted atom, including the zero-amount case. `relation_iff` then
derives equality of total amount and monotonicity of total energy as the exact
accessibility criterion. The thermal family has positive amounts, arbitrary
finite work dimensions with zero pressure, positive scaling, thermal joins,
and transversality. `canonical_represent` identifies the unit primitive system
with the actual atomic presentation on its positive-energy domain.
`canonical_represent_ne` checks that the ambient extensions differ at zero
energy, where the reservoir assigns a reference atom. `exchangeComparison`
invokes the physical endpoint using domain agreement and no CH/ECH premise.

The checked regression `atomicOnly_mixing_impossible` excludes
`(1/2)[1] + (1/2)[3] → [2]` for the old atomic-only heating relation: the
extensive observable `max(U - 5/2, 0)` would decrease from `1/4` to `0`.
`mixing_example` proves this process for the new relation, while
`mixing_raw_distinct` proves its endpoints are distinct raw states and
`heating_irreversible` proves `[1] → [2]` but not the reverse. This is a
constant-temperature reservoir example, not a varying-temperature model.

## Reaction bookkeeping and unreachable labels

For the idealized reaction

$$
2\mathrm H_2+\mathrm O_2\longrightarrow2\mathrm H_2\mathrm O,
$$

order the species as $(\mathrm H_2,\mathrm O_2,\mathrm H_2\mathrm O)$. The reaction vector and the two elemental amounts are

$$
\nu=(-2,-1,2),\qquad B(t)=t\nu,
$$

$$
h(n)=2n_{\mathrm H_2}+2n_{\mathrm H_2\mathrm O},\qquad
o(n)=2n_{\mathrm O_2}+n_{\mathrm H_2\mathrm O}.
$$

Both amounts annihilate $\nu$. More strongly,

$$
\operatorname{range}B=\ker(h,o),\qquad
\mathbb R^3/\operatorname{range}B\cong\mathbb R^2.
$$

Thus the reaction span has codimension two, and every real linear conserved observable factors uniquely through the elemental amounts. These are statements about formal real composition differences. They do not assert that arbitrary signed compositions are physical states, or determine which reactions are thermodynamically accessible.

[Stoichiometry.lean](../ProjectAInos/Thermodynamics/Stoichiometry.lean) proves `conserved_iff_factors`, `waterReaction_conserved`, `waterReaction_range`, `elementAmounts_surjective`, and `waterConservationEquiv`. This verifies the conservation quotient, not the full entropy principle for a water-forming physical system. The general factorization statement is described in [the physical development](thermodynamics-physical.md#stoichiometric-conservation).

A second diagnostic model distinguishes forbidden transitions from finite reaction costs. Give each label one state of zero entropy and allow only transitions preserving the label. Its direct and chain costs are zero on the diagonal and $+\infty$ between distinct labels. If label addition is cancellative, adding the same catalyst preserves that obstruction, so the catalytic cost also remains $+\infty$. The model still satisfies absence of sinks: existing connections are reversible, while disconnected labels need not become connected. These claims are proved in [ReactionModels.lean](../ProjectAInos/Thermodynamics/ReactionModels.lean); see also [the note on infinite costs](thermodynamics-notes.md#t05-infinite-reaction-costs-distinguish-two-different-failures).

## The monatomic ideal-gas entropy formula

An equilibrium box in [IdealGas.lean](../ProjectAInos/Thermodynamics/IdealGas.lean) has strictly positive real energy $U$, volume $V$, and amount $N$. The model uses

$$
S_{k,c}(U,V,N)
=kN\left[\frac32\log\!\left(\frac UN\right)
+\log\!\left(\frac VN\right)+c\right].
$$

The logarithms are natural. The real constant $c$ selects an entropy reference; changing it adds a multiple of the conserved amount. The formula is an input to this macroscopic model, not a microscopic phase-volume derivation.

The proved properties have the following precise assumptions:

| Property | Assumptions | Lean theorem |
| --- | --- | --- |
| $S_{k,c}(tU,tV,tN)=tS_{k,c}(U,V,N)$ | $t>0$; arbitrary real $k,c$ | `entropy_scale` |
| Entropy of separate boxes adds under concatenation | Arbitrary finite lists of positive boxes | `compositeEntropy_append` |
| Concavity in all three extensive coordinates | $k\ge0$, positive input coordinates, nonnegative weights summing to one | `entropyValue_concave` |
| Strict concavity in $(U,V)$ at fixed $N$ | $k>0$, $N>0$, positive weights summing to one, and distinct positive $(U,V)$ endpoints | `entropyValue_strictConcave_fixedAmount` |

Separate-box composition uses the **sum of the box entropies**. Evaluating the formula at combined equilibrium coordinates describes a different state; concavity compares these expressions. Full strict concavity in $(U,V,N)$ is not claimed, since positive homogeneity makes the function affine along scaling rays.

## A two-step operational entropy criterion

Define the logarithmic adiabat coordinate

$$
A(U,V)=\frac32\log U+\log V.
$$

At fixed positive amount and $k>0$, entropy order is exactly the order of $A$. Equal adiabats can equivalently be written

$$
A(X)=A(Y)\quad\Longleftrightarrow\quad
U_X^3V_X^2=U_Y^3V_Y^2.
$$

The model's generating operation `Step X Y` preserves amount and permits either motion between equal-$A$ states, or constant-energy expansion with $V_X\le V_Y$. Reversible motion along adiabats and free expansion followed by equilibration are explicit operational inputs. `Accessible` is the reflexive transitive closure of these steps, not a relation defined by entropy order.

For $k>0$, `accessible_iff` proves

$$
X\mathrel{\mathrm{Accessible}}Y
\quad\Longleftrightarrow\quad
N_X=N_Y\ \text{ and }\ S_{k,c}(X)\le S_{k,c}(Y).
$$

Every generating step preserves amount and increases $A$, which proves the forward direction. For the reverse direction, the proof constructs the positive state

$$
U_Z=U_Y,\qquad
N_Z=N_X,\qquad
V_Z=\exp\!\left(A(X)-\frac32\log U_Y\right).
$$

Then $A(Z)=A(X)$, while the entropy inequality gives $V_Z\le V_Y$. Hence $X\to Z$ is an allowed reversible step and $Z\to Y$ is an allowed free-expansion step. This establishes reachability using at most two generating operations. `entropy_le_iff_adiabat_le`, `entropy_eq_iff_adiabat_eq`, `adiabat_eq_iff`, and `accessible_iff` are the corresponding public theorems in [IdealGas.lean](../ProjectAInos/Thermodynamics/IdealGas.lean).

## The ideal-gas composite consistency model

[IdealGasModel.lean](../ProjectAInos/Thermodynamics/IdealGasModel.lean) puts the operational result into an extensive algebraic model. Its states are

$$
M_{\mathrm{gas}}=\{(0,0)\}\ \cup\ \{(s,n)\in\mathbb R^2:n>0\},
$$

with addition and nonnegative scaling. The empty system is $(0,0)$; there are no nonempty states of zero amount. Entropy $s$ may be any real number. The order compares $s$ only at equal $n$, as in the sector model. A box maps to

$$
X\longmapsto (S_{k,c}(X),N_X).
$$

For $k>0$, `accessible_iff_extensive_le` proves that this map preserves and reflects the operational accessibility of individual boxes. Every $s\in\mathbb R$ occurs at every positive amount $n$: `exists_state_of_entropy_amount` chooses

$$
U=n,\qquad V=n\exp\!\left(\frac{s}{kn}-c\right),\qquad N=n.
$$

The model satisfies A6 and ECH by `extensive_stability` and `extensive_exchangeComparison`. Every formal entropy–amount vector is a difference of positive-amount states, yielding the explicit real linear equivalence

$$
\operatorname{Completion}(M_{\mathrm{gas}})\cong\mathbb R^2.
$$

Under this equivalence,

$$
P=\{(s,0):s\ge0\},\qquad
W=\{(s,0):s\in\mathbb R\},\qquad
C\cong\mathbb R.
$$

The conserved quotient is exactly amount. These are machine-checked by `extensiveCompletionEquiv`, `extensive_mem_processCone_iff`, `extensive_mem_processSpan_iff`, `extensiveAmount_ker`, and `extensiveConservationEquiv`.

This construction represents a collection of separate boxes by its total entropy and total amount. Its composite order is part of the consistency model; the single-box operational theorem verifies the embedding into that order. The development does not construct a concrete ideal-gas `ThermalFamily` satisfying every simple-system and thermal-contact axiom, or derive all multi-box processes from microscopic operations. The microscopic phase-volume calculation remains a statistical-mechanics topic in the [README research plan](../README.md).
