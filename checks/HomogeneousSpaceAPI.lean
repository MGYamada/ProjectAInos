/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFrame
import ProjectAinos.GeneralRelativity.StructureConstants
import ProjectAinos.GeneralRelativity.HomogeneousSpace
import ProjectAinos.GeneralRelativity.BianchiClassA
import ProjectAinos.GeneralRelativity.BianchiFrames
import ProjectAinos.GeneralRelativity.BianchiExamples

/-! Public consumers of homogeneous cosmology (Landau–Lifshitz §116): orthonormal frames of a
coordinate metric built from their components, with their brackets, commutator coefficients and
Ricci tensor; the structure constants of three-dimensional Lie algebras, their Bianchi
decomposition, the Jacobi identity and the canonical Bianchi types; the homogeneous metric of an
invariant frame and a triad, with the reduction of the vacuum and perfect-fluid Einstein equations
to ordinary differential equations; the diagonal models of class A; the invariant frames of the
types I, II, V and IX; and the Kasner metric as a type I model. Default elaborator options are
intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section

section CoordinateFrame

open Bundle VectorField Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)}

local notation "E" => MinkowskiModel d

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

example (ξ η : MinkowskiModel d → MinkowskiModel d) (y : MinkowskiModel d) :
    MinkowskiModel d :=
  lieBracketOf ξ η y

example {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U) (x₀ y : U) :
    ContMDiffAt I ((I).prod I) ∞ (T% (vectorFieldOf x₀ ξ)) y :=
  contMDiffAt_vectorFieldOf hξ x₀ y

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : MinkowskiModel d → F}
    (hφ : ContDiffOn ℝ ∞ φ U) (x₀ y : U) (ξ : MinkowskiModel d → MinkowskiModel d) :
    mvfderiv I (fun z : U => φ z) y (vectorFieldOf x₀ ξ y) = fderiv ℝ φ y (ξ y) :=
  mvfderiv_vectorFieldOf hφ x₀ y ξ

example {ξ η : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U)
    (hη : ContDiffOn ℝ ∞ η U) (x₀ y : U) :
    mlieBracket I (vectorFieldOf x₀ ξ) (vectorFieldOf x₀ η) y =
      vectorFieldOf x₀ (lieBracketOf ξ η) y :=
  mlieBracket_vectorFieldOf hξ hη x₀ y

example (g : CoordinateMetric σ d U) (x₀ : U)
    (ξ : Fin (d + 1) → MinkowskiModel d → MinkowskiModel d) (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) U)
    (horth : ∀ y ∈ U, ∀ a b, g.form y (ξ a y) (ξ b y) = if a = b then lorentzSign σ a else 0) :
    g.toLorentzMetric.OrthonormalFrame (univ : Set U) :=
  orthonormalFrameOf g x₀ ξ hξ horth

variable (g : CoordinateMetric σ d U) (x₀ : U)
  {ξ : Fin (d + 1) → MinkowskiModel d → MinkowskiModel d} (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) U)
  (horth : ∀ y ∈ U, ∀ a b, g.form y (ξ a y) (ξ b y) = if a = b then lorentzSign σ a else 0)

example (a : Fin (d + 1)) :
    (orthonormalFrameOf g x₀ ξ hξ horth).field a = vectorFieldOf x₀ (ξ a) :=
  field_orthonormalFrameOf g x₀ hξ horth a

example (a b c : Fin (d + 1)) (y : U) :
    (orthonormalFrameOf g x₀ ξ hξ horth).commutator a b c y =
      g.form y (ξ a y) (lieBracketOf (ξ b) (ξ c) y) :=
  commutator_orthonormalFrameOf g x₀ hξ horth a b c y

example (Λ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → MinkowskiModel d → ℝ) (a b c : Fin (d + 1))
    (z : MinkowskiModel d) :
    ℝ :=
  rotationOf Λ a b c z

example (Λ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → MinkowskiModel d → ℝ)
    (ξ : Fin (d + 1) → MinkowskiModel d → MinkowskiModel d) (z : MinkowskiModel d)
    (b k : Fin (d + 1)) :
    ℝ :=
  ricciOfFrame σ Λ ξ z b k

example {Λ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → MinkowskiModel d → ℝ}
    (hcomm : ∀ z ∈ U, ∀ a b c, g.form z (ξ a z) (lieBracketOf (ξ b) (ξ c) z) = Λ a b c z)
    (a b c : Fin (d + 1)) :
    (orthonormalFrameOf g x₀ ξ hξ horth).rotation a b c =
      fun z : U => rotationOf Λ a b c z :=
  rotation_orthonormalFrameOf g x₀ hξ horth hcomm a b c

example {Λ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → MinkowskiModel d → ℝ}
    (hΛ : ∀ a b c, ContDiffOn ℝ ∞ (Λ a b c) U)
    (hcomm : ∀ z ∈ U, ∀ a b c, g.form z (ξ a z) (lieBracketOf (ξ b) (ξ c) z) = Λ a b c z) (y : U)
    (b k : Fin (d + 1)) :
    g.toLorentzMetric.ricci y ((orthonormalFrameOf g x₀ ξ hξ horth).field b y)
        ((orthonormalFrameOf g x₀ ξ hξ horth).field k y) =
      ricciOfFrame σ Λ ξ y b k :=
  ricci_orthonormalFrameOf g x₀ hξ horth hΛ hcomm y b k

example :
    (∀ y : U, g.toLorentzMetric.ricci y = 0) ↔
      ∀ y : U, ∀ b k, g.toLorentzMetric.ricci y
        ((orthonormalFrameOf g x₀ ξ hξ horth).field b y)
        ((orthonormalFrameOf g x₀ ξ hξ horth).field k y) = 0 :=
  ricci_eq_zero_iff_frame g x₀ hξ horth

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end CoordinateFrame

section StructureConstants

namespace ProjectAinos.GeneralRelativity.StructureConstants

open Matrix

example :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  levi

example :
    levi 0 1 2 = 1 :=
  levi_zero_one_two

example (a b c : Fin 3) :
    levi b a c = -levi a b c :=
  levi_swap_left a b c

example (a b c : Fin 3) :
    levi a c b = -levi a b c :=
  levi_swap_right a b c

example (a b c : Fin 3) :
    levi b c a = levi a b c :=
  levi_cycle a b c

example (C : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    Prop :=
  IsAntisymm C

example (C : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    Prop :=
  Jacobi C

example (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  ofBianchi n a

example (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    IsAntisymm (ofBianchi n a) :=
  isAntisymm_ofBianchi n a

example (C : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  bianchiA C

example (C : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  dualMatrix C

example (C : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  bianchiN C

example (C : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    (bianchiN C).IsSymm :=
  bianchiN_isSymm C

example (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    dualMatrix (ofBianchi n a) = n + Matrix.of fun e c => ∑ d, levi e d c * a d :=
  dualMatrix_ofBianchi n a

example {n : Matrix (Fin 3) (Fin 3) ℝ} (hn : n.IsSymm) (a : Fin 3 → ℝ) :
    bianchiN (ofBianchi n a) = n :=
  bianchiN_ofBianchi hn a

example {n : Matrix (Fin 3) (Fin 3) ℝ} (hn : n.IsSymm) (a : Fin 3 → ℝ) :
    bianchiA (ofBianchi n a) = a :=
  bianchiA_ofBianchi hn a

example {C : Fin 3 → Fin 3 → Fin 3 → ℝ} (hC : IsAntisymm C) :
    ofBianchi (bianchiN C) (bianchiA C) = C :=
  ofBianchi_bianchiN_bianchiA hC

example {C : Fin 3 → Fin 3 → Fin 3 → ℝ} (hC : IsAntisymm C) :
    ∃! p : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ), p.1.IsSymm ∧ ofBianchi p.1 p.2 = C :=
  existsUnique_bianchi hC

example {n : Matrix (Fin 3) (Fin 3) ℝ} (hn : n.IsSymm) (a : Fin 3 → ℝ) (e i j k : Fin 3) :
    ∑ d, (ofBianchi n a d i j * ofBianchi n a e d k + ofBianchi n a d j k * ofBianchi n a e d i +
      ofBianchi n a d k i * ofBianchi n a e d j) = 2 * levi i j k * (n *ᵥ a) e :=
  jacobi_ofBianchi_apply hn a e i j k

example {n : Matrix (Fin 3) (Fin 3) ℝ} (hn : n.IsSymm) (a : Fin 3 → ℝ) :
    Jacobi (ofBianchi n a) ↔ n *ᵥ a = 0 :=
  jacobi_ofBianchi_iff hn a

example {C : Fin 3 → Fin 3 → Fin 3 → ℝ} (hC : IsAntisymm C) :
    Jacobi C ↔ bianchiN C *ᵥ bianchiA C = 0 :=
  jacobi_iff hC

example :
    ¬ Jacobi (ofBianchi 1 ![1, 0, 0]) :=
  not_jacobi_ofBianchi_one

example (C : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    bianchiA C = 0 ↔ ∀ b, ∑ c, C c b c = 0 :=
  bianchiA_eq_zero_iff C

example :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  bianchiI

example :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  bianchiII

example :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  bianchiIV

example :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  bianchiV

example (h : ℝ) :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  bianchiVI h

example (h : ℝ) :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  bianchiVII h

example :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  bianchiVIII

example :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  bianchiIX

example :
    Jacobi bianchiI :=
  jacobi_bianchiI

example :
    Jacobi bianchiII :=
  jacobi_bianchiII

example :
    Jacobi bianchiIV :=
  jacobi_bianchiIV

example :
    Jacobi bianchiV :=
  jacobi_bianchiV

example (h : ℝ) :
    Jacobi (bianchiVI h) :=
  jacobi_bianchiVI h

example (h : ℝ) :
    Jacobi (bianchiVII h) :=
  jacobi_bianchiVII h

example :
    Jacobi bianchiVIII :=
  jacobi_bianchiVIII

example :
    Jacobi bianchiIX :=
  jacobi_bianchiIX

example (c a b : Fin 3) :
    bianchiI c a b = 0 :=
  bianchiI_apply c a b

example (c a b : Fin 3) :
    bianchiIX c a b = levi a b c :=
  bianchiIX_apply c a b

example (c a b : Fin 3) :
    bianchiII c a b = if c = 0 then levi a b 0 else 0 :=
  bianchiII_apply c a b

example (c : Fin 3) :
    bianchiII c 0 1 = 0 :=
  bianchiII_zero_one c

example (c : Fin 3) :
    bianchiII c 0 2 = 0 :=
  bianchiII_zero_two c

example (c : Fin 3) :
    bianchiII c 1 2 = if c = 0 then 1 else 0 :=
  bianchiII_one_two c

example (c a b : Fin 3) :
    bianchiV c a b = (if a = 0 ∧ c = b then 1 else 0) - (if b = 0 ∧ c = a then 1 else 0) :=
  bianchiV_apply c a b

example (c : Fin 3) :
    bianchiV c 0 1 = if c = 1 then 1 else 0 :=
  bianchiV_zero_one c

example (c : Fin 3) :
    bianchiV c 0 2 = if c = 2 then 1 else 0 :=
  bianchiV_zero_two c

example (c : Fin 3) :
    bianchiV c 1 2 = 0 :=
  bianchiV_one_two c

end ProjectAinos.GeneralRelativity.StructureConstants

end StructureConstants

section HomogeneousSpace

open ContinuousLinearMap Set TopologicalSpace Filter

open scoped ContDiff Topology Manifold

namespace ProjectAinos.GeneralRelativity.HomogeneousSpace

open SmoothGeometry CoordinateMetric LorentzMetric

local notation "E" => MinkowskiModel 3

example :
    E →L[ℝ] (Fin 3 → ℝ) :=
  spatial

example (z : E) (α : Fin 3) :
    spatial z α = z α.succ :=
  spatial_apply z α

example :
    (Fin 3 → ℝ) →L[ℝ] E :=
  ofSpatial

example (v : Fin 3 → ℝ) :
    ofSpatial v 0 = 0 :=
  ofSpatial_zero v

example (v : Fin 3 → ℝ) (α : Fin 3) :
    ofSpatial v α.succ = v α :=
  ofSpatial_succ v α

example (v : Fin 3 → ℝ) :
    spatial (ofSpatial v) = v :=
  spatial_ofSpatial v

example :
    E :=
  timeUnit

example :
    timeUnit 0 = 1 :=
  timeUnit_zero

example (α : Fin 3) :
    timeUnit α.succ = 0 :=
  timeUnit_succ α

example :
    spatial timeUnit = 0 :=
  spatial_timeUnit

namespace Data

variable (D : Data)

example :
    Opens E :=
  domain D

variable {D}

example {z : E} (hz : z ∈ D.domain) :
    z 0 ∈ D.I :=
  time_mem hz

example {z : E} (hz : z ∈ D.domain) :
    spatial z ∈ D.F.V :=
  spatial_mem hz

example (t : ℝ) (s : Fin 3 → ℝ) :
    E :=
  point t s

example (t : ℝ) (s : Fin 3 → ℝ) :
    point t s 0 = t :=
  point_zero t s

example (t : ℝ) (s : Fin 3 → ℝ) :
    spatial (point t s) = s :=
  spatial_point t s

example {t : ℝ} {s : Fin 3 → ℝ} (ht : t ∈ D.I) (hs : s ∈ D.F.V) :
    point t s ∈ D.domain :=
  point_mem ht hs

example {t : ℝ} (ht : t ∈ D.I) :
    D.triadInv t * D.triad t = 1 :=
  triadInv_mul ht

example (z : E) (k α : Fin 3) :
    ℝ :=
  theta D z k α

example (z : E) (k : Fin 3) :
    E →L[ℝ] ℝ :=
  thetaForm D z k

example (z v : E) (k : Fin 3) :
    D.thetaForm z k v = ∑ α, D.theta z k α * v α.succ :=
  thetaForm_apply z v k

example (z : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  form D z

example (z v w : E) :
    D.form z v w = -(v 0 * w 0) + ∑ k, D.thetaForm z k v * D.thetaForm z k w :=
  form_apply z v w

example (z v w : E) :
    D.form z v w = D.form z w v :=
  form_symm z v w

example (k a : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : E => D.triad (z 0) k a) D.domain :=
  contDiffOn_time_triad k a

example (a α : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : E => D.F.coframe a (spatial z) α) D.domain :=
  contDiffOn_coframe a α

example (k α : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : E => D.theta z k α) D.domain :=
  contDiffOn_theta k α

example :
    ContDiffOn ℝ ∞ D.form D.domain :=
  contDiffOn_form

example {z : E} (hz : z ∈ D.domain) (k c : Fin 3) :
    ∑ α, D.theta z k α * D.F.field c (spatial z) α = D.triad (z 0) k c :=
  theta_field hz k c

example {z : E} (hz : z ∈ D.domain) (k : Fin 3) (μ : Fin 3 → ℝ) :
    D.thetaForm z k (ofSpatial (∑ c, μ c • D.F.field c (spatial z))) =
      ∑ c, D.triad (z 0) k c * μ c :=
  thetaForm_ofSpatial hz k μ

open Matrix in

example {z : E} (hz : z ∈ D.domain) {v : Fin 3 → ℝ} (hv : ∀ k, ∑ α, D.theta z k α * v α = 0) :
    v = 0 :=
  eq_zero_of_theta hz hv

example :
    CoordinateMetric .timeNegative 3 D.domain :=
  metric D

example :
    (metric D).form = D.form :=
  metric_form

example (a : Fin 4) (z : E) :
    E :=
  frameField D a z

example (z : E) :
    D.frameField 0 z = timeUnit :=
  frameField_zero z

example (i : Fin 3) (z : E) :
    D.frameField i.succ z = ofSpatial (∑ b, D.triadInv (z 0) b i • D.F.field b (spatial z)) :=
  frameField_succ i z

example (z : E) (k : Fin 3) :
    D.thetaForm z k timeUnit = 0 :=
  thetaForm_timeUnit z k

example {z : E} (hz : z ∈ D.domain) (k i : Fin 3) :
    D.thetaForm z k (D.frameField i.succ z) = if k = i then 1 else 0 :=
  thetaForm_frameField_succ hz k i

example {z : E} (hz : z ∈ D.domain) (a b : Fin 4) :
    D.form z (D.frameField a z) (D.frameField b z) =
      if a = b then lorentzSign .timeNegative a else 0 :=
  form_frameField hz a b

example {t : ℝ} (ht : t ∈ D.I) (a i : Fin 3) :
    HasDerivAt (fun s => D.triadInv s a i) (deriv (fun s => D.triadInv s a i) t) t :=
  hasDerivAt_triadInv ht a i

example {z : E} (hz : z ∈ D.domain) (b : Fin 3) :
    DifferentiableAt ℝ (D.F.field b) (spatial z) :=
  differentiableAt_field hz b

example (b : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : E => D.F.field b (spatial z)) D.domain :=
  contDiffOn_field b

example (a i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : E => D.triadInv (z 0) a i) D.domain :=
  contDiffOn_time_triadInv a i

example (a : Fin 4) :
    ContDiffOn ℝ ∞ (D.frameField a) D.domain :=
  contDiffOn_frameField a

example {z : E} (hz : z ∈ D.domain) (i : Fin 3) (v : E) :
    fderiv ℝ (D.frameField i.succ) z v =
      ofSpatial (∑ b, ((deriv (fun s => D.triadInv s b i) (z 0) * v 0) • D.F.field b (spatial z) +
        D.triadInv (z 0) b i • fderiv ℝ (D.F.field b) (spatial z) (spatial v))) :=
  fderiv_frameField_succ hz i v

example (a : Fin 4) (z : E) :
    D.frameField a z 0 = if a = 0 then 1 else 0 :=
  frameField_apply_zero a z

example (z : E) :
    lieBracketOf (D.frameField 0) (D.frameField 0) z = 0 :=
  bracket_zero_zero z

example {z : E} (hz : z ∈ D.domain) (j : Fin 3) :
    lieBracketOf (D.frameField 0) (D.frameField j.succ) z =
      ofSpatial (∑ b, deriv (fun s => D.triadInv s b j) (z 0) • D.F.field b (spatial z)) :=
  bracket_zero_succ hz j

example {z : E} (hz : z ∈ D.domain) (i : Fin 3) :
    lieBracketOf (D.frameField i.succ) (D.frameField 0) z =
      -ofSpatial (∑ b, deriv (fun s => D.triadInv s b i) (z 0) • D.F.field b (spatial z)) :=
  bracket_succ_zero hz i

example {z : E} (hz : z ∈ D.domain) (i j : Fin 3) :
    lieBracketOf (D.frameField i.succ) (D.frameField j.succ) z =
      ofSpatial (∑ c, (∑ a, ∑ b, D.triadInv (z 0) a i * D.triadInv (z 0) b j * D.F.C c a b) •
        D.F.field c (spatial z)) :=
  bracket_succ_succ hz i j

example (z : E) (w : Fin 3 → ℝ) :
    D.form z timeUnit (ofSpatial w) = 0 :=
  form_timeUnit_ofSpatial z w

example {z : E} (hz : z ∈ D.domain) (k : Fin 3) (w : Fin 3 → ℝ) :
    D.form z (D.frameField k.succ z) (ofSpatial w) = D.thetaForm z k (ofSpatial w) :=
  form_frameField_succ_ofSpatial hz k w

example (t : ℝ) (k j : Fin 3) :
    ℝ :=
  velocity D t k j

example (t : ℝ) (k i j : Fin 3) :
    ℝ :=
  spatialStructure D t k i j

example (t : ℝ) (a b c : Fin 4) :
    ℝ :=
  lam D t a b c

example (t : ℝ) (b c : Fin 4) :
    D.lam t 0 b c = 0 :=
  lam_zero t b c

example (t : ℝ) (k : Fin 3) :
    D.lam t k.succ 0 0 = 0 :=
  lam_succ_zero_zero t k

example (t : ℝ) (k j : Fin 3) :
    D.lam t k.succ 0 j.succ = D.velocity t k j :=
  lam_succ_zero_succ t k j

example (t : ℝ) (k i : Fin 3) :
    D.lam t k.succ i.succ 0 = -D.velocity t k i :=
  lam_succ_succ_zero t k i

example (t : ℝ) (k i j : Fin 3) :
    D.lam t k.succ i.succ j.succ = D.spatialStructure t k i j :=
  lam_succ_succ_succ t k i j

example {z : E} (hz : z ∈ D.domain) (a b c : Fin 4) :
    D.form z (D.frameField a z) (lieBracketOf (D.frameField b) (D.frameField c) z) =
      D.lam (z 0) a b c :=
  commutator_frame hz a b c

example (k j : Fin 3) :
    ContDiffOn ℝ ∞ (fun t => D.velocity t k j) D.I :=
  contDiffOn_velocity k j

example (k i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun t => D.spatialStructure t k i j) D.I :=
  contDiffOn_spatialStructure k i j

example (a b c : Fin 4) :
    ContDiffOn ℝ ∞ (fun t => D.lam t a b c) D.I :=
  contDiffOn_lam a b c

example (y : D.domain) :
    (metric D).toLorentzMetric.OrthonormalFrame (univ : Set D.domain) :=
  frame D y

example (t : ℝ) (a b c : Fin 4) :
    ℝ :=
  rot D t a b c

example (t : ℝ) (b k : Fin 4) :
    ℝ :=
  frameRicci D t b k

example (a b c : Fin 4) :
    ContDiffOn ℝ ∞ (fun t => D.rot t a b c) D.I :=
  contDiffOn_rot a b c

example {z : E} (hz : z ∈ D.domain) (a b c : Fin 4) (v : E) :
    fderiv ℝ (rotationOf (fun a b c (y : E) => D.lam (y 0) a b c) a b c) z v =
      deriv (fun s => D.rot s a b c) (z 0) * v 0 :=
  fderiv_rotationOf hz a b c v

example (y : D.domain) (b k : Fin 4) :
    (metric D).toLorentzMetric.ricci y ((frame D y).field b y) ((frame D y).field k y) =
      D.frameRicci ((y : E) 0) b k :=
  ricci_frame y b k

example {t : ℝ} {s : Fin 3 → ℝ} (ht : t ∈ D.I) (hs : s ∈ D.F.V) :
    D.domain :=
  pointOf ht hs

example :
    (∀ y : D.domain, (metric D).toLorentzMetric.ricci y = 0) ↔
      ∀ t ∈ D.I, ∀ b k, D.frameRicci t b k = 0 :=
  ricci_eq_zero_iff

example (ρ p : ℝ → ℝ) (y : D.domain) :
    TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ :=
  fluid D ρ p y

example (t : ℝ) :
    ℝ :=
  frameScalar D t

example (ρ p : ℝ → ℝ) (t : ℝ) (a b : Fin 4) :
    ℝ :=
  fluidFrame ρ p t a b

example (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (∀ y : D.domain, (metric D).toLorentzMetric.einstein y +
        Λ • (metric D).toLorentzMetric.form y = κ • D.fluid ρ p y) ↔
      ∀ t ∈ D.I, ∀ a b, D.frameRicci t a b -
          D.frameScalar t / 2 * (if a = b then lorentzSign .timeNegative a else 0) +
          Λ * (if a = b then lorentzSign .timeNegative a else 0) =
        κ * fluidFrame ρ p t a b :=
  einstein_iff κ Λ ρ p

end Data

end ProjectAinos.GeneralRelativity.HomogeneousSpace

end HomogeneousSpace

section BianchiClassA

open Set Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.HomogeneousSpace

open SmoothGeometry CoordinateMetric LorentzMetric StructureConstants

example (n : Fin 3 → ℝ) (c a b : Fin 3) :
    ofBianchi (Matrix.diagonal n) 0 c a b = levi a b c * n c :=
  ofBianchi_diagonal n c a b

namespace Data

example (F : InvariantFrame) (I : Set ℝ) (hI : IsOpen I) (a : Fin 3 → ℝ → ℝ)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) I) (hpos : ∀ i, ∀ t ∈ I, 0 < a i t) :
    Data :=
  diagonal F I hI a ha hpos

variable {F : InvariantFrame} {I : Set ℝ} {hI : IsOpen I} {a : Fin 3 → ℝ → ℝ}
  {ha : ∀ i, ContDiffOn ℝ ∞ (a i) I} {hpos : ∀ i, ∀ t ∈ I, 0 < a i t} {t : ℝ}

example (ht : t ∈ I) (k j : Fin 3) :
    (diagonal F I hI a ha hpos).velocity t k j =
      if k = j then -(deriv (a k) t / a k t) else 0 :=
  velocity_diagonal ht k j

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (k i j : Fin 3) :
    (diagonal F I hI a ha hpos).spatialStructure t k i j =
      levi i j k * n k * a k t / (a i t * a j t) :=
  spatialStructure_diagonal hC k i j

example (t : ℝ) (k j : Fin 3) :
    ℝ :=
  diagVelocity a t k j

example (t : ℝ) (k j : Fin 3) :
    ℝ :=
  diagVelocityDeriv a t k j

example (n : Fin 3 → ℝ) (t : ℝ) (k i j : Fin 3) :
    ℝ :=
  diagStructure a n t k i j

example (n : Fin 3 → ℝ) (t : ℝ) (k i j : Fin 3) :
    ℝ :=
  diagStructureDeriv a n t k i j

example (n : Fin 3 → ℝ) (t : ℝ) (p b c : Fin 4) :
    ℝ :=
  diagLam a n t p b c

example (n : Fin 3 → ℝ) (t : ℝ) (p b c : Fin 4) :
    ℝ :=
  diagLamDeriv a n t p b c

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) (p b c : Fin 4) :
    (diagonal F I hI a ha hpos).lam t p b c = diagLam a n t p b c :=
  lam_diagonal hC ht p b c

example (ht : t ∈ I) (k j : Fin 3) :
    HasDerivAt (fun s => diagVelocity a s k j) (diagVelocityDeriv a t k j) t :=
  hasDerivAt_diagVelocity (hI := hI) (ha := ha) (hpos := hpos) ht k j

example (ht : t ∈ I) (n : Fin 3 → ℝ) (k i j : Fin 3) :
    HasDerivAt (fun s => diagStructure a n s k i j) (diagStructureDeriv a n t k i j) t :=
  hasDerivAt_diagStructure (hI := hI) (ha := ha) (hpos := hpos) ht n k i j

example (ht : t ∈ I) (n : Fin 3 → ℝ) (p b c : Fin 4) :
    HasDerivAt (fun s => diagLam a n s p b c) (diagLamDeriv a n t p b c) t :=
  hasDerivAt_diagLam (hI := hI) (ha := ha) (hpos := hpos) ht n p b c

example (n : Fin 3 → ℝ) (t : ℝ) (p b c : Fin 4) :
    ℝ :=
  diagRot a n t p b c

example (n : Fin 3 → ℝ) (t : ℝ) (p b c : Fin 4) :
    ℝ :=
  diagRotDeriv a n t p b c

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) (p b c : Fin 4) :
    (diagonal F I hI a ha hpos).rot t p b c = diagRot a n t p b c :=
  rot_diagonal hC ht p b c

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) (p b c : Fin 4) :
    deriv (fun s => (diagonal F I hI a ha hpos).rot s p b c) t = diagRotDeriv a n t p b c :=
  deriv_rot_diagonal hC ht p b c

example (n : Fin 3 → ℝ) (t : ℝ) (b k : Fin 4) :
    ℝ :=
  diagFrameRicci a n t b k

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) (b k : Fin 4) :
    (diagonal F I hI a ha hpos).frameRicci t b k = diagFrameRicci a n t b k :=
  frameRicci_diagonal hC ht b k

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 0 0 =
      -(deriv (deriv (a 0)) t / a 0 t + deriv (deriv (a 1)) t / a 1 t +
        deriv (deriv (a 2)) t / a 2 t) :=
  frameRicci_zero_zero hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 1 1 =
      deriv (deriv (a 0)) t / a 0 t +
        deriv (a 0) t / a 0 t * (deriv (a 1) t / a 1 t + deriv (a 2) t / a 2 t) +
        ((n 0 * a 0 t ^ 2) ^ 2 - (n 1 * a 1 t ^ 2 - n 2 * a 2 t ^ 2) ^ 2) /
          (2 * (a 0 t * a 1 t * a 2 t) ^ 2) :=
  frameRicci_one_one hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 2 2 =
      deriv (deriv (a 1)) t / a 1 t +
        deriv (a 1) t / a 1 t * (deriv (a 0) t / a 0 t + deriv (a 2) t / a 2 t) +
        ((n 1 * a 1 t ^ 2) ^ 2 - (n 0 * a 0 t ^ 2 - n 2 * a 2 t ^ 2) ^ 2) /
          (2 * (a 0 t * a 1 t * a 2 t) ^ 2) :=
  frameRicci_two_two hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 3 3 =
      deriv (deriv (a 2)) t / a 2 t +
        deriv (a 2) t / a 2 t * (deriv (a 0) t / a 0 t + deriv (a 1) t / a 1 t) +
        ((n 2 * a 2 t ^ 2) ^ 2 - (n 0 * a 0 t ^ 2 - n 1 * a 1 t ^ 2) ^ 2) /
          (2 * (a 0 t * a 1 t * a 2 t) ^ 2) :=
  frameRicci_three_three hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 0 1 = 0 :=
  frameRicci_zero_one hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 0 2 = 0 :=
  frameRicci_zero_two hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 0 3 = 0 :=
  frameRicci_zero_three hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 1 0 = 0 :=
  frameRicci_one_zero hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 1 2 = 0 :=
  frameRicci_one_two hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 1 3 = 0 :=
  frameRicci_one_three hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 2 0 = 0 :=
  frameRicci_two_zero hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 2 1 = 0 :=
  frameRicci_two_one hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 2 3 = 0 :=
  frameRicci_two_three hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 3 0 = 0 :=
  frameRicci_three_zero hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 3 1 = 0 :=
  frameRicci_three_one hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) :
    (diagonal F I hI a ha hpos).frameRicci t 3 2 = 0 :=
  frameRicci_three_two hC ht

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) (ht : t ∈ I) {b k : Fin 4}
    (hbk : b ≠ k) :
    (diagonal F I hI a ha hpos).frameRicci t b k = 0 :=
  frameRicci_ne hC ht hbk

example {n : Fin 3 → ℝ} (hC : F.C = ofBianchi (Matrix.diagonal n) 0) :
    (∀ y : (diagonal F I hI a ha hpos).domain,
        (metric (diagonal F I hI a ha hpos)).toLorentzMetric.ricci y = 0) ↔
      ∀ t ∈ I,
        deriv (deriv (a 0)) t / a 0 t + deriv (deriv (a 1)) t / a 1 t +
            deriv (deriv (a 2)) t / a 2 t = 0 ∧
        deriv (deriv (a 0)) t / a 0 t +
            deriv (a 0) t / a 0 t * (deriv (a 1) t / a 1 t + deriv (a 2) t / a 2 t) +
            ((n 0 * a 0 t ^ 2) ^ 2 - (n 1 * a 1 t ^ 2 - n 2 * a 2 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 ∧
        deriv (deriv (a 1)) t / a 1 t +
            deriv (a 1) t / a 1 t * (deriv (a 0) t / a 0 t + deriv (a 2) t / a 2 t) +
            ((n 1 * a 1 t ^ 2) ^ 2 - (n 0 * a 0 t ^ 2 - n 2 * a 2 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 ∧
        deriv (deriv (a 2)) t / a 2 t +
            deriv (a 2) t / a 2 t * (deriv (a 0) t / a 0 t + deriv (a 1) t / a 1 t) +
            ((n 2 * a 2 t ^ 2) ^ 2 - (n 0 * a 0 t ^ 2 - n 1 * a 1 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 :=
  ricci_eq_zero_iff_diagonal hC

end Data

end ProjectAinos.GeneralRelativity.HomogeneousSpace

end BianchiClassA

section BianchiFrames

open ContinuousLinearMap Set

open scoped ContDiff Real

namespace ProjectAinos.GeneralRelativity.HomogeneousSpace

open StructureConstants (levi)

example :
    Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fieldI

example :
    Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  coframeI

example (s : Fin 3 → ℝ) (a b : Fin 3) :
    ∑ α, coframeI a s α * fieldI b s α = if a = b then 1 else 0 :=
  coframe_fieldI s a b

example (s : Fin 3 → ℝ) (a b : Fin 3) :
    fderiv ℝ (fieldI b) s (fieldI a s) - fderiv ℝ (fieldI a) s (fieldI b s) =
      ∑ c, StructureConstants.bianchiI c a b • fieldI c s :=
  bracket_fieldI s a b

example :
    InvariantFrame :=
  InvariantFrame.bianchiI

example :
    InvariantFrame.bianchiI.C = StructureConstants.bianchiI :=
  InvariantFrame.bianchiI_C

example :
    InvariantFrame.bianchiI.V = univ :=
  InvariantFrame.bianchiI_V

example (a : Fin 3) (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiI.field a s = Pi.single a 1 :=
  InvariantFrame.bianchiI_field a s

example (a : Fin 3) (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiI.coframe a s = Pi.single a 1 :=
  InvariantFrame.bianchiI_coframe a s

example :
    Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fieldII

example :
    Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  coframeII

example (a : Fin 3) :
    ContDiff ℝ ∞ (fieldII a) :=
  contDiff_fieldII a

example (a : Fin 3) :
    ContDiff ℝ ∞ (coframeII a) :=
  contDiff_coframeII a

example (s : Fin 3 → ℝ) (a b : Fin 3) :
    ∑ α, coframeII a s α * fieldII b s α = if a = b then 1 else 0 :=
  coframe_fieldII s a b

example (s : Fin 3 → ℝ) (a b : Fin 3) :
    fderiv ℝ (fieldII b) s (fieldII a s) - fderiv ℝ (fieldII a) s (fieldII b s) =
      ∑ c, StructureConstants.bianchiII c a b • fieldII c s :=
  bracket_fieldII s a b

example :
    InvariantFrame :=
  InvariantFrame.bianchiII

example :
    InvariantFrame.bianchiII.C = StructureConstants.bianchiII :=
  InvariantFrame.bianchiII_C

example :
    InvariantFrame.bianchiII.V = univ :=
  InvariantFrame.bianchiII_V

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.field 0 s = ![1, 0, 0] :=
  InvariantFrame.bianchiII_field_zero s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.field 1 s = ![0, 1, 0] :=
  InvariantFrame.bianchiII_field_one s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.field 2 s = ![s 1, 0, 1] :=
  InvariantFrame.bianchiII_field_two s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.coframe 0 s = ![1, 0, -s 1] :=
  InvariantFrame.bianchiII_coframe_zero s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.coframe 1 s = ![0, 1, 0] :=
  InvariantFrame.bianchiII_coframe_one s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiII.coframe 2 s = ![0, 0, 1] :=
  InvariantFrame.bianchiII_coframe_two s

example :
    Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fieldV

example :
    Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  coframeV

example (a : Fin 3) :
    ContDiff ℝ ∞ (fieldV a) :=
  contDiff_fieldV a

example (a : Fin 3) :
    ContDiff ℝ ∞ (coframeV a) :=
  contDiff_coframeV a

example (s : Fin 3 → ℝ) (a b : Fin 3) :
    ∑ α, coframeV a s α * fieldV b s α = if a = b then 1 else 0 :=
  coframe_fieldV s a b

example (s : Fin 3 → ℝ) (a b : Fin 3) :
    fderiv ℝ (fieldV b) s (fieldV a s) - fderiv ℝ (fieldV a) s (fieldV b s) =
      ∑ c, StructureConstants.bianchiV c a b • fieldV c s :=
  bracket_fieldV s a b

example :
    InvariantFrame :=
  InvariantFrame.bianchiV

example :
    InvariantFrame.bianchiV.C = StructureConstants.bianchiV :=
  InvariantFrame.bianchiV_C

example :
    InvariantFrame.bianchiV.V = univ :=
  InvariantFrame.bianchiV_V

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.field 0 s = ![1, 0, 0] :=
  InvariantFrame.bianchiV_field_zero s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.field 1 s = ![0, Real.exp (s 0), 0] :=
  InvariantFrame.bianchiV_field_one s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.field 2 s = ![0, 0, Real.exp (s 0)] :=
  InvariantFrame.bianchiV_field_two s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.coframe 0 s = ![1, 0, 0] :=
  InvariantFrame.bianchiV_coframe_zero s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.coframe 1 s = ![0, Real.exp (-s 0), 0] :=
  InvariantFrame.bianchiV_coframe_one s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiV.coframe 2 s = ![0, 0, Real.exp (-s 0)] :=
  InvariantFrame.bianchiV_coframe_two s

example :
    Set (Fin 3 → ℝ) :=
  domainIX

example :
    IsOpen domainIX :=
  isOpen_domainIX

example :
    domainIX.Nonempty :=
  nonempty_domainIX

example {s : Fin 3 → ℝ} (hs : s ∈ domainIX) :
    0 < Real.sin (s 0) :=
  sin_pos_of_mem_domainIX hs

example :
    Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fieldIX

example :
    Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  coframeIX

example (a : Fin 3) :
    ContDiffOn ℝ ∞ (fieldIX a) domainIX :=
  contDiffOn_fieldIX a

example (a : Fin 3) :
    ContDiff ℝ ∞ (coframeIX a) :=
  contDiff_coframeIX a

example {s : Fin 3 → ℝ} (hs : s ∈ domainIX) (a b : Fin 3) :
    ∑ α, coframeIX a s α * fieldIX b s α = if a = b then 1 else 0 :=
  coframe_fieldIX hs a b

example {s : Fin 3 → ℝ} (hs : s ∈ domainIX) (a b : Fin 3) :
    fderiv ℝ (fieldIX b) s (fieldIX a s) - fderiv ℝ (fieldIX a) s (fieldIX b s) =
      ∑ c, StructureConstants.bianchiIX c a b • fieldIX c s :=
  bracket_fieldIX hs a b

example :
    InvariantFrame :=
  InvariantFrame.bianchiIX

example :
    InvariantFrame.bianchiIX.C = StructureConstants.bianchiIX :=
  InvariantFrame.bianchiIX_C

example :
    InvariantFrame.bianchiIX.V = domainIX :=
  InvariantFrame.bianchiIX_V

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.field 0 s = ![Real.sin (s 2), -Real.cos (s 2) / Real.sin (s 0),
      Real.cos (s 0) * Real.cos (s 2) / Real.sin (s 0)] :=
  InvariantFrame.bianchiIX_field_zero s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.field 1 s = ![Real.cos (s 2), Real.sin (s 2) / Real.sin (s 0),
      -Real.cos (s 0) * Real.sin (s 2) / Real.sin (s 0)] :=
  InvariantFrame.bianchiIX_field_one s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.field 2 s = ![0, 0, 1] :=
  InvariantFrame.bianchiIX_field_two s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.coframe 0 s =
      ![Real.sin (s 2), -(Real.sin (s 0) * Real.cos (s 2)), 0] :=
  InvariantFrame.bianchiIX_coframe_zero s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.coframe 1 s =
      ![Real.cos (s 2), Real.sin (s 0) * Real.sin (s 2), 0] :=
  InvariantFrame.bianchiIX_coframe_one s

example (s : Fin 3 → ℝ) :
    InvariantFrame.bianchiIX.coframe 2 s = ![0, Real.cos (s 0), 1] :=
  InvariantFrame.bianchiIX_coframe_two s

end ProjectAinos.GeneralRelativity.HomogeneousSpace

end BianchiFrames

section BianchiExamples

open Set

open scoped ContDiff

namespace ProjectAinos.GeneralRelativity.HomogeneousSpace

open SmoothGeometry CoordinateMetric LorentzMetric StructureConstants

example :
    StructureConstants.bianchiI = ofBianchi (Matrix.diagonal 0) 0 :=
  bianchiI_eq_diagonal

example :
    StructureConstants.bianchiII = ofBianchi (Matrix.diagonal ![1, 0, 0]) 0 :=
  bianchiII_eq_diagonal

example :
    StructureConstants.bianchiIX = ofBianchi (Matrix.diagonal fun _ => 1) 0 :=
  bianchiIX_eq_diagonal

example {I : Set ℝ} {hI : IsOpen I} {a : Fin 3 → ℝ → ℝ} {ha : ∀ i, ContDiffOn ℝ ∞ (a i) I}
    {hpos : ∀ i, ∀ t ∈ I, 0 < a i t} :
    (∀ y : (Data.diagonal InvariantFrame.bianchiIX I hI a ha hpos).domain,
        (Data.diagonal InvariantFrame.bianchiIX I hI a ha hpos).metric.toLorentzMetric.ricci y =
          0) ↔
      ∀ t ∈ I,
        deriv (deriv (a 0)) t / a 0 t + deriv (deriv (a 1)) t / a 1 t +
            deriv (deriv (a 2)) t / a 2 t = 0 ∧
        deriv (deriv (a 0)) t / a 0 t +
            deriv (a 0) t / a 0 t * (deriv (a 1) t / a 1 t + deriv (a 2) t / a 2 t) +
            ((a 0 t ^ 2) ^ 2 - (a 1 t ^ 2 - a 2 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 ∧
        deriv (deriv (a 1)) t / a 1 t +
            deriv (a 1) t / a 1 t * (deriv (a 0) t / a 0 t + deriv (a 2) t / a 2 t) +
            ((a 1 t ^ 2) ^ 2 - (a 0 t ^ 2 - a 2 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 ∧
        deriv (deriv (a 2)) t / a 2 t +
            deriv (a 2) t / a 2 t * (deriv (a 0) t / a 0 t + deriv (a 1) t / a 1 t) +
            ((a 2 t ^ 2) ^ 2 - (a 0 t ^ 2 - a 1 t ^ 2) ^ 2) /
              (2 * (a 0 t * a 1 t * a 2 t) ^ 2) = 0 :=
  ricci_eq_zero_iff_bianchiIX

example (p : Fin 3 → ℝ) :
    Data :=
  kasnerModel p

example {p : Fin 3 → ℝ} (h : ∑ α, p α = 1 ∧ ∑ α, p α ^ 2 = 1) :
    ∀ y : (kasnerModel p).domain, (kasnerModel p).metric.toLorentzMetric.ricci y = 0 :=
  ricci_kasnerModel_eq_zero h

end ProjectAinos.GeneralRelativity.HomogeneousSpace

end BianchiExamples
