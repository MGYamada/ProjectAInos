/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.Tetrad

/-! Public consumers of orthonormal frames: the fields of a frame and its coordinates, the
expansion of vectors and of the metric, the rotation and commutator coefficients with their
relations, the curvature, Ricci, scalar and Einstein tensors in a frame, the Einstein equations
in the frames of a cover, the change of frame, and the coordinate frame of the Minkowski
metric. Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section

open Bundle FiberBundle VectorField Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

namespace LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

local notation "E" => MinkowskiModel d

local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

namespace OrthonormalFrame

variable {g : LorentzMetric σ d M} {W : Set M} (F : OrthonormalFrame g W) {x : M}

local instance (x : M) : FiniteDimensional ℝ (TM x) :=
  inferInstanceAs (FiniteDimensional ℝ (MinkowskiModel d))

example : IsOpen W := F.isOpen

example : ∀ a, ∀ x ∈ W, ContMDiffAt I ((I).prod I) ∞ (T% (F.field a)) x := F.smooth

example : ∀ x ∈ W, ∀ a b, g.form x (F.field a x) (F.field b x) =
    if a = b then lorentzSign σ a else 0 := F.orthonormal

example (hx : x ∈ W) (a : Fin (d + 1)) :
    MDifferentiableAt I ((I).prod I) (T% (F.field a)) x :=
  mdiff F hx a

example (x : M) :
    TM x →L[ℝ] E :=
  coord F x

example (x : M) (v : TM x) (a : Fin (d + 1)) :
    F.coord x v a = lorentzSign σ a * g.form x v (F.field a x) :=
  coord_apply F x v a

example (x : M) :
    E →L[ℝ] TM x :=
  combine F x

example (x : M) (c : E) :
    F.combine x c = ∑ a, c a • F.field a x :=
  combine_apply F x c

example (hx : x ∈ W) (c : E) :
    F.coord x (F.combine x c) = c :=
  coord_combine F hx c

example (hx : x ∈ W) (v : TM x) :
    ∑ a, F.coord x v a • F.field a x = v :=
  sum_coord_smul F hx v

example (hx : x ∈ W) (v : TM x) :
    F.combine x (F.coord x v) = v :=
  combine_coord F hx v

example (hx : x ∈ W) :
    TM x ≃L[ℝ] E :=
  coordEquiv F hx

example (hx : x ∈ W) (v : TM x) :
    F.coordEquiv hx v = F.coord x v :=
  coordEquiv_apply F hx v

example (hx : x ∈ W) (a : Fin (d + 1)) :
    (F.coordEquiv hx).symm (Pi.single a 1) = F.field a x :=
  coordEquiv_symm_single F hx a

example (hx : x ∈ W) (u w : TM x) :
    g.form x u w = ∑ a, lorentzSign σ a * g.form x u (F.field a x) * g.form x w (F.field a x) :=
  form_eq_sum F hx u w

example (hx : x ∈ W) {B B' : TM x →L[ℝ] TM x →L[ℝ] ℝ}
    (h : ∀ a b, B (F.field a x) (F.field b x) = B' (F.field a x) (F.field b x)) :
    B = B' :=
  bilinear_ext F hx h

example (a b c : Fin (d + 1)) (x : M) :
    ℝ :=
  rotation F a b c x

example (a b c : Fin (d + 1)) (x : M) :
    ℝ :=
  commutator F a b c x

example (hx : x ∈ W) (a b c : Fin (d + 1)) :
    F.rotation a b c x = -F.rotation b a c x :=
  rotation_antisymm F hx a b c

example (hx : x ∈ W) (a b c : Fin (d + 1)) :
    F.commutator a b c x = F.rotation a b c x - F.rotation a c b x :=
  commutator_eq F hx a b c

example (hx : x ∈ W) (a b c : Fin (d + 1)) :
    F.rotation a b c x =
      (F.commutator a b c x + F.commutator b c a x - F.commutator c a b x) / 2 :=
  rotation_eq F hx a b c

example (hx : x ∈ W) (b : Fin (d + 1)) :
    F.coord x (F.field b x) = Pi.single b 1 :=
  coord_field F hx b

example (a b c k : Fin (d + 1)) (x : M) :
    ℝ :=
  curvatureComponent F a b c k x

example (hx : x ∈ W) (a b c k : Fin (d + 1)) :
    g.form x (g.covariantField (F.field c) (g.covariantField (F.field k) (F.field b)) x)
        (F.field a x) =
      mvfderiv I (F.rotation b a k) x (F.field c x) -
        ∑ f, lorentzSign σ f * F.rotation b f k x * F.rotation a f c x :=
  form_covariantField_covariantField F hx a b c k

example (hx : x ∈ W) (a b c k : Fin (d + 1)) :
    g.form x (g.covariantField (mlieBracket I (F.field c) (F.field k)) (F.field b) x)
        (F.field a x) =
      ∑ f, lorentzSign σ f * F.commutator f c k x * F.rotation b a f x :=
  form_covariantField_bracket F hx a b c k

example (hx : x ∈ W) (a b c k : Fin (d + 1)) :
    F.curvatureComponent a b c k x =
      mvfderiv I (F.rotation b a k) x (F.field c x) -
        mvfderiv I (F.rotation b a c) x (F.field k x) -
        ∑ f, lorentzSign σ f * (F.rotation b f k x * F.rotation a f c x -
          F.rotation b f c x * F.rotation a f k x + F.commutator f c k x * F.rotation b a f x) :=
  curvatureComponent_eq F hx a b c k

example (hx : x ∈ W) (u v : TM x) :
    g.ricci x u v =
      ∑ i, lorentzSign σ i * g.form x (g.curvature x (F.field i x) u v) (F.field i x) :=
  ricci_eq_sum_frame F hx u v

example (hx : x ∈ W) (b k : Fin (d + 1)) :
    g.ricci x (F.field b x) (F.field k x) =
      ∑ i, lorentzSign σ i * F.curvatureComponent i k i b x :=
  ricci_field F hx b k

example (hx : x ∈ W) (b k : Fin (d + 1)) :
    g.ricci x (F.field b x) (F.field k x) =
      ∑ i, lorentzSign σ i * (mvfderiv I (F.rotation k i b) x (F.field i x) -
        mvfderiv I (F.rotation k i i) x (F.field b x) -
        ∑ f, lorentzSign σ f * (F.rotation k f b x * F.rotation i f i x -
          F.rotation k f i x * F.rotation i f b x +
            F.commutator f i b x * F.rotation k i f x)) :=
  ricci_field_eq F hx b k

example (hx : x ∈ W) :
    g.scalarCurvature x = ∑ i, lorentzSign σ i * g.ricci x (F.field i x) (F.field i x) :=
  scalarCurvature_eq F hx

example (hx : x ∈ W) (a b : Fin (d + 1)) :
    g.einstein x (F.field a x) (F.field b x) =
      g.ricci x (F.field a x) (F.field b x) -
        g.scalarCurvature x / 2 * if a = b then lorentzSign σ a else 0 :=
  einstein_field F hx a b

example (hx : x ∈ W) (κ Λ : ℝ) (T : TM x →L[ℝ] TM x →L[ℝ] ℝ) :
    g.einstein x + Λ • g.form x = κ • T ↔ ∀ a b,
      g.einstein x (F.field a x) (F.field b x) + Λ * (if a = b then lorentzSign σ a else 0) =
        κ * T (F.field a x) (F.field b x) :=
  einstein_eq_iff F hx κ Λ T

example {ι : Type*} {V : ι → Set M} (G : ∀ i, OrthonormalFrame g (V i)) (hcov : ∀ x, ∃ i, x ∈ V i)
    (κ Λ : ℝ) (T : Tensor.SmoothBilinear («I» := I) (M := M)) :
    g.SatisfiesEinstein κ Λ T ↔ ∀ i, ∀ x ∈ V i, ∀ a b,
      g.einstein x ((G i).field a x) ((G i).field b x) +
          Λ * (if a = b then lorentzSign σ a else 0) =
        κ * T x ((G i).field a x) ((G i).field b x) :=
  LorentzMetric.satisfiesEinstein_iff_frames G hcov κ Λ T

example {W' : Set M} (F' : OrthonormalFrame g W') (hx : x ∈ W) (hx' : x ∈ W')
    (b k : Fin (d + 1)) :
    ∑ a, lorentzSign σ a * F.coord x (F'.field b x) a * F.coord x (F'.field k x) a =
      if b = k then lorentzSign σ b else 0 :=
  transition_orthonormal F F' hx hx' b k

end OrthonormalFrame

end LorentzMetric

namespace CoordinateMetric

open LorentzMetric

example (U : Opens (MinkowskiModel d)) :
    (minkowski σ d U).toLorentzMetric.OrthonormalFrame univ :=
  minkowskiFrame U

end CoordinateMetric

end ProjectAinos.SmoothGeometry

