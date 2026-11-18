/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.ExponentialConformalExample

/-! Public consumers of the covariant derivative of the curvature and the Einstein tensor: the
three-slot tensoriality constructor, the covariant derivative of tangent-valued trilinear tensors
for any connection, the covariant derivative of the Riemann tensor with its coordinate formula
and the second Bianchi identity, the chart contractions and the derivatives at the centre of an
inertial chart, the contracted Bianchi identity, the Einstein tensor and its vanishing
divergence, the connection and curvature of a coordinate metric, and the four-dimensional
conformally flat regression. Default elaborator options are intentional: these checks must not
rely on the implementation's transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Bundle FiberBundle Module

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.Tensor

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {A B C : SmoothBundle I (M := M)} {n : ℕ∞}
  {T : Type} [AddCommGroup T] [Module ℝ T]

namespace ContMDiffTensorialAt

variable {Φ : (∀ y, A.Fiber y) → (∀ y, B.Fiber y) → (∀ y, C.Fiber y) → T} {x : M}

example
    (h₁ : ∀ (t : ∀ y, B.Fiber y) (r : ∀ y, C.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r y)) x →
      ContMDiffTensorialAt A n (fun s => Φ s t r) x)
    (h₂ : ∀ (s : ∀ y, A.Fiber y) (r : ∀ y, C.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r y)) x →
      ContMDiffTensorialAt B n (fun t => Φ s t r) x)
    (h₃ : ∀ (s : ∀ y, A.Fiber y) (t : ∀ y, B.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x →
      ContMDiffTensorialAt C n (fun r => Φ s t r) x)
    {s s' : ∀ y, A.Fiber y} {t t' : ∀ y, B.Fiber y} {r r' : ∀ y, C.Fiber y}
    (hs : ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s y)) x)
    (hs' : ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s' y)) x)
    (ht : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x)
    (ht' : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t' y)) x)
    (hr : ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r y)) x)
    (hr' : ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r' y)) x)
    (hss' : s x = s' x) (htt' : t x = t' x) (hrr' : r x = r' x) :
    Φ s t r = Φ s' t' r' :=
  pointwise₃ h₁ h₂ h₃ hs hs' ht ht' hr hr' hss' htt' hrr'

variable [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousSMul ℝ T]

example (Φ : (∀ y, A.Fiber y) → (∀ y, B.Fiber y) → (∀ y, C.Fiber y) → T) (x : M)
    (h₁ : ∀ (t : ∀ y, B.Fiber y) (r : ∀ y, C.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r y)) x →
      ContMDiffTensorialAt A n (fun s => Φ s t r) x)
    (h₂ : ∀ (s : ∀ y, A.Fiber y) (r : ∀ y, C.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r y)) x →
      ContMDiffTensorialAt B n (fun t => Φ s t r) x)
    (h₃ : ∀ (s : ∀ y, A.Fiber y) (t : ∀ y, B.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x →
      ContMDiffTensorialAt C n (fun r => Φ s t r) x) :
    A.Fiber x →L[ℝ] B.Fiber x →L[ℝ] C.Fiber x →L[ℝ] T :=
  mkHom₃ Φ x h₁ h₂ h₃

example
    (h₁ : ∀ (t : ∀ y, B.Fiber y) (r : ∀ y, C.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r y)) x →
      ContMDiffTensorialAt A n (fun s => Φ s t r) x)
    (h₂ : ∀ (s : ∀ y, A.Fiber y) (r : ∀ y, C.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r y)) x →
      ContMDiffTensorialAt B n (fun t => Φ s t r) x)
    (h₃ : ∀ (s : ∀ y, A.Fiber y) (t : ∀ y, B.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x →
      ContMDiffTensorialAt C n (fun r => Φ s t r) x)
    (u : A.Fiber x) (v : B.Fiber x) (w : C.Fiber x) :
    mkHom₃ Φ x h₁ h₂ h₃ u v w =
      Φ (extend A.Model u) (extend B.Model v) (extend C.Model w) :=
  mkHom₃_apply_eq_extend h₁ h₂ h₃ u v w

example
    (h₁ : ∀ (t : ∀ y, B.Fiber y) (r : ∀ y, C.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r y)) x →
      ContMDiffTensorialAt A n (fun s => Φ s t r) x)
    (h₂ : ∀ (s : ∀ y, A.Fiber y) (r : ∀ y, C.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r y)) x →
      ContMDiffTensorialAt B n (fun t => Φ s t r) x)
    (h₃ : ∀ (s : ∀ y, A.Fiber y) (t : ∀ y, B.Fiber y),
      ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x →
      ContMDiffTensorialAt C n (fun r => Φ s t r) x)
    {s : ∀ y, A.Fiber y} {t : ∀ y, B.Fiber y} {r : ∀ y, C.Fiber y}
    (hs : ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) n (fun y => TotalSpace.mk' A.Model y (s y)) x)
    (ht : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) n (fun y => TotalSpace.mk' B.Model y (t y)) x)
    (hr : ContMDiffAt I (I.prod 𝓘(ℝ, C.Model)) n (fun y => TotalSpace.mk' C.Model y (r y)) x) :
    mkHom₃ Φ x h₁ h₂ h₃ (s x) (t x) (r x) = Φ s t r :=
  mkHom₃_apply h₁ h₂ h₃ hs ht hr

end ContMDiffTensorialAt

end ProjectAinos.SmoothGeometry.Tensor

open Bundle FiberBundle ContinuousLinearMap

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.Tensor

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "TM" => TangentSpace I (M := M)

example :
    SmoothBundle I (M := M) :=
  trilinearBundle

example (R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x) :
    Prop :=
  IsSmoothTrilinear R

example {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x} (hR : IsSmoothTrilinear R)
    {X Y Z : ∀ x, TM x} {x : M} (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Z) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (fun y => R y (X y) (Y y) (Z y))) x :=
  IsSmoothTrilinear.mdifferentiableAt_apply hR hX hY hZ

variable (connection : _root_.CovariantDerivative I E (TangentSpace I (M := M)))

example (R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x) (X Y Z : ∀ x, TM x) (x : M) :
    TM x →L[ℝ] TM x :=
  trilinearDerivativeAux connection R X Y Z x

example (R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x) (X Y Z : ∀ x, TM x) (x : M)
    (u : TM x) :
    trilinearDerivativeAux connection R X Y Z x u =
      connection (fun y => R y (X y) (Y y) (Z y)) x u - R x (connection X x u) (Y x) (Z x) -
        R x (X x) (connection Y x u) (Z x) - R x (X x) (Y x) (connection Z x u) :=
  trilinearDerivativeAux_apply connection R X Y Z x u

example {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x} (hR : IsSmoothTrilinear R)
    {Y Z : ∀ x, TM x} {x : M} (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Z) x) :
    ContMDiffTensorialAt (SmoothBundle.tangent I) 1
      (fun X => trilinearDerivativeAux connection R X Y Z x) x :=
  trilinearDerivative_tensorial_left connection hR hY hZ

example {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x} (hR : IsSmoothTrilinear R)
    {X Z : ∀ x, TM x} {x : M} (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Z) x) :
    ContMDiffTensorialAt (SmoothBundle.tangent I) 1
      (fun Y => trilinearDerivativeAux connection R X Y Z x) x :=
  trilinearDerivative_tensorial_middle connection hR hX hZ

example {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x} (hR : IsSmoothTrilinear R)
    {X Y : ∀ x, TM x} {x : M} (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x) :
    ContMDiffTensorialAt (SmoothBundle.tangent I) 1
      (fun Z => trilinearDerivativeAux connection R X Y Z x) x :=
  trilinearDerivative_tensorial_right connection hR hX hY

example (R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x) (hR : IsSmoothTrilinear R) (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x :=
  trilinearCovariantDerivative connection R hR x

example (R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x) (hR : IsSmoothTrilinear R) (x : M)
    (v w z u : TM x) :
    trilinearCovariantDerivative connection R hR x v w z u =
      trilinearDerivativeAux connection R (extend E v) (extend E w) (extend E z) x u :=
  trilinearCovariantDerivative_apply_eq_extend connection R hR x v w z u

example {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x} (hR : IsSmoothTrilinear R)
    {X Y Z : ∀ x, TM x} {x : M} (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% Z) x) (u : TM x) :
    trilinearCovariantDerivative connection R hR x (X x) (Y x) (Z x) u =
      connection (fun y => R y (X y) (Y y) (Z y)) x u - R x (connection X x u) (Y x) (Z x) -
        R x (X x) (connection Y x u) (Z x) - R x (X x) (Y x) (connection Z x u) :=
  trilinearCovariantDerivative_apply connection hR hX hY hZ u

end ProjectAinos.SmoothGeometry.Tensor

open Bundle FiberBundle VectorField ContinuousLinearMap

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

local notation "E" => MinkowskiModel d

local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

example (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x :=
  curvatureDerivative g x

example {n : ℕ∞} {X Y Z : ∀ x, TM x} {x : M} (hX : ContMDiffAt I ((I).prod I) n (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) n (T% Y) x) (hZ : ContMDiffAt I ((I).prod I) n (T% Z) x) :
    ContMDiffAt I ((I).prod I) n (T% (fun y => g.curvature y (X y) (Y y) (Z y))) x :=
  contMDiffAt_curvature_apply g hX hY hZ

example {X Y Z : ∀ x, TM x} {x : M} (hX : ContMDiffAt I ((I).prod I) 1 (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) 1 (T% Y) x) (hZ : ContMDiffAt I ((I).prod I) 1 (T% Z) x)
    (u : TM x) :
    g.curvatureDerivative x (X x) (Y x) (Z x) u =
      g.leviCivita (fun y => g.curvature y (X y) (Y y) (Z y)) x u -
        g.curvature x (g.leviCivita X x u) (Y x) (Z x) -
        g.curvature x (X x) (g.leviCivita Y x u) (Z x) -
        g.curvature x (X x) (Y x) (g.leviCivita Z x u) :=
  curvatureDerivative_apply g hX hY hZ u

example (x : M) :
    g.opposite.curvatureDerivative x = g.curvatureDerivative x :=
  curvatureDerivative_opposite g x

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) {V : ∀ x, TM x} (hV : ContMDiffAt I ((I).prod I) 1 (T% V) x) (v : E)
    (k : Fin (d + 1)) :
    chartTangentMap e x (g.leviCivita V x (chartField e v x)) k =
      mvfderiv I (fun y => chartTangentMap e y (V y) k) x (chartField e v x) +
        ∑ i, ∑ j, g.chartChristoffel e x k i j * v i * chartTangentMap e x (V x) j :=
  leviCivita_chart_components g he hx hV v k

example (e : OpenPartialHomeomorph M E) (x : M) (l i j k m : Fin (d + 1)) :
    ℝ :=
  chartCurvatureDerivative g e x l i j k m

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (a b : Fin (d + 1)) :
    g.leviCivita (chartField e (Pi.single b 1)) x (chartField e (Pi.single a 1) x) =
      ∑ l, g.chartChristoffel e x l a b • chartField e (Pi.single l 1) x :=
  leviCivita_chartField_eq_sum g he hx a b

example (B : Tensor.SmoothBilinear («I» := I) (M := M)) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (i j k : Fin (d + 1)) :
    Tensor.bilinearCovariantDerivative g.leviCivita B x (chartField e (Pi.single i 1) x)
        (chartField e (Pi.single j 1) x) (chartField e (Pi.single k 1) x) =
      mvfderiv I (fun y => B y (chartField e (Pi.single i 1) y)
        (chartField e (Pi.single j 1) y)) x (chartField e (Pi.single k 1) x) -
      ∑ l, g.chartChristoffel e x l k i *
        B x (chartField e (Pi.single l 1) x) (chartField e (Pi.single j 1) x) -
      ∑ l, g.chartChristoffel e x l k j *
        B x (chartField e (Pi.single i 1) x) (chartField e (Pi.single l 1) x) :=
  bilinearCovariantDerivative_chart g B he hx i j k

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (l i j k m : Fin (d + 1)) :
    g.chartCurvatureDerivative e x l i j k m =
      mvfderiv I (fun y => g.chartCurvature e y l i j k) x (chartField e (Pi.single m 1) x) +
      ∑ a, g.chartChristoffel e x l m a * g.chartCurvature e x a i j k -
      ∑ a, g.chartChristoffel e x a m i * g.chartCurvature e x l a j k -
      ∑ a, g.chartChristoffel e x a m j * g.chartCurvature e x l i a k -
      ∑ a, g.chartChristoffel e x a m k * g.chartCurvature e x l i j a :=
  chartCurvatureDerivative_eq g he hx l i j k m

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (a b : E) :
    g.covariantField (chartField e a) (chartField e b) x =
      g.covariantField (chartField e b) (chartField e a) x :=
  covariantField_chartField_comm g he hx a b

example (x : M) (u v w z : TM x) :
    g.curvatureDerivative x v w z u + g.curvatureDerivative x w u z v +
      g.curvatureDerivative x u v z w = 0 :=
  curvature_second_bianchi g x u v w z

example (e : OpenPartialHomeomorph M E) (x : M) (l i j k m : Fin (d + 1)) :
    g.chartCurvatureDerivative e x l i j k m + g.chartCurvatureDerivative e x l j m k i +
      g.chartCurvatureDerivative e x l m i k j = 0 :=
  chartCurvatureDerivative_bianchi g e x l i j k m

end ProjectAinos.SmoothGeometry.LorentzMetric

open Bundle FiberBundle VectorField ContinuousLinearMap

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

local notation "E" => MinkowskiModel d

local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

example {ι : Type} (s : Finset ι) {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (f i) x) :
    mvfderiv I (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, mvfderiv I (f i) x :=
  mvfderiv_finset_sum s hf

example {ι : Type} (s : Finset ι) {f k : ι → M → ℝ} {x : M}
    (hf : ∀ n ∈ s, MDifferentiableAt I 𝓘(ℝ) (f n) x)
    (hk : ∀ n ∈ s, MDifferentiableAt I 𝓘(ℝ) (k n) x) (hk0 : ∀ n ∈ s, mvfderiv I (k n) x = 0) :
    mvfderiv I (fun y => ∑ n ∈ s, f n y * k n y) x =
      ∑ n ∈ s, k n x • mvfderiv I (f n) x :=
  mvfderiv_sum_mul_of_mvfderiv_eq_zero s hf hk hk0

example {f k : Fin (d + 1) → Fin (d + 1) → M → ℝ} {x : M}
    (hf : ∀ a c, MDifferentiableAt I 𝓘(ℝ) (f a c) x)
    (hk : ∀ a c, MDifferentiableAt I 𝓘(ℝ) (k a c) x) (hk0 : ∀ a c, mvfderiv I (k a c) x = 0) :
    mvfderiv I (fun y => ∑ a, ∑ c, f a c y * k a c y) x =
      ∑ a, ∑ c, k a c x • mvfderiv I (f a c) x :=
  mvfderiv_sum_sum_mul_of_mvfderiv_eq_zero hf hk hk0

example {F : Type} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) {L L' : TM x →L[ℝ] F}
    (h : ∀ k, L (chartField e (Pi.single k 1) x) = L' (chartField e (Pi.single k 1) x)) :
    L = L' :=
  ext_chartField he hx h

variable (g : LorentzMetric σ d M)

example (e : OpenPartialHomeomorph M E) (x : M) (i j : Fin (d + 1)) :
    ℝ :=
  chartInverse g e x i j

example (e : OpenPartialHomeomorph M E) (x : M) (i j : Fin (d + 1)) :
    g.chartInverse e x i j = g.chartInverse e x j i :=
  chartInverse_symmetric g e x i j

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (i j : Fin (d + 1)) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => g.chartInverse e y i j) x :=
  chartInverse_contMDiffAt g he hx i j

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (i : Fin (d + 1)) :
    g.chartRaisedCovector e x i =
      ∑ l, g.chartInverse e x l i • chartField e (Pi.single l 1) x :=
  chartRaisedCovector_eq_sum g he hx i

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (B : TM x →L[ℝ] TM x →L[ℝ] ℝ) :
    g.contract x B = ∑ a, ∑ c,
      B (chartField e (Pi.single a 1) x) (chartField e (Pi.single c 1) x) *
        g.chartInverse e x a c :=
  contract_chart g he hx B

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (j k : Fin (d + 1)) :
    g.ricci x (chartField e (Pi.single j 1) x) (chartField e (Pi.single k 1) x) =
      ∑ i, g.chartCurvature e x i i j k :=
  ricci_chartField g he hx j k

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) :
    g.scalarCurvature x = ∑ a, ∑ c,
      g.ricci x (chartField e (Pi.single a 1) x) (chartField e (Pi.single c 1) x) *
        g.chartInverse e x a c :=
  scalarCurvature_chart g he hx

example (x : M) (B C : TM x →L[ℝ] TM x →L[ℝ] ℝ) :
    g.contract x (B - C) = g.contract x B - g.contract x C :=
  contract_sub g x B C

example (x : M) (A : TM x →L[ℝ] TM x) :
    g.contract x ((g.form x).comp A) = LinearMap.trace ℝ (TM x) A.toLinearMap :=
  contract_comp_form g x A

example (x : M) (α : TM x →L[ℝ] ℝ) (w : TM x) :
    g.contract x ((compL ℝ (TM x) (TM x) ℝ α).comp (g.curvature x w)) =
      g.ricci x (g.sharp x α) w :=
  contract_curvature_covector g x α w

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (i j : Fin (d + 1)) :
    ∑ m, ∑ k, g.chartCurvature e x i j m k * g.chartInverse e x m k =
      ∑ l, g.ricci x (chartField e (Pi.single l 1) x) (chartField e (Pi.single j 1) x) *
        g.chartInverse e x l i :=
  chartCurvature_contract g he hx i j

section Inertial

variable {g} {e : OpenPartialHomeomorph M (MinkowskiModel d)} {p : M}

example (h : g.IsInertialChartAt e p) (w : E) :
    g.leviCivita (chartField e w) p = 0 :=
  IsInertialChartAt.leviCivita_chartField h w

example (h : g.IsInertialChartAt e p) (i : Fin (d + 1)) :
    g.leviCivita (fun y => g.chartRaisedCovector e y i) p = 0 :=
  IsInertialChartAt.leviCivita_chartRaisedCovector h i

example (h : g.IsInertialChartAt e p) (i j : Fin (d + 1)) :
    mvfderiv I (fun y => g.chartInverse e y i j) p = 0 :=
  IsInertialChartAt.mvfderiv_chartInverse h i j

example (h : g.IsInertialChartAt e p) (B : Tensor.SmoothBilinear («I» := I) (M := M)) (a c : E)
    (u : TM p) :
    Tensor.bilinearCovariantDerivative g.leviCivita B p (chartField e a p) (chartField e c p) u =
      mvfderiv I (fun y => B y (chartField e a y) (chartField e c y)) p u :=
  IsInertialChartAt.bilinearCovariantDerivative_chartField h B a c u

example (h : g.IsInertialChartAt e p) (l i j k m : Fin (d + 1)) :
    g.chartCurvatureDerivative e p l i j k m =
      mvfderiv I (fun y => g.chartCurvature e y l i j k) p (chartField e (Pi.single m 1) p) :=
  IsInertialChartAt.chartCurvatureDerivative_eq h l i j k m

end Inertial

end ProjectAinos.SmoothGeometry.LorentzMetric

open Bundle FiberBundle VectorField ContinuousLinearMap

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

local notation "E" => MinkowskiModel d

local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

local instance (x : M) : T2Space (TM x) := FiberBundle.t2Space E TM x

local instance (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

example (B : Tensor.SmoothBilinear («I» := I) (M := M)) (x : M) :
    TM x →L[ℝ] ℝ :=
  bilinearDivergenceCovector g B x

example (B : Tensor.SmoothBilinear («I» := I) (M := M)) (x : M) (v : TM x) :
    g.bilinearDivergenceCovector B x v =
      g.contract x ((Tensor.bilinearCovariantDerivative g.leviCivita B x).flip v) :=
  bilinearDivergenceCovector_apply g B x v

example :
    Tensor.SmoothBilinear («I» := I) (M := M) :=
  ricciBilinear g

example (x : M) :
    g.ricciBilinear x = g.ricci x :=
  ricciBilinear_apply g x

example (x : M) (v : TM x) :
    g.bilinearDivergenceCovector g.ricciBilinear x v =
      mvfderiv I (fun y => g.scalarCurvature y) x v / 2 :=
  ricci_contracted_bianchi g x v

example (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  einstein g x

example (x : M) (u v : TM x) :
    g.einstein x u v = g.ricci x u v - g.scalarCurvature x / 2 * g.form x u v :=
  einstein_apply g x u v

example (x : M) (u v : TM x) :
    g.einstein x u v = g.einstein x v u :=
  einstein_symmetric g x u v

example :
    ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (g.einstein x)) :=
  einstein_smooth g

example :
    Tensor.SmoothBilinear («I» := I) (M := M) :=
  einsteinBilinear g

example (x : M) :
    g.einsteinBilinear x = g.einstein x :=
  einsteinBilinear_apply g x

example :
    CovariantTwoTensor d M :=
  einsteinTensor g

example (x : M) :
    g.opposite.einstein x = g.einstein x :=
  einstein_opposite g x

example (x : M) :
    g.contract x (g.einstein x) = (1 - ((d : ℝ) + 1) / 2) * g.scalarCurvature x :=
  contract_einstein g x

example (hd : d ≠ 1) {x : M} (h : g.einstein x = 0) :
    g.ricci x = 0 :=
  ricci_eq_zero_of_einstein_eq_zero g hd h

example (x : M) (v w u : TM x) :
    Tensor.bilinearCovariantDerivative g.leviCivita g.einsteinBilinear x v w u =
      Tensor.bilinearCovariantDerivative g.leviCivita g.ricciBilinear x v w u -
        mvfderiv I (fun y => g.scalarCurvature y) x u / 2 * g.form x v w :=
  bilinearCovariantDerivative_einstein g x v w u

example (x : M) :
    g.bilinearDivergenceCovector g.einsteinBilinear x = 0 :=
  einstein_divergence_eq_zero g x

end ProjectAinos.SmoothGeometry.LorentzMetric

open Bundle ContinuousLinearMap Set TopologicalSpace VectorField

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace LorentzMetric

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]

example (e : OpenPartialHomeomorph M (MinkowskiModel d)) (u v : MinkowskiModel d) (x : M) :
    chartField e (u - v) x = chartField e u x - chartField e v x :=
  chartField_sub e u v x

end LorentzMetric

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)

example (x y : U) (u v w : MinkowskiModel d) :
    mvfderiv 𝓘(ℝ, MinkowskiModel d)
        (fun z => g.toLorentzMetric.form z (chartField (physicalChart x) v z)
          (chartField (physicalChart x) w z)) y (chartField (physicalChart x) u y) =
      fderiv ℝ (fun q => g.form q v w) y u :=
  toLorentzMetric_pairing_derivative g x y u v w

example (x y : U) (v w c : MinkowskiModel d)
    (hc : ∀ z, g.form y c z = (fderiv ℝ (fun q => g.form q w z) y v +
      fderiv ℝ (fun q => g.form q z v) y w - fderiv ℝ (fun q => g.form q v w) y z) / 2) :
    g.toLorentzMetric.leviCivita (chartField (physicalChart x) w) y
      (chartField (physicalChart x) v y) = chartField (physicalChart x) c y :=
  toLorentzMetric_leviCivita_eq g x y v w c hc

example (x : U) (Γ : MinkowskiModel d → MinkowskiModel d → MinkowskiModel d)
    (hΓ : ∀ (y : U) (v w : MinkowskiModel d),
      g.toLorentzMetric.leviCivita (chartField (physicalChart x) w) y
        (chartField (physicalChart x) v y) = chartField (physicalChart x) (Γ v w) y)
    (y : U) (u v w : MinkowskiModel d) :
    g.toLorentzMetric.curvature y (chartField (physicalChart x) u y)
        (chartField (physicalChart x) v y) (chartField (physicalChart x) w y) =
      chartField (physicalChart x) (Γ u (Γ v w) - Γ v (Γ u w)) y :=
  toLorentzMetric_curvature_of_connection g x Γ hΓ y u v w

example (x : U) (Γ : MinkowskiModel d → MinkowskiModel d → MinkowskiModel d)
    (hΓ : ∀ (y : U) (v w : MinkowskiModel d),
      g.toLorentzMetric.leviCivita (chartField (physicalChart x) w) y
        (chartField (physicalChart x) v y) = chartField (physicalChart x) (Γ v w) y)
    (ℛ : MinkowskiModel d → MinkowskiModel d → MinkowskiModel d → MinkowskiModel d)
    (hR : ∀ (y : U) (u v w : MinkowskiModel d),
      g.toLorentzMetric.curvature y (chartField (physicalChart x) u y)
        (chartField (physicalChart x) v y) (chartField (physicalChart x) w y) =
      chartField (physicalChart x) (ℛ u v w) y)
    (y : U) (a u v w : MinkowskiModel d) :
    g.toLorentzMetric.curvatureDerivative y (chartField (physicalChart x) u y)
        (chartField (physicalChart x) v y) (chartField (physicalChart x) w y)
        (chartField (physicalChart x) a y) =
      chartField (physicalChart x)
        (Γ a (ℛ u v w) - ℛ (Γ a u) v w - ℛ u (Γ a v) w - ℛ u v (Γ a w)) y :=
  toLorentzMetric_curvatureDerivative_of_connection g x Γ hΓ ℛ hR y a u v w

end CoordinateMetric

end ProjectAinos.SmoothGeometry

open Bundle ContinuousLinearMap TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.ExponentialConformalExample

open LorentzMetric CoordinateMetric

local notation "E" => MinkowskiModel 3

local notation "η" => minkowskiForm LorentzConvention.timeNegative 3

example (q : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  form q

example (q v w : E) :
    form q v w = Real.exp (2 * q 3) * η v w :=
  form_apply q v w

example :
    ContDiff ℝ ∞ form :=
  contDiff_form

example :
    CoordinateMetric .timeNegative 3 ⊤ :=
  metric

example (v : E) :
    η (Pi.single 3 1) v = v 3 :=
  minkowskiForm_single_three v

example (v : E) :
    η v (Pi.single 3 1) = v 3 :=
  minkowskiForm_single_three_right v

example (v w : E) :
    E :=
  connection v w

example (v : E) :
    connection (Pi.single 3 1) v = v :=
  connection_single_three v

example (q v w : E) :
    HasFDerivAt (fun p => form p v w)
      ((2 * Real.exp (2 * q 3) * η v w) • (proj 3 : E →L[ℝ] ℝ)) q :=
  hasFDerivAt_form_apply q v w

example (x y : (⊤ : Opens E)) (v w : E) :
    metric.toLorentzMetric.leviCivita (chartField (physicalChart x) w) y
      (chartField (physicalChart x) v y) = chartField (physicalChart x) (connection v w) y :=
  metric_leviCivita x y v w

example (u v w : E) :
    E :=
  curvatureVector u v w

example (u v w : E) :
    connection u (connection v w) - connection v (connection u w) = curvatureVector u v w :=
  connection_connection u v w

example (x y : (⊤ : Opens E)) (u v w : E) :
    metric.toLorentzMetric.curvature y (chartField (physicalChart x) u y)
      (chartField (physicalChart x) v y) (chartField (physicalChart x) w y) =
      chartField (physicalChart x) (curvatureVector u v w) y :=
  metric_curvature x y u v w

example (x y : (⊤ : Opens E)) (v w : E) :
    metric.toLorentzMetric.form y (chartField (physicalChart x) v y)
      (chartField (physicalChart x) w y) = Real.exp (2 * (y : E) 3) * η v w :=
  metric_form_chartField x y v w

example (x y : (⊤ : Opens E)) (v : E) :
    chartCovector (physicalChart x) y 3 (chartField (physicalChart x) v y) = v 3 :=
  chartCovector_three x y v

example (x y : (⊤ : Opens E)) (v w : E) :
    metric.toLorentzMetric.ricci y (chartField (physicalChart x) v y)
      (chartField (physicalChart x) w y) = 2 * (v 3 * w 3 - η v w) :=
  metric_ricci_chartField x y v w

example (x y : (⊤ : Opens E)) :
    metric.toLorentzMetric.ricci y =
      (2 : ℝ) • (chartCovector (physicalChart x) y 3).smulRight
          (chartCovector (physicalChart x) y 3) -
        (2 * Real.exp (-(2 * (y : E) 3))) • metric.toLorentzMetric.form y :=
  metric_ricci x y

example (x y : (⊤ : Opens E)) :
    metric.toLorentzMetric.sharp y (chartCovector (physicalChart x) y 3) =
      Real.exp (-(2 * (y : E) 3)) • chartField (physicalChart x) (Pi.single 3 1) y :=
  metric_sharp_dz x y

example (y : (⊤ : Opens E)) :
    metric.toLorentzMetric.scalarCurvature y = -6 * Real.exp (-(2 * (y : E) 3)) :=
  metric_scalarCurvature y

example (x y : (⊤ : Opens E)) (v w : E) :
    metric.toLorentzMetric.einstein y (chartField (physicalChart x) v y)
      (chartField (physicalChart x) w y) = 2 * (v 3 * w 3) + η v w :=
  metric_einstein_chartField x y v w

example (y : (⊤ : Opens E)) :
    metric.toLorentzMetric.einstein y ≠ 0 :=
  metric_einstein_ne_zero y

example (x y : (⊤ : Opens E)) (u v w : E) :
    metric.toLorentzMetric.curvatureDerivative y (chartField (physicalChart x) u y)
        (chartField (physicalChart x) v y) (chartField (physicalChart x) w y)
        (chartField (physicalChart x) (Pi.single 3 1) y) =
      chartField (physicalChart x) ((-2 : ℝ) • curvatureVector u v w) y :=
  metric_curvatureDerivative_dz x y u v w

example (y : (⊤ : Opens E)) :
    metric.toLorentzMetric.curvatureDerivative y ≠ 0 :=
  metric_curvatureDerivative_ne_zero y

example (x y : (⊤ : Opens E)) :
    mvfderiv 𝓘(ℝ, E) (fun z => metric.toLorentzMetric.scalarCurvature z) y
        (chartField (physicalChart x) (Pi.single 3 1) y) =
      12 * Real.exp (-(2 * (y : E) 3)) :=
  metric_scalarCurvature_derivative x y

example (x y : (⊤ : Opens E)) :
    metric.toLorentzMetric.bilinearDivergenceCovector metric.toLorentzMetric.ricciBilinear y
        (chartField (physicalChart x) (Pi.single 3 1) y) =
      6 * Real.exp (-(2 * (y : E) 3)) :=
  metric_ricci_divergence x y

end ProjectAinos.SmoothGeometry.ExponentialConformalExample
