/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.CylindricalCavity

/-! Public consumers of the characteristic vibrations of the field (Landau–Lifshitz §52): the
explicit modes of a perfectly conducting rectangular cavity with Maxwell's equations and the wall
conditions; the coefficients of fields periodic in a box, the mode equations, transversality,
Parseval and the energy as a sum over the modes.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section CavityModes

open MeasureTheory Set Filter

open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics.CavityModes

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

open ProjectAinos.Electrodynamics

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (MeasureTheory.volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddRightInvariant (MeasureTheory.volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddRightInvariant AddCircle.haarAddCircle)

example (k a b t : ℝ) :
    ℝ :=
  trigFactor k a b t

example (k a b t : ℝ) :
    HasDerivAt (trigFactor k a b) (trigFactor k (k * b) (-(k * a)) t) t :=
  hasDerivAt_trigFactor k a b t

example (k a b : Fin 4 → ℝ) (y : Spacetime) :
    ℝ :=
  trigProduct k a b y

example (k a b : Fin 4 → ℝ) (μ : Fin 4) :
    partialAt (trigProduct k a b) μ =
      trigProduct k (Function.update a μ (k μ * b μ))
        (Function.update b μ (-(k μ * a μ))) :=
  partialAt_trigProduct k a b μ

example (k a b : Fin 4 → ℝ) (μ : Fin 4) (c : ℝ) (y : Spacetime) :
    trigProduct k (Function.update a μ (c * a μ)) (Function.update b μ (c * b μ)) y =
      c * trigProduct k a b y :=
  trigProduct_update_smul k a b μ c y

example (k a b : Fin 4 → ℝ) (μ : Fin 4) :
    partialAt (partialAt (trigProduct k a b) μ) μ = fun y => -k μ ^ 2 * trigProduct k a b y :=
  partialAt_partialAt_trigProduct k a b μ

example (k a b : Fin 4 → ℝ) (y : Spacetime) :
    box (trigProduct k a b) y = (k 0 ^ 2 - ∑ i : Fin 3, k i.succ ^ 2) * trigProduct k a b y :=
  box_trigProduct k a b y

example {n : ℕ∞ω} (k a b : Fin 4 → ℝ) :
    ContDiff ℝ n (trigProduct k a b) :=
  contDiff_trigProduct k a b

example {k a b : Fin 4 → ℝ} {y : Spacetime} {ν : Fin 4}
    (h : trigFactor (k ν) (a ν) (b ν) (y ν) = 0) :
    trigProduct k a b y = 0 :=
  trigProduct_eq_zero h

example {k a b : Fin 4 → ℝ} {y : Spacetime} {μ ν : Fin 4} (hμν : μ ≠ ν)
    (h : trigFactor (k ν) (a ν) (b ν) (y ν) = 0) :
    partialAt (trigProduct k a b) μ y = 0 :=
  partialAt_trigProduct_eq_zero hμν h

example (φ : Spacetime → ℝ) (a : Spacetime → Fin 3 → ℝ) :
    potentialComponent (potentialOf φ a) 0 = fun y => -φ y :=
  potentialComponent_potentialOf_zero φ a

example (φ : Spacetime → ℝ) (a : Spacetime → Fin 3 → ℝ) (j : Fin 3) :
    potentialComponent (potentialOf φ a) j.succ = fun y => a y j :=
  potentialComponent_potentialOf_succ φ a j

example {n : ℕ∞ω} {φ : Spacetime → ℝ} {a : Spacetime → Fin 3 → ℝ} (hφ : ContDiff ℝ n φ)
    (ha : ∀ i, ContDiff ℝ n fun y => a y i) :
    ContDiff ℝ n (potentialOf φ a) :=
  contDiff_potentialOf hφ ha

example {α : Type*} (x : α) (p : Fin 3 → α) :
    (Fin.cons x p : Fin 4 → α) 2 = p 1 :=
  fin4_cons_two x p

example {α : Type*} (x : α) (p : Fin 3 → α) :
    (Fin.cons x p : Fin 4 → α) 3 = p 2 :=
  fin4_cons_three x p

example (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (i : Fin 3) :
    ℝ :=
  wallWavenumber L n i

example (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (freq : ℝ) :
    Fin 4 → ℝ :=
  modeWavenumbers L n freq

example (c : ℝ) (i : Fin 3) :
    Fin 4 → ℝ :=
  modeCosCoeff c i

example (i : Fin 3) :
    Fin 4 → ℝ :=
  modeSinCoeff i

example (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (i : Fin 3) :
    Spacetime → ℝ :=
  modeComponent L n c freq i

example (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) :
    Potential :=
  conductingMode L n c freq

example (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) :
    potentialComponent (conductingMode L n c freq) 0 = fun _ => 0 :=
  potentialComponent_conductingMode_zero L n c freq

example (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (j : Fin 3) :
    potentialComponent (conductingMode L n c freq) j.succ = modeComponent L n c freq j :=
  potentialComponent_conductingMode_succ L n c freq j

example {m : ℕ∞ω} (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) :
    ContDiff ℝ m (conductingMode L n c freq) :=
  contDiff_conductingMode L n c freq

example (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (i : Fin 3) (y : Spacetime) :
    box (modeComponent L n c freq i) y =
      (freq ^ 2 - ∑ j : Fin 3, wallWavenumber L n j ^ 2) * modeComponent L n c freq i y :=
  box_modeComponent L n c freq i y

example (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (y : Spacetime) :
    lorenzDivergence (conductingMode L n c freq) y =
      -(∑ j : Fin 3, wallWavenumber L n j * c j) * (Real.cos (freq * y 0) *
        Real.sin (wallWavenumber L n 0 * y 1) * Real.sin (wallWavenumber L n 1 * y 2) *
        Real.sin (wallWavenumber L n 2 * y 3)) :=
  lorenzDivergence_conductingMode L n c freq y

example {L : Fin 3 → ℝ} {i j : Fin 3} (hL : L i ≠ 0) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ)
    (hij : j ≠ i) {μ : Fin 4} (hμ : μ ≠ i.succ) {y : Spacetime}
    (hy : y i.succ = 0 ∨ y i.succ = L i) :
    partialAt (modeComponent L n c freq j) μ y = 0 :=
  partialAt_modeComponent_wall hL n c freq hij hμ hy

example (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (j : Fin 3) (y : Spacetime) :
    electricField (fieldTensor (conductingMode L n c freq)) j y =
      -partialAt (modeComponent L n c freq j) 0 y :=
  electricField_conductingMode L n c freq j y

example (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (y : Spacetime) :
    magneticField (fieldTensor (conductingMode L n c freq)) 0 y =
        partialAt (modeComponent L n c freq 2) 2 y -
          partialAt (modeComponent L n c freq 1) 3 y ∧
      magneticField (fieldTensor (conductingMode L n c freq)) 1 y =
        partialAt (modeComponent L n c freq 0) 3 y -
          partialAt (modeComponent L n c freq 2) 1 y ∧
      magneticField (fieldTensor (conductingMode L n c freq)) 2 y =
        partialAt (modeComponent L n c freq 1) 1 y -
          partialAt (modeComponent L n c freq 0) 2 y :=
  magneticField_conductingMode L n c freq y

example {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (i : Fin 3)
    {y : Spacetime} (hy : y i.succ = 0 ∨ y i.succ = L i) :
    (∀ j, j ≠ i → electricField (fieldTensor (conductingMode L n c freq)) j y = 0) ∧
      magneticField (fieldTensor (conductingMode L n c freq)) i y = 0 :=
  conductingMode_boundary hL n c freq i hy

example {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (i : Fin 3)
    {y : Spacetime} (hy : y i.succ = 0 ∨ y i.succ = L i) :
    crossProduct (Pi.single i 1 : Fin 3 → ℝ)
        (fun j => electricField (fieldTensor (conductingMode L n c freq)) j y) = 0 ∧
      dotProduct (Pi.single i 1 : Fin 3 → ℝ)
        (fun j => magneticField (fieldTensor (conductingMode L n c freq)) j y) = 0 :=
  conductingMode_boundary_cross hL n c freq i hy

example (y : Spacetime) :
    box (fun _ => 0) y = 0 :=
  box_zero y

example (A : Potential) (y : Spacetime) :
    Prop :=
  VacuumMaxwellAt A y

example {A : Potential} (hA : ContDiff ℝ 2 A) (hL : ∀ y, lorenzDivergence A y = 0) :
    (∀ y, VacuumMaxwellAt A y) ↔ ∀ y ν, box (potentialComponent A ν) y = 0 :=
  vacuumMaxwellAt_iff_box hA hL

example {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) (n : Fin 3 → ℕ) {c : Fin 3 → ℝ} {freq : ℝ}
    (hc : ∑ i : Fin 3, wallWavenumber L n i * c i = 0)
    (hfreq : freq ^ 2 = ∑ i : Fin 3, wallWavenumber L n i ^ 2) :
    (∀ y, lorenzDivergence (conductingMode L n c freq) y = 0) ∧
    (∀ y, VacuumMaxwellAt (conductingMode L n c freq) y) ∧
    (∀ (i : Fin 3) (y : Spacetime), (y i.succ = 0 ∨ y i.succ = L i) →
      (∀ j, j ≠ i → electricField (fieldTensor (conductingMode L n c freq)) j y = 0) ∧
        magneticField (fieldTensor (conductingMode L n c freq)) i y = 0) :=
  conductingMode_maxwell hL n hc hfreq

example :
    ∑ i : Fin 3, wallWavenumber 1 ![1, 1, 0] i * ![0, 0, 1] i = 0 ∧
      (Real.pi * Real.sqrt 2) ^ 2 = ∑ i : Fin 3, wallWavenumber 1 ![1, 1, 0] i ^ 2 ∧
      modeComponent 1 ![1, 1, 0] ![0, 0, 1] (Real.pi * Real.sqrt 2) 2 ![0, 1 / 2, 1 / 2, 0] =
        1 :=
  conductingMode_unitCube

example (L : Fin 3 → ℝ) :
    Set (Fin 3 → ℝ) :=
  boxSet L

example (L : Fin 3 → ℝ) :
    MeasurableSet (boxSet L) :=
  measurableSet_boxSet L

example (L : Fin 3 → ℝ) :
    ℝ :=
  boxVolume L

example (L : Fin 3 → ℝ) (x : Fin 3 → ℝ) :
    UnitAddTorus (Fin 3) :=
  toTorus L x

example (L : Fin 3 → ℝ) (z : UnitAddTorus (Fin 3)) :
    Fin 3 → ℝ :=
  fromTorus L z

example {E : Type*} (L : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → E) :
    Prop :=
  BoxPeriodic L f

example (L x y : Fin 3 → ℝ) :
    toTorus L (x + y) = toTorus L x + toTorus L y :=
  toTorus_add L x y

example {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) (z : UnitAddTorus (Fin 3)) :
    toTorus L (fromTorus L z) = z :=
  toTorus_fromTorus hL z

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {x : Fin 3 → ℝ} (hx : x ∈ boxSet L) :
    fromTorus L (toTorus L x) = x :=
  fromTorus_toTorus hL hx

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) (z : UnitAddTorus (Fin 3)) :
    fromTorus L z ∈ Set.pi univ fun i => Icc 0 (L i) :=
  fromTorus_mem_Icc hL z

example (L : Fin 3 → ℝ) :
    Measurable (fromTorus L) :=
  measurable_fromTorus L

example {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) {x y : Fin 3 → ℝ} (h : toTorus L x = toTorus L y) :
    ∃ m : Fin 3 → ℤ, x = fun i => y i + m i * L i :=
  exists_period_of_toTorus_eq hL h

example {E : Type*} {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) {f : (Fin 3 → ℝ) → E}
    (hf : BoxPeriodic L f) {x y : Fin 3 → ℝ} (h : toTorus L x = toTorus L y) :
    f x = f y :=
  BoxPeriodic.eq_of_toTorus_eq hL hf h

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) :
    0 < boxVolume L :=
  boxVolume_pos hL

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i)
    (G : UnitAddTorus (Fin 3) → E) :
    ∫ x in boxSet L, G (toTorus L x) = boxVolume L • ∫ z, G z :=
  integral_boxSet_toTorus hL G

example (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    ℂ :=
  boxWave L k x

example (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    boxWave L k x =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * ((x j / L j : ℝ) : ℂ)) :=
  boxWave_apply L k x

example (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    Continuous (boxWave L k) :=
  continuous_boxWave L k

example (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    ‖boxWave L k x‖ = 1 :=
  norm_boxWave L k x

example (n : Fin 3 → ℤ) (z w : UnitAddTorus (Fin 3)) :
    UnitAddTorus.mFourier n (z - w) =
      UnitAddTorus.mFourier n z * UnitAddTorus.mFourier (-n) w :=
  mFourier_sub n z w

example (L : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → ℝ) (k : Fin 3 → ℤ) :
    ℂ :=
  boxCoeff L f k

example (L : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → ℝ) (z : UnitAddTorus (Fin 3)) :
    ℂ :=
  torusLift L f z

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) (f : (Fin 3 → ℝ) → ℝ) (k : Fin 3 → ℤ) :
    boxCoeff L f k = UnitAddTorus.mFourierCoeff (torusLift L f) k :=
  boxCoeff_eq_mFourierCoeff hL f k

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {f : (Fin 3 → ℝ) → ℝ} (hf : BoxPeriodic L f)
    (v : Fin 3 → ℝ) (z : UnitAddTorus (Fin 3)) :
    torusLift L (fun x => f (x + v)) z = torusLift L f (z + toTorus L v) :=
  torusLift_add hL hf v z

example (F : UnitAddTorus (Fin 3) → ℂ) (w : UnitAddTorus (Fin 3)) (k : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun z => F (z + w)) k =
      UnitAddTorus.mFourier k w * UnitAddTorus.mFourierCoeff F k :=
  mFourierCoeff_comp_add F w k

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {f : (Fin 3 → ℝ) → ℝ} (hf : BoxPeriodic L f)
    (v : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    boxCoeff L (fun x => f (x + v)) k = boxWave L k v * boxCoeff L f k :=
  boxCoeff_comp_add hL hf v k

example (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) (j : Fin 3) :
    ℝ :=
  boxWavevector L k j

example (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    ℝ :=
  boxFreq L k

example (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    boxFreq L k ^ 2 = ∑ j, boxWavevector L k j ^ 2 :=
  boxFreq_sq L k

example (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) (j : Fin 3) (s : ℝ) :
    boxWave L k (s • Pi.single j 1) =
      Complex.exp (Complex.I * (boxWavevector L k j : ℂ) * (s : ℂ)) :=
  boxWave_smul_single L k j s

example (L : Fin 3 → ℝ) :
    boxSet L ⊆ Set.pi univ fun i => Icc 0 (L i) :=
  boxSet_subset_Icc L

example (L : Fin 3 → ℝ) :
    (MeasureTheory.volume : Measure (Fin 3 → ℝ)) (boxSet L) ≠ ⊤ :=
  volume_boxSet_ne_top L

example {E : Type*} [NormedAddCommGroup E] {g : (Fin 3 → ℝ) → E} (hg : Continuous g)
    (L : Fin 3 → ℝ) :
    IntegrableOn g (boxSet L) :=
  integrableOn_boxSet hg L

example (L : Fin 3 → ℝ) {F F' : ℝ → (Fin 3 → ℝ) → ℂ} (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F')) (hd : ∀ s x, HasDerivAt (fun s => F s x) (F' s x) s)
    (t : ℝ) :
    HasDerivAt (fun s => ∫ x in boxSet L, F s x) (∫ x in boxSet L, F' t x) t :=
  hasDerivAt_integral_boxSet L hF hF' hd t

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hper : BoxPeriodic L f) (j : Fin 3) (k : Fin 3 → ℤ) :
    boxCoeff L (fun x => fderiv ℝ f x (Pi.single j 1)) k =
      Complex.I * boxWavevector L k j * boxCoeff L f k :=
  boxCoeff_partial hL hf hper j k

example (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) :
    IntegrableOn (fun x => boxWave L k x * (f x : ℂ)) (boxSet L) :=
  integrableOn_boxWave_mul L k hf

example (L : Fin 3 → ℝ) {f g : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (k : Fin 3 → ℤ) :
    boxCoeff L (fun x => f x + g x) k = boxCoeff L f k + boxCoeff L g k :=
  boxCoeff_add L hf hg k

example (L : Fin 3 → ℝ) {f g : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (k : Fin 3 → ℤ) :
    boxCoeff L (fun x => f x - g x) k = boxCoeff L f k - boxCoeff L g k :=
  boxCoeff_sub L hf hg k

example {ι : Type*} (L : Fin 3 → ℝ) (s : Finset ι) {f : ι → (Fin 3 → ℝ) → ℝ}
    (hf : ∀ i, Continuous (f i)) (k : Fin 3 → ℤ) :
    boxCoeff L (fun x => ∑ i ∈ s, f i x) k = ∑ i ∈ s, boxCoeff L (f i) k :=
  boxCoeff_sum L s hf k

example (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    boxCoeff L (fun _ => 0) k = 0 :=
  boxCoeff_zero L k

example (u : Spacetime → ℝ) (t : ℝ) (x : Fin 3 → ℝ) :
    ℝ :=
  slice u t x

example {n : ℕ∞ω} :
    ContDiff ℝ n fun p : ℝ × (Fin 3 → ℝ) => (Fin.cons p.1 p.2 : Spacetime) :=
  contDiff_cons

example {n : ℕ∞ω} {u : Spacetime → ℝ} (hu : ContDiff ℝ n u) (t : ℝ) :
    ContDiff ℝ n (slice u t) :=
  contDiff_slice hu t

example {u : Spacetime → ℝ} (hu : Continuous u) :
    Continuous fun p : ℝ × (Fin 3 → ℝ) => u (Fin.cons p.1 p.2) :=
  continuous_slice_uncurry hu

example {n : ℕ∞ω} {u : Spacetime → ℝ} (hu : ContDiff ℝ (n + 1) u) (μ : Fin 4) :
    ContDiff ℝ n (partialAt u μ) :=
  contDiff_partialAt hu μ

example {u : Spacetime → ℝ} (hu : ContDiff ℝ 1 u) (t : ℝ) (x : Fin 3 → ℝ) (j : Fin 3) :
    fderiv ℝ (slice u t) x (Pi.single j 1) = partialAt u j.succ (Fin.cons t x) :=
  fderiv_slice hu t x j

example {u : Spacetime → ℝ} (hu : ContDiff ℝ 1 u) (t : ℝ) (x : Fin 3 → ℝ) :
    HasDerivAt (fun s => u (Fin.cons s x)) (partialAt u 0 (Fin.cons t x)) t :=
  hasDerivAt_cons hu t x

example {L : Fin 3 → ℝ} {u : Spacetime → ℝ} (hper : ∀ t, BoxPeriodic L (slice u t)) (μ : Fin 4)
    (t : ℝ) :
    BoxPeriodic L (slice (partialAt u μ) t) :=
  BoxPeriodic.slice_partialAt hper μ t

example (L : Fin 3 → ℝ) {u : Spacetime → ℝ} (hu : ContDiff ℝ 1 u) (k : Fin 3 → ℤ) (t : ℝ) :
    HasDerivAt (fun s => boxCoeff L (slice u s) k) (boxCoeff L (slice (partialAt u 0) t) k) t :=
  hasDerivAt_boxCoeff_slice L hu k t

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {u : Spacetime → ℝ} (hu : ContDiff ℝ 2 u)
    (hper : ∀ t, BoxPeriodic L (slice u t)) (j : Fin 3) (t : ℝ) (k : Fin 3 → ℤ) :
    boxCoeff L (slice (partialAt (partialAt u j.succ) j.succ) t) k =
      -(boxWavevector L k j : ℂ) ^ 2 * boxCoeff L (slice u t) k :=
  boxCoeff_partial_partial hL hu hper j t k

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {u : Spacetime → ℝ} (hu : ContDiff ℝ 2 u)
    (hper : ∀ t, BoxPeriodic L (slice u t)) (hbox : ∀ y, box u y = 0) (k : Fin 3 → ℤ) (t : ℝ) :
    HasDerivAt (fun s => boxCoeff L (slice u s) k) (boxCoeff L (slice (partialAt u 0) t) k) t ∧
      HasDerivAt (fun s => boxCoeff L (slice (partialAt u 0) s) k)
        (-(boxFreq L k : ℂ) ^ 2 * boxCoeff L (slice u t) k) t :=
  hasDerivAt_boxCoeff_of_box hL hu hper hbox k t

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {a : Fin 3 → Spacetime → ℝ}
    (ha : ∀ j, ContDiff ℝ 1 (a j)) (hper : ∀ j t, BoxPeriodic L (slice (a j) t))
    (hdiv : ∀ y, divergence3 a y = 0) (t : ℝ) (k : Fin 3 → ℤ) :
    ∑ j : Fin 3, (boxWavevector L k j : ℂ) * boxCoeff L (slice (a j) t) k = 0 :=
  transverse_boxCoeff hL ha hper hdiv t k

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) :
    HasSum (fun k => ‖boxCoeff L f k‖ ^ 2) ((boxVolume L)⁻¹ * ∫ x in boxSet L, f x ^ 2) :=
  hasSum_sq_boxCoeff hL hf

example (K : Fin 3 → ℝ) (a : Fin 3 → ℂ) :
    ‖(K 1 : ℂ) * a 2 - K 2 * a 1‖ ^ 2 + ‖(K 2 : ℂ) * a 0 - K 0 * a 2‖ ^ 2 +
        ‖(K 0 : ℂ) * a 1 - K 1 * a 0‖ ^ 2 =
      (∑ j, K j ^ 2) * ∑ j, ‖a j‖ ^ 2 - ‖∑ j, (K j : ℂ) * a j‖ ^ 2 :=
  norm_cross_sq K a

example {A : Potential} (hA : ContDiff ℝ 2 A) (ν : Fin 4) :
    ContDiff ℝ 2 (potentialComponent A ν) :=
  contDiff_potentialComponent hA ν

example {A : Potential} (hA : ContDiff ℝ 1 A) (hφ : ∀ y, potentialComponent A 0 y = 0) (i : Fin 3)
    (y : Spacetime) :
    electricField (fieldTensor A) i y = -partialAt (potentialComponent A i.succ) 0 y :=
  electricField_of_coulomb hA hφ i y

example {A : Potential} (hA : ContDiff ℝ 1 A) (y : Spacetime) :
    magneticField (fieldTensor A) 0 y =
        partialAt (potentialComponent A 3) 2 y - partialAt (potentialComponent A 2) 3 y ∧
      magneticField (fieldTensor A) 1 y =
        partialAt (potentialComponent A 1) 3 y - partialAt (potentialComponent A 3) 1 y ∧
      magneticField (fieldTensor A) 2 y =
        partialAt (potentialComponent A 2) 1 y - partialAt (potentialComponent A 1) 2 y :=
  magneticField_fieldTensor_apply hA y

example {A : Potential} (hφ : ∀ y, potentialComponent A 0 y = 0)
    (hdiv : ∀ y, lorenzDivergence A y = 0) (y : Spacetime) :
    divergence3 (fun j => potentialComponent A j.succ) y = 0 :=
  divergence3_of_coulomb hφ hdiv y

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {A : Potential} (hA : ContDiff ℝ 2 A)
    (hφ : ∀ y, potentialComponent A 0 y = 0) (hdiv : ∀ y, lorenzDivergence A y = 0)
    (hper : ∀ (j : Fin 3) t, BoxPeriodic L (slice (potentialComponent A j.succ) t)) (t : ℝ) :
    HasSum (fun k => boxVolume L *
        ((∑ j : Fin 3,
            ‖deriv (fun s => boxCoeff L (slice (potentialComponent A j.succ) s) k) t‖ ^ 2 +
          boxFreq L k ^ 2 *
            ∑ j : Fin 3, ‖boxCoeff L (slice (potentialComponent A j.succ) t) k‖ ^ 2) / 2))
      (∫ x in boxSet L, energyDensity (fieldTensor A) (Fin.cons t x)) :=
  hasSum_fieldEnergy hL hA hφ hdiv hper t

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {A : Potential} (hA : ContDiff ℝ 2 A)
    (hφ : ∀ y, potentialComponent A 0 y = 0) (hdiv : ∀ y, lorenzDivergence A y = 0)
    (hper : ∀ (j : Fin 3) t, BoxPeriodic L (slice (potentialComponent A j.succ) t)) (t : ℝ) :
    ∫ x in boxSet L, energyDensity (fieldTensor A) (Fin.cons t x) =
      ∑' k, boxVolume L *
        ((∑ j : Fin 3,
            ‖deriv (fun s => boxCoeff L (slice (potentialComponent A j.succ) s) k) t‖ ^ 2 +
          boxFreq L k ^ 2 *
            ∑ j : Fin 3, ‖boxCoeff L (slice (potentialComponent A j.succ) t) k‖ ^ 2) / 2) :=
  fieldEnergy_eq_tsum hL hA hφ hdiv hper t

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {A : Potential} (hA : ContDiff ℝ 2 A)
    (hφ : ∀ y, potentialComponent A 0 y = 0) (hdiv : ∀ y, lorenzDivergence A y = 0)
    (hvac : ∀ y, VacuumMaxwellAt A y)
    (hper : ∀ (j : Fin 3) t, BoxPeriodic L (slice (potentialComponent A j.succ) t))
    (k : Fin 3 → ℤ) (t : ℝ) :
    (∀ j : Fin 3,
      HasDerivAt (fun s => boxCoeff L (slice (potentialComponent A j.succ) s) k)
          (boxCoeff L (slice (partialAt (potentialComponent A j.succ) 0) t) k) t ∧
        HasDerivAt (fun s => boxCoeff L (slice (partialAt (potentialComponent A j.succ) 0) s) k)
          (-(boxFreq L k : ℂ) ^ 2 * boxCoeff L (slice (potentialComponent A j.succ) t) k) t) ∧
      ∑ j : Fin 3, (boxWavevector L k j : ℂ) *
        boxCoeff L (slice (potentialComponent A j.succ) t) k = 0 :=
  hasDerivAt_boxCoeff_of_maxwell hL hA hφ hdiv hvac hper k t

example {L : ℝ} (hL : L ≠ 0) (n : ℕ) (a b t : ℝ) (m : ℤ) :
    trigFactor (Real.pi * n / L) a b (t + m * (2 * L)) = trigFactor (Real.pi * n / L) a b t :=
  trigFactor_add_two_mul hL n a b t m

example {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (j : Fin 3)
    (t : ℝ) :
    BoxPeriodic (fun i => 2 * L i) (slice (modeComponent L n c freq j) t) :=
  boxPeriodic_modeComponent hL n c freq j t

example {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) (n : Fin 3 → ℕ) {c : Fin 3 → ℝ} (freq : ℝ)
    (hc : ∑ i : Fin 3, wallWavenumber L n i * c i = 0) (t : ℝ) :
    HasSum (fun k => boxVolume (fun i => 2 * L i) *
        ((∑ j : Fin 3, ‖deriv (fun s => boxCoeff (fun i => 2 * L i)
              (slice (modeComponent L n c freq j) s) k) t‖ ^ 2 +
          boxFreq (fun i => 2 * L i) k ^ 2 * ∑ j : Fin 3,
            ‖boxCoeff (fun i => 2 * L i) (slice (modeComponent L n c freq j) t) k‖ ^ 2) / 2))
      (∫ x in boxSet (fun i => 2 * L i),
        energyDensity (fieldTensor (conductingMode L n c freq)) (Fin.cons t x)) :=
  hasSum_fieldEnergy_conductingMode hL n freq hc t

example (k : ℝ) (x : Spacetime) : VacuumMaxwellAt (cylinderMode k) x :=
  cylinderMode_maxwell k x

example (k : ℝ) (x : Spacetime) :
    electricField (fieldTensor (cylinderMode k)) 0 x = 0 ∧
    electricField (fieldTensor (cylinderMode k)) 1 x = 0 ∧
    magneticField (fieldTensor (cylinderMode k)) 2 x = 0 := cylinderMode_endPlates k x

example {k R : ℝ} (hk : Complex.besselJ 0 ((k * R : ℝ) : ℂ) = 0) (x : Spacetime)
    (hx : x 1 ^ 2 + x 2 ^ 2 = R ^ 2) :
    (∀ i, electricField (fieldTensor (cylinderMode k)) i x = 0) ∧
      x 1 * magneticField (fieldTensor (cylinderMode k)) 0 x +
      x 2 * magneticField (fieldTensor (cylinderMode k)) 1 x = 0 := cylinderMode_side hk x hx

example {R : ℝ} (hR : 0 < R) (a : ℝ) :
    ∃ k : ℝ, a < k ∧ 0 < k ∧ Complex.besselJ 0 ((k * R : ℝ) : ℂ) = 0 ∧
      electricField (fieldTensor (cylinderMode k)) 2 ![Real.pi / (2 * k), 0, 0, 0] = k :=
  exists_cylinderMode hR a

end ProjectAinos.Electrodynamics.CavityModes

end CavityModes
