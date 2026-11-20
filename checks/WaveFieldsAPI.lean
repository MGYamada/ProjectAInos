/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.WaveEquation
import ProjectAinos.Electrodynamics.PlaneWave
import ProjectAinos.Electrodynamics.Monochromatic

/-! Public consumers of electromagnetic waves (Landau–Lifshitz §§46–48, 50): the wave operator
and the Lorenz divergence, Maxwell's equations as wave equations in Lorenz gauge, the change of
gauge, uniqueness by the energy identity and the propagation of the constraints; plane waves with
their transversality and stress; and monochromatic waves with their gauge classes, the two
polarizations, the polarization ellipse and the Doppler effect.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section WaveEquation

open MeasureTheory Set Filter

open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (f : Spacetime → ℝ) (x : Spacetime) :
    ℝ :=
  box f x

example (A : Potential) (x : Spacetime) :
    ℝ :=
  lorenzDivergence A x

example {f g : Spacetime → ℝ} {x : Spacetime} (h : f =ᶠ[𝓝 x] g) (μ : Fin 4) :
    partialAt f μ x = partialAt g μ x :=
  partialAt_congr_of_eventuallyEq h μ

example (c : ℝ) (μ : Fin 4) (x : Spacetime) :
    partialAt (fun _ => c) μ x = 0 :=
  partialAt_const c μ x

example {m n : ℕ∞ω} {f : Spacetime → ℝ} {x : Spacetime} (hf : ContDiffAt ℝ n f x)
    (hmn : m + 1 ≤ n) (μ : Fin 4) :
    ContDiffAt ℝ m (partialAt f μ) x :=
  contDiffAt_partialAt hf hmn μ

example {f : Spacetime → ℝ} {x : Spacetime} (hf : ContDiffAt ℝ 2 f x) (μ ν : Fin 4) :
    partialAt (partialAt f ν) μ x = partialAt (partialAt f μ) ν x :=
  partialAt_partialAt_comm hf μ ν

example {ι : Type*} (s : Finset ι) {f : ι → Spacetime → ℝ} {x : Spacetime}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (μ : Fin 4) :
    partialAt (fun y => ∑ i ∈ s, f i y) μ x = ∑ i ∈ s, partialAt (f i) μ x :=
  partialAt_sum s hf μ

example {n : ℕ∞ω} {A : Potential} {x : Spacetime} (hA : ContDiffAt ℝ n A x) (ν : Fin 4) :
    ContDiffAt ℝ n (potentialComponent A ν) x :=
  contDiffAt_potentialComponent hA ν

example {A : Potential} {x : Spacetime} (hA : DifferentiableAt ℝ A x) (ν : Fin 4) :
    DifferentiableAt ℝ (potentialComponent A ν) x :=
  differentiableAt_potentialComponent hA ν

example {A : Potential} {x : Spacetime} (hA : ContDiffAt ℝ 1 A x) (μ ν : Fin 4) :
    (fun y => component (fieldTensor A y) μ ν) =ᶠ[𝓝 x]
      fun y => partialAt (potentialComponent A ν) μ y - partialAt (potentialComponent A μ) ν y :=
  component_fieldTensor_eventuallyEq hA μ ν

example {A : Potential} {x : Spacetime} (hA : ContDiffAt ℝ 1 A x) (i : Fin 3) :
    electricField (fieldTensor A) i =ᶠ[𝓝 x] fun y =>
      partialAt (potentialComponent A 0) i.succ y - partialAt (potentialComponent A i.succ) 0 y :=
  electricField_fieldTensor_eventuallyEq hA i

example {A : Potential} {x : Spacetime} (hA : ContDiffAt ℝ 1 A x) :
    (magneticField (fieldTensor A) 0 =ᶠ[𝓝 x] fun y =>
      partialAt (potentialComponent A 3) 2 y - partialAt (potentialComponent A 2) 3 y) ∧
    (magneticField (fieldTensor A) 1 =ᶠ[𝓝 x] fun y =>
      partialAt (potentialComponent A 1) 3 y - partialAt (potentialComponent A 3) 1 y) ∧
    (magneticField (fieldTensor A) 2 =ᶠ[𝓝 x] fun y =>
      partialAt (potentialComponent A 2) 1 y - partialAt (potentialComponent A 1) 2 y) :=
  magneticField_fieldTensor_eventuallyEq hA

example {A : Potential} {x : Spacetime} (hA : ContDiffAt ℝ 2 A x) (μ : Fin 4) :
    partialAt (lorenzDivergence A) μ x =
      -partialAt (partialAt (potentialComponent A 0) 0) μ x +
        ∑ i : Fin 3, partialAt (partialAt (potentialComponent A i.succ) i.succ) μ x :=
  partialAt_lorenzDivergence hA μ

example {A : Potential} {x : Spacetime} (hA : ContDiffAt ℝ 2 A x) :
    divergence3 (electricField (fieldTensor A)) x =
      box (potentialComponent A 0) x - partialAt (lorenzDivergence A) 0 x :=
  divergence3_electricField_fieldTensor hA

example {A : Potential} {x : Spacetime} (hA : ContDiffAt ℝ 2 A x) (i : Fin 3) :
    curl (magneticField (fieldTensor A)) x i - partialAt (electricField (fieldTensor A) i) 0 x =
      -box (potentialComponent A i.succ) x + partialAt (lorenzDivergence A) i.succ x :=
  curl_magneticField_sub_fieldTensor hA i

example {U : Set Spacetime} (hU : IsOpen U) {A : Potential} (hA : ContDiffOn ℝ 2 A U)
    (hL : ∀ y ∈ U, lorenzDivergence A y = 0) (k : Spacetime → Spacetime) :
    (∀ y ∈ U, (divergence3 (magneticField (fieldTensor A)) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor A) i) 0 y +
          curl (electricField (fieldTensor A)) y i = 0) ∧
      (divergence3 (electricField (fieldTensor A)) y = k y 0 ∧
        ∀ i, curl (magneticField (fieldTensor A)) y i -
          partialAt (electricField (fieldTensor A) i) 0 y = k y i.succ)) ↔
    ∀ y ∈ U, box (potentialComponent A 0) y = k y 0 ∧
      ∀ i : Fin 3, box (potentialComponent A i.succ) y = -k y i.succ :=
  maxwell_iff_box_of_lorenz hU hA hL k

example (A B : Potential) (ν : Fin 4) :
    potentialComponent (A + B) ν =
      fun y => potentialComponent A ν y + potentialComponent B ν y :=
  potentialComponent_add A B ν

example {A B : Potential} {x : Spacetime} (hA : DifferentiableAt ℝ A x)
    (hB : DifferentiableAt ℝ B x) :
    lorenzDivergence (A + B) x = lorenzDivergence A x + lorenzDivergence B x :=
  lorenzDivergence_add hA hB

example {U : Set Spacetime} (hU : IsOpen U) {A : Potential} (hA : ContDiffOn ℝ 2 A U)
    (hL : ∀ y ∈ U, lorenzDivergence A y = 0) (k : Spacetime → Spacetime) :
    (∀ y ∈ U, exteriorDerivative (fun z => -star (fieldTensor A z)) y =
      SourcedAction.matterCurrentForm k y) ↔
    ∀ y ∈ U, box (potentialComponent A 0) y = k y 0 ∧
      ∀ i : Fin 3, box (potentialComponent A i.succ) y = -k y i.succ :=
  excitation_iff_box_of_lorenz hU hA hL k

example (A : Potential) (χ : Spacetime → ℝ) (ν : Fin 4) :
    potentialComponent (gaugeShift A χ) ν =
      fun y => potentialComponent A ν y + partialAt χ ν y :=
  potentialComponent_gaugeShift A χ ν

example {A : Potential} {χ : Spacetime → ℝ} {x : Spacetime} (hA : DifferentiableAt ℝ A x)
    (hχ : ContDiffAt ℝ 2 χ x) :
    lorenzDivergence (gaugeShift A χ) x = lorenzDivergence A x + box χ x :=
  lorenzDivergence_gaugeShift hA hχ

example {U : Set Spacetime} (hU : IsOpen U) {A : Potential} {χ : Spacetime → ℝ}
    (hA : ContDiffOn ℝ 1 A U) (hχ : ContDiffOn ℝ 2 χ U)
    (hbox : ∀ y ∈ U, box χ y = -lorenzDivergence A y) :
    (∀ y ∈ U, lorenzDivergence (gaugeShift A χ) y = 0) ∧
      Set.EqOn (fieldTensor (gaugeShift A χ)) (fieldTensor A) U :=
  lorenz_gaugeShift hU hA hχ hbox

example (f : Spacetime → ℝ) (x : Spacetime) :
    box (fun y => -f y) x = -box f x :=
  box_neg f x

example {f g : Spacetime → ℝ} {x : Spacetime} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    box (fun y => f y + g y) x = box f x + box g x :=
  box_add hf hg

example {m n : ℕ∞ω} {f : Spacetime → ℝ} {x : Spacetime} (hf : ContDiffAt ℝ n f x)
    (hmn : m + 2 ≤ n) :
    ContDiffAt ℝ m (box f) x :=
  contDiffAt_box hf hmn

example {f : Spacetime → ℝ} {x : Spacetime} (hf : ContDiffAt ℝ 3 f x) (ν : Fin 4) :
    box (partialAt f ν) x = partialAt (box f) ν x :=
  box_partialAt hf ν

example {U : Set Spacetime} (hU : IsOpen U) {A : Potential} (hA : ContDiffOn ℝ 3 A U)
    {k : Spacetime → Spacetime} (hk0 : ∀ y ∈ U, box (potentialComponent A 0) y = k y 0)
    (hk : ∀ y ∈ U, ∀ i : Fin 3, box (potentialComponent A i.succ) y = -k y i.succ)
    (hdiv : ∀ y ∈ U, divergence4 k y = 0) {x : Spacetime} (hx : x ∈ U) :
    box (lorenzDivergence A) x = 0 :=
  box_lorenzDivergence hU hA hk0 hk hdiv hx

example {n : ℕ∞ω} {G : Field} {x : Spacetime} (hG : ContDiffAt ℝ n G x) (i : Fin 3) :
    ContDiffAt ℝ n (electricField G i) x :=
  contDiffAt_electricField hG i

example {n : ℕ∞ω} {G : Field} {x : Spacetime} (hG : ContDiffAt ℝ n G x) (i : Fin 3) :
    ContDiffAt ℝ n (magneticField G i) x :=
  contDiffAt_magneticField hG i

example {f : Fin 3 → Spacetime → ℝ} {x : Spacetime} (hf : ∀ i, ContDiffAt ℝ 2 (f i) x) :
    partialAt (fun y => curl f y 0) 1 x + partialAt (fun y => curl f y 1) 2 x +
      partialAt (fun y => curl f y 2) 3 x = 0 :=
  partialAt_curl_sum hf

example {U : Set Spacetime} (hU : IsOpen U) {F : Field} (hF : ContDiffOn ℝ 2 F U)
    {k : Spacetime → Spacetime} (hk : DifferentiableOn ℝ k U)
    (hfar : ∀ y ∈ U, ∀ i, partialAt (magneticField F i) 0 y + curl (electricField F) y i = 0)
    (hamp : ∀ y ∈ U, ∀ i,
      curl (magneticField F) y i - partialAt (electricField F i) 0 y = k y i.succ)
    (hdiv : ∀ y ∈ U, divergence4 k y = 0) {x : Spacetime} (hx : x ∈ U) :
    partialAt (divergence3 (magneticField F)) 0 x = 0 ∧
      partialAt (fun y => divergence3 (electricField F) y - k y 0) 0 x = 0 :=
  constraint_propagation hU hF hk hfar hamp hdiv hx

example {m n : ℕ∞ω} {f : Spacetime → ℝ} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) (μ : Fin 4) :
    ContDiff ℝ m (partialAt f μ) :=
  contDiff_partialAt_of_le hf hmn μ

example {m n : ℕ∞ω} {A : Potential} (hA : ContDiff ℝ n A) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (lorenzDivergence A) :=
  contDiff_lorenzDivergence hA hmn

example {u : Spacetime → ℝ} {y : Spacetime} {r : ℝ} (μ : Fin 4)
    (hu : DifferentiableAt ℝ u (y + r • Pi.single μ 1)) :
    HasDerivAt (fun s => u (y + s • Pi.single μ 1)) (partialAt u μ (y + r • Pi.single μ 1)) r :=
  hasDerivAt_comp_line μ hu

example {u : Spacetime → ℝ} {y : Spacetime} (μ : Fin 4) (hu : DifferentiableAt ℝ u y)
    (h : ∀ᶠ s in 𝓝 (0 : ℝ), u (y + s • Pi.single μ 1) = 0) :
    partialAt u μ y = 0 :=
  partialAt_eq_zero_of_eventually μ hu h

example (u : Spacetime → ℝ) :
    Spacetime → Spacetime :=
  waveEnergyCurrent u

example (u : Spacetime → ℝ) (y : Spacetime) (i : Fin 3) :
    waveEnergyCurrent u y i.succ = -(partialAt u 0 y * partialAt u i.succ y) :=
  waveEnergyCurrent_succ u y i

example {u : Spacetime → ℝ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (waveEnergyCurrent u) :=
  contDiff_waveEnergyCurrent hu

example {u : Spacetime → ℝ} (hu : ContDiff ℝ 2 u) (y : Spacetime) :
    divergence4 (waveEnergyCurrent u) y = -(partialAt u 0 y * box u y) :=
  divergence4_waveEnergyCurrent hu y

example {u : Spacetime → ℝ} (hu : ContDiff ℝ 2 u) {T R : ℝ}
    (hbox : ∀ y, 0 ≤ y 0 → y 0 ≤ T → box u y = 0)
    (hsupp : ∀ y, 0 ≤ y 0 → y 0 ≤ T → u y ≠ 0 → ∀ i : Fin 3, |y i.succ| < R)
    (h0 : ∀ y, y 0 = 0 → u y = 0) (h1 : ∀ y, y 0 = 0 → partialAt u 0 y = 0) :
    ∀ y, 0 ≤ y 0 → y 0 ≤ T → u y = 0 :=
  eq_zero_of_box_eq_zero hu hbox hsupp h0 h1

example {A : Potential} (hA : ContDiff ℝ 3 A) {U : Set Spacetime} (hU : IsOpen U) {T R : ℝ}
    (hslab : ∀ y, 0 ≤ y 0 → y 0 ≤ T → y ∈ U) {k : Spacetime → Spacetime}
    (hk0 : ∀ y ∈ U, box (potentialComponent A 0) y = k y 0)
    (hk : ∀ y ∈ U, ∀ i : Fin 3, box (potentialComponent A i.succ) y = -k y i.succ)
    (hdiv : ∀ y ∈ U, divergence4 k y = 0)
    (hsupp : ∀ y, 0 ≤ y 0 → y 0 ≤ T → lorenzDivergence A y ≠ 0 → ∀ i : Fin 3, |y i.succ| < R)
    (h0 : ∀ y, y 0 = 0 → lorenzDivergence A y = 0)
    (h1 : ∀ y, y 0 = 0 → partialAt (lorenzDivergence A) 0 y = 0) :
    ∀ y, 0 ≤ y 0 → y 0 ≤ T → lorenzDivergence A y = 0 :=
  lorenzDivergence_eq_zero_of_initial hA hU hslab hk0 hk hdiv hsupp h0 h1

end ProjectAinos.Electrodynamics

end WaveEquation

section PlaneWave

open Set Filter Matrix

open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (α β : FourCovector) :
    ℝ :=
  covectorInner α β

example (α β : FourCovector) :
    covectorInner α β = -(α (Pi.single 0 1) * β (Pi.single 0 1)) +
      α (Pi.single 1 1) * β (Pi.single 1 1) + α (Pi.single 2 1) * β (Pi.single 2 1) +
      α (Pi.single 3 1) * β (Pi.single 3 1) :=
  covectorInner_apply α β

example (α β : FourCovector) :
    covectorInner α β = minkowskiForm .timeNegative 3 (sharp .timeNegative α)
      (sharp .timeNegative β) :=
  covectorInner_eq_minkowskiForm α β

example (ℓ a : FourCovector) (f : ℝ → ℝ) :
    Potential :=
  planeWave ℓ a f

example (ℓ a : FourCovector) (f : ℝ → ℝ) (ν : Fin 4) :
    potentialComponent (planeWave ℓ a f) ν = fun y => a (Pi.single ν 1) * f (ℓ y) :=
  potentialComponent_planeWave ℓ a f ν

example {n : ℕ∞ω} (ℓ a : FourCovector) {f : ℝ → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (planeWave ℓ a f) :=
  contDiff_planeWave ℓ a hf

example (ℓ : FourCovector) {f : ℝ → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f (ℓ x)) :
    HasFDerivAt (fun y => f (ℓ y)) (deriv f (ℓ x) • ℓ) x :=
  hasFDerivAt_comp_covector ℓ hf

example (ℓ : FourCovector) {f : ℝ → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f (ℓ x))
    (μ : Fin 4) :
    partialAt (fun y => f (ℓ y)) μ x = deriv f (ℓ x) * ℓ (Pi.single μ 1) :=
  partialAt_comp_covector ℓ hf μ

example (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f (ℓ x))
    (v w : Spacetime) :
    fieldTensor (planeWave ℓ a f) x ![v, w] = deriv f (ℓ x) * (ℓ v * a w - ℓ w * a v) :=
  fieldTensor_planeWave ℓ a hf v w

example (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f (ℓ x))
    (i : Fin 3) :
    electricVector (fieldTensor (planeWave ℓ a f) x) i =
      deriv f (ℓ x) * (ℓ (Pi.single i.succ 1) * a (Pi.single 0 1) -
        ℓ (Pi.single 0 1) * a (Pi.single i.succ 1)) :=
  electricVector_planeWave ℓ a hf i

example (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f (ℓ x)) :
    magneticVector (fieldTensor (planeWave ℓ a f) x) =
      ![deriv f (ℓ x) * (ℓ (Pi.single 2 1) * a (Pi.single 3 1) -
          ℓ (Pi.single 3 1) * a (Pi.single 2 1)),
        deriv f (ℓ x) * (ℓ (Pi.single 3 1) * a (Pi.single 1 1) -
          ℓ (Pi.single 1 1) * a (Pi.single 3 1)),
        deriv f (ℓ x) * (ℓ (Pi.single 1 1) * a (Pi.single 2 1) -
          ℓ (Pi.single 2 1) * a (Pi.single 1 1))] :=
  magneticVector_planeWave ℓ a hf

example (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f (ℓ x))
    (ν μ : Fin 4) :
    partialAt (potentialComponent (planeWave ℓ a f) ν) μ x =
      a (Pi.single ν 1) * (deriv f (ℓ x) * ℓ (Pi.single μ 1)) :=
  partialAt_potentialComponent_planeWave ℓ a hf ν μ

example (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f (ℓ x)) :
    lorenzDivergence (planeWave ℓ a f) x = deriv f (ℓ x) * covectorInner ℓ a :=
  lorenzDivergence_planeWave ℓ a hf

example {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (deriv f) :=
  differentiable_deriv_of_contDiff_two hf

example (ℓ a : FourCovector) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (ν : Fin 4) (x : Spacetime) :
    box (potentialComponent (planeWave ℓ a f) ν) x =
      deriv (deriv f) (ℓ x) * covectorInner ℓ ℓ * a (Pi.single ν 1) :=
  box_planeWave ℓ a hf ν x

example (y : Spacetime) :
    SourcedAction.matterCurrentForm (fun _ => (0 : Spacetime)) y = 0 :=
  matterCurrentForm_const_zero y

example {ℓ a : FourCovector} (hnull : covectorInner ℓ ℓ = 0) (horth : covectorInner ℓ a = 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    (∀ x, exteriorDerivative (fieldTensor (planeWave ℓ a f)) x = 0) ∧
    (∀ x, exteriorDerivative (fun y => -star (fieldTensor (planeWave ℓ a f) y)) x = 0) ∧
    ∀ x, (divergence3 (magneticField (fieldTensor (planeWave ℓ a f))) x = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (planeWave ℓ a f)) i) 0 x +
          curl (electricField (fieldTensor (planeWave ℓ a f))) x i = 0) ∧
      (divergence3 (electricField (fieldTensor (planeWave ℓ a f))) x = 0 ∧
        ∀ i, curl (magneticField (fieldTensor (planeWave ℓ a f))) x i -
          partialAt (electricField (fieldTensor (planeWave ℓ a f)) i) 0 x = 0) :=
  vacuum_planeWave hnull horth hf

example {ℓ a : FourCovector} (hnull : covectorInner ℓ ℓ = 0) (horth : covectorInner ℓ a = 0)
    {f : ℝ → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f (ℓ x)) :
    scalarInvariant (fieldTensor (planeWave ℓ a f) x) = 0 :=
  scalarInvariant_planeWave hnull horth hf

example (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f (ℓ x)) :
    pseudoscalarInvariant (fieldTensor (planeWave ℓ a f) x) = 0 :=
  pseudoscalarInvariant_planeWave ℓ a hf

example {ℓ : FourCovector} (hℓ : ℓ ≠ 0) :
    ∃ v, ℓ v = 1 :=
  exists_apply_eq_one hℓ

example {ℓ c : FourCovector} (hℓ : ℓ ≠ 0) (h : ∀ v w, ℓ v * c w - ℓ w * c v = 0) :
    ∃ t : ℝ, c = t • ℓ :=
  exists_eq_smul_of_wedge_eq_zero hℓ h

example {ℓ a : FourCovector} (hℓ : ℓ ≠ 0) (ha : ∀ t : ℝ, a ≠ t • ℓ) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (ℓ x)) (hf' : deriv f (ℓ x) ≠ 0) :
    fieldTensor (planeWave ℓ a f) x ≠ 0 :=
  fieldTensor_planeWave_ne_zero hℓ ha hf hf'

example (κ : ℝ) (n : Fin 3 → ℝ) :
    FourCovector :=
  wavevector κ n

example (κ : ℝ) (n : Fin 3 → ℝ) (v : Spacetime) :
    wavevector κ n v = κ * (v 0 - ∑ i : Fin 3, n i * v i.succ) :=
  wavevector_apply κ n v

example (κ : ℝ) (n : Fin 3 → ℝ) :
    wavevector κ n (Pi.single 0 1) = κ :=
  wavevector_single_zero κ n

example (κ : ℝ) (n : Fin 3 → ℝ) (i : Fin 3) :
    wavevector κ n (Pi.single i.succ 1) = -(κ * n i) :=
  wavevector_single_succ κ n i

example (κ : ℝ) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) :
    covectorInner (wavevector κ n) (wavevector κ n) = 0 :=
  covectorInner_wavevector_self κ hn

example (F : Field) (x : Spacetime) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1)
    (hE : ∑ i, electricVector (F x) i * n i = 0)
    (hB : magneticVector (F x) = n ⨯₃ electricVector (F x)) :
    ∑ i, magneticVector (F x) i ^ 2 = ∑ i, electricVector (F x) i ^ 2 ∧
      energyDensity F x = ∑ i, electricVector (F x) i ^ 2 ∧
      (∀ i, poyntingVector F i x = (∑ j, electricVector (F x) j ^ 2) * n i) ∧
      ∀ i j, maxwellStress F i j x = (∑ l, electricVector (F x) l ^ 2) * (n i * n j) :=
  transverse_stress F x hn hE hB

example (κ : ℝ) (n : Fin 3 → ℝ) :
    wavevector κ n (Pi.single 1 1) = -(κ * n 0) :=
  wavevector_single_one κ n

example (κ : ℝ) (n : Fin 3 → ℝ) :
    wavevector κ n (Pi.single 2 1) = -(κ * n 1) :=
  wavevector_single_two κ n

example (κ : ℝ) (n : Fin 3 → ℝ) :
    wavevector κ n (Pi.single 3 1) = -(κ * n 2) :=
  wavevector_single_three κ n

example {κ : ℝ} (hκ : κ ≠ 0) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) {a : FourCovector}
    (horth : covectorInner (wavevector κ n) a = 0) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (wavevector κ n x)) :
    let F := fieldTensor (planeWave (wavevector κ n) a f)
    ∑ i, electricVector (F x) i * n i = 0 ∧
      magneticVector (F x) = n ⨯₃ electricVector (F x) ∧
      ∑ i, magneticVector (F x) i ^ 2 = ∑ i, electricVector (F x) i ^ 2 ∧
      energyDensity F x = ∑ i, electricVector (F x) i ^ 2 ∧
      (∀ i, poyntingVector F i x = (∑ j, electricVector (F x) j ^ 2) * n i) ∧
      ∀ μ ν, raisedStress F μ ν x = (∑ j, electricVector (F x) j ^ 2) *
        (sharp .timeNegative (wavevector κ n) μ * sharp .timeNegative (wavevector κ n) ν) /
          κ ^ 2 :=
  transverse_planeWave hκ hn horth hf

example {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s) (hz : ∀ s, g' s = 0) (s t : ℝ) :
    g s = g t :=
  const_of_hasDerivAt_zero hg hz s t

example {n : Fin 3 → ℝ} {F : Field} {G : ℝ → TwoForm} (hG : Differentiable ℝ G)
    (hF : F = fun y => G (wavevector 1 n y)) (hgE : ∀ y, divergence3 (electricField F) y = 0)
    (hgB : ∀ y, divergence3 (magneticField F) y = 0)
    (hfar : ∀ y i, partialAt (magneticField F i) 0 y + curl (electricField F) y i = 0)
    (y z : Spacetime) :
    ∑ i, electricVector (F y) i * n i = ∑ i, electricVector (F z) i * n i ∧
      ∑ i, magneticVector (F y) i * n i = ∑ i, magneticVector (F z) i * n i ∧
      magneticVector (F y) - n ⨯₃ electricVector (F y) =
        magneticVector (F z) - n ⨯₃ electricVector (F z) :=
  transverse_of_vacuum hG hF hgE hgB hfar y z

end ProjectAinos.Electrodynamics

end PlaneWave

section Monochromatic

open Set Filter Matrix Real

open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (ℓ a b : FourCovector) :
    Potential :=
  monochromatic ℓ a b

example (ℓ a b : FourCovector) (ν : Fin 4) :
    potentialComponent (monochromatic ℓ a b) ν =
      fun y => a (Pi.single ν 1) * Real.cos (ℓ y) + b (Pi.single ν 1) * Real.sin (ℓ y) :=
  potentialComponent_monochromatic ℓ a b ν

example {n : ℕ∞ω} (ℓ a b : FourCovector) :
    ContDiff ℝ n (monochromatic ℓ a b) :=
  contDiff_monochromatic ℓ a b

example (ℓ a b : FourCovector) (x v w : Spacetime) :
    fieldTensor (monochromatic ℓ a b) x ![v, w] =
      -Real.sin (ℓ x) * (ℓ v * a w - ℓ w * a v) + Real.cos (ℓ x) * (ℓ v * b w - ℓ w * b v) :=
  fieldTensor_monochromatic ℓ a b x v w

example {ℓ a b : FourCovector} (hnull : covectorInner ℓ ℓ = 0) (ha : covectorInner ℓ a = 0)
    (hb : covectorInner ℓ b = 0) :
    (∀ x, exteriorDerivative (fieldTensor (monochromatic ℓ a b)) x = 0) ∧
    (∀ x, exteriorDerivative (fun y => -star (fieldTensor (monochromatic ℓ a b) y)) x = 0) ∧
    ∀ x, (divergence3 (magneticField (fieldTensor (monochromatic ℓ a b))) x = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (monochromatic ℓ a b)) i) 0 x +
          curl (electricField (fieldTensor (monochromatic ℓ a b))) x i = 0) ∧
      (divergence3 (electricField (fieldTensor (monochromatic ℓ a b))) x = 0 ∧
        ∀ i, curl (magneticField (fieldTensor (monochromatic ℓ a b))) x i -
          partialAt (electricField (fieldTensor (monochromatic ℓ a b)) i) 0 x = 0) :=
  vacuum_monochromatic hnull ha hb

example :
    covectorInner (wavevector 1 ![1, 0, 0]) (wavevector 1 ![1, 0, 0]) = 0 ∧
      covectorInner (wavevector 1 ![1, 0, 0]) (ContinuousLinearMap.proj 2 : FourCovector) = 0 ∧
      fieldTensor (planeWave (wavevector 1 ![1, 0, 0]) (ContinuousLinearMap.proj 2 : FourCovector)
        Real.sin) 0 ≠ 0 :=
  planeWave_instance

example {F G : TwoForm} (h : ∀ v w, F ![v, w] = G ![v, w]) :
    F = G :=
  twoForm_eq_of_apply_pair h

example (ℓ a b : FourCovector) (c d : ℝ) :
    monochromatic ℓ (a + c • ℓ) (b + d • ℓ) =
      gaugeShift (monochromatic ℓ a b) (fun y => c * Real.sin (ℓ y) - d * Real.cos (ℓ y)) :=
  monochromatic_eq_gaugeShift ℓ a b c d

example {ℓ : FourCovector} (hℓ : ℓ ≠ 0) (a b a' b' : FourCovector) :
    fieldTensor (monochromatic ℓ a b) = fieldTensor (monochromatic ℓ a' b') ↔
      (∃ c : ℝ, a = a' + c • ℓ) ∧ ∃ d : ℝ, b = b' + d • ℓ :=
  fieldTensor_monochromatic_eq_iff hℓ a b a' b'

example (ℓ a : FourCovector) :
    covectorInner ℓ a = a (sharp .timeNegative ℓ) :=
  covectorInner_eq_apply_sharp ℓ a

example (ℓ : FourCovector) :
    FourCovector →ₗ[ℝ] ℝ :=
  covectorInnerLeft ℓ

example (ℓ a : FourCovector) :
    covectorInnerLeft ℓ a = covectorInner ℓ a :=
  covectorInnerLeft_apply ℓ a

example (ℓ : FourCovector) :
    Submodule ℝ FourCovector :=
  transverseAmplitudes ℓ

example (ℓ a : FourCovector) :
    a ∈ transverseAmplitudes ℓ ↔ covectorInner ℓ a = 0 :=
  mem_transverseAmplitudes ℓ a

example {ℓ : FourCovector} (hnull : covectorInner ℓ ℓ = 0) :
    Submodule.span ℝ {ℓ} ≤ transverseAmplitudes ℓ :=
  span_le_transverseAmplitudes hnull

example (ℓ : FourCovector) (hnull : covectorInner ℓ ℓ = 0) :
    Submodule ℝ (FourCovector ⧸ Submodule.span ℝ {ℓ}) :=
  polarizations ℓ hnull

example {ℓ : FourCovector} (hnull : covectorInner ℓ ℓ = 0) :
    polarizations ℓ hnull = (transverseAmplitudes ℓ).map (Submodule.span ℝ {ℓ}).mkQ :=
  polarizations_eq_map hnull

example :
    Module.finrank ℝ FourCovector = 4 :=
  finrank_fourCovector

example {ℓ : FourCovector} (hℓ : ℓ ≠ 0) (hnull : covectorInner ℓ ℓ = 0) :
    Module.finrank ℝ (polarizations ℓ hnull) = 2 :=
  finrank_polarization_quotient hℓ hnull

example (ℓ a : FourCovector) :
    Fin 3 → ℝ :=
  electricAmplitude ℓ a

example (ℓ a b : FourCovector) (x : Spacetime) :
    electricVector (fieldTensor (monochromatic ℓ a b) x) =
      Real.cos (ℓ x) • electricAmplitude ℓ b + Real.sin (ℓ x) • -electricAmplitude ℓ a :=
  electricVector_monochromatic ℓ a b x

example (p q : Fin 3 → ℝ) :
    ∃ θ : ℝ, (Real.cos θ • p + Real.sin θ • q) ⬝ᵥ (-Real.sin θ • p + Real.cos θ • q) = 0 ∧
      ∀ φ : ℝ, Real.cos (φ + θ) • p + Real.sin (φ + θ) • q =
        Real.cos φ • (Real.cos θ • p + Real.sin θ • q) +
          Real.sin φ • (-Real.sin θ • p + Real.cos θ • q) :=
  exists_phase_orthogonal p q

example {p q : Fin 3 → ℝ} (h : p ⬝ᵥ q = 0) (φ : ℝ) :
    (Real.cos φ • p + Real.sin φ • q) ⬝ᵥ (Real.cos φ • p + Real.sin φ • q) =
      Real.cos φ ^ 2 * (p ⬝ᵥ p) + Real.sin φ ^ 2 * (q ⬝ᵥ q) :=
  dotProduct_self_phase_of_orthogonal h φ

example {p q : Fin 3 → ℝ} (h : p ⬝ᵥ q = 0) (hpq : p ⬝ᵥ p = q ⬝ᵥ q) (φ : ℝ) :
    (Real.cos φ • p + Real.sin φ • q) ⬝ᵥ (Real.cos φ • p + Real.sin φ • q) = p ⬝ᵥ p :=
  dotProduct_self_phase_of_circular h hpq φ

example (κ : ℝ) (n : Fin 3 → ℝ) (V : ℝ) (hV : |V| < 1) (v : Spacetime) :
    wavevector κ n ((boost (axisVelocity V hV).neg).val v) =
      (axisVelocity V hV).gamma * κ * (1 - V * n 0) * v 0 -
        ((axisVelocity V hV).gamma * κ * (n 0 - V) * v 1 + κ * n 1 * v 2 + κ * n 2 * v 3) :=
  wavevector_boost κ n V hV v

example (κ : ℝ) (n : Fin 3 → ℝ) (V : ℝ) (hV : |V| < 1) :
    wavevector κ n ((boost (axisVelocity V hV).neg).val (Pi.single 0 1)) =
      (axisVelocity V hV).gamma * κ * (1 - V * n 0) :=
  frequency_boost κ n V hV

end ProjectAinos.Electrodynamics

end Monochromatic
