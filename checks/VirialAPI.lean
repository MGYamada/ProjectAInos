/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.Virial
import ProjectAinos.Electrodynamics.VirialExamples

/-! Public consumers of the virial theorem (Landau–Lifshitz §34): the slice integrals and the
Fubini split of a box, the moment current and the virial moment, the moment identity on a box for
a conserved stress vanishing on the spatial faces, the time averages of the spatial trace and of the
energy plus the four-trace, the traceless field stress and the charged-dust corollary with its
static neutral instance; and the improvement stress of a bump, a conserved stress with a nonzero
spatial trace that satisfies every hypothesis. Default elaborator options are intentional: these
checks must not rely on the implementation's transparency settings. Every statement is pinned with
its type. -/

noncomputable section

section Virial

open MeasureTheory Set Filter

open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (f : Spacetime → ℝ) (a b : Spacetime) (t : ℝ) :
    ℝ :=
  sliceIntegral f a b t

example (k : Spacetime → Spacetime) (a b : Spacetime) (t : ℝ) :
    charge k a b t = sliceIntegral (fun y => k y 0) a b t :=
  charge_eq_sliceIntegral k a b t

example {f : Spacetime → ℝ} {a b : Spacetime} (hle : a ≤ b) (hf : IntegrableOn f (Icc a b)) :
    ∫ y in Icc a b, f y = ∫ t in a 0..b 0, sliceIntegral f a b t :=
  integral_Icc_eq_intervalIntegral hle hf

example (T : Fin 4 → Fin 4 → Spacetime → ℝ) :
    Spacetime → Spacetime :=
  momentCurrent T

example (T : Fin 4 → Fin 4 → Spacetime → ℝ) (a b : Spacetime) (t : ℝ) :
    ℝ :=
  virialMoment T a b t

example (T : Fin 4 → Fin 4 → Spacetime → ℝ) (y : Spacetime) :
    ℝ :=
  spatialTrace T y

example (T : Fin 4 → Fin 4 → Spacetime → ℝ) (y : Spacetime) :
    ℝ :=
  fourTrace T y

example (T : Fin 4 → Fin 4 → Spacetime → ℝ) (y : Spacetime) :
    fourTrace T y = ∑ μ : Fin 4, lorentzSign .timeNegative μ * T μ μ y :=
  fourTrace_eq T y

example (T : Fin 4 → Fin 4 → Spacetime → ℝ) (y : Spacetime) :
    T 0 0 y + fourTrace T y = spatialTrace T y :=
  energy_add_fourTrace T y

namespace Virial

example {ι : Type*} (s : Finset ι) {f : ι → Spacetime → ℝ} {x : Spacetime}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (μ : Fin 4) :
    partialAt (fun y => ∑ i ∈ s, f i y) μ x = ∑ i ∈ s, partialAt (f i) μ x :=
  partialAt_sum s hf μ

example (β μ : Fin 4) (x : Spacetime) :
    partialAt (fun y => y β) μ x = if μ = β then 1 else 0 :=
  partialAt_coordinate β μ x

end Virial

open Virial

example {n : ℕ∞ω} {T : Fin 4 → Fin 4 → Spacetime → ℝ} (hT : ∀ μ ν, ContDiff ℝ n (T μ ν)) :
    ContDiff ℝ n (momentCurrent T) :=
  contDiff_momentCurrent hT

example {T : Fin 4 → Fin 4 → Spacetime → ℝ} {x : Spacetime}
    (hT : ∀ μ ν, DifferentiableAt ℝ (T μ ν) x) :
    divergence4 (momentCurrent T) x = spatialTrace T x +
      ∑ α : Fin 3, x α.succ * ∑ μ : Fin 4, partialAt (T μ α.succ) μ x :=
  divergence4_momentCurrent hT

example {T : Fin 4 → Fin 4 → Spacetime → ℝ} (hT : ∀ μ ν, ContDiff ℝ 1 (T μ ν)) {a b : Spacetime}
    (hle : a ≤ b) (hcons : ∀ y ∈ Icc a b, ∀ ν, ∑ μ : Fin 4, partialAt (T μ ν) μ y = 0)
    (hface : ∀ y ∈ Icc a b, ∀ i : Fin 3, (y i.succ = a i.succ ∨ y i.succ = b i.succ) →
      ∀ α : Fin 3, T i.succ α.succ y = 0) :
    virialMoment T a b (b 0) - virialMoment T a b (a 0) = ∫ y in Icc a b, spatialTrace T y :=
  virial_box hT hle hcons hface

example {T : Fin 4 → Fin 4 → Spacetime → ℝ} (hT : ∀ μ ν, Continuous (T μ ν)) :
    Continuous (spatialTrace T) :=
  continuous_spatialTrace hT

example {T : Fin 4 → Fin 4 → Spacetime → ℝ} (hT : ∀ μ ν, ContDiff ℝ 1 (T μ ν)) {a b : Spacetime}
    (hle : a ≤ b) (hcons : ∀ y ∈ Icc a b, ∀ ν, ∑ μ : Fin 4, partialAt (T μ ν) μ y = 0)
    (hface : ∀ y ∈ Icc a b, ∀ i : Fin 3, (y i.succ = a i.succ ∨ y i.succ = b i.succ) →
      ∀ α : Fin 3, T i.succ α.succ y = 0) :
    virialMoment T a b (b 0) - virialMoment T a b (a 0) =
      ∫ t in a 0..b 0, sliceIntegral (spatialTrace T) a b t :=
  virialMoment_sub_eq_intervalIntegral hT hle hcons hface

example {f : Spacetime → ℝ} (hf : Continuous f) (a b : Spacetime) (t : ℝ) :
    IntegrableOn (fun z => f (Fin.insertNth 0 t z))
      (Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0)) :=
  integrableOn_slice hf a b t

example {f g : Spacetime → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : Spacetime) (t : ℝ) :
    sliceIntegral (fun y => f y + g y) a b t = sliceIntegral f a b t + sliceIntegral g a b t :=
  sliceIntegral_add hf hg a b t

example (a : Spacetime) (s : ℝ) :
    Function.update a 0 s ∘ Fin.succAbove 0 = a ∘ Fin.succAbove 0 :=
  update_zero_comp_succAbove a s

example (f : Spacetime → ℝ) (a b : Spacetime) (s s' t : ℝ) :
    sliceIntegral f (Function.update a 0 s) (Function.update b 0 s') t =
      sliceIntegral f a b t :=
  sliceIntegral_update f a b s s' t

example (T : Fin 4 → Fin 4 → Spacetime → ℝ) (a b : Spacetime) (s s' t : ℝ) :
    virialMoment T (Function.update a 0 s) (Function.update b 0 s') t = virialMoment T a b t :=
  virialMoment_update T a b s s' t

example {T : Fin 4 → Fin 4 → Spacetime → ℝ} (hT : ∀ μ ν, ContDiff ℝ 1 (T μ ν)) {a b : Spacetime}
    (hab : ∀ i : Fin 3, a i.succ ≤ b i.succ)
    (hcons : ∀ y : Spacetime, 0 ≤ y 0 → ∀ ν, ∑ μ : Fin 4, partialAt (T μ ν) μ y = 0)
    (hsupp : ∀ y : Spacetime, 0 ≤ y 0 →
      (∃ i : Fin 3, y i.succ ≤ a i.succ ∨ b i.succ ≤ y i.succ) → ∀ μ ν, T μ ν y = 0)
    {B : ℝ} (hB : ∀ t : ℝ, 0 ≤ t → |virialMoment T a b t| ≤ B) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ, sliceIntegral (spatialTrace T) a b t)
      atTop (𝓝 0) :=
  tendsto_average_spatialTrace hT hab hcons hsupp hB

example {T : Fin 4 → Fin 4 → Spacetime → ℝ} (hT : ∀ μ ν, ContDiff ℝ 1 (T μ ν)) {a b : Spacetime}
    (hab : ∀ i : Fin 3, a i.succ ≤ b i.succ)
    (hcons : ∀ y : Spacetime, 0 ≤ y 0 → ∀ ν, ∑ μ : Fin 4, partialAt (T μ ν) μ y = 0)
    (hsupp : ∀ y : Spacetime, 0 ≤ y 0 →
      (∃ i : Fin 3, y i.succ ≤ a i.succ ∨ b i.succ ≤ y i.succ) → ∀ μ ν, T μ ν y = 0)
    {B : ℝ} (hB : ∀ t : ℝ, 0 ≤ t → |virialMoment T a b t| ≤ B) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      (sliceIntegral (T 0 0) a b t + sliceIntegral (fourTrace T) a b t)) atTop (𝓝 0) :=
  tendsto_average_energy_add_fourTrace hT hab hcons hsupp hB

example (F : Field) (y : Spacetime) :
    fourTrace (raisedStress F) y = 0 :=
  fourTrace_raisedStress F y

example {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) (μ ν : Fin 4) :
    ContDiff ℝ n (raisedStress F μ ν) :=
  Virial.contDiff_raisedStress hF μ ν

namespace ChargedDust

example (D : ChargedDust) (F : Field) :
    Fin 4 → Fin 4 → Spacetime → ℝ :=
  totalStress D F

example {n : ℕ∞ω} {D : ChargedDust} (hμ : ContDiff ℝ n D.massDensity)
    (hU : ContDiff ℝ n D.velocity) (μ ν : Fin 4) :
    ContDiff ℝ n (D.matterStress μ ν) :=
  contDiff_matterStress hμ hU μ ν

example (D : ChargedDust) {y : Spacetime}
    (hU : minkowskiForm .timeNegative 3 (D.velocity y) (D.velocity y) = -1) :
    fourTrace D.matterStress y = -D.massDensity y :=
  fourTrace_matterStress D hU

example (D : ChargedDust) (F : Field) {y : Spacetime}
    (hU : minkowskiForm .timeNegative 3 (D.velocity y) (D.velocity y) = -1) :
    fourTrace (D.totalStress F) y = -D.massDensity y :=
  fourTrace_totalStress D F hU

example {F : Field} {D : ChargedDust} (hF : ContDiff ℝ 1 F) (hμ : ContDiff ℝ 1 D.massDensity)
    (hU : ContDiff ℝ 1 D.velocity)
    (hcont : ∀ y : Spacetime, 0 ≤ y 0 →
      ∑ l : Fin 4, partialAt (fun z => D.massDensity z * D.velocity z l) l y = 0)
    (hmotion : ∀ y : Spacetime, 0 ≤ y 0 → ∀ ν : Fin 4, D.massDensity y * D.convective y ν =
      lorentzForce (D.chargeDensity y) (F y) (D.velocity y) ν)
    (hgB : ∀ y : Spacetime, 0 ≤ y 0 → divergence3 (magneticField F) y = 0)
    (hfar : ∀ y : Spacetime, 0 ≤ y 0 → ∀ i,
      partialAt (magneticField F i) 0 y + curl (electricField F) y i = 0)
    (hgE : ∀ y : Spacetime, 0 ≤ y 0 → divergence3 (electricField F) y = D.current y 0)
    (hamp : ∀ y : Spacetime, 0 ≤ y 0 → ∀ i,
      curl (magneticField F) y i - partialAt (electricField F i) 0 y = D.current y i.succ)
    (hnorm : ∀ y : Spacetime, 0 ≤ y 0 →
      minkowskiForm .timeNegative 3 (D.velocity y) (D.velocity y) = -1)
    {a b : Spacetime} (hab : ∀ i : Fin 3, a i.succ ≤ b i.succ)
    (hsupp : ∀ y : Spacetime, 0 ≤ y 0 →
      (∃ i : Fin 3, y i.succ ≤ a i.succ ∨ b i.succ ≤ y i.succ) →
        ∀ μ ν, D.totalStress F μ ν y = 0)
    {B : ℝ} (hB : ∀ t : ℝ, 0 ≤ t → |virialMoment (D.totalStress F) a b t| ≤ B) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      (sliceIntegral (D.totalStress F 0 0) a b t - sliceIntegral D.massDensity a b t))
      atTop (𝓝 0) :=
  tendsto_average_energy_sub_restMass hF hμ hU hcont hmotion hgB hfar hgE hamp hnorm hab hsupp hB

example (μ₀ : Spacetime → ℝ) :
    ChargedDust :=
  staticNeutral μ₀

example {μ₀ : Spacetime → ℝ} (hμ₀ : ContDiff ℝ 1 μ₀)
    (hstat : ∀ y : Spacetime, partialAt μ₀ 0 y = 0) {a b : Spacetime}
    (hab : ∀ i : Fin 3, a i.succ ≤ b i.succ)
    (hsupp : ∀ y : Spacetime, 0 ≤ y 0 →
      (∃ i : Fin 3, y i.succ ≤ a i.succ ∨ b i.succ ≤ y i.succ) → μ₀ y = 0) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      (sliceIntegral ((staticNeutral μ₀).totalStress (fun _ => 0) 0 0) a b t -
        sliceIntegral (staticNeutral μ₀).massDensity a b t)) atTop (𝓝 0) :=
  tendsto_average_energy_sub_restMass_static hμ₀ hstat hab hsupp

end ChargedDust

end ProjectAinos.Electrodynamics

end Virial

section VirialExamples

open MeasureTheory Set Filter

open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics.Virial.Examples

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

example {m n : ℕ∞ω} {f : Spacetime → ℝ} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) (μ : Fin 4) :
    ContDiff ℝ m (partialAt f μ) :=
  contDiff_partialAt hf hmn μ

example {f : Spacetime → ℝ} (hf : ContDiff ℝ 2 f) (μ ν : Fin 4) :
    partialAt (partialAt f ν) μ = partialAt (partialAt f μ) ν :=
  partialAt_comm hf μ ν

example {f : Spacetime → ℝ} {y : Spacetime} (hy : y ∉ tsupport f) (μ : Fin 4) :
    partialAt f μ y = 0 :=
  partialAt_eq_zero_of_notMem_tsupport hy μ

example (f : Spacetime → ℝ) (μ : Fin 4) :
    tsupport (partialAt f μ) ⊆ tsupport f :=
  tsupport_partialAt_subset f μ

example (χ : Spacetime → ℝ) (y : Spacetime) :
    ℝ :=
  dAlembertian χ y

example (χ : Spacetime → ℝ) (μ ν : Fin 4) (y : Spacetime) :
    ℝ :=
  improvementStress χ μ ν y

example {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 3 χ) (μ ν : Fin 4) :
    ContDiff ℝ 1 (improvementStress χ μ ν) :=
  contDiff_improvementStress hχ μ ν

example {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (μ ν : Fin 4) (y : Spacetime) :
    improvementStress χ μ ν y = improvementStress χ ν μ y :=
  improvementStress_symm hχ μ ν y

example {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 3 χ) (y : Spacetime) (ν : Fin 4) :
    ∑ μ : Fin 4, partialAt (improvementStress χ μ ν) μ y = 0 :=
  improvementStress_conserved hχ y ν

example (χ : Spacetime → ℝ) (y : Spacetime) :
    spatialTrace (improvementStress χ) y = 3 * partialAt (partialAt χ 0) 0 y -
      2 * ∑ α : Fin 3, partialAt (partialAt χ α.succ) α.succ y :=
  spatialTrace_improvementStress χ y

example (χ : Spacetime → ℝ) (α : Fin 3) (y : Spacetime) :
    improvementStress χ 0 α.succ y = -partialAt (partialAt χ α.succ) 0 y :=
  improvementStress_zero_succ χ α y

example {χ : Spacetime → ℝ} {y : Spacetime} (hy : y ∉ tsupport χ) (μ ν : Fin 4) :
    improvementStress χ μ ν y = 0 :=
  improvementStress_eq_zero_of_notMem hy μ ν

example :
    Spacetime →L[ℝ] (Fin 3 → ℝ) :=
  spatialPart

example (y : Spacetime) (i : Fin 3) :
    spatialPart y i = y i.succ :=
  spatialPart_apply y i

example :
    spatialPart (Pi.single 0 1) = 0 :=
  spatialPart_single_zero

example (i : Fin 3) :
    spatialPart (Pi.single i.succ 1) = Pi.single i 1 :=
  spatialPart_single_succ i

example (t : ℝ) (z : Fin 3 → ℝ) (α : Fin 3) :
    (Fin.insertNth 0 t z : Spacetime) α.succ = z α :=
  insertNth_zero_succ t z α

example (t : ℝ) (z : Fin 3 → ℝ) :
    spatialPart (Fin.insertNth 0 t z) = z :=
  spatialPart_insertNth t z

example (g : (Fin 3 → ℝ) → ℝ) (i : Fin 3) (z : Fin 3 → ℝ) :
    ℝ :=
  spatialPartial g i z

example {m n : ℕ∞ω} {g : (Fin 3 → ℝ) → ℝ} (hg : ContDiff ℝ n g) (hmn : m + 1 ≤ n) (i : Fin 3) :
    ContDiff ℝ m (spatialPartial g i) :=
  contDiff_spatialPartial hg hmn i

example {g : (Fin 3 → ℝ) → ℝ} {z : Fin 3 → ℝ} (hz : z ∉ tsupport g) (i : Fin 3) :
    spatialPartial g i z = 0 :=
  spatialPartial_eq_zero_of_notMem hz i

example (f : ℝ → ℝ) (g : (Fin 3 → ℝ) → ℝ) :
    Spacetime → ℝ :=
  separated f g

example (f : ℝ → ℝ) (g : (Fin 3 → ℝ) → ℝ) (t : ℝ) (z : Fin 3 → ℝ) :
    separated f g (Fin.insertNth 0 t z) = f t * g z :=
  separated_insertNth f g t z

example {n : ℕ∞ω} {f : ℝ → ℝ} {g : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (separated f g) :=
  contDiff_separated hf hg

example {f : ℝ → ℝ} {g : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (μ : Fin 4) (y : Spacetime) :
    partialAt (separated f g) μ y =
      f (y 0) * fderiv ℝ g (spatialPart y) (spatialPart (Pi.single μ 1)) +
        g (spatialPart y) * (deriv f (y 0) * (Pi.single μ 1 : Spacetime) 0) :=
  partialAt_separated hf hg μ y

example {f : ℝ → ℝ} {g : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    partialAt (separated f g) 0 = separated (deriv f) g :=
  partialAt_separated_zero hf hg

example {f : ℝ → ℝ} {g : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) :
    partialAt (separated f g) i.succ = separated f (spatialPartial g i) :=
  partialAt_separated_succ hf hg i

example (f : ℝ → ℝ) (g : (Fin 3 → ℝ) → ℝ) :
    tsupport (separated f g) ⊆ spatialPart ⁻¹' tsupport g :=
  tsupport_separated_subset f g

example :
    ContDiffBump (0 : Fin 3 → ℝ) :=
  cubeBump

example :
    ContDiff ℝ 3 cubeBump :=
  contDiff_cubeBump

example :
    tsupport cubeBump = Metric.closedBall 0 2 :=
  tsupport_cubeBump

example {z : Fin 3 → ℝ} {i : Fin 3} (hz : 3 ≤ |z i|) :
    z ∉ Metric.closedBall (0 : Fin 3 → ℝ) 2 :=
  notMem_closedBall_of_le_abs hz

example :
    Set (Fin 3 → ℝ) :=
  cube

example (z : Fin 3 → ℝ) :
    ℝ :=
  laplacianBump z

example :
    Continuous laplacianBump :=
  continuous_laplacianBump

example :
    ∫ z in cube, laplacianBump z = 0 :=
  integral_laplacianBump

example :
    0 < ∫ z in cube, cubeBump z :=
  integral_cubeBump_pos

example :
    Spacetime → ℝ :=
  improvementPotential

example :
    Fin 4 → Fin 4 → Spacetime → ℝ :=
  improvement

example :
    Spacetime :=
  cubeLo

example :
    Spacetime :=
  cubeHi

example :
    ContDiff ℝ 3 improvementPotential :=
  contDiff_improvementPotential

example :
    Differentiable ℝ cubeBump :=
  differentiable_cubeBump

example (i : Fin 3) :
    Differentiable ℝ (spatialPartial cubeBump i) :=
  differentiable_spatialPartial_cubeBump i

example :
    deriv (fun x => -Real.sin x) = fun x => -Real.cos x :=
  deriv_neg_sin

example :
    partialAt (partialAt improvementPotential 0) 0 =
      separated (fun x => -Real.cos x) cubeBump :=
  partialAt_improvementPotential_zero_zero

example (α : Fin 3) :
    partialAt (partialAt improvementPotential α.succ) α.succ =
      separated Real.cos (spatialPartial (spatialPartial cubeBump α) α) :=
  partialAt_improvementPotential_succ_succ α

example (α : Fin 3) :
    partialAt (partialAt improvementPotential α.succ) 0 =
      separated (fun x => -Real.sin x) (spatialPartial cubeBump α) :=
  partialAt_improvementPotential_succ_zero α

example (μ ν : Fin 4) (y : Spacetime) :
    improvement μ ν y = improvement ν μ y :=
  improvement_symm μ ν y

example (t : ℝ) (z : Fin 3 → ℝ) :
    spatialTrace improvement (Fin.insertNth 0 t z) =
      Real.cos t * (-3 * cubeBump z - 2 * laplacianBump z) :=
  spatialTrace_improvement t z

example (t : ℝ) :
    sliceIntegral (spatialTrace improvement) cubeLo cubeHi t =
      -3 * Real.cos t * ∫ z in cube, cubeBump z :=
  sliceIntegral_spatialTrace_improvement t

example :
    sliceIntegral (spatialTrace improvement) cubeLo cubeHi 0 ≠ 0 :=
  sliceIntegral_spatialTrace_improvement_zero_ne

example (t : ℝ) :
    virialMoment improvement cubeLo cubeHi t =
      Real.sin t * ∫ z in cube, ∑ α : Fin 3, z α * spatialPartial cubeBump α z :=
  virialMoment_improvement t

example :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      sliceIntegral (spatialTrace improvement) cubeLo cubeHi t) atTop (𝓝 0) :=
  tendsto_average_spatialTrace_improvement

example :
    Spacetime → ℝ :=
  staticDensity

example :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      (sliceIntegral ((ChargedDust.staticNeutral staticDensity).totalStress (fun _ => 0) 0 0)
          cubeLo cubeHi t -
        sliceIntegral (ChargedDust.staticNeutral staticDensity).massDensity cubeLo cubeHi t))
      atTop (𝓝 0) :=
  tendsto_average_energy_sub_restMass_cubeBump

end ProjectAinos.Electrodynamics.Virial.Examples

end VirialExamples
