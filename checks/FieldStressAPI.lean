/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.ChargedDust

/-! Public consumers of the energy and the momentum of the field: the rules of the derivative,
the theorem of Poynting and the balance of the momentum in an inertial frame, the balances on a
box, the stress tensor with its symmetry, its trace, the energy density of an observer, its
components and its divergence, and the conservation of the total stress with charged dust.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open MeasureTheory Set
open scoped ContDiff
namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    partialAt (fun y => f y * g y) μ x = f x * partialAt g μ x + g x * partialAt f μ x :=
  partialAt_mul hf hg μ

example {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    partialAt (fun y => f y + g y) μ x = partialAt f μ x + partialAt g μ x :=
  partialAt_add hf hg μ

example {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    partialAt (fun y => f y - g y) μ x = partialAt f μ x - partialAt g μ x :=
  partialAt_sub hf hg μ

example (c : ℝ) {f : Spacetime → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f x) (μ : Fin 4) :
    partialAt (fun y => c * f y) μ x = c * partialAt f μ x :=
  partialAt_const_mul c hf μ

example {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x)
    (a b : Fin 4) : DifferentiableAt ℝ (fun y => component (G y) a b) x :=
  differentiableAt_component hG a b

example {G : Field} {x : Spacetime}
    (hG : DifferentiableAt ℝ G x) (i : Fin 3) : DifferentiableAt ℝ (electricField G i) x :=
  differentiableAt_electricField hG i

example {G : Field} {x : Spacetime}
    (hG : DifferentiableAt ℝ G x) (i : Fin 3) : DifferentiableAt ℝ (magneticField G i) x :=
  differentiableAt_magneticField hG i

example : (Fin.succ (0 : Fin 3) : Fin 4) = 1 :=
  fin_succ_zero

example : (Fin.succ (1 : Fin 3) : Fin 4) = 2 :=
  fin_succ_one

example : (Fin.succ (2 : Fin 3) : Fin 4) = 3 :=
  fin_succ_two

example {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime}
    (hfar : ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0)
    (hamp : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ) :
    partialAt (energyDensity F) 0 x + divergence3 (poyntingVector F) x =
      -(electricField F 0 x * k x 1 + electricField F 1 x * k x 2 +
        electricField F 2 x * k x 3) :=
  poynting_local hF hfar hamp

example {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime}
    (hgB : divergence3 (magneticField F) x = 0)
    (hfar : ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0)
    (hgE : divergence3 (electricField F) x = k x 0)
    (hamp : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ)
    (i : Fin 3) :
    partialAt (poyntingVector F i) 0 x + ∑ j : Fin 3, partialAt (maxwellStress F i j) j.succ x =
      -forceDensity F k x i :=
  momentum_local hF hgB hfar hgE hamp i

example {P : Spacetime → Spacetime} (hP : ContDiff ℝ 1 P) {a b : Spacetime}
    (hle : a ≤ b) :
    charge P a b (b 0) - charge P a b (a 0) + ∑ i : Fin 3, faceFlux P a b i.succ =
      ∫ y in Icc a b, divergence4 P y :=
  box_divergence hP hle

example {P : Spacetime → Spacetime} {x : Spacetime}
    (hP : DifferentiableAt ℝ P x) :
    divergence4 P x = ∑ μ : Fin 4, partialAt (fun y => P y μ) μ x :=
  divergence4_eq hP

example {n : ℕ∞ω} {G : Field} (hG : ContDiff ℝ n G) (a b : Fin 4) :
    ContDiff ℝ n (fun y => component (G y) a b) :=
  contDiff_component hG a b

example {n : ℕ∞ω} {G : Field} (hG : ContDiff ℝ n G) (i : Fin 3) :
    ContDiff ℝ n (electricField G i) :=
  contDiff_electricField hG i

example {n : ℕ∞ω} {G : Field} (hG : ContDiff ℝ n G) (i : Fin 3) :
    ContDiff ℝ n (magneticField G i) :=
  contDiff_magneticField hG i

example {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (energyCurrent F) :=
  contDiff_energyCurrent hF

example {F : Field} (hF : ContDiff ℝ 2 F) {k : Spacetime → Spacetime}
    {a b : Spacetime} (hle : a ≤ b)
    (hfar : ∀ y ∈ Icc a b, ∀ i,
      partialAt (magneticField F i) 0 y + curl (electricField F) y i = 0)
    (hamp : ∀ y ∈ Icc a b, ∀ i,
      curl (magneticField F) y i - partialAt (electricField F i) 0 y = k y i.succ) :
    charge (energyCurrent F) a b (b 0) - charge (energyCurrent F) a b (a 0) =
      -∑ i : Fin 3, faceFlux (energyCurrent F) a b i.succ -
        ∫ y in Icc a b, (electricField F 0 y * k y 1 + electricField F 1 y * k y 2 +
          electricField F 2 y * k y 3) :=
  energy_balance hF hle hfar hamp

example {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (energyDensity F) :=
  contDiff_energyDensity hF

example {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) (i : Fin 3) :
    ContDiff ℝ n (poyntingVector F i) :=
  contDiff_poyntingVector hF i

example {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) (i j : Fin 3) :
    ContDiff ℝ n (maxwellStress F i j) :=
  contDiff_maxwellStress hF i j

example {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) (i : Fin 3) :
    ContDiff ℝ n (momentumCurrent F i) :=
  contDiff_momentumCurrent hF i

example {F : Field} (hF : ContDiff ℝ 2 F) {k : Spacetime → Spacetime}
    {a b : Spacetime} (hle : a ≤ b)
    (hgB : ∀ y ∈ Icc a b, divergence3 (magneticField F) y = 0)
    (hfar : ∀ y ∈ Icc a b, ∀ i,
      partialAt (magneticField F i) 0 y + curl (electricField F) y i = 0)
    (hgE : ∀ y ∈ Icc a b, divergence3 (electricField F) y = k y 0)
    (hamp : ∀ y ∈ Icc a b, ∀ i,
      curl (magneticField F) y i - partialAt (electricField F i) 0 y = k y i.succ)
    (i : Fin 3) :
    charge (momentumCurrent F i) a b (b 0) - charge (momentumCurrent F i) a b (a 0) =
      -∑ j : Fin 3, faceFlux (momentumCurrent F i) a b j.succ -
        ∫ y in Icc a b, forceDensity F k y i :=
  momentum_balance hF hle hgB hfar hgE hamp i

end ProjectAinos.Electrodynamics

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (a b : OneForm) : covectorPairing a b = covectorPairing b a :=
  covectorPairing_comm a b

example (G : TwoForm) (v w : Spacetime) : stressForm G v w = stressForm G w v :=
  stressForm_symm G v w

example (G : TwoForm) (v : Spacetime) (α : Fin 4) :
    oneCovector (G.curryLeft v) (Pi.single α 1) = G ![v, Pi.single α 1] :=
  oneCovector_curryLeft_single G v α

example (μ : Fin 4) :
    lorentzSign .timeNegative μ * lorentzSign .timeNegative μ = 1 :=
  lorentzSign_sq μ

example (μ ν : Fin 4) :
    minkowskiForm .timeNegative 3 (Pi.single μ 1) (Pi.single ν 1) =
      if μ = ν then lorentzSign .timeNegative μ else 0 :=
  minkowskiForm_single μ ν

example (G : TwoForm) :
    ∑ μ : Fin 4, lorentzSign .timeNegative μ * stressForm G (Pi.single μ 1) (Pi.single μ 1) =
      0 :=
  stressForm_trace G

example (u : Observer 3) (G : TwoForm) :
    stressForm G u.velocity u.velocity =
      (1 / 2 : ℝ) * (covectorPairing (electric u G) (electric u G) +
        covectorPairing (magnetic u G) (magnetic u G)) :=
  stressForm_observer u G

example (G : TwoForm) :
    tensorContraction G G = 2 * (∑ i : Fin 3, magneticVector G i ^ 2 -
      ∑ i : Fin 3, electricVector G i ^ 2) :=
  tensorContraction_vectors G

example (G : TwoForm) :
    stressForm G (Pi.single 0 1) (Pi.single 0 1) =
      (1 / 2 : ℝ) * (∑ i : Fin 3, electricVector G i ^ 2 +
        ∑ i : Fin 3, magneticVector G i ^ 2) :=
  stressForm_zero_zero G

example (G : TwoForm) :
    stressForm G (Pi.single 0 1) (Pi.single 1 1) =
        -(electricVector G 1 * magneticVector G 2 - electricVector G 2 * magneticVector G 1) ∧
      stressForm G (Pi.single 0 1) (Pi.single 2 1) =
        -(electricVector G 2 * magneticVector G 0 - electricVector G 0 * magneticVector G 2) ∧
      stressForm G (Pi.single 0 1) (Pi.single 3 1) =
        -(electricVector G 0 * magneticVector G 1 - electricVector G 1 * magneticVector G 0) :=
  stressForm_zero_succ G

example (G : TwoForm) (i j : Fin 3) :
    stressForm G (Pi.single i.succ 1) (Pi.single j.succ 1) =
      -(electricVector G i * electricVector G j + magneticVector G i * magneticVector G j) +
        if i = j then (1 / 2 : ℝ) * (∑ l : Fin 3, electricVector G l ^ 2 +
          ∑ l : Fin 3, magneticVector G l ^ 2) else 0 :=
  stressForm_succ_succ G i j

example : lorentzSign .timeNegative (0 : Fin 4) = -1 :=
  lorentzSign_zero

example (i : Fin 3) : lorentzSign .timeNegative i.succ = 1 :=
  lorentzSign_succ i

example (F : Field) : raisedStress F 0 0 = energyDensity F :=
  raisedStress_zero_zero F

example (F : Field) (i : Fin 3) :
    raisedStress F i.succ 0 = poyntingVector F i :=
  raisedStress_succ_zero F i

example (F : Field) (i : Fin 3) :
    raisedStress F 0 i.succ = poyntingVector F i :=
  raisedStress_zero_succ F i

example (F : Field) (i j : Fin 3) :
    raisedStress F i.succ j.succ = maxwellStress F i j :=
  raisedStress_succ_succ F i j

example {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime}
    (hfar : ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0)
    (hamp : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ) :
    ∑ μ : Fin 4, partialAt (raisedStress F μ 0) μ x =
      -(electricField F 0 x * k x 1 + electricField F 1 x * k x 2 +
        electricField F 2 x * k x 3) :=
  divergence_raisedStress_zero hF hfar hamp

example {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime}
    (hgB : divergence3 (magneticField F) x = 0)
    (hfar : ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0)
    (hgE : divergence3 (electricField F) x = k x 0)
    (hamp : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ)
    (i : Fin 3) :
    ∑ μ : Fin 4, partialAt (raisedStress F μ i.succ) μ x = -forceDensity F k x i :=
  divergence_raisedStress_succ hF hgB hfar hgE hamp i

end ProjectAinos.Electrodynamics

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

namespace ChargedDust

variable (D : ChargedDust)

variable {D}

example {x : Spacetime}
    (hμ : ∀ l : Fin 4, DifferentiableAt ℝ (fun y => D.massDensity y * D.velocity y l) x)
    (hU : ∀ ν : Fin 4, DifferentiableAt ℝ (fun y => D.velocity y ν) x)
    (hcont : ∑ l : Fin 4, partialAt (fun y => D.massDensity y * D.velocity y l) l x = 0)
    (ν : Fin 4) :
    ∑ μ : Fin 4, partialAt (D.matterStress μ ν) μ x = D.massDensity x * D.convective x ν :=
  divergence_matterStress hμ hU hcont ν

end ChargedDust

example (e : ℝ) (G : TwoForm) (v : Spacetime) :
    lorentzForce e G v 0 = e * (electricVector G 0 * v 1 + electricVector G 1 * v 2 +
      electricVector G 2 * v 3) :=
  lorentzForce_zero_eq e G v

example (e : ℝ) (G : TwoForm) (v : Spacetime) :
    lorentzForce e G v 1 = e * (v 0 * electricVector G 0 + (v 2 * magneticVector G 2 -
      v 3 * magneticVector G 1)) ∧
    lorentzForce e G v 2 = e * (v 0 * electricVector G 1 + (v 3 * magneticVector G 0 -
      v 1 * magneticVector G 2)) ∧
    lorentzForce e G v 3 = e * (v 0 * electricVector G 2 + (v 1 * magneticVector G 1 -
      v 2 * magneticVector G 0)) :=
  lorentzForce_succ_eq e G v

example {F : Field} {D : ChargedDust} {x : Spacetime}
    (hF : DifferentiableAt ℝ F x)
    (hμ : ∀ l : Fin 4, DifferentiableAt ℝ (fun y => D.massDensity y * D.velocity y l) x)
    (hU : ∀ ν : Fin 4, DifferentiableAt ℝ (fun y => D.velocity y ν) x)
    (hcont : ∑ l : Fin 4, partialAt (fun y => D.massDensity y * D.velocity y l) l x = 0)
    (hmotion : ∀ ν : Fin 4, D.massDensity x * D.convective x ν =
      lorentzForce (D.chargeDensity x) (F x) (D.velocity x) ν)
    (hgB : divergence3 (magneticField F) x = 0)
    (hfar : ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0)
    (hgE : divergence3 (electricField F) x = D.current x 0)
    (hamp : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x =
      D.current x i.succ)
    (ν : Fin 4) :
    ∑ μ : Fin 4, partialAt (raisedStress F μ ν) μ x +
      ∑ μ : Fin 4, partialAt (D.matterStress μ ν) μ x = 0 :=
  total_stress_conserved hF hμ hU hcont hmotion hgB hfar hgE hamp ν

example (c : ℝ) (μ : Fin 4) (x : Spacetime) :
    partialAt (fun _ => c) μ x = 0 :=
  partialAt_const c μ x

example (μ₀ : ℝ) (U₀ : Spacetime) (F₀ : TwoForm)
    (x : Spacetime) (ν : Fin 4) :
    ∑ μ : Fin 4, partialAt (raisedStress (fun _ => F₀) μ ν) μ x +
      ∑ μ : Fin 4, partialAt ((ChargedDust.uniform μ₀ U₀).matterStress μ ν) μ x = 0 :=
  total_stress_conserved_uniform μ₀ U₀ F₀ x ν

end ProjectAinos.Electrodynamics
