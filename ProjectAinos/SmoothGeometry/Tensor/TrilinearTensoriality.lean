/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Tensor.Tensoriality

/-! # Tensoriality in three slots

An operation `Φ s t r` on locally `Cⁿ` sections of three bundles that is linear over scalar
germs in each slot, for every choice of locally `Cⁿ` sections in the other two slots, descends
to a continuous trilinear map on the fibres at a point. The hypotheses quantify over the other
two slots, so the three slots may need different regularity of the remaining arguments.

* `ContMDiffTensorialAt.pointwise₃`: such an operation depends only on the three fibre values.
* `ContMDiffTensorialAt.mkHom₃`: the continuous trilinear map on the actual fibres, evaluated on
  the canonical local extensions `extend` of the three vectors (`mkHom₃_apply_eq_extend`).
* `ContMDiffTensorialAt.mkHom₃_apply`: its value on the values of any locally `Cⁿ` sections is
  the operation applied to these sections.

The construction iterates `ContMDiffTensorialAt.mkHom`; it uses no global frame or extension.
-/

@[expose] public section
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

/-- An operation that is tensorial in each of three slots depends only on the three values of
its arguments at the point. -/
theorem pointwise₃
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
    Φ s t r = Φ s' t' r' := by
  calc
    Φ s t r = Φ s' t r := (h₁ t r ht hr).pointwise hs hs' hss'
    _ = Φ s' t' r := (h₂ s' r hs' hr).pointwise ht ht' htt'
    _ = Φ s' t' r' := (h₃ s' t' hs' ht').pointwise hr hr' hrr'

variable [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousSMul ℝ T]

/-- The continuous trilinear map on the actual fibres defined by an operation that is
tensorial in each of three slots. Its value is the operation on the canonical local
extensions of the three vectors. -/
def mkHom₃ (Φ : (∀ y, A.Fiber y) → (∀ y, B.Fiber y) → (∀ y, C.Fiber y) → T) (x : M)
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
  have : T2Space (A.Fiber x) := FiberBundle.t2Space A.Model A.Fiber x
  have : FiniteDimensional ℝ (A.Fiber x) := VectorBundle.finiteDimensional ℝ A.Model A.Fiber x
  have : T2Space (B.Fiber x) := FiberBundle.t2Space B.Model B.Fiber x
  have : FiniteDimensional ℝ (B.Fiber x) := VectorBundle.finiteDimensional ℝ B.Model B.Fiber x
  LinearMap.toContinuousLinearMap {
    toFun u := LinearMap.toContinuousLinearMap {
      toFun v := mkHom (fun r => Φ (extend A.Model u) (extend B.Model v) r) x
        (h₃ _ _ (contMDiffAt_extend ..) (contMDiffAt_extend ..))
      map_add' v w := by
        ext z
        change Φ (extend A.Model u) (extend B.Model (v + w)) (extend C.Model z) =
          Φ (extend A.Model u) (extend B.Model v) (extend C.Model z) +
          Φ (extend A.Model u) (extend B.Model w) (extend C.Model z)
        have h := h₂ (extend A.Model u) (extend C.Model z) (contMDiffAt_extend ..)
          (contMDiffAt_extend ..)
        rw [← h.add (contMDiffAt_extend ..) (contMDiffAt_extend ..)]
        exact h.pointwise (contMDiffAt_extend ..)
          ((contMDiffAt_extend ..).add_section (contMDiffAt_extend ..)) (by simp)
      map_smul' a v := by
        ext z
        change Φ (extend A.Model u) (extend B.Model (a • v)) (extend C.Model z) =
          a • Φ (extend A.Model u) (extend B.Model v) (extend C.Model z)
        have h := h₂ (extend A.Model u) (extend C.Model z) (contMDiffAt_extend ..)
          (contMDiffAt_extend ..)
        rw [← h.smul (f := fun _ => a) contMDiffAt_const (contMDiffAt_extend ..)]
        exact h.pointwise (contMDiffAt_extend ..)
          (contMDiffAt_const.smul_section (contMDiffAt_extend ..)) (by simp) }
    map_add' u u' := by
      ext v z
      change Φ (extend A.Model (u + u')) (extend B.Model v) (extend C.Model z) =
        Φ (extend A.Model u) (extend B.Model v) (extend C.Model z) +
        Φ (extend A.Model u') (extend B.Model v) (extend C.Model z)
      have h := h₁ (extend B.Model v) (extend C.Model z) (contMDiffAt_extend ..)
        (contMDiffAt_extend ..)
      rw [← h.add (contMDiffAt_extend ..) (contMDiffAt_extend ..)]
      exact h.pointwise (contMDiffAt_extend ..)
        ((contMDiffAt_extend ..).add_section (contMDiffAt_extend ..)) (by simp)
    map_smul' a u := by
      ext v z
      change Φ (extend A.Model (a • u)) (extend B.Model v) (extend C.Model z) =
        a • Φ (extend A.Model u) (extend B.Model v) (extend C.Model z)
      have h := h₁ (extend B.Model v) (extend C.Model z) (contMDiffAt_extend ..)
        (contMDiffAt_extend ..)
      rw [← h.smul (f := fun _ => a) contMDiffAt_const (contMDiffAt_extend ..)]
      exact h.pointwise (contMDiffAt_extend ..)
        (contMDiffAt_const.smul_section (contMDiffAt_extend ..)) (by simp) }

/-- The trilinear map is the operation on the canonical local extensions of its arguments. -/
@[simp] theorem mkHom₃_apply_eq_extend
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
      Φ (extend A.Model u) (extend B.Model v) (extend C.Model w) := rfl

/-- On the values of locally `Cⁿ` sections, the trilinear map is the operation applied to
these sections. -/
theorem mkHom₃_apply
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
  pointwise₃ h₁ h₂ h₃ (contMDiffAt_extend ..) hs (contMDiffAt_extend ..) ht
    (contMDiffAt_extend ..) hr (by simp) (by simp) (by simp)

end ContMDiffTensorialAt
end ProjectAinos.SmoothGeometry.Tensor
