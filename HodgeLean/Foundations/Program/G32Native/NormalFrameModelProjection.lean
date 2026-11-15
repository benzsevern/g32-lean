import Mathlib.Topology.FiberBundle.Trivialization
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.VectorBundle.Basic

/-! # Base projection in the retained bundle model

The inverse product coordinates recover the original base chart inverse.
-/

namespace HodgeLean.Foundations.TubularEuler
open Bundle

theorem normal_frame_model_inverse_proj
    {B A F : Type*} [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace F]
    (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
    (e : Trivialization F (π F E)) (b : OpenPartialHomeomorph B A)
    (q : A × F)
    (hq : q ∈ (e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl F))).target) :
    ((e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl F))).symm q).proj = b.symm q.1 := by
  let P := e.toOpenPartialHomeomorph.trans (b.prod (OpenPartialHomeomorph.refl F))
  let z := P.symm q
  have hz : z ∈ P.source := P.map_target hq
  have he : z.proj ∈ e.baseSet := e.mem_source.mp hz.1
  have hb : z.proj ∈ b.source := by
    have h : (e z).1 ∈ b.source := hz.2.1
    rwa [e.coe_fst' he] at h
  have hv : b z.proj = q.1 := by
    have h := congrArg Prod.fst (P.right_inv hq)
    change b (e z).1 = q.1 at h
    rwa [e.coe_fst' he] at h
  change z.proj = b.symm q.1
  rw [← hv, b.left_inv hb]

#print axioms normal_frame_model_inverse_proj

theorem normal_frame_model_inverse_fibre
    {K B A F : Type*} [Field K]
    [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace F]
    [AddCommGroup F] [Module K F]
    (E : B → Type*) [∀ y, AddCommGroup (E y)] [∀ y, Module K (E y)]
    [TopologicalSpace (TotalSpace F E)]
    (e : Trivialization F (π F E)) [e.IsLinear K]
    (b : OpenPartialHomeomorph B A) (q : A)
    (hq0 : (q, (0 : F)) ∈ (e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl F))).target) :
    ∃ (y : B) (hy : y ∈ e.baseSet), y ∈ b.source ∧ b y = q ∧
      ∀ w : F, ((e.toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl F))).symm (q, w)) =
          (⟨y, (e.linearEquivAt K y hy).symm w⟩ : TotalSpace F E) := by
  let P := e.toOpenPartialHomeomorph.trans (b.prod (OpenPartialHomeomorph.refl F))
  have hq : q ∈ b.target := hq0.1.1
  let y := b.symm q
  have he0 : (P.symm (q, (0 : F))).proj = y :=
    normal_frame_model_inverse_proj E e b (q, 0) hq0
  have hy : y ∈ e.baseSet := he0 ▸ e.mem_source.mp (P.map_target hq0).1
  refine ⟨y, hy, b.map_target hq, b.right_inv hq, ?_⟩
  intro w
  let L := e.linearEquivAt K y hy
  let z : TotalSpace F E := ⟨y, L.symm w⟩
  have hez : e z = (y, w) := by
    apply Prod.ext
    · exact e.coe_fst' hy
    · change L (L.symm w) = w
      exact L.apply_symm_apply w
  have hz : z ∈ P.source := by
    refine ⟨e.mem_source.mpr hy, ?_⟩
    change e z ∈ (b.prod (OpenPartialHomeomorph.refl F)).source
    rw [hez]
    exact ⟨b.map_target hq, Set.mem_univ _⟩
  have hPz : P z = (q, w) := by
    change (b.prod (OpenPartialHomeomorph.refl F)) (e z) = _
    rw [hez]
    change (b (b.symm q), w) = (q, w)
    rw [b.right_inv hq]
  change P.symm (q, w) = z
  rw [← hPz, P.left_inv hz]

#print axioms normal_frame_model_inverse_fibre
end HodgeLean.Foundations.TubularEuler
