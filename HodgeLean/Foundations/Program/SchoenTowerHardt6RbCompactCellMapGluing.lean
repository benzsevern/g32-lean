import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Set.UnionLift

/-! Compatible homeomorphisms on a finite compact cell cover assemble to an actual global homeomorphism. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_cell_map_gluing {E F ι : Type*}
    [TopologicalSpace E] [T2Space E] [TopologicalSpace F] [T2Space F] [Zero F] [Finite ι]
    (C : ι → Set E) (D : ι → Set F) (hC : ∀ i, IsCompact (C i))
    (e : ∀ i, C i ≃ₜ D i)
    (hagree : ∀ i j (x : E) (hi : x ∈ C i) (hj : x ∈ C j),
      (e i ⟨x, hi⟩).val = (e j ⟨x, hj⟩).val)
    (hinj : ∀ i j (x : C i) (y : C j), (e i x).val = (e j y).val → x.val = y.val) :
    ∃ H : (⋃ i, C i) ≃ₜ (⋃ i, D i),
      ∀ i (x : C i), (H ⟨x.val, Set.mem_iUnion.mpr ⟨i, x.property⟩⟩).val = (e i x).val := by
  classical
  let U := ⋃ i, C i
  let p : U → F := Set.iUnionLift C (fun i x => (e i x).val) hagree U Set.Subset.rfl
  let φ : E → F := fun x => if hx : x ∈ U then p ⟨x, hx⟩ else 0
  have hφ (i : ι) (x : C i) : φ x.val = (e i x).val := by
    dsimp only [φ]
    rw [dif_pos (Set.mem_iUnion.mpr ⟨i, x.property⟩)]
    exact Set.iUnionLift_mk (S := C) (f := fun i x => (e i x).val) (hf := hagree)
      (hT := Set.Subset.rfl) x _
  have hc : ContinuousOn φ U := by
    apply LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite C) (fun i => (hC i).isClosed)
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    exact (e i).continuous.subtype_val.congr (fun x => (hφ i x).symm)
  have hbij : Set.BijOn φ U (⋃ i, D i) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rw [hφ i ⟨x, hi⟩]
      exact Set.mem_iUnion.mpr ⟨i, (e i ⟨x, hi⟩).property⟩
    · intro x hx y hy he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
      exact hinj i j ⟨x, hi⟩ ⟨y, hj⟩ ((hφ i ⟨x, hi⟩).symm.trans (he.trans (hφ j ⟨y, hj⟩)))
    · intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      let x := (e i).symm ⟨y, hi⟩
      refine ⟨x.val, Set.mem_iUnion.mpr ⟨i, x.property⟩, ?_⟩
      exact (hφ i x).trans (congrArg Subtype.val ((e i).apply_symm_apply ⟨y, hi⟩))
  letI : CompactSpace U := isCompact_iff_compactSpace.mp (isCompact_iUnion hC)
  have he : Continuous (hbij.equiv φ) := hc.domRestrict.subtype_mk _
  exact ⟨he.homeoOfEquivCompactToT2, fun i x => hφ i x⟩

end HodgeLean.Foundations.Program
