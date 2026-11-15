import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Separation.Hausdorff

/-! Ambient limit membership for finite continuous section families. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_mem_of_closure_finite_sections
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {ι : Type*} [Finite ι] (C : Set X) (hC : IsOpen C) (f : ι → C → Y)
    (hf : ∀ i, Continuous (f i)) (S : Set (Y × X))
    (hS : ∀ y a (ha : a ∈ C), (y, a) ∈ S ↔ ∃ i, y = f i ⟨a, ha⟩)
    (y : Y) (a : X) (ha : a ∈ C) (hx : (y, a) ∈ closure S) : (y, a) ∈ S := by
  let e : Y × C → Y × X := Prod.map id Subtype.val
  have he : IsOpenMap e := IsOpenMap.id.prodMap hC.isOpenMap_subtype_val
  have hT : e ⁻¹' S = ⋃ i, {p : Y × C | p.1 = f i p.2} := by
    ext p
    rw [Set.mem_iUnion]
    exact hS p.1 p.2.val p.2.property
  have hc : IsClosed (e ⁻¹' S) := by
    rw [hT]
    exact isClosed_iUnion_of_finite (fun i => isClosed_eq continuous_fst ((hf i).comp continuous_snd))
  have hx' : (y, (⟨a, ha⟩ : C)) ∈ closure (e ⁻¹' S) :=
    he.preimage_closure_subset_closure_preimage hx
  exact hc.closure_subset hx'

end HodgeLean.Foundations.Program
