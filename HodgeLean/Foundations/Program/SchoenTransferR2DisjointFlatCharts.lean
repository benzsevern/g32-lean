import HodgeLean.Foundations.Program.SchoenTransferR2CompactFlatDeformation
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! # Flat charts for finite disjoint unions of smooth supports

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Removing the other finitely many closed supports turns a component chart
into a chart for the actual union.
Source: Munkres, Topology, §§16 and 18; finite unions of closed sets.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_disjoint_union_flat_charts
    {X A : Type*} [TopologicalSpace X] [Finite A] (S : A → Closeds X)
    (hdisj : Pairwise (fun i j => Disjoint (S i : Set X) (S j)))
    (hcharts : ∀ i x, x ∈ S i → ∃ r c : ℕ,
      ∃ e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin c → ℂ)),
        x ∈ e.source ∧ ∀ y ∈ e.source, y ∈ S i ↔ (e y).2 = 0) :
    ∀ x ∈ ⋃ i, (S i : Set X), ∃ r c : ℕ,
      ∃ e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin c → ℂ)),
        x ∈ e.source ∧ ∀ y ∈ e.source, y ∈ ⋃ i, (S i : Set X) ↔ (e y).2 = 0 := by
  classical
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨r, c, e, hxe, hflat⟩ := hcharts i x hxi
  let T : Set X := (⋃ j, ⋃ (_ : j ≠ i), (S j : Set X))ᶜ
  have hT : IsOpen T := (isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => (S j).isClosed).isOpen_compl
  have hxT : x ∈ T := by
    intro hx'
    obtain ⟨j, hji, hxj⟩ := Set.mem_iUnion₂.mp hx'
    exact Set.disjoint_left.mp (hdisj hji) hxj hxi
  refine ⟨r, c, e.restrOpen T hT, ⟨hxe, hxT⟩, ?_⟩
  intro y hy
  have hmem : (y ∈ ⋃ j, (S j : Set X)) ↔ y ∈ S i := by
    constructor
    · intro h
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp h
      by_cases hji : j = i
      · exact hji ▸ hyj
      · exact (hy.2 (Set.mem_iUnion₂.mpr ⟨j, hji, hyj⟩)).elim
    · exact fun h => Set.mem_iUnion.mpr ⟨i, h⟩
  exact hmem.trans (hflat y hy.1)

#print axioms s4_assembly_disjoint_union_flat_charts
end HodgeLean.Foundations.Program
