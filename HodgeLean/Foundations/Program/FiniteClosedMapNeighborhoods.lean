module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Maps.Basic

/-! # Neighborhoods of finite fibres of closed maps -/
public section
namespace HodgeLean.Foundations.Program

/-- A closed map carries containment of its fibre in an open set to containment
of the preimage of a target neighborhood in that open set. -/
theorem closedMap_fibre_neighborhood
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : IsClosedMap q) (y : B)
    {U : Set A} (hU : IsOpen U) (hfibre : q ⁻¹' {y} ⊆ U) :
    ∃ V : Set B, IsOpen V ∧ y ∈ V ∧ q ⁻¹' V ⊆ U := by
  refine ⟨(q '' Uᶜ)ᶜ, (hq _ hU.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hfibre (by simpa using hxy))
  · intro x hx
    by_contra hxu
    exact hx ⟨x, hxu, rfl⟩

/-- Prescribed neighborhoods of a finite fibre can be refined to disjoint open
sets whose union contains the full preimage of a target neighborhood. -/
theorem finite_closedMap_disjoint_fibre_neighborhoods
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space A]
    {q : A → B} (hq : IsClosedMap q) (y : B)
    (hfinite : (q ⁻¹' {y}).Finite) (O : A → Set A)
    (hO : ∀ x ∈ q ⁻¹' {y}, IsOpen (O x) ∧ x ∈ O x) :
    ∃ (U : A → Set A) (V : Set B),
      (∀ x ∈ q ⁻¹' {y}, IsOpen (U x) ∧ x ∈ U x ∧ U x ⊆ O x) ∧
      (q ⁻¹' {y}).PairwiseDisjoint U ∧
      IsOpen V ∧ y ∈ V ∧ q ⁻¹' V ⊆ ⋃ x ∈ q ⁻¹' {y}, U x := by
  obtain ⟨W, hW, hdisj⟩ := hfinite.t2_separation
  let U : A → Set A := fun x => W x ∩ O x
  have hopen : IsOpen (⋃ x ∈ q ⁻¹' {y}, U x) := by
    apply isOpen_iUnion
    intro x
    apply isOpen_iUnion
    intro hx
    exact (hW x).2.inter (hO x hx).1
  have hfibre : q ⁻¹' {y} ⊆ ⋃ x ∈ q ⁻¹' {y}, U x := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨x, hx, (hW x).1, (hO x hx).2⟩
  obtain ⟨V, hV, hy, hpre⟩ := closedMap_fibre_neighborhood hq y hopen hfibre
  refine ⟨U, V, ?_, ?_, hV, hy, hpre⟩
  · intro x hx
    exact ⟨(hW x).2.inter (hO x hx).1,
      ⟨(hW x).1, (hO x hx).2⟩, Set.inter_subset_right⟩
  · intro x hx z hz hne
    exact (hdisj hx hz hne).mono Set.inter_subset_left Set.inter_subset_left

end HodgeLean.Foundations.Program
