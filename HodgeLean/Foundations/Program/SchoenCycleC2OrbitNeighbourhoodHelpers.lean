import HodgeLean.Foundations.Program.SchoenCycleC2MultiplicityHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A point in one of finitely many disjoint closed sets has an open neighbourhood
missing every other member of the family. -/
theorem s2e_disjoint_closed_family_neighbourhood
    {M : Type} [TopologicalSpace M] {m : ℕ} (S : Fin m → Set M)
    (hclosed : ∀ t, IsClosed (S t))
    (hdisj : ∀ s t, s ≠ t → Disjoint (S s) (S t))
    (t : Fin m) (x : M) (hx : x ∈ S t) :
    ∃ V : Opens M, x ∈ V ∧ ∀ s, s ≠ t → ∀ y ∈ V, y ∉ S s := by
  let A : Set M := ⋃ s : Fin m, ⋃ (_ : s ≠ t), S s
  have hc : IsClosed A := isClosed_iUnion_of_finite fun s =>
    isClosed_iUnion_of_finite fun _ => hclosed s
  refine ⟨⟨Aᶜ, hc.isOpen_compl⟩, ?_, ?_⟩
  · intro h
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
    obtain ⟨hne, hxs⟩ := Set.mem_iUnion.mp hs
    exact Set.disjoint_left.mp (hdisj s t hne) hxs hx
  · intro s hne y hy hys
    exact hy (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hne, hys⟩⟩)

end HodgeLean.Foundations.Program
