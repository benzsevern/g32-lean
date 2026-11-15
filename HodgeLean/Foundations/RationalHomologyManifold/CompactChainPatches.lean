import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Sets.Opens

/-! Compact open shrinkings for finite supported-chain patching.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
open TopologicalSpace
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A finite open cover of a compact set can be shrunk while retaining that cover.
Source: Bredon, Sheaf Theory, second edition, II.9; compact Hausdorff shrinkings.
HC no distance; AV milestone no distance.
-/
theorem compact_open_patch_shrinking {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {ι : Type*} [Fintype ι]
    (K : Set X) (hK : IsCompact K) (U : ι → Opens X)
    (hcover : K ⊆ ⋃ i, (U i : Set X)) :
    ∃ W : ι → Opens X, K ⊆ ⋃ i, (W i : Set X) ∧
      ∀ i, closure (W i : Set X) ⊆ U i := by
  classical
  obtain ⟨A, hAc, hAU, hKA⟩ := hK.finite_compact_cover (Finset.univ : Finset ι)
    (fun i => (U i : Set X)) (fun i _ => (U i).isOpen) (by simpa using hcover)
  choose V hVo hAV hcl using fun i =>
    normal_exists_closure_subset (hAc i).isClosed (U i).isOpen (hAU i)
  refine ⟨fun i => ⟨V i, hVo i⟩, ?_, hcl⟩
  intro x hx
  rw [hKA] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, _, hxA⟩ := hx
  exact Set.mem_iUnion.mpr ⟨i, hAV i hxA⟩

#print axioms compact_open_patch_shrinking
end HodgeLean.Foundations.RationalHomologyManifold
