import HodgeLean.Foundations.RationalHomologyManifold.FiniteOverlapComparison
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionSupportedPatching

/-! Actual finite ambient-chain patching from compatible subdivision sheaf sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Finitely many compatible ambient subdivision sections yield one actual subdivided ambient-chain representative on smaller patches.
Source: Bredon, Sheaf Theory, second edition, VI.12; compact supported-chain patching.
HC no distance; AV milestone no distance.
-/
theorem finite_ambient_sections_patching {ι : Type} [Fintype ι]
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] (n m : ℕ)
    (V W : ι → Opens X) (hcl : ∀ i, closure (W i : Set X) ⊆ V i)
    (z : ι → (SingularChainComplex ℚ X).X n)
    (hcompat : ∀ i j, (subdivisionAmbientSectionMap X n (V i ⊓ V j) m).hom (z i) =
      (subdivisionAmbientSectionMap X n (V i ⊓ V j) m).hom (z j)) :
    ∃ (T : ℕ) (w : (SingularChainComplex ℚ X).X n), ∀ i,
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W i : Set X)ᶜ)).f n w =
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W i : Set X)ᶜ)).f n
          ((rationalSubdivisionIterate X T).f n (z i)) := by
  obtain ⟨D, N, hN⟩ := finite_ambient_overlap_comparison X n m V W hcl z hcompat
  obtain ⟨t, w, hw⟩ := subdivision_finite_supported_patching X n W N
    (fun i j => (hN i j).1) (fun i => (rationalSubdivisionIterate X D).f n (z i))
    (fun i j => (hN i j).2.2)
  refine ⟨D + t, w, fun i => ?_⟩
  have hi := hw i
  change (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W i : Set X)ᶜ)).f n w =
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W i : Set X)ᶜ)).f n
      ((rationalSubdivisionIterate X D ≫ rationalSubdivisionIterate X t).f n (z i)) at hi
  rw [← rationalSubdivisionIterate_add] at hi
  exact hi

#print axioms finite_ambient_sections_patching
end HodgeLean.Foundations.RationalHomologyManifold
