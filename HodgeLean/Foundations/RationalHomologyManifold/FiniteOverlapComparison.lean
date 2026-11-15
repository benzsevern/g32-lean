import HodgeLean.Foundations.RationalHomologyManifold.CompactSubdivisionEquality
import Mathlib.Topology.Separation.Regular

/-! Uniform actual relative-chain comparisons on finitely many compact overlaps.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Finitely many ambient representatives agreeing as sheaf sections yield one subdivision depth and actual relative-chain equality near every compact overlap.
Source: Bredon, Sheaf Theory, second edition, VI.12; compact overlap comparison for supported chains.
HC no distance; AV milestone no distance.
-/
theorem finite_ambient_overlap_comparison {ι : Type} [Fintype ι]
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] (n m : ℕ)
    (V W : ι → Opens X) (hcl : ∀ i, closure (W i : Set X) ⊆ V i)
    (z : ι → (SingularChainComplex ℚ X).X n)
    (hcompat : ∀ i j, (subdivisionAmbientSectionMap X n (V i ⊓ V j) m).hom (z i) =
      (subdivisionAmbientSectionMap X n (V i ⊓ V j) m).hom (z j)) :
    ∃ (D : ℕ) (N : ι → ι → Opens X), ∀ i j,
      closure (W i : Set X) ∩ closure (W j : Set X) ⊆ N i j ∧
      N i j ≤ V i ⊓ V j ∧
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (N i j : Set X)ᶜ)).f n
        ((rationalSubdivisionIterate X D).f n (z i)) =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (N i j : Set X)ᶜ)).f n
        ((rationalSubdivisionIterate X D).f n (z j)) := by
  classical
  have hp (ij : ι × ι) := subdivisionAmbientSection_eq_near_compact X n m
    (V ij.1 ⊓ V ij.2) (z ij.1) (z ij.2) (hcompat ij.1 ij.2)
    (closure (W ij.1 : Set X) ∩ closure (W ij.2 : Set X))
    (isClosed_closure.inter isClosed_closure).isCompact
    (fun _ hx => ⟨hcl ij.1 hx.1, hcl ij.2 hx.2⟩)
  choose N hN r hKN he using hp
  let D := Finset.univ.sup r
  refine ⟨D, (fun i j => N (i, j)), fun i j => ⟨hKN (i, j), hN (i, j), ?_⟩⟩
  have hr : r (i, j) ≤ D := Finset.le_sup (Finset.mem_univ (i, j))
  have he' := rationalSubdivision_preserves_supported_equality X n (D - r (i, j)) (N (i, j))
    ((rationalSubdivisionIterate X (r (i, j))).f n (z i))
    ((rationalSubdivisionIterate X (r (i, j))).f n (z j)) (he (i, j))
  change (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (N (i, j) : Set X)ᶜ)).f n
      ((rationalSubdivisionIterate X (r (i, j)) ≫
        rationalSubdivisionIterate X (D - r (i, j))).f n (z i)) =
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (N (i, j) : Set X)ᶜ)).f n
      ((rationalSubdivisionIterate X (r (i, j)) ≫
        rationalSubdivisionIterate X (D - r (i, j))).f n (z j)) at he'
  rw [← rationalSubdivisionIterate_add, Nat.add_sub_of_le hr] at he'
  exact he'

#print axioms finite_ambient_overlap_comparison
end HodgeLean.Foundations.RationalHomologyManifold
