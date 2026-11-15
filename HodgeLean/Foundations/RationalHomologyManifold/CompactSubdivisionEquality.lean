import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionEquality
import HodgeLean.Foundations.RationalHomologyManifold.SupportedRelativePatching

/-! Uniform actual subdivision equality near compact supports.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Equality of ambient subdivision sections near a compact set is witnessed by one actual subdivision depth on a neighborhood of that set.
Source: Bredon, Sheaf Theory, second edition, VI.12; compact equality in supported subdivision limits.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSection_eq_near_compact (X : TopCat.{0}) (n m : ℕ)
    (U : Opens X) (z w : (SingularChainComplex ℚ X).X n)
    (hab : (subdivisionAmbientSectionMap X n U m).hom z =
      (subdivisionAmbientSectionMap X n U m).hom w)
    (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (N : Opens X) (hN : N ≤ U) (R : ℕ), K ⊆ N ∧
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (N : Set X)ᶜ)).f n
        ((rationalSubdivisionIterate X R).f n z) =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (N : Set X)ᶜ)).f n
        ((rationalSubdivisionIterate X R).f n w) := by
  classical
  have hloc (x : K) := subdivisionAmbientSection_eq_locally_subdivided X n m U z w hab
    x.val (hKU x.property)
  choose V hV r hxV he using hloc
  have hcover : K ⊆ ⋃ x : K, (V x : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun x : K => (V x : Set X))
    (fun x => (V x).isOpen) hcover
  let N : Opens X := ⨆ i : I, V i
  let R := I.sup r
  have hNU : N ≤ U := iSup_le (fun i => hV i)
  refine ⟨N, hNU, R, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI hx)
    obtain ⟨hiI, hxi⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, hiI⟩, hxi⟩
  · apply supportedChainProjection_eq_of_cover X n (N : Set X)
      (fun i : I => (V i : Set X))
      (fun _ hx => Set.mem_iUnion.mpr (Opens.mem_iSup.mp hx))
    intro i
    have hi : r i ≤ R := Finset.le_sup i.property
    have he' := rationalSubdivision_preserves_supported_equality X n (R - r i) (V i)
      ((rationalSubdivisionIterate X (r i)).f n z)
      ((rationalSubdivisionIterate X (r i)).f n w) (he i)
    change (relativeChainProjection ℚ (TopPair.ofSubset (X := X) ((V i : Opens X) : Set X)ᶜ)).f n
        ((rationalSubdivisionIterate X (r i) ≫ rationalSubdivisionIterate X (R - r i)).f n z) =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) ((V i : Opens X) : Set X)ᶜ)).f n
        ((rationalSubdivisionIterate X (r i) ≫ rationalSubdivisionIterate X (R - r i)).f n w) at he'
    rw [← rationalSubdivisionIterate_add, Nat.add_sub_of_le hi] at he'
    exact he'

#print axioms subdivisionAmbientSection_eq_near_compact
end HodgeLean.Foundations.RationalHomologyManifold
