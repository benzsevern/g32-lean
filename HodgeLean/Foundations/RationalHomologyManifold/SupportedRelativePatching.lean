import HodgeLean.Foundations.RationalHomologyManifold.ChainSupport
import HodgeLean.Foundations.RationalHomologyManifold.RelativeCoefficientCriterion

/-! Finite patching for actual relative chains supported on subsets.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Relative chains supported on a subset agree precisely on coefficients of simplices meeting that subset.
Source: Bredon, Sheaf Theory, second edition, VI.12; supported singular chains.
HC no distance; AV milestone no distance.
-/
theorem supportedChainProjection_eq_iff_coefficients (X : TopCat.{0}) (U : Set X) (n : ℕ)
    (z w : (SingularChainComplex ℚ X).X n) :
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) Uᶜ)).f n z =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) Uᶜ)).f n w ↔
      ∀ s, (∃ x, (X.toSSetObjEquiv _ s) x ∈ U) →
        (singularChainCoefficient X n s).hom z = (singularChainCoefficient X n s).hom w := by
  rw [relativeChainProjection_eq_iff_coefficients]
  simp_rw [singularSimplex_absent_subspace_iff, Set.mem_compl_iff, not_not]
  rfl

#print axioms supportedChainProjection_eq_iff_coefficients
/-- Finitely many chains with compatible coefficients on meeting simplices yield one chain with every prescribed supported projection.
Source: Bredon, Sheaf Theory, second edition, VI.12; finite supported-chain patching.
HC no distance; AV milestone no distance.
-/
theorem singularChain_finite_supported_patching {κ : Type} [Fintype κ]
    (X : TopCat.{0}) (n : ℕ) (U : κ → Set X) (z : κ → (SingularChainComplex ℚ X).X n)
    (hcompat : ∀ i j s, (∃ x, (X.toSSetObjEquiv _ s) x ∈ U i) →
      (∃ x, (X.toSSetObjEquiv _ s) x ∈ U j) →
      (singularChainCoefficient X n s).hom (z i) =
        (singularChainCoefficient X n s).hom (z j)) :
    ∃ w : (SingularChainComplex ℚ X).X n, ∀ i,
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U i)ᶜ)).f n w =
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U i)ᶜ)).f n (z i) := by
  obtain ⟨w, hw⟩ := singularChain_finite_coefficient_patching X n z
    (fun i s => ∃ x, (X.toSSetObjEquiv _ s) x ∈ U i) hcompat
  refine ⟨w, fun i => ?_⟩
  exact (supportedChainProjection_eq_iff_coefficients X (U i) n w (z i)).mpr (hw i)

#print axioms singularChain_finite_supported_patching
/-- Supported relative-chain equality is detected on any family covering the support set.
Source: Bredon, Sheaf Theory, second edition, VI.12; separatedness of supported chains.
HC no distance; AV milestone no distance.
-/
theorem supportedChainProjection_eq_of_cover {ι : Type} (X : TopCat.{0}) (n : ℕ)
    (U : Set X) (V : ι → Set X) (hcover : U ⊆ ⋃ i, V i)
    (z w : (SingularChainComplex ℚ X).X n)
    (h : ∀ i, (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V i)ᶜ)).f n z =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V i)ᶜ)).f n w) :
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) Uᶜ)).f n z =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) Uᶜ)).f n w := by
  apply (supportedChainProjection_eq_iff_coefficients X U n z w).mpr
  rintro s ⟨a, ha⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ha)
  exact (supportedChainProjection_eq_iff_coefficients X (V i) n z w).mp (h i) s ⟨a, hi⟩

#print axioms supportedChainProjection_eq_of_cover
/-- Projection to chains supported on the whole space retains every ambient chain.
Source: Hatcher, Algebraic Topology, section 2.1, relative chains modulo the empty subspace.
HC no distance; AV milestone no distance.
-/
theorem topSupportedChainProjection_injective (X : TopCat.{0}) (n : ℕ) :
    Function.Injective ((relativeChainProjection ℚ
      (TopPair.ofSubset (X := X) ((⊤ : TopologicalSpace.Opens X) : Set X)ᶜ)).f n) := by
  classical
  intro z w h
  apply singularChain_ext X n z w
  intro s
  exact (supportedChainProjection_eq_iff_coefficients X
    ((⊤ : TopologicalSpace.Opens X) : Set X) n z w).mp h s ⟨Classical.arbitrary _, trivial⟩

#print axioms topSupportedChainProjection_injective
end HodgeLean.Foundations.RationalHomologyManifold
