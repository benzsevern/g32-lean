import HodgeLean.Foundations.RationalHomologyManifold.SmallChainSupport
import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionEquality
import HodgeLean.Foundations.RationalHomologyManifold.SupportedRelativePatching

/-! Actual subdivision and finite supported-chain patching.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Ambient chains agreeing near every compact patch overlap can be actually subdivided and patched by one ambient chain.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision and finite supported-chain patching.
HC no distance; AV milestone no distance.
-/
theorem subdivision_finite_supported_patching {ι : Type} [Fintype ι]
    (X : TopCat.{0}) (n : ℕ) (W : ι → Opens X) (N : ι → ι → Opens X)
    (hN : ∀ i j, closure (W i : Set X) ∩ closure (W j : Set X) ⊆ N i j)
    (z : ι → (SingularChainComplex ℚ X).X n)
    (heq : ∀ i j,
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (N i j : Set X)ᶜ)).f n (z i) =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (N i j : Set X)ᶜ)).f n (z j)) :
    ∃ (t : ℕ) (w : (SingularChainComplex ℚ X).X n), ∀ i,
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W i : Set X)ᶜ)).f n w =
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W i : Set X)ᶜ)).f n
          ((rationalSubdivisionIterate X t).f n (z i)) := by
  classical
  let C (ij : ι × ι) : Fin 3 → Set X :=
    ![(N ij.1 ij.2 : Set X), (closure (W ij.1 : Set X))ᶜ, (closure (W ij.2 : Set X))ᶜ]
  have hCo (ij : ι × ι) (k : Fin 3) : IsOpen (C ij k) := by
    fin_cases k
    · exact (N ij.1 ij.2).isOpen
    · exact isClosed_closure.isOpen_compl
    · exact isClosed_closure.isOpen_compl
  have hCc (ij : ι × ι) : ⋃ k, C ij k = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hi : x ∈ closure (W ij.1 : Set X)
    · by_cases hj : x ∈ closure (W ij.2 : Set X)
      · exact Set.mem_iUnion.mpr ⟨0, hN ij.1 ij.2 ⟨hi, hj⟩⟩
      · exact Set.mem_iUnion.mpr ⟨2, hj⟩
    · exact Set.mem_iUnion.mpr ⟨1, hi⟩
  obtain ⟨t, ht⟩ := rationalSubdivision_finite_covers_eventually_small X C hCo hCc n z
  choose w hw using ht
  refine ⟨t, ?_⟩
  apply singularChain_finite_supported_patching X n (fun i => (W i : Set X))
    (fun i => (rationalSubdivisionIterate X t).f n (z i))
  intro i j s hsi hsj
  have hEqt := rationalSubdivision_preserves_supported_equality X n t (N i j) (z i) (z j) (heq i j)
  have hsmall (k : ι)
      (hs : (singularChainCoefficient X n s).hom
        ((rationalSubdivisionIterate X t).f n (z k)) ≠ 0) :
      Set.range (X.toSSetObjEquiv _ s) ⊆ N i j := by
    apply coverSmallChain_meeting_both X (closure (W i : Set X)) (closure (W j : Set X))
      (N i j : Set X) n (w (i, j) k) s
    · rw [hw (i, j) k]
      exact hs
    · obtain ⟨x, hx⟩ := hsi
      exact ⟨x, subset_closure hx⟩
    · obtain ⟨x, hx⟩ := hsj
      exact ⟨x, subset_closure hx⟩
  by_cases hsN : Set.range (X.toSSetObjEquiv _ s) ⊆ N i j
  · obtain ⟨x, hx⟩ := hsi
    exact (supportedChainProjection_eq_iff_coefficients X (N i j : Set X) n
      ((rationalSubdivisionIterate X t).f n (z i))
      ((rationalSubdivisionIterate X t).f n (z j))).mp hEqt s ⟨x, hsN ⟨x, rfl⟩⟩
  · have hi0 : (singularChainCoefficient X n s).hom
        ((rationalSubdivisionIterate X t).f n (z i)) = 0 := by
      by_contra hi
      exact hsN (hsmall i hi)
    have hj0 : (singularChainCoefficient X n s).hom
        ((rationalSubdivisionIterate X t).f n (z j)) = 0 := by
      by_contra hj
      exact hsN (hsmall j hj)
    exact hi0.trans hj0.symm

#print axioms subdivision_finite_supported_patching
end HodgeLean.Foundations.RationalHomologyManifold
