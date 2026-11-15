import HodgeLean.Foundations.RationalHomologyManifold.CapSmallChains

/-! Subordinate subdivision prisms for the actual local cap construction.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual cover-small integral subdivision prism extended to rational coefficients.
Source: Hatcher, Algebraic Topology, section 2.1; the subordinate subdivision prism.
HC no distance; AV milestone no distance.
-/
def coverSmallRationalPrism {ι : Type} (X : TopCat.{0}) (U : ι → Set X) (i j : ℕ) :
    (CoverSmallCoefficientSingularChainComplex ℚ X U).X i ⟶
      (CoverSmallCoefficientSingularChainComplex ℚ X U).X j :=
  coefficientizeSimplicialChainComponent ℚ (coverSmallSingularSubcomplex X U : SSet)
    (coverSmallSingularSubcomplex X U : SSet) i j
      ((coverSmallAffineSubdivisionHomotopy X U).hom i j)

#print axioms coverSmallRationalPrism
/-- Inclusion intertwines the actual subordinate rational prism with the ambient rational prism.
Source: Hatcher, Algebraic Topology, section 2.1; naturality and support of the subdivision prism.
HC no distance; AV milestone no distance.
-/
theorem coverSmallRationalPrism_comp_inclusion {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (i j : ℕ) :
    coverSmallRationalPrism X U i j ≫ (coverSmallCoefficientSingularChainInclusion ℚ X U).f j =
      (coverSmallCoefficientSingularChainInclusion ℚ X U).f i ≫
        (rationalSubdivisionHomotopy X).hom i j := by
  let S := (coverSmallSingularSubcomplex X U : SSet)
  have hI :
      (coverSmallAffineSubdivisionHomotopy X U).hom i j ≫
          (coverSmallIntegralSingularChainInclusion X U).f j =
        (coverSmallIntegralSingularChainInclusion X U).f i ≫
          (affineSingularSubdivisionHomotopy X).hom i j := by
    by_cases hij : i + 1 = j
    · subst j
      simpa only [coverSmallAffineSubdivisionHomotopy, coverSmallAffinePrismHom_succ,
        affineSingularSubdivisionHomotopy, affineSingularSubdivisionPrismHom_succ] using
          coverSmallAffinePrismComponent_comp_inclusion X U i
    · rw [(coverSmallAffineSubdivisionHomotopy X U).zero i j
          (by simpa only [ComplexShape.down_Rel] using hij),
        (affineSingularSubdivisionHomotopy X).zero i j
          (by simpa only [ComplexShape.down_Rel] using hij), zero_comp, comp_zero]
  have h := congrArg
    (coefficientizeSimplicialChainComponent ℚ S (TopCat.toSSet.obj X) i j) hI
  simpa only [coefficientizeSimplicialChainComponent_comp,
    coefficientizeSimplicialChainComponent_chainComplexMap,
    coverSmallIntegralSingularChainInclusion, coverSmallCoefficientSingularChainInclusion,
    coverSmallRationalPrism, rationalSubdivisionHomotopy, Homotopy.trans, Homotopy.ofEq,
    coefficientizeSimplicialChainHomotopy, Pi.add_apply, add_zero] using h

#print axioms coverSmallRationalPrism_comp_inclusion

/-- Cap of every sufficiently late actual subdivision-prism term vanishes in the prescribed relative support.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; small prisms preserve the two support regions.
HC no distance; AV milestone no distance.
-/
theorem relative_cap_subdivision_prism_eventually_zero (X : TopCat.{0}) (U A : Set X)
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) (n p q : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) U).map) p φ = 0)
    (z : (SingularChainComplex ℚ X).X n) :
    ∃ m : ℕ, ∀ r : ℕ,
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f q
        (cap ℚ p q φ ((rationalSubdivisionHomotopy X).hom n (p + q)
          ((rationalSubdivisionIterate X (m + r)).f n z))) = 0 := by
  obtain ⟨m, w, hw⟩ := rationalSubdivision_eventually_small X ![U, A]
    (by intro i; fin_cases i <;> assumption)
    (by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      have hx : x ∈ U ∪ A := by rw [hcover]; trivial
      rcases hx with hx | hx
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩) n z
  refine ⟨m, fun r => ?_⟩
  obtain ⟨v, hv⟩ := rationalSubdivision_small_add X ![U, A] n m r z w hw
  have hp := ConcreteCategory.congr_hom
    (coverSmallRationalPrism_comp_inclusion X ![U, A] n (p + q)) v
  change (coverSmallCoefficientSingularChainInclusion ℚ X ![U, A]).f (p + q)
      (coverSmallRationalPrism X ![U, A] n (p + q) v) =
    (rationalSubdivisionHomotopy X).hom n (p + q)
      ((coverSmallCoefficientSingularChainInclusion ℚ X ![U, A]).f n v) at hp
  rw [← hv, ← hp]
  exact relative_cap_coverSmall_zero X U A p q φ hφ _

#print axioms relative_cap_subdivision_prism_eventually_zero
end HodgeLean.Foundations.RationalHomologyManifold
