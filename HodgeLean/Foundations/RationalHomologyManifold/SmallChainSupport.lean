import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionSmallChains
import HodgeLean.Foundations.RationalHomologyManifold.ChainSupport

/-! Geometric support of nonzero coefficients in actual cover-small chains.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Every simplex with a nonzero coefficient in a cover-small chain lies in one member of the cover.
Source: Hatcher, Algebraic Topology, section 2.1, chains subordinate to an open cover.
HC no distance; AV milestone no distance.
-/
theorem coverSmallChain_nonzero_coefficient {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (n : ℕ) (w : (CoverSmallCoefficientSingularChainComplex ℚ X U).X n)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (hs : (singularChainCoefficient X n s).hom
      ((coverSmallCoefficientSingularChainInclusion ℚ X U).f n w) ≠ 0) :
    ∃ i, Set.range (X.toSSetObjEquiv _ s) ⊆ U i := by
  classical
  let S := (coverSmallSingularSubcomplex X U : SSet)
  have hpre : ∃ t : S.obj (Opposite.op (SimplexCategory.mk n)),
      (coverSmallSingularSubcomplex X U).ι.app _ t = s := by
    by_contra hn
    have hzero := singularChainCoefficient_simplicialMap_zero S X
      (coverSmallSingularSubcomplex X U).ι n s (fun t heq => hn ⟨t, heq.symm⟩)
    have hz := ConcreteCategory.congr_hom hzero w
    change (singularChainCoefficient X n s).hom
      ((coverSmallCoefficientSingularChainInclusion ℚ X U).f n w) = 0 at hz
    exact hs hz
  obtain ⟨t, ht⟩ := hpre
  have hmem : s ∈ (coverSmallSingularSubcomplex X U).obj (Opposite.op (SimplexCategory.mk n)) := by
    rw [← ht]
    exact t.property
  obtain ⟨i, v, hv⟩ := (mem_coverSmallSingularSubcomplex_iff_exists_preimage X U s).mp hmem
  refine ⟨i, (singularSimplex_subspace_image_iff X (U i) n s).mp ⟨v, ?_⟩⟩
  exact hv

#print axioms coverSmallChain_nonzero_coefficient
/-- In the three-set overlap cover, a nonzero simplex meeting both designated sets lies in their chosen overlap neighborhood.
Source: Bredon, Sheaf Theory, second edition, VI.12; the supported-chain patching argument.
HC no distance; AV milestone no distance.
-/
theorem coverSmallChain_meeting_both (X : TopCat.{0}) (A B N : Set X) (n : ℕ)
    (w : (CoverSmallCoefficientSingularChainComplex ℚ X ![N, Aᶜ, Bᶜ]).X n)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (hs : (singularChainCoefficient X n s).hom
      ((coverSmallCoefficientSingularChainInclusion ℚ X ![N, Aᶜ, Bᶜ]).f n w) ≠ 0)
    (ha : ∃ x, (X.toSSetObjEquiv _ s) x ∈ A)
    (hb : ∃ x, (X.toSSetObjEquiv _ s) x ∈ B) :
    Set.range (X.toSSetObjEquiv _ s) ⊆ N := by
  obtain ⟨i, hi⟩ := coverSmallChain_nonzero_coefficient X ![N, Aᶜ, Bᶜ] n w s hs
  fin_cases i
  · exact hi
  · obtain ⟨x, hx⟩ := ha
    exact False.elim ((hi ⟨x, rfl⟩) hx)
  · obtain ⟨x, hx⟩ := hb
    exact False.elim ((hi ⟨x, rfl⟩) hx)

#print axioms coverSmallChain_meeting_both
end HodgeLean.Foundations.RationalHomologyManifold
