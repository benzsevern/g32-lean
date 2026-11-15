import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexOriginalCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenCoverCapExcision

/-! # Bijectivity of the original relative caps through actual quotient comparisons -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original triad cap bijectivity is equivalent to bijectivity of its actual subcomplex quotient cap.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap products and chain comparisons.
HC no distance; AV milestone no distance. -/
lemma properCycle_original_triad_cap_bijective_iff
    (X : TopCat.{0}) (A T : Set X) (p q : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0) :
    let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
      ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ, by
        change AlgebraicTopology.Simplicial.coboundary ℚ p _ = 0
        exact (relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p φ).symm.trans
          ((congrArg (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) (p + 1)) hφ).trans
            (map_zero _))⟩
    Function.Bijective (properCycle_subcomplex_cap_homology_map
      (subsetSingularSubcomplex X A) (subsetSingularSubcomplex X T)
      p q hp ψ.1 (properCycle_relative_cochain_subcomplex_zero X A p φ) ψ.2).hom ↔
    Function.Bijective (triadCapHomologyMap ℚ X A T p q φ hφ) := by
  let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
    ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ, by
      change AlgebraicTopology.Simplicial.coboundary ℚ p _ = 0
      exact (relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p φ).symm.trans
        ((congrArg (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) (p + 1)) hφ).trans
          (map_zero _))⟩
  let C := properCycle_subcomplex_cap_homology_map
    (subsetSingularSubcomplex X A) (subsetSingularSubcomplex X T)
    p q hp ψ.1 (properCycle_relative_cochain_subcomplex_zero X A p φ) ψ.2
  change Function.Bijective C.hom ↔ _
  have he := properCycle_subcomplex_original_triad_cap_homology X A T p q hp φ hφ
  let F := HomologicalComplex.homologyMap (properCycle_subset_union_subcomplex_triad_iso X A T).inv (p + q)
  let G := HomologicalComplex.homologyMap (properCycle_subset_subcomplex_relative_iso X T).hom q
  have hF := ConcreteCategory.bijective_of_isIso F
  have hG := ConcreteCategory.bijective_of_isIso G
  constructor
  · intro hc
    have h := hG.comp (hc.comp hF)
    change Function.Bijective ((F ≫ C ≫ G).hom) at h
    dsimp only [F, C, G] at h
    rw [he] at h
    exact h
  · intro hc
    have h : Function.Bijective ((F ≫ C ≫ G).hom) := by
      dsimp only [F, C, G]
      rw [he]
      exact hc
    exact (Function.Bijective.of_comp_iff _ hF).mp
      ((Function.Bijective.of_comp_iff' hG _).mp h)

end HodgeLean.Foundations.QuotientDuality
