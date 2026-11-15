import HodgeLean.Foundations.BundleResolution.ChernRelativeClassNaturalityHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeCupCocycleHelpers

/-! # Relative cup multiplication under pair pullback

The standard relative cohomology pullback respects the actual relative
cup action and the absolute pullback of its second factor.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

set_option backward.isDefEq.respectTransparency false in
theorem i1_relativeCup_naturality {P Q : TopPair} (f : P ⟶ Q) (p q : ℕ)
    (α : RelativeCohomology ℚ Q p) (β : Cohomology ℚ Q.fst q) :
    relativeCohomologyMap ℚ (p + q) f (i1_relativeCup Q p q α β) =
      i1_relativeCup P p q (relativeCohomologyMap ℚ p f α)
        (cohomologyMap ℚ q (TopPair.Hom.fst f) β) := by
  obtain ⟨φ, rfl⟩ := i1_relativeCocycleClass_surjective Q p α
  obtain ⟨ψ, rfl⟩ := cohomologyClass_surjective Q.fst q β
  let ψ' : Cocycle ℚ (TopCat.toSSet.obj P.fst) q :=
    ⟨cochainMap ℚ (TopCat.toSSet.map (TopPair.Hom.fst f)) q ψ.val, by
      change coboundary ℚ q _ = 0
      have h := ConcreteCategory.congr_hom
        ((singularCochainComplexMap ℚ (TopPair.Hom.fst f)).comm q (q + 1)) ψ.val
      change coboundary ℚ q (cochainMap ℚ (TopCat.toSSet.map (TopPair.Hom.fst f)) q ψ.val) =
        cochainMap ℚ (TopCat.toSSet.map (TopPair.Hom.fst f)) (q + 1)
          (coboundary ℚ q ψ.val) at h
      rw [ψ.property, map_zero] at h
      exact h⟩
  rw [i1_relativeCup_on_class, i1_relativeCohomologyMap_class,
    i1_relativeCohomologyMap_class,
    cohomologyMap_class Q.fst (TopPair.Hom.fst f) q ψ ψ' rfl,
    i1_relativeCup_on_class]
  apply congrArg (i1_relativeCocycleClass P (p + q))
  apply Subtype.ext
  exact i1_relativeCupCochain_naturality f p q φ.val ψ.val

end HodgeLean.Foundations.BundleResolution
