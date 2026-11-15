import HodgeLean.Foundations.QuotientDuality.LocalHomeomorphPairIso

/-! Homeomorphism transport on supported classes with target-indexed local pairs. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable {X Y : TopCat.{0}}

def targetPointHomeomorphPairIso (H : X ≃ₜ Y) (y : Y) :
    pointComplementPair (H.symm y) ≅ pointComplementPair y :=
  (localPointHomeomorphPairIso H.symm y).symm

def homeomorphSupportPairMap (H : X ≃ₜ Y) (U : Set X) :
    TopPair.ofSubset (X := X) Uᶜ ⟶ TopPair.ofSubset (X := Y) (H '' U)ᶜ :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨H, H.continuous⟩) fun z hz => by
    rintro ⟨x, hx, he⟩
    exact hz ((H.injective he) ▸ hx)

theorem homeomorph_support_restriction_square (H : X ≃ₜ Y) (U : Set X) (y : Y)
    (hy : y ∈ H '' U) (hx : H.symm y ∈ U) :
    supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx) ≫
        (targetPointHomeomorphPairIso H y).hom =
      homeomorphSupportPairMap H U ≫
        supportInclusionPairMap Y (Set.singleton_subset_iff.mpr hy) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext z <;> rfl

#print axioms targetPointHomeomorphPairIso
#print axioms homeomorphSupportPairMap
#print axioms homeomorph_support_restriction_square
end HodgeLean.Foundations.QuotientDuality
