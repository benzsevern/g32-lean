import HodgeLean.Foundations.RationalHomologyManifold.KernelCapHomotopy
import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainCokernelUniversal
import HodgeLean.Foundations.RationalHomologyManifold.InjectiveHomotopyDescent

/-! Descent of the actual fixed-cycle cap through local singular cochains.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- After mapping the actual bounded cap target into degreewise injective terms, its literal fixed-cycle cap descends up to homotopy through the actual local cochain restriction.
Source: Bredon, Sheaf Theory, second edition, VI.12; Weibel, An Introduction to Homological Algebra, section 2.3.
HC no distance; AV milestone no distance.
-/
theorem exists_fixedCycleCap_descent (X : TopCat.{0}) [RegularSpace X] (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0)
    (I : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    [∀ p, Injective (I.X p)] (j : capTargetComplex X N ⟶ I) :
    ∃ d : singularCochainSheafComplex ℚ X ⟶ I,
      Nonempty (Homotopy (ambientFixedCycleCapComplexHom X N z hz ≫ j)
        (ambientCochainSheafRestriction X ≫ d)) := by
  letI (p : ℕ) : Mono ((ambientLocalZeroSheafInclusion X).f p) :=
    ambientLocalZeroSheafInclusion_mono X p
  have h : Homotopy (ambientLocalZeroSheafInclusion X ≫
      (ambientFixedCycleCapComplexHom X N z hz ≫ j)) 0 := by
    simpa only [Category.assoc, zero_comp] using
      (kernelFixedCycleCapNullHomotopy X N z hz).compRight j
  exact exists_homotopy_descent_of_cokernel (ambientLocalZeroSheafInclusion X)
    (ambientCochainSheafRestriction X) (ambientLocalZeroSheafInclusion_restriction X)
    (ambientCochainSheafRestrictionIsCokernel X) _ h

#print axioms exists_fixedCycleCap_descent
end HodgeLean.Foundations.RationalHomologyManifold
