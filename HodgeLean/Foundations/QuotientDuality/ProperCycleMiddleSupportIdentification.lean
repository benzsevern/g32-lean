import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeSingularComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleDerivedSplitChecks
import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedSheaf
import HodgeLean.Foundations.QuotientDuality.ProperCycleShiftedDerivedSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleDerivedSupportChainClass
import HodgeLean.Foundations.QuotientDuality.ProperCyclePositiveSupportChecks
import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalSupportCap

/-! # Derived supported degree identification for original middle cycles
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

local instance middleSupportSheafDerived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _
local instance middleSupportGroupDerived :
    HasDerivedCategory AddCommGrpCat.{0} := HasDerivedCategory.standard _

/-- Identification of degree minus twice k derived sections of the original rational object in degree minus four times k with original relative supported cohomology in degree twice k. The support and coefficient object are literal, including components in the ambient singular locus.
Source: Bredon, Sheaf Theory, second edition, V.9; Iversen, Cohomology of Sheaves, III and IX; properCycle_shifted_derived_support_sheaf_iso.
HC no distance; AV milestone no distance. -/
def properCycle_middle_support_identification_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} (-((2*k : ℕ) : ℤ))).obj
        ((TopCat.Sheaf.derivedClosedSupportSections (a3b4_an X.hom)
          (⟨a3b4_cycleSupport X.hom γ, a3b4a_classSupport_isClosed X.hom γ⟩)).obj
          ((DerivedCategory.Plus.singleFunctor
            (TopCat.Sheaf AddCommGrpCat.{0} (a3b4_an X.hom)) (-((2*k+2*k : ℕ) : ℤ))).obj
            (TopCat.Sheaf.const (a3b4_an X.hom) (AddCommGrpCat.of ℚ)))) ≅
      AddCommGrpCat.of (s2e_supportedClass X γ k) :=
  properCycle_shifted_derived_support_sheaf_iso (a3b4_an X.hom)
    ⟨a3b4_cycleSupport X.hom γ, a3b4a_classSupport_isClosed X.hom γ⟩
    (2*k+2*k) (2*k) (2*k) rfl ≪≫
  properCycle_relative_singular_comparison X
    ⟨a3b4_cycleSupport X.hom γ, a3b4a_classSupport_isClosed X.hom γ⟩ (2*k)

/-- The middle comparison is the specified shifted comparison followed by the fixed relative singular comparison, retaining its augmentation normalization.
Source: properCycle_shifted_derived_support_sheaf_iso; properCycle_relative_singular_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_middle_support_identification_eq
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k) :
    properCycle_middle_support_identification_aux X k hk hdim γ hc =
      properCycle_shifted_derived_support_sheaf_iso (a3b4_an X.hom)
        ⟨a3b4_cycleSupport X.hom γ, a3b4a_classSupport_isClosed X.hom γ⟩
        (2*k+2*k) (2*k) (2*k) rfl ≪≫
      properCycle_relative_singular_comparison X
        ⟨a3b4_cycleSupport X.hom γ, a3b4a_classSupport_isClosed X.hom γ⟩ (2*k) := rfl

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k) :
    (properCycle_middle_support_identification_aux X k hk hdim γ hc).inv ≫
      (properCycle_middle_support_identification_aux X k hk hdim γ hc).hom = 𝟙 _ :=
  (properCycle_middle_support_identification_aux X k hk hdim γ hc).inv_hom_id

example := ProperCycleDerivedSplitChecks.middle_support_identification_shifted_example

end HodgeLean.Foundations.QuotientDuality
