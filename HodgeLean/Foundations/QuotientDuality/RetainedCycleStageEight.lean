import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportSum
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicClassProperties
import HodgeLean.Foundations.QuotientDuality.ProperCycleMiddleSupportIdentification
import HodgeLean.Foundations.QuotientDuality.RetainedCycleDefs

/-! # Stage nine representatives from the specified stage eight comparison

The actual shifted comparison fixes both the coefficient object and its normalization.
The original collar cap recovery remains a separate input.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

local instance stageNineSheafDerived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _
local instance stageNineGroupDerived : HasDerivedCategory AddCommGrpCat.{0} :=
  HasDerivedCategory.standard _
local instance stageNineT2 (X : Over (Spec ↧ℂ)) [IsProjective X.hom] :
    T2Space (a3b4_an X.hom) := HodgeLean.Foundations.Analytic.f4_t2Space X

/-- The supported representative of the intrinsic component coefficients through the specified derived comparison and its original complex cap scalar.
Source: Bredon, Sheaf Theory, second edition, V.9; Iversen, Cohomology of Sheaves, III and IX; properCycle_middle_support_identification_aux; properCycle_standard_complex_cap_scalar.
HC no distance; AV milestone no distance. -/
def retainedDerivedSupportedClass
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (hlocal : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hvan : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (v : γ.support → ℚ) : s2e_supportedClass X γ k :=
  properCycle_standard_complex_cap_scalar k k •
    (properCycle_middle_support_identification_aux X k hk hdim γ hc).hom
    (properCycle_derived_support_chain_class_map (a3b4_an X.hom)
      ⟨a3b4_cycleSupport X.hom γ, a3b4a_classSupport_isClosed X.hom γ⟩
      (2*k+2*k) c hlocal hvan (2*k)
      (properCycle_intrinsic_support_sum X k hdim γ hc v))

example := ProperCycleDerivedSplitChecks.middle_support_identification_shifted_example

/-- The intrinsic component orientation supplied by stage eight, with its actual component dimension.
Source: Bredon, Sheaf Theory, second edition, V.9; properCycle_intrinsic_class; properCycle_middle_component_dimension.
HC no distance; AV milestone no distance. -/
def retainedIntrinsicFundamentalClass
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (ξ : X.left) (hc : Order.coheight ξ = k) :
    Homology ℚ (a3b4_an (intrinsicComponent X ξ).hom) (2*k) :=
  properCycle_intrinsic_class (intrinsicComponent X ξ) k
    (properCycle_middle_component_dimension X k hdim ξ hc)

example := ProperCyclePositiveSupportChecks.global_support_factorization_intrinsic_factor_example

end HodgeLean.Foundations.QuotientDuality
