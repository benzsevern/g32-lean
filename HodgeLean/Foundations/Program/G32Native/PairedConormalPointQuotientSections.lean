import Mathlib.LinearAlgebra.Dual.Defs
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Sections.AffineEpi
import HodgeLean.Foundations.Program.G32Native.PairedConormalPullbackAdditive
import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFrameIso

/-! # Actual global sections of quotient maps at complex points -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A supplied quotient arrow remains surjective on actual complex-point sections
when its two specialized modules are quasicoherent. -/
theorem conormal_point_quotient_sections_surjective {X : Scheme}
    {M N : X.Modules} (φ : M ⟶ N) [Epi φ]
    (x : Spec (CommRingCat.of ℂ) ⟶ X)
    [((Scheme.Modules.pullback x).obj M).IsQuasicoherent]
    [((Scheme.Modules.pullback x).obj N).IsQuasicoherent] :
    Function.Surjective ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullback x).map φ)) := by
  exact Scheme.Modules.surjective_moduleSpecΓ_of_epi
    ((Scheme.Modules.pullback x).map φ)

/-- Local frames supply the quasicoherence needed for actual point-section
surjectivity of the supplied quotient, without a global-section exactness premise. -/
theorem conormal_locallyFree_point_quotient_sections_surjective {X : Scheme}
    {M N : X.Modules} [M.IsLocallyFree] [N.IsLocallyFree]
    (φ : M ⟶ N) [Epi φ] (x : Spec (CommRingCat.of ℂ) ⟶ X) :
    Function.Surjective ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullback x).map φ)) := by
  letI : ((Scheme.Modules.pullback x).obj M).IsLocallyFree :=
    paired_module_pullback_locallyFree x M
  letI : ((Scheme.Modules.pullback x).obj N).IsLocallyFree :=
    paired_module_pullback_locallyFree x N
  exact conormal_point_quotient_sections_surjective φ x

/-- Evaluation on the actual quotient generators separates dual fibre vectors. -/
theorem conormal_locallyFree_point_quotient_dual_injective {X : Scheme}
    {M N : X.Modules} [M.IsLocallyFree] [N.IsLocallyFree]
    (φ : M ⟶ N) [Epi φ] (x : Spec (CommRingCat.of ℂ) ⟶ X) :
    Function.Injective (((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullback x).map φ)).hom.dualMap) := by
  exact LinearMap.dualMap_injective_of_surjective
    (conormal_locallyFree_point_quotient_sections_surjective φ x)

end HodgeLean.Foundations.Program.G32Native
