import HodgeLean.Foundations.Program.SchoenCycleC2AffinePushforwardSectionsHelpers
import Mathlib.CategoryTheory.Adjunction.Unique

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback of an associated module sheaf along an actual affine scheme
map is the associated sheaf of scalar extension. -/
def s2e_affine_pullback_tilde_iso
    (R S : CommRingCat.{0}) (φ : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S := by
  let a := (tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
  let b := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))
  exact Adjunction.leftAdjointUniq
    (a.ofNatIsoRight (s2e_affine_pushforward_sections_iso R S φ)) b

end HodgeLean.Foundations.Program
