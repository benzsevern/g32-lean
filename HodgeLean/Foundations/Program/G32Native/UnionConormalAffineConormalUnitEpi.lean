import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineSchemeUnitEpi
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineConormalPresentation

/-! # Epic affine pullback units on actual conormals -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The unit on the actual conormal of an affine morphism is epic
along any supplied immersion into its source. -/
lemma unionConormal_affineConormalUnit_epi
    {Q W S : Scheme.{0}} [IsAffine Q] [IsAffine W]
    (i : Q ⟶ W) (f : S ⟶ Q) [IsClosedImmersion f] :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (s2c_conormal i)) := by
  haveI : IsAffine S := isAffine_of_isAffineHom f
  exact unionConormal_affineSchemeUnit_epi f (s2c_conormal i)
    ((ModuleCat.extendScalars i.appTop.hom).obj
      (ModuleCat.of Γ(W, ⊤) (RingHom.ker i.appTop.hom)))
    (unionConormalAffineConormalPresentation i)

end HodgeLean.Foundations.Program.G32Native
