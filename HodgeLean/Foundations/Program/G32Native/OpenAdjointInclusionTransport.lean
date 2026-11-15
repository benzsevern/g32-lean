import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitComparisonForms

/-! # Original inclusions through the open pullback adjunction -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Transport through the actual open adjunction retains an original
inclusion whenever its original pushforward square commutes. -/
theorem openAdjointTransport_inclusion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (K : X.Modules)
    (E : (Scheme.Modules.pushforward f).obj K ≅ M)
    (jM : M ⟶ unit Y) (jK : K ⟶ unit X)
    (h : E.inv ≫ (Scheme.Modules.pushforward f).map jK = jM ≫ pushforwardUnit f) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv ≫
      (Scheme.Modules.restrictFunctor f).map E.inv ≫
      (Scheme.Modules.restrictFunctorAdjCounitIso f).hom.app K ≫ jK =
    (Scheme.Modules.pullback f).map jM ≫ (pullbackUnit f).hom := by
  let A := Scheme.Modules.restrictAdjunction f
  have hc : A.homEquiv M K
      ((Scheme.Modules.restrictFunctor f).map E.inv ≫
        (Scheme.Modules.restrictFunctorAdjCounitIso f).hom.app K) = E.inv := by
    change A.homEquiv M K ((Scheme.Modules.restrictFunctor f).map E.inv ≫ A.counit.app K) = E.inv
    rw [← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M (unit X)).injective
  rw [restrictPullback_adjunct]
  rw [← Category.assoc]
  rw [A.homEquiv_naturality_right]
  change A.homEquiv M K
    ((Scheme.Modules.restrictFunctor f).map E.inv ≫
      (Scheme.Modules.restrictFunctorAdjCounitIso f).hom.app K) ≫
        (Scheme.Modules.pushforward f).map jK = _
  rw [hc]
  rw [Adjunction.homEquiv_naturality_left, pullbackUnit_adjunct]
  exact h

#print axioms openAdjointTransport_inclusion
end HodgeLean.Foundations.Program.G32Native
