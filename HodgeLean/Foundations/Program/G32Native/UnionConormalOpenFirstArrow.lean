import HodgeLean.Foundations.Program.G32Native.UnionConormalFirstArrowBaseChange
import HodgeLean.Foundations.AlgebraicGeometry.ConormalOpenComparison

/-! # The actual first arrow on ambient open charts -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- The natural first arrow restricts to its first arrow on any ambient open chart. -/
def unionConormalOpenFirstArrowIso
    {V T T₁ : Scheme.{0}} (t : T ⟶ V) (t₁ : T₁ ⟶ V)
    (a : T₁ ⟶ T) (ha : a ≫ t = t₁) (U : V.Opens)
    (a' : (t₁ ⁻¹ᵁ U).toScheme ⟶ (t ⁻¹ᵁ U).toScheme)
    (ha' : a' ≫ (t ∣_ U) = t₁ ∣_ U)
    (hb : a' ≫ (t ⁻¹ᵁ U).ι = (t₁ ⁻¹ᵁ U).ι ≫ a) :
    Arrow.mk ((Scheme.Modules.restrictFunctor (t₁ ⁻¹ᵁ U).ι).map
      (unionConormalFirst t t₁ a ha)) ≅
      Arrow.mk (unionConormalFirst (t ∣_ U) (t₁ ∣_ U) a' ha') := by
  let h₀ := (morphismRestrict_ι t U).symm
  let h₁ := (morphismRestrict_ι t₁ U).symm
  haveI : IsIso (idealPullbackMap t (t ∣_ U) U.ι (t ⁻¹ᵁ U).ι h₀) :=
    idealPullbackMap_open_isIso t U
  haveI : IsIso (idealPullbackMap t₁ (t₁ ∣_ U) U.ι (t₁ ⁻¹ᵁ U).ι h₁) :=
    idealPullbackMap_open_isIso t₁ U
  exact Arrow.isoOfNatIso (Scheme.Modules.restrictFunctorIsoPullback (t₁ ⁻¹ᵁ U).ι)
      (Arrow.mk (unionConormalFirst t t₁ a ha)) ≪≫
    unionConormalFirstArrowBaseChangeIso t t₁ a ha (t ∣_ U) (t₁ ∣_ U) a' ha'
      U.ι (t ⁻¹ᵁ U).ι (t₁ ⁻¹ᵁ U).ι h₀ h₁ hb

end HodgeLean.Foundations.Program.G32Native
