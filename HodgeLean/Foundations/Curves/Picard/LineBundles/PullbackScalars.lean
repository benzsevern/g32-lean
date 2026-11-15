import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitPullback

/-! # Actual scalar endomorphisms under module pullback

Adjunction identifies the coefficient of the transported structure-module map.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The transported unit endomorphism has the actual coefficient-map adjoint. -/
theorem pullbackUnitEnd_adjunct {X Y : Scheme} (f : X ⟶ Y) (a : unit Y ⟶ unit Y) :
    pushforwardUnit f ≫ (Scheme.Modules.pushforward f).map
      ((pullbackUnit f).inv ≫ (Scheme.Modules.pullback f).map a ≫ (pullbackUnit f).hom) =
      a ≫ pushforwardUnit f := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  calc
    _ = A.homEquiv _ _ ((pullbackUnit f).hom ≫
        ((pullbackUnit f).inv ≫ (Scheme.Modules.pullback f).map a ≫ (pullbackUnit f).hom)) := by
      rw [Adjunction.homEquiv_naturality_right, pullbackUnit_adjunct]
    _ = A.homEquiv _ _ ((Scheme.Modules.pullback f).map a ≫ (pullbackUnit f).hom) := by
      simp only [Iso.hom_inv_id_assoc]
    _ = _ := by rw [Adjunction.homEquiv_naturality_left, pullbackUnit_adjunct]

/-- Pullback of a scalar endomorphism reads the actual structure-ring coefficient. -/
theorem pullbackUnitEnd_coefficient {X Y : Scheme} (f : X ⟶ Y)
    (a : unit Y ⟶ unit Y) (U : Y.Opens) :
    ((pullbackUnit f).inv ≫ (Scheme.Modules.pullback f).map a ≫ (pullbackUnit f).hom).app
        (f ⁻¹ᵁ U) (1 : Γ(X, f ⁻¹ᵁ U)) =
      f.app U (a.app U (1 : Γ(Y, U))) := by
  have he := congrArg (fun k => k.app U (1 : Γ(Y, U))) (pullbackUnitEnd_adjunct f a)
  change ((pullbackUnit f).inv ≫ (Scheme.Modules.pullback f).map a ≫ (pullbackUnit f).hom).app
      (f ⁻¹ᵁ U) (f.app U (1 : Γ(Y, U))) = f.app U (a.app U (1 : Γ(Y, U))) at he
  simpa only [map_one] using he

end HodgeLean.Foundations.Curves.Picard.LineBundles
