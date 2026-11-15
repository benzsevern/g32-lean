import HodgeLean.Foundations.Program.G32Native.PullbackAssociativity
import HodgeLean.Foundations.Program.G32Native.PullbackSectionValueComposition

/-! # Original local section values through three specified pullbacks -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Pulling an original local section through three actual morphisms
retains its original value and the original structure-module unit. -/
theorem pullbackSectionValue_triple {X Y Z T : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (M : T.Modules)
    (s : unit Z ⟶ (Scheme.Modules.pullback h).obj M) :
    (pullbackUnit f).inv ≫ (Scheme.Modules.pullback f).map
      ((pullbackUnit g).inv ≫ (Scheme.Modules.pullback g).map s ≫
        (Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M =
    (pullbackUnit (f ≫ g)).inv ≫ (Scheme.Modules.pullback (f ≫ g)).map s ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M := by
  have hs := pullbackSectionValue_composition f g (f ≫ g) rfl
    ((Scheme.Modules.pullback h).obj M) s
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id] at hs
  have hv := congrArg (fun t => t ≫ (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M) hs
  simp only [Functor.map_comp, Category.assoc] at hv
  simp only [Functor.map_comp, Category.assoc]
  rw [pullbackComp_associativity_hom]
  exact hv

#print axioms pullbackSectionValue_triple
end HodgeLean.Foundations.Program.G32Native
