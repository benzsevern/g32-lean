import HodgeLean.Foundations.Program.G32Native.PullbackUnitInverseComposition

/-! # Original global section values under point pullback composition -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Pulling an original global section through a composition and its specified
point equality preserves the original section and its structure-module unit. -/
theorem pullbackSectionValue_composition
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (h : f ≫ g = p)
    (M : Z.Modules) (s : unit Z ⟶ M) :
    (pullbackUnit f).inv ≫
      (Scheme.Modules.pullback f).map ((pullbackUnit g).inv ≫ (Scheme.Modules.pullback g).map s) ≫
      ((Scheme.Modules.pullbackComp f g).app M).hom ≫
      ((Scheme.Modules.pullbackCongr h).app M).hom =
      (pullbackUnit p).inv ≫ (Scheme.Modules.pullback p).map s := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (Scheme.Modules.pullbackComp f g).hom.naturality s
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s) ≫
      ((Scheme.Modules.pullbackComp f g).app M).hom =
      ((Scheme.Modules.pullbackComp f g).app (unit Z)).hom ≫
        (Scheme.Modules.pullback (f ≫ g)).map s at hn
  have hg := (Scheme.Modules.pullbackCongr h).hom.naturality s
  change (Scheme.Modules.pullback (f ≫ g)).map s ≫
      ((Scheme.Modules.pullbackCongr h).app M).hom =
      ((Scheme.Modules.pullbackCongr h).app (unit Z)).hom ≫
        (Scheme.Modules.pullback p).map s at hg
  rw [reassoc_of% hn, hg]
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ (Scheme.Modules.pullback p).map s)
    (pullbackUnit_inverse_composition_congr f g p h)

#print axioms pullbackSectionValue_composition
end HodgeLean.Foundations.Program.G32Native
