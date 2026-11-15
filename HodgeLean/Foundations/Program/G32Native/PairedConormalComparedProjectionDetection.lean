import HodgeLean.Foundations.Program.G32Native.PairedConormalPullbackAdditive
import HodgeLean.Foundations.Curves.Picard.LineBundles.Transport

/-! # Actual coordinate detection with the specified structural unit comparisons -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles HodgeLean.Foundations.BundleThom

/-- Successive actual scheme pullbacks retain coordinate zero detection after
the specified unit comparison on every original row. -/
theorem conormal_compared_unit_free_projections_detect_zero
    {X Y Z : Scheme.{0}} (f : X ⟶ Y) (x : Z ⟶ X) (k : ℕ) {B : Z.Modules}
    (u : B ⟶ (Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback f).obj
      (SheafOfModules.unit Y.ringCatSheaf ⊞ SheafOfModules.free (R := Y.ringCatSheaf) (Fin k))))
    (h0 : u ≫ (Scheme.Modules.pullback x).map
      ((Scheme.Modules.pullback f).map (biprod.fst :
        SheafOfModules.unit Y.ringCatSheaf ⊞ SheafOfModules.free (R := Y.ringCatSheaf) (Fin k) ⟶ _) ≫
          (pullbackUnit f).hom) = 0)
    (hi : ∀ i : Fin k, u ≫ (Scheme.Modules.pullback x).map
      ((Scheme.Modules.pullback f).map ((biprod.snd :
        SheafOfModules.unit Y.ringCatSheaf ⊞ SheafOfModules.free (R := Y.ringCatSheaf) (Fin k) ⟶ _) ≫
          i1_freeSheafProjection Y k i) ≫ (pullbackUnit f).hom) = 0) : u = 0 := by
  let F := Scheme.Modules.pullback f
  let G := Scheme.Modules.pullback x
  letI : F.Additive := conormal_scheme_pullback_additive f
  letI : G.Additive := conormal_scheme_pullback_additive x
  apply conormal_map_unit_free_projections_detect_zero Y k (F ⋙ G) u
  · apply (cancel_mono (G.map (pullbackUnit f).hom)).mp
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_map, F, G, Category.assoc, zero_comp] using h0
  · intro i
    apply (cancel_mono (G.map (pullbackUnit f).hom)).mp
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_map, F, G, Category.assoc, zero_comp] using hi i

end HodgeLean.Foundations.Program.G32Native
