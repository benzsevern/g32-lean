import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealInclusion
import HodgeLean.Foundations.Program.G32Native.CanonicalConormalEvaluation

/-! # Original local ideal sections in canonical affine coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Transport an original local ideal section to the actual ideal module
in its canonical ambient affine coordinates, retaining the original unit map. -/
def affineOpenIdealSection {Q W : Scheme.{0}} (i : Q ⟶ W)
    (U : W.Opens) (hU : IsAffineOpen U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i)) :
    unit (Spec Γ(W, U)) ⟶ Conormal.idealModule ((i ∣_ U) ≫ hU.isoSpec.hom) :=
  (pullbackUnit hU.isoSpec.inv).inv ≫
    (Scheme.Modules.pullback hU.isoSpec.inv).map s ≫
    (Scheme.Modules.pullbackComp hU.isoSpec.inv U.ι).hom.app (Conormal.idealModule i) ≫
    (affineOpenIdealPullbackIso i U hU).hom

/-- The transported original equation has exactly the pullback of its
original structure-module value, with the original unit comparisons. -/
theorem affineOpenIdealSection_inclusion {Q W : Scheme.{0}} (i : Q ⟶ W)
    (U : W.Opens) (hU : IsAffineOpen U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i)) :
    affineOpenIdealSection i U hU s ≫
      conormalIdealInclusion ((i ∣_ U) ≫ hU.isoSpec.hom) =
    (pullbackUnit hU.isoSpec.inv).inv ≫
      (Scheme.Modules.pullback hU.isoSpec.inv).map
        (s ≫ (Scheme.Modules.pullback U.ι).map (conormalIdealInclusion i) ≫
          (pullbackUnit U.ι).hom) ≫ (pullbackUnit hU.isoSpec.inv).hom := by
  let C := Scheme.Modules.pullbackComp hU.isoSpec.inv U.ι
  have hn := C.hom.naturality (conormalIdealInclusion i)
  change (Scheme.Modules.pullback hU.isoSpec.inv).map
      ((Scheme.Modules.pullback U.ι).map (conormalIdealInclusion i)) ≫ (C.app (unit W)).hom =
    (C.app (Conormal.idealModule i)).hom ≫
      (Scheme.Modules.pullback hU.fromSpec).map (conormalIdealInclusion i) at hn
  have he : (affineOpenIdealPullbackIso i U hU).hom ≫
      conormalIdealInclusion ((i ∣_ U) ≫ hU.isoSpec.hom) =
    (Scheme.Modules.pullback hU.fromSpec).map (conormalIdealInclusion i) ≫
      (pullbackUnit hU.fromSpec).hom := affineOpenIdealPullback_inclusion i U hU
  have hu := pullbackUnit_composition_hom hU.isoSpec.inv U.ι
  change (Scheme.Modules.pullback hU.isoSpec.inv).map (pullbackUnit U.ι).hom ≫
    (pullbackUnit hU.isoSpec.inv).hom = (C.app (unit W)).hom ≫
      (pullbackUnit hU.fromSpec).hom at hu
  unfold affineOpenIdealSection
  simp only [Category.assoc]
  rw [he]
  change (pullbackUnit hU.isoSpec.inv).inv ≫
    (Scheme.Modules.pullback hU.isoSpec.inv).map s ≫
    (C.app (Conormal.idealModule i)).hom ≫
    (Scheme.Modules.pullback hU.fromSpec).map (conormalIdealInclusion i) ≫
    (pullbackUnit hU.fromSpec).hom = _
  rw [← reassoc_of% hn, ← hu]
  simp only [Functor.map_comp, Category.assoc]

#print axioms affineOpenIdealSection_inclusion
#print axioms affineOpenIdealSection
end HodgeLean.Foundations.Program.G32Native
