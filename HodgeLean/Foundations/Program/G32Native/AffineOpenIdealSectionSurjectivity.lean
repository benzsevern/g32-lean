import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealSection
import HodgeLean.Foundations.Program.G32Native.ModulePullbackEquivalence

/-! # Original local ideal sections fill their actual canonical affine module -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Every actual canonical affine ideal section is the transport of an
original local ideal section on the same ambient open. -/
theorem affineOpenIdealSection_surjective {Q W : Scheme.{0}} (i : Q ⟶ W)
    (U : W.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (affineOpenIdealSection i U hU) := by
  let f := hU.isoSpec.inv
  let F := Scheme.Modules.pullback f
  let M := (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i)
  let L : F.obj M ≅ Conormal.idealModule ((i ∣_ U) ≫ hU.isoSpec.hom) :=
    (Scheme.Modules.pullbackComp f U.ι).app _ ≪≫ affineOpenIdealPullbackIso i U hU
  letI : F.IsEquivalence := by
    change (modulePullbackEquivalence hU.isoSpec.symm).functor.IsEquivalence
    infer_instance
  intro t
  let a : F.obj (unit U.toScheme) ⟶ F.obj M := (pullbackUnit f).hom ≫ t ≫ L.inv
  let s := F.preimage a
  refine ⟨s, ?_⟩
  change (pullbackUnit f).inv ≫ F.map s ≫ L.hom = t
  rw [F.map_preimage]
  simp only [a, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

#print axioms affineOpenIdealSection_surjective
end HodgeLean.Foundations.Program.G32Native
