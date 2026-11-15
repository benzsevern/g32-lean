import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealSection
import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealPoint
import HodgeLean.Foundations.Program.G32Native.ModuleSectionValueFactorization
import HodgeLean.Foundations.Program.G32Native.PullbackSectionValueTriple

/-! # Original local ideal section values in the actual affine point fibre -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual affine fibre transport retains the value of each original
local ideal section at its original ambient point. -/
theorem affineOpenIdealPointEquiv_section {Q : Scheme.{0}} {W : Over (Spec ↧ℂ)}
    (i : Q ⟶ W.left) (U : W.left.Opens) (hU : IsAffineOpen U)
    (p : ComplexPoint W) (hp : p ∈ Point.overOpen U)
    (ε : Γ(W.left, U) ⟶ CommRingCat.of ℂ)
    (hε : Spec.map ε ≫ hU.fromSpec = p.left)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i)) :
    (affineOpenIdealPointEquiv i U hU p.left ε hε).symm
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback (Spec.map ε)).map (affineOpenIdealSection i U hU s))
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).inv
          (1 : Γ(Spec ↧ℂ, ⊤)))) =
      moduleSectionValue (Conormal.idealModule i) U s p hp := by
  let I := Conormal.idealModule i
  let f := hU.isoSpec.inv
  let q := Spec.map ε ≫ f
  have hq : q ≫ U.ι = p.left := by
    change (Spec.map ε ≫ f) ≫ U.ι = p.left
    rw [Category.assoc]
    exact hε
  let E := affineOpenIdealPullbackIso i U hU
  let t := affineOpenIdealSection i U hU s
  have ht : t ≫ E.inv = (pullbackUnit f).inv ≫ (Scheme.Modules.pullback f).map s ≫
      (Scheme.Modules.pullbackComp f U.ι).hom.app I := by
    unfold t affineOpenIdealSection
    change (pullbackUnit f).inv ≫ (Scheme.Modules.pullback f).map s ≫
      (Scheme.Modules.pullbackComp f U.ι).hom.app I ≫ E.hom ≫ E.inv = _
    simp only [Iso.hom_inv_id, Category.comp_id]
  have hm : (pullbackUnit (Spec.map ε)).inv ≫
      (Scheme.Modules.pullback (Spec.map ε)).map t ≫
      (Scheme.Modules.pullback (Spec.map ε)).map E.inv ≫
      (Scheme.Modules.pullbackComp (Spec.map ε) hU.fromSpec).hom.app I ≫
      (Scheme.Modules.pullbackCongr hε).hom.app I =
    (pullbackUnit q).inv ≫ (Scheme.Modules.pullback q).map s ≫
      (Scheme.Modules.pullbackComp q U.ι).hom.app I ≫
      (Scheme.Modules.pullbackCongr hq).hom.app I := by
    rw [← Functor.map_comp_assoc, ht]
    exact congrArg (fun a => a ≫ (Scheme.Modules.pullbackCongr hε).hom.app I)
      (pullbackSectionValue_triple (Spec.map ε) f U.ι I s)
  have hv := congrArg (fun a : unit (Spec ↧ℂ) ⟶ (Scheme.Modules.pullback p.left).obj I =>
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map a
    (1 : Γ(Spec ↧ℂ, ⊤))) hm
  change (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
    ((pullbackUnit (Spec.map ε)).inv ≫ (Scheme.Modules.pullback (Spec.map ε)).map t ≫
      (Scheme.Modules.pullback (Spec.map ε)).map E.inv ≫
      (Scheme.Modules.pullbackComp (Spec.map ε) hU.fromSpec).hom.app I ≫
      (Scheme.Modules.pullbackCongr hε).hom.app I) (1 : Γ(Spec ↧ℂ, ⊤)) = _
  exact hv.trans (moduleSectionValue_factorization I U s p hp q hq)

#print axioms affineOpenIdealPointEquiv_section
end HodgeLean.Foundations.Program.G32Native
