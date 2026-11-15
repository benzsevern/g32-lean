import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeMap
import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealPointSection
import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealEquation
import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalSectionClass
import HodgeLean.Foundations.Program.G32Native.PairedC3EqualityTransport

/-! # Original local equations in the actual conormal point derivative -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- On an actual ambient affine open, the actual conormal point pairing
retains the derivative of every original local ideal equation. -/
theorem conormalPointDerivativeMap_localSection {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    [IsClosedImmersion i.left] (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (x : ComplexPoint Q) (U : W.left.Opens) (hU : IsAffineOpen U)
    (hx : Point.map i x ∈ Point.overOpen U) (v : Fin d → ℂ)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) :
    conormalPointDerivativeMap i d x U hU hx v (conormalLocalClass i U s x hx) =
      conormalLocalDerivative i d U s x v := by
  let R := Γ(W.left, U)
  let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
  let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
  let t := affineOpenIdealSection i.left U hU s
  let γ := (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
    ((Scheme.Modules.pullback (Spec.map ε)).map t)
    ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).inv
      (1 : Γ(Spec ↧ℂ, ⊤)))
  have he : (conormalAffinePointEquiv i d x U hU hx).symm γ = conormalLocalClass i U s x hx :=
    conormalPointDerivativeMap_section_class i d x U hU hx s
  have hD := conormalPointDerivativeMap_affineSection i d x U hU hx v t
  change conormalPointDerivativeMap i d x U hU hx v
    ((conormalAffinePointEquiv i d x U hU hx).symm γ) =
    analyticPointDerivation d v φ (affineIdealSectionInclusion R j
      (show (moduleSpecΓFunctor (R := R)).obj _ from
        t.val.app (Opposite.op ⊤) (1 : Γ(Spec R, ⊤)))) at hD
  have hfun := affineOpenIdealSection_function i U hU s
  change affineIdealSectionInclusion R j
    (show (moduleSpecΓFunctor (R := R)).obj _ from
      t.val.app (Opposite.op ⊤) (1 : Γ(Spec R, ⊤))) = conormalLocalFunction i U s at hfun
  exact mapped_value_transport (conormalPointDerivativeMap i d x U hU hx v)
    (analyticPointDerivation d v φ) he.symm hD hfun
    (regularSection_pointDerivative W d (Point.map i x) U hx (conormalLocalFunction i U s) v)

#print axioms conormalPointDerivativeMap_localSection
end HodgeLean.Foundations.Program.G32Native
