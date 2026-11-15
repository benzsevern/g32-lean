import HodgeLean.Foundations.Program.G32Native.ConormalAffineLocalClass
import HodgeLean.Foundations.Program.G32Native.AffinePointGlobalSection
import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleAffineHelpers

/-! # Original local class evaluations in the actual affine dual comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Opposite
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual affine dual comparison retains evaluation of the original
dual conormal vector on each original local ideal class. -/
theorem conormalAffinePointDual_localClass {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    [IsClosedImmersion i.left] (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (x : ComplexPoint Q) (U : W.left.Opens) (hU : IsAffineOpen U)
    (hx : Point.map i x ∈ Point.overOpen U)
    (ν : normalFibreOfModule (Conormal.sheaf i.left) x)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) :
    let R := Γ(W.left, U)
    let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
    let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
    let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
    letI := s2e_idealModule_spec_fromTilde_isIso R j
    affinePointDualEquiv R ε (Conormal.idealModule j)
      ((conormalAffinePointEquiv i d x U hU hx).dualMap.symm ν)
      (show (moduleSpecΓFunctor (R := R)).obj _ from
        (affineOpenIdealSection i.left U hU s).val.app (op ⊤) (1 : Γ(Spec R, ⊤))) =
      ν (conormalLocalClass i U s x hx) := by
  let R := Γ(W.left, U)
  let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
  let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  letI : Algebra R ℂ := ε.hom.toAlgebra
  let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
  let M := Conormal.idealModule j
  letI := s2e_idealModule_spec_fromTilde_isIso R j
  let e := conormalAffinePointEquiv i d x U hU hx
  let t := affineOpenIdealSection i.left U hU s
  have h := affinePointDualEquiv_globalSection R ε M t (e.dualMap.symm ν)
  change affinePointDualEquiv R ε M (e.dualMap.symm ν)
    (show (moduleSpecΓFunctor (R := R)).obj M from t.val.app (op ⊤) (1 : Γ(Spec R, ⊤))) =
    ν (e.symm ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullback (Spec.map ε)).map t)
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).inv
        (1 : Γ(Spec ↧ℂ, ⊤))))) at h
  rw [conormalAffinePointEquiv_localClass] at h
  exact h

#print axioms conormalAffinePointDual_localClass
end HodgeLean.Foundations.Program.G32Native
