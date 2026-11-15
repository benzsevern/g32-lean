import HodgeLean.Foundations.Program.G32Native.ConormalAffinePointDualEvaluation
import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealSectionSurjectivity
import HodgeLean.Foundations.Program.G32Native.ModuleGlobalSectionHom
import HodgeLean.Foundations.Program.G32Native.AffinePointGlobalSection
import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleAffineHelpers

/-! # Original local ideal classes detect actual dual conormal vectors -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Opposite
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- On an actual ambient affine open containing the original point,
evaluation on all original local ideal classes determines the dual conormal vector. -/
theorem conormalLocalClasses_ext {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    [IsClosedImmersion i.left] (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (x : ComplexPoint Q) (U : W.left.Opens) (hU : IsAffineOpen U)
    (hx : Point.map i x ∈ Point.overOpen U)
    (ν μ : normalFibreOfModule (Conormal.sheaf i.left) x)
    (h : ∀ s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left),
      ν (conormalLocalClass i U s x hx) = μ (conormalLocalClass i U s x hx)) : ν = μ := by
  let R := Γ(W.left, U)
  let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
  let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  letI : Algebra R ℂ := ε.hom.toAlgebra
  let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
  let M := Conormal.idealModule j
  letI := s2e_idealModule_spec_fromTilde_isIso R j
  let e := conormalAffinePointEquiv i d x U hU hx
  let T := e.dualMap
  let D := affinePointDualEquiv R ε M
  apply T.symm.injective
  apply D.injective
  ext m
  let t := moduleGlobalSectionHom M (show Γ(M, ⊤) from m)
  have ht : (show (moduleSpecΓFunctor (R := R)).obj M from
      t.val.app (op ⊤) (1 : Γ(Spec R, ⊤))) = m := moduleGlobalSectionHom_top M m
  obtain ⟨s, hs⟩ := affineOpenIdealSection_surjective i.left U hU t
  have hν := conormalAffinePointDual_localClass i d x U hU hx ν s
  rw [hs] at hν
  change D (T.symm ν) (show (moduleSpecΓFunctor (R := R)).obj M from
      t.val.app (op ⊤) (1 : Γ(Spec R, ⊤))) = ν (conormalLocalClass i U s x hx) at hν
  rw [ht] at hν
  have hμ := conormalAffinePointDual_localClass i d x U hU hx μ s
  rw [hs] at hμ
  change D (T.symm μ) (show (moduleSpecΓFunctor (R := R)).obj M from
      t.val.app (op ⊤) (1 : Γ(Spec R, ⊤))) = μ (conormalLocalClass i U s x hx) at hμ
  rw [ht] at hμ
  exact hν.trans ((h s).trans hμ.symm)

#print axioms conormalLocalClasses_ext
end HodgeLean.Foundations.Program.G32Native
