import HodgeLean.Foundations.BundleResolution.ModuleFrameFibreHelpers

/-! # Naturality of actual module-section specialization

Specializing a local section commutes with a morphism of algebraic modules.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution
variable {Q : Over (Spec ↧ℂ)}
theorem i1_moduleSectionValue_naturality {M N : Q.left.Modules} (f : M ⟶ N) (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_moduleSectionValue N U (s ≫ (Scheme.Modules.pullback U.ι).map f) x hx =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback x.left).map f) (i1_moduleSectionValue M U s x hx) := by
  let a := ComplexPoint.liftToOpen Q U x hx
  let : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  let t := inv (SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom)
  let c := Scheme.Modules.pullbackComp a U.ι
  let d := Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)
  have h : t ≫ (Scheme.Modules.pullback a).map
      (s ≫ (Scheme.Modules.pullback U.ι).map f) ≫ c.hom.app N ≫ d.hom.app N =
      (t ≫ (Scheme.Modules.pullback a).map s ≫ c.hom.app M ≫ d.hom.app M) ≫
        (Scheme.Modules.pullback x.left).map f := by
    simp only [Functor.map_comp, Category.assoc]
    erw [← d.hom.naturality f]
    erw [← c.hom.naturality_assoc f]
    rfl
  have hh := congrArg (fun v : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶
      (Scheme.Modules.pullback x.left).obj N => (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map v
      (1 : Γ(Spec ↧ℂ, ⊤))) h
  simpa only [i1_moduleSectionValue, t, c, d, a, Functor.map_comp,
    ModuleCat.comp_apply] using hh
end HodgeLean.Foundations.BundleResolution
