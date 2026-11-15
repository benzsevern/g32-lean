import HodgeLean.Foundations.Program.G32Native.ModuleAffineSectionValues

/-! # Affine fibre transport through a specified point presentation -/
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

/-- The affine fibre chart with its target point supplied explicitly.
Source: `moduleAffineFibreChartIso`; the pullback comparison for equal points. -/
def moduleAffinePresentedFibreIso
    {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U)
    (p : Spec ↧ℂ ⟶ Spec (Q.left.presheaf.obj (.op U)))
    (hp : ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom = p) :
    i1_moduleFibre M x ≅ (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback p).obj N) :=
  moduleAffinePointFibreIso M U hU x hx ≪≫
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
      ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).mapIso e) ≪≫
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
      ((Scheme.Modules.pullbackCongr hp).app N)

/-- Descended sections specialize to the supplied affine section at the
specified point, without selecting an inverse to the spectrum functor.
Source: `moduleAffinePointFibreIso_section_naturality`,
`i1_module_pointValue_congr`, and `ModuleAffineSectionData.chart_equation`. -/
theorem ModuleAffineSectionData.point_value_presented
    {Q : Over (Spec ↧ℂ)} {M : Q.left.Modules}
    {U : Q.left.Opens} {hU : IsAffineOpen U}
    {N : (Spec (Q.left.presheaf.obj (.op U))).Modules}
    {e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N}
    {t : SheafOfModules.unit.{0} (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N}
    (s : ModuleAffineSectionData M U hU N e t)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U)
    (p : Spec ↧ℂ ⟶ Spec (Q.left.presheaf.obj (.op U)))
    (hp : ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom = p) :
    (moduleAffinePresentedFibreIso M U hU N e x hx p hp).hom
      (i1_moduleSectionValue M U s.localSection x hx) = i1_module_pointValue N t p := by
  have h0 := moduleAffinePointFibreIso_section_naturality M U hU s.localSection N e.hom x hx
  have h1 := congrArg
    (fun v : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).obj N) =>
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullbackCongr hp).hom.app N) v) h0
  have h2 := i1_module_pointValue_congr N
    (i1_module_sectionPullback hU.isoSpec.inv ((Scheme.Modules.pullback U.ι).obj M)
      s.localSection ≫ e.hom) hp
  have h3 := congrArg (fun sec => i1_module_pointValue N sec p) s.chart_equation
  exact moduleIso_apply_eq_of_functor_natIso (moduleSpecΓFunctor (R := CommRingCat.of ℂ))
    (Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom))
    (Scheme.Modules.pullback p) (Scheme.Modules.pullbackCongr hp)
    (moduleAffinePointFibreIso M U hU x hx) e
    (moduleAffinePresentedFibreIso M U hU N e x hx p hp) rfl
    (i1_moduleSectionValue M U s.localSection x hx) (i1_module_pointValue N t p)
    (h1.trans (h2.trans h3))

#print axioms ModuleAffineSectionData.point_value_presented
end HodgeLean.Foundations.TubularEuler
