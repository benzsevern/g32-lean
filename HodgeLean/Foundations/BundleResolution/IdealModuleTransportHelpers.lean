import HodgeLean.Foundations.Program.SchoenCycleS3ConormalIsoTransport

/-! # Ideal module transport through scheme isomorphisms

A commuting square with isomorphic source and ambient schemes transports
the actual kernel-defined ideal module by ambient pullback.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.BundleResolution

def i1_idealModule_arrowIso {Y' Y X' X : Scheme.{0}}
    (m : Y' ≅ Y) (j : X' ≅ X) (f : Y ⟶ X) (f' : Y' ⟶ X')
    (h : m.hom ≫ f = f' ≫ j.hom) :
    (Scheme.Modules.pullback j.hom).obj (s2c_idealModule f) ≅ s2c_idealModule f' :=
  (Scheme.Modules.pullback j.hom).mapIso (s2e_sourceIsoIdealModuleIso m.hom f).symm ≪≫
    (Scheme.Modules.pullback j.hom).mapIso (eqToIso (congrArg s2c_idealModule h)) ≪≫
    s2e_ambientIsoIdealPullbackIso f' j.hom

def i1_idealModule_comapIso {X' X : Scheme.{0}} (I : X.IdealSheafData) (j : X' ≅ X) :
    (Scheme.Modules.pullback j.hom).obj (s2c_idealModule I.subschemeι) ≅
      s2c_idealModule (I.comap j.hom).subschemeι := by
  let m : (I.comap j.hom).subscheme ≅ I.subscheme :=
    I.comapIso j.hom ≪≫ asIso (pullback.snd j.hom I.subschemeι)
  refine i1_idealModule_arrowIso m j I.subschemeι (I.comap j.hom).subschemeι ?_
  change (I.comapIso j.hom).hom ≫ pullback.snd j.hom I.subschemeι ≫ I.subschemeι = _
  rw [← pullback.condition, ← Category.assoc, I.comapIso_hom_fst]
end HodgeLean.Foundations.BundleResolution
