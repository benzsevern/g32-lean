import HodgeLean.Foundations.TubularEuler.ModuleAffinePointFibreHelpers
import HodgeLean.Foundations.BundleResolution.ModulePointValueAlgebraHelpers
import HodgeLean.Foundations.BundleResolution.ModulePullbackTransportHelpers

/-! # Section values through the original affine open factorization

The canonical pullback comparisons retain the original local section and point maps.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem modulePointValue_factorization_transport {V U X : Scheme.{0}}
    (a : Spec (CommRingCat.of ℂ) ⟶ V) (b : V ⟶ U) (u : U ⟶ X)
    (v : V ⟶ X) (w : Spec (CommRingCat.of ℂ) ⟶ U)
    (x : Spec (CommRingCat.of ℂ) ⟶ X)
    (hv : b ≫ u = v) (hw : a ≫ b = w) (hxv : a ≫ v = x) (hxu : w ≫ u = x)
    (M : X.Modules)
    (s : SheafOfModules.unit.{0} U.ringCatSheaf ⟶ (Scheme.Modules.pullback u).obj M) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullback a).map
          ((Scheme.Modules.pullbackComp b u).hom.app M ≫
            (Scheme.Modules.pullbackCongr hv).hom.app M) ≫
        (Scheme.Modules.pullbackComp a v).hom.app M ≫
          (Scheme.Modules.pullbackCongr hxv).hom.app M)
      (i1_module_pointValue ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback u).obj M))
        (i1_module_sectionPullback b ((Scheme.Modules.pullback u).obj M) s) a) =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullbackComp w u).hom.app M ≫
          (Scheme.Modules.pullbackCongr hxu).hom.app M)
        (i1_module_pointValue ((Scheme.Modules.pullback u).obj M) s w) := by
  rw [i1_module_pullback_factorization_coherence a b u v w x hv hw hxv hxu M]
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  let N := (Scheme.Modules.pullback u).obj M
  let F := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  have hc := i1_module_pointValue_pullback_comp a b N s
  have he := i1_module_pointValue_congr N s hw
  have ht := (congrArg (fun t : F.obj ((Scheme.Modules.pullback (a ≫ b)).obj N) =>
    F.map ((Scheme.Modules.pullbackCongr hw).hom.app N) t) hc).trans he
  exact congrArg (fun t : F.obj ((Scheme.Modules.pullback w).obj N) =>
    F.map ((Scheme.Modules.pullbackCongr hxu).hom.app M)
      (F.map ((Scheme.Modules.pullbackComp w u).hom.app M) t)) ht

theorem moduleAffinePointFibreIso_inverse_section_value
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    (moduleAffinePointFibreIso M U hU x hx).inv
      (i1_module_pointValue
        ((Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M))
        (i1_module_sectionPullback hU.isoSpec.inv ((Scheme.Modules.pullback U.ι).obj M) s)
        (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)) =
      i1_moduleSectionValue M U s x hx := by
  let a := ComplexPoint.liftToOpen Q U x hx
  let b := a ≫ hU.isoSpec.hom
  let c := hU.isoSpec.inv ≫ U.ι
  have hba : b ≫ hU.isoSpec.inv = a := by
    dsimp only [b]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hbc : b ≫ c = x.left := by
    dsimp only [b, c]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact ComplexPoint.liftToOpen_fac Q U x hx
  have h := modulePointValue_factorization_transport b hU.isoSpec.inv U.ι c a x.left
    rfl hba hbc (ComplexPoint.liftToOpen_fac Q U x hx) M s
  simp only [moduleAffinePointFibreIso, i1_moduleSectionValue_pointValue,
    i1_module_openFibreIso, Functor.mapIso_inv, Iso.symm_inv, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Scheme.Modules.pullbackCongr, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id, Functor.map_comp,
    ConcreteCategory.comp_apply, a, b, c] at h ⊢
  dsimp only [ConcreteCategory.hom] at h ⊢
  exact h

theorem moduleAffinePointFibreIso_section_value
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    (moduleAffinePointFibreIso M U hU x hx).hom (i1_moduleSectionValue M U s x hx) =
      i1_module_pointValue
        ((Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M))
        (i1_module_sectionPullback hU.isoSpec.inv ((Scheme.Modules.pullback U.ι).obj M) s)
        (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom) := by
  let e := moduleAffinePointFibreIso M U hU x hx
  have h := congrArg (fun t => e.hom t)
    (moduleAffinePointFibreIso_inverse_section_value M U hU s x hx)
  exact h.symm.trans (Iso.inv_hom_id_apply e _)

theorem moduleAffinePointFibreIso_section_naturality
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (f : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ⟶ N)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    let b := ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map ((Scheme.Modules.pullback b).map f)
      ((moduleAffinePointFibreIso M U hU x hx).hom (i1_moduleSectionValue M U s x hx)) =
      i1_module_pointValue N
        (i1_module_sectionPullback hU.isoSpec.inv ((Scheme.Modules.pullback U.ι).obj M) s ≫ f) b := by
  let b := ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom
  have h := congrArg (fun t => (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullback b).map f) t)
    (moduleAffinePointFibreIso_section_value M U hU s x hx)
  exact h.trans (i1_module_pointValue_naturality
    (i1_module_sectionPullback hU.isoSpec.inv ((Scheme.Modules.pullback U.ι).obj M) s) f b).symm

#print axioms moduleAffinePointFibreIso_section_naturality

#print axioms moduleAffinePointFibreIso_section_value

#print axioms moduleAffinePointFibreIso_inverse_section_value

#print axioms modulePointValue_factorization_transport

end HodgeLean.Foundations.TubularEuler
