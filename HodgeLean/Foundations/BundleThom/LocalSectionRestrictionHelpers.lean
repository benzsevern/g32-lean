import HodgeLean.Foundations.BundleThom.ModuleSectionTransportHelpers

/-! # Compatibility of actual local section restriction and specialization

The complex point and every open factorization are retained in the transport maps.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- The existing local specialization uses the canonical module-section pullback and its actual factors.
Source: Hartshorne, Algebraic Geometry, II.5, restriction and specialization of local sections. -/
theorem i1_localModuleSectionSpecialization_transport {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    (U : Q.left.Opens)
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_localModuleSectionSpecialization M U s x hx =
      i1_moduleSectionPullback (ComplexPoint.liftToOpen Q U x hx)
          ((Scheme.Modules.pullback U.ι).obj M) s ≫
        (Scheme.Modules.pullbackComp (ComplexPoint.liftToOpen Q U x hx) U.ι).hom.app M ≫
          (Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)).hom.app M := by
  let a := ComplexPoint.liftToOpen Q U x hx
  let F := Scheme.Modules.pullback a
  let u := i1_unitPullbackIso a
  let p := (Scheme.Modules.pullbackComp a U.ι).hom.app M ≫
    (Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)).hom.app M
  change u.inv ≫ F.map s ≫ p = (u.inv ≫ F.map s) ≫ p
  exact (Category.assoc _ _ _).symm

/-- Restrict the actual local module section along the specified inclusion of scheme opens.
Source: Hartshorne, Algebraic Geometry, II.5, restriction of module sheaf sections. -/
def i1_localModuleSectionRestriction {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    {U V : Q.left.Opens} (hVU : V ≤ U)
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M) :
    SheafOfModules.unit.{0} V.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback V.ι).obj M :=
  i1_moduleSectionPullback (Q.left.homOfLE hVU) ((Scheme.Modules.pullback U.ι).obj M) s ≫
    (Scheme.Modules.pullbackComp (Q.left.homOfLE hVU) U.ι).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Q.left.homOfLE_ι hVU)).hom.app M

/-- The supplied point's lifts through nested opens respect the actual open inclusion.
Source: Hartshorne, Algebraic Geometry, II.2, factorization through open subschemes. -/
theorem i1_liftToOpen_restriction (Q : Over (Spec ↧ℂ)) {U V : Q.left.Opens}
    (hVU : V ≤ U) (x : ComplexPoint Q) (hxV : x ∈ Point.overOpen V) :
    ComplexPoint.liftToOpen Q V x hxV ≫ Q.left.homOfLE hVU =
      ComplexPoint.liftToOpen Q U x (hVU hxV) := by
  apply (cancel_mono U.ι).mp
  calc
    (ComplexPoint.liftToOpen Q V x hxV ≫ Q.left.homOfLE hVU) ≫ U.ι =
        ComplexPoint.liftToOpen Q V x hxV ≫ V.ι :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => ComplexPoint.liftToOpen Q V x hxV ≫ z) (Q.left.homOfLE_ι hVU))
    _ = x.left := ComplexPoint.liftToOpen_fac Q V x hxV
    _ = ComplexPoint.liftToOpen Q U x (hVU hxV) ≫ U.ι :=
      (ComplexPoint.liftToOpen_fac Q U x (hVU hxV)).symm

/-- Actual local section specialization is unchanged by restriction to a smaller open containing the point.
Source: Hartshorne, Algebraic Geometry, II.5, restriction and fibres of module sheaves. -/
theorem i1_localModuleSectionSpecialization_restriction {Q : Over (Spec ↧ℂ)}
    (M : Q.left.Modules) {U V : Q.left.Opens} (hVU : V ≤ U)
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hxV : x ∈ Point.overOpen V) :
    i1_localModuleSectionSpecialization M V (i1_localModuleSectionRestriction M hVU s) x hxV =
      i1_localModuleSectionSpecialization M U s x (hVU hxV) := by
  have ht := i1_moduleSectionTransport_factorization
    (ComplexPoint.liftToOpen Q V x hxV) (Q.left.homOfLE hVU) U.ι V.ι
    (ComplexPoint.liftToOpen Q U x (hVU hxV)) x.left
    (Q.left.homOfLE_ι hVU) (i1_liftToOpen_restriction Q hVU x hxV)
    (ComplexPoint.liftToOpen_fac Q V x hxV)
    (ComplexPoint.liftToOpen_fac Q U x (hVU hxV)) M s
  exact (i1_localModuleSectionSpecialization_transport M V
    (i1_localModuleSectionRestriction M hVU s) x hxV).trans
      (ht.trans (i1_localModuleSectionSpecialization_transport M U s x (hVU hxV)).symm)

/-- The actual local section value is unchanged by restriction around its supplied complex point.
Source: Hartshorne, Algebraic Geometry, II.5, restriction and evaluation of module sections. -/
theorem i1_localModuleSectionValue_restriction {Q : Over (Spec ↧ℂ)}
    (M : Q.left.Modules) {U V : Q.left.Opens} (hVU : V ≤ U)
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hxV : x ∈ Point.overOpen V) :
    i1_localModuleSectionValue M V (i1_localModuleSectionRestriction M hVU s) x hxV =
      i1_localModuleSectionValue M U s x (hVU hxV) := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  exact congrArg (fun z : SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf ⟶
      (Scheme.Modules.pullback x.left).obj M =>
      (G.map z).hom (1 : Γ(Spec ↧ℂ, ⊤)))
    (i1_localModuleSectionSpecialization_restriction M hVU s x hxV)

/-- The fixed conormal section-value operation respects the actual open restriction.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, restriction of conormal sections. -/
theorem i1_conormalSectionValue_restriction {Q : Over (Spec ↧ℂ)} {W : Scheme}
    (j : Q.left ⟶ W) {U V : Q.left.Opens} (hVU : V ≤ U)
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j))
    (x : ComplexPoint Q) (hxV : x ∈ Point.overOpen V) :
    i1_conormalSectionValue j V
        (i1_localModuleSectionRestriction (Conormal.sheaf j) hVU s) x hxV =
      i1_conormalSectionValue j U s x (hVU hxV) := by
  exact i1_localModuleSectionValue_restriction (Conormal.sheaf j) hVU s x hxV

end HodgeLean.Foundations.BundleThom
