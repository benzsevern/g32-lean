import HodgeLean.Foundations.Program.G32Native.OriginalConormalAffineSectionNaturality
import HodgeLean.Foundations.Program.G32Native.ModuleAffineSectionValues
import HodgeLean.Foundations.TubularEuler.ActualConormalSectionDataHelpers

/-! # An intrinsic representative of the descended original conormal section -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution

/-- Pulling back a section transported by an inverse isomorphism cancels the chart transport. -/
theorem moduleSectionPullback_inverseIso {X Y : Scheme.{0}} (f : X ⟶ Y)
    {M N : Y.Modules} (e : M ≅ N)
    (s : SheafOfModules.unit.{0} Y.ringCatSheaf ⟶ N)
    {T : X.Modules} (a : (Scheme.Modules.pullback f).obj N ≅ T) :
    i1_module_sectionPullback f M (s ≫ e.inv) ≫
        ((Scheme.Modules.pullback f).mapIso e ≪≫ a).hom =
      i1_module_sectionPullback f N s ≫ a.hom := by
  rw [conormalSection_pullback_map]
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    (Scheme.Modules.pullback f).map_id, Category.id_comp]

/-- Comparison between restriction of the original conormal and the restricted immersion. -/
def originalConormalOpenIso {Q W : Scheme.{0}} (j : Q ⟶ W) (A : W.Opens) :
    (Scheme.Modules.pullback (j ⁻¹ᵁ A).ι).obj (Conormal.sheaf j) ≅
      Conormal.sheaf (j ∣_ A) :=
  (Scheme.Modules.restrictFunctorIsoPullback (j ⁻¹ᵁ A).ι).symm.app (Conormal.sheaf j) ≪≫
    s2e_conormal_restrict_ambient_open_iso j A

/-- Pull the original ideal equation to its actual conormal on the inverse-image open. -/
def originalConormalIntrinsicSection {Q W : Scheme.{0}} (j : Q ⟶ W)
    (A : W.Opens) (u : RingHom.ker (j.app A).hom) :
    SheafOfModules.unit.{0} (j ⁻¹ᵁ A).toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback (j ⁻¹ᵁ A).ι).obj (Conormal.sheaf j) :=
  i1_module_sectionPullback (j ∣_ A) (Conormal.idealModule (j ∣_ A))
      (originalIdealOpenSection j A u) ≫ (originalConormalOpenIso j A).inv

/-- The intrinsic section has the original inverse-comparison construction. -/
theorem originalConormalIntrinsicSection_construction {Q W : Scheme.{0}}
    (j : Q ⟶ W) (A : W.Opens) (u : RingHom.ker (j.app A).hom) :
    originalConormalIntrinsicSection j A u =
      i1_module_sectionPullback (j ∣_ A) (Conormal.idealModule (j ∣_ A))
        (originalIdealOpenSection j A u) ≫ (originalConormalOpenIso j A).inv := by
  rfl

/-- The actual chart comparison factors through the original open conormal comparison. -/
theorem actualConormalAffineChartIso_open_construction
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}} (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) :
    actualConormalAffineChartIso j A hA =
      (Scheme.Modules.pullback (hA.preimage j).isoSpec.inv).mapIso
        (originalConormalOpenIso j A) ≪≫ s2e_immersion_affine_chart_conormal_iso j A hA := by
  rfl

/-- The intrinsic section satisfies the specified affine chart equation. -/
theorem originalConormalIntrinsicSection_chart
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}} (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom) :
    i1_module_sectionPullback (hA.preimage j).isoSpec.inv
        ((Scheme.Modules.pullback (j ⁻¹ᵁ A).ι).obj (Conormal.sheaf j))
        (originalConormalIntrinsicSection j A u) ≫
      (actualConormalAffineChartIso j A hA).hom =
        affineConormalSection (W.presheaf.obj (.op A))
          (Q.left.presheaf.obj (.op (j ⁻¹ᵁ A))) (j.app A) u := by
  rw [originalConormalIntrinsicSection_construction j A u,
    actualConormalAffineChartIso_open_construction j A hA]
  rw [moduleSectionPullback_inverseIso (hA.preimage j).isoSpec.inv
    (originalConormalOpenIso j A)]
  exact originalConormalOpenSection_affine_chart j A hA u

/-- The selected descended section agrees with the intrinsic representative. -/
theorem actualConormalAffineSectionData_eq_intrinsic
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom) :
    (actualConormalAffineSectionData j A hA u).localSection =
      originalConormalIntrinsicSection j A u := by
  exact ModuleAffineSectionData.localSection_unique (actualConormalAffineSectionData j A hA u)
    ⟨originalConormalIntrinsicSection j A u, originalConormalIntrinsicSection_chart j A hA u⟩

end HodgeLean.Foundations.TubularEuler
