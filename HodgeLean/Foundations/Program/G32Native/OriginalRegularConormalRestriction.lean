import HodgeLean.Foundations.Program.G32Native.OriginalRegularConormalValue
import HodgeLean.Foundations.Program.G32Native.ActualConormalSectionRestrictionChart
import HodgeLean.Foundations.Program.G32Native.ModuleAffineSectionValues
import HodgeLean.Foundations.Program.G32Native.OriginalIdealEquationRestriction

/-! # Restriction compatibility of the original descended conormal values -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open BundleResolution

/-- Restricting an original regular immersion equation preserves its value
in the original conormal fibre at the specified point.
Source: Hartshorne, Algebraic Geometry, II.5, restriction and pullback of
module sheaves, and II.8, the natural conormal sequence. -/
theorem originalRegularConormalValue_restriction_aux
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A B : W.Opens) (hA : IsAffineOpen A) (hB : IsAffineOpen B) (hBA : B ≤ A)
    (u : RingHom.ker (j.app A).hom) (v : RingHom.ker (j.app B).hom)
    (hv : v.val = W.presheaf.map (homOfLE hBA).op u.val)
    (x : ComplexPoint Q) (hxA : x ∈ Point.overOpen (j ⁻¹ᵁ A))
    (hx : x ∈ Point.overOpen (j ⁻¹ᵁ B)) :
    originalRegularConormalValue j A hA u x hxA =
      originalRegularConormalValue j B hB v x hx := by
  let hpre : j ⁻¹ᵁ B ≤ j ⁻¹ᵁ A := fun y hy => hBA hy
  let s := i1_moduleSectionRefine (Conormal.sheaf j) hpre
    (actualConormalAffineSectionData j A hA u).localSection
  have hc : i1_module_sectionPullback (hB.preimage j).isoSpec.inv
      ((Scheme.Modules.pullback (j ⁻¹ᵁ B).ι).obj (Conormal.sheaf j)) s ≫
      (actualConormalAffineChartIso j B hB).hom =
        affineConormalSection (W.presheaf.obj (.op B))
          (Q.left.presheaf.obj (.op (j ⁻¹ᵁ B))) (j.app B) v :=
    actualConormalSection_restriction_chart_aux j A B hA hB hBA u v hv
  let d : ModuleAffineSectionData (Q := Q) (Conormal.sheaf j)
      (j ⁻¹ᵁ B) (hB.preimage j) (Conormal.sheaf (Spec.map (j.app B)))
      (actualConormalAffineChartIso j B hB)
      (affineConormalSection (W.presheaf.obj (.op B))
        (Q.left.presheaf.obj (.op (j ⁻¹ᵁ B))) (j.app B) v) := ⟨s, hc⟩
  have hs : s = (actualConormalAffineSectionData j B hB v).localSection :=
    ModuleAffineSectionData.localSection_unique d (actualConormalAffineSectionData j B hB v)
  have hm := congrArg (fun t : SheafOfModules.unit.{0} (j ⁻¹ᵁ B).toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback (j ⁻¹ᵁ B).ι).obj (Conormal.sheaf j) =>
      i1_moduleSectionValue (Conormal.sheaf j) (j ⁻¹ᵁ B) t x hx) hs
  have href := i1_moduleSectionValue_refine (Conormal.sheaf j) hpre
    (actualConormalAffineSectionData j A hA u).localSection x hx
  exact (originalRegularConormalValue_eq j A hA u x hxA).trans
    (href.symm.trans (hm.trans (originalRegularConormalValue_eq j B hB v x hx).symm))

#print axioms originalRegularConormalValue_restriction_aux
end HodgeLean.Foundations.TubularEuler
