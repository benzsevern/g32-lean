import HodgeLean.Foundations.Program.G32Native.OriginalConormalIntrinsicRestriction
import HodgeLean.Foundations.TubularEuler.ActualConormalSectionDataHelpers
import HodgeLean.Foundations.BundleResolution.ModuleSectionRefineHelpers

/-! # The affine chart equation for restriction of an original conormal section -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open BundleResolution

/-- The restriction of the actual descended equation section has the
canonical affine chart equation for the restricted original ideal equation.
Source: Hartshorne, Algebraic Geometry, II.5, restriction and pullback of
module sheaves, and II.8, Proposition 8.12, naturality of the conormal sequence. -/
theorem actualConormalSection_restriction_chart_aux
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A B : W.Opens) (hA : IsAffineOpen A) (hB : IsAffineOpen B) (hBA : B ≤ A)
    (u : RingHom.ker (j.app A).hom) (v : RingHom.ker (j.app B).hom)
    (hv : v.val = W.presheaf.map (homOfLE hBA).op u.val) :
    let hpre : j ⁻¹ᵁ B ≤ j ⁻¹ᵁ A := fun y hy => hBA hy
    i1_module_sectionPullback (hB.preimage j).isoSpec.inv
        ((Scheme.Modules.pullback (j ⁻¹ᵁ B).ι).obj (Conormal.sheaf j))
        (i1_moduleSectionRefine (Conormal.sheaf j) hpre
          (actualConormalAffineSectionData j A hA u).localSection) ≫
      (actualConormalAffineChartIso j B hB).hom =
        affineConormalSection (W.presheaf.obj (.op B))
          (Q.left.presheaf.obj (.op (j ⁻¹ᵁ B))) (j.app B) v := by
  dsimp only
  rw [actualConormalAffineSectionData_eq_intrinsic j A hA u]
  rw [originalConormalIntrinsicSection_refine j A B hBA u v hv]
  exact originalConormalIntrinsicSection_chart j B hB v

end HodgeLean.Foundations.TubularEuler
