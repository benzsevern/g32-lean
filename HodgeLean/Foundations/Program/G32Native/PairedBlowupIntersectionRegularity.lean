import HodgeLean.Foundations.Program.G32Native.BranchIntersectionsSnc
import HodgeLean.Foundations.Program.G32Native.PairCentreSnc
import HodgeLean.Foundations.Program.G32Native.StrictTransformSnc
import HodgeLean.Foundations.Program.G32Native.LabelledBranchFamily
import HodgeLean.Foundations.Program.G32Native.SmoothBranchTransformComparison
import HodgeLean.Foundations.Program.G32Native.SncIntersectionRegularity
import HodgeLean.Foundations.Program.G32Native.PairedBlowupSmooth
import HodgeLean.Foundations.Program.G32Native.PairedBlowupIntegral

/-! Smoothness, integrality and all finite branch intersections on the native paired blow-up. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Blowing up a pair preserves the full smooth-intersection and conormal-frame invariant. -/
theorem g32l4_paired_blowup_intersection_regularity
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Over (Spec ↧ℂ)) [Smooth B.hom] [IsIntegral B.left]
    (D : ι → B.left.IdealSheafData) (u v : ι)
    (hintersections : ∀ J : Finset ι,
      Smooth (s2c_subscheme B (J.sup D)).hom ∧
      ∀ x : (J.sup D).subscheme, ∃ U : (J.sup D).subscheme.Opens, x ∈ U ∧ Nonempty
        (Scheme.Modules.restrict (s2c_conormal (J.sup D).subschemeι) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) : U.toScheme.Modules))) :
    let K := D u ⊔ D v
    let B' : Over (Spec ↧ℂ) := Over.mk (K.blowUpπ ≫ B.hom)
    let D' := fun j => s2c_strictTransform K.blowUpπ (D j) K
    (Smooth B'.hom ∧ IsIntegral B'.left) ∧
    ∀ J : Finset ι,
      Smooth (s2c_subscheme B' (J.sup D')).hom ∧
      ∀ x : (J.sup D').subscheme, ∃ U : (J.sup D').subscheme.Opens, x ∈ U ∧ Nonempty
        (Scheme.Modules.restrict (s2c_conormal (J.sup D').subschemeι) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) : U.toScheme.Modules)) := by
  let K := D u ⊔ D v
  let B' : Over (Spec ↧ℂ) := Over.mk (K.blowUpπ ≫ B.hom)
  let D' := fun j => s2c_strictTransform K.blowUpπ (D j) K
  let E := g32l4_labelledBranchFamily D
  let F := g32l4_strictTransformFamily E K
  have hsm := g32l4_paired_blowup_smooth B D u v (fun J => (hintersections J).1)
  have hu := (hintersections {u}).2
  rw [Finset.sup_singleton, Finset.card_singleton] at hu
  have hint := g32l4_paired_blowup_integral B (D u) (D v) hu
  letI : Smooth B'.hom := hsm
  letI : IsIntegral B'.left := hint
  letI : SmoothOfRelativeDimension (TopologicalSpace.dim B.left) B.hom := inferInstance
  have hE : E.IsSnc :=
    g32l4_isSnc_of_branch_intersections B (TopologicalSpace.dim B.left) E hintersections
  have hK : E.HasSncWith K := g32l4_pair_centre_hasSncWith E hE u v
  have hF : F.IsSnc := g32l4_strictTransformFamily_isSnc B E K hE hK
  letI : IsLocallyNoetherian B.left := B.hom.isLocallyNoetherian_of_field
  have hD' : D' = F.component := by
    funext j
    have hj := (hintersections {j}).1
    rw [Finset.sup_singleton] at hj
    letI : Smooth (s2c_subscheme B (D j)).hom := hj
    exact g32l4_smooth_branch_strictTransform_eq B (D j) K
  change (Smooth B'.hom ∧ IsIntegral B'.left) ∧
    ∀ J : Finset ι, Smooth (s2c_subscheme B' (J.sup D')).hom ∧
      ∀ x : (J.sup D').subscheme, ∃ U : (J.sup D').subscheme.Opens, x ∈ U ∧ Nonempty
        (Scheme.Modules.restrict (s2c_conormal (J.sup D').subschemeι) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) : U.toScheme.Modules))
  refine ⟨⟨hsm, hint⟩, ?_⟩
  rw [hD']
  intro J
  letI : SmoothOfRelativeDimension (TopologicalSpace.dim B'.left) B'.hom := inferInstance
  exact g32l4_snc_intersection_regularity B' (TopologicalSpace.dim B'.left) F hF J

end HodgeLean.Foundations.Program
