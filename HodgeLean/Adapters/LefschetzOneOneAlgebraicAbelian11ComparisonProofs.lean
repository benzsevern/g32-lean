import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11Proofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11Normalization

/-! # Compositions from support comparison to the period square

Implication from the named comparison primitives and the bh10 relative square.
HC no distance; AV milestone no distance.
-/
set_option maxRecDepth 2048
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
open TopCat.Sheaf
namespace HodgeLean.Adapters

/-- The sheaf-to-singular comparison commutes with forgetting support.
Source: the singular-section edge and sheaf-support edge comparisons. -/
theorem bh11_forget_support_singular_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (S : Closeds (ComplexPoint X)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    singularToFieldCohomology ℚ X n
      (cohomologyMap ℚ n
        (TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint X)).symm,
          (Homeomorph.Set.univ (ComplexPoint X)).symm.continuous⟩)
        (relativeCohomologyToAbsolute ℚ
          (neighborhoodSupportComplementPair Set.univ (S : Set (ComplexPoint X))) n
          (supportedSingularClass X S n u))) = ComplexPoint.forgetSupport ℚ X S n u := by
  let Y := TopCat.of (ComplexPoint X)
  let (V : Opens (ComplexPoint X)) : ParacompactSpace V := openParacompactSpace X V
  let a := (complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)).inv
    (rationalSupportAddEquivSupportedInjectiveHomology X S n u)
  change singularToFieldCohomology ℚ X n
    (cohomologyMap ℚ n _ (relativeCohomologyToAbsolute ℚ _ n
      (supportedRationalSingularSectionCohomologyEquivSupportComplement Y S S.isClosed ⊤ n a))) = _
  exact (bh11_singular_section_edge_aux X S n a).trans
    ((congrArg (fun w => (hypercohomologyAddEquivConstantCohomology ℚ X n)
      ((fieldHypercohomologySingularCochainAddEquiv ℚ X (n : ℤ)).symm w))
      (bh11_sheaf_support_edge_aux X S n u)).trans
      (by rw [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]))

/-- The normalized cup comparison of a supported class is its absolute singular image.
Source: the forget-support bridge and the scalar-one cup comparison. -/
theorem bh11_cup_forget_support_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (S : Closeds (ComplexPoint X)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    cupComparison X n (forgetSupport ℚ X S n u) =
      cohomologyMap ℚ n
        (TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint X)).symm,
          (Homeomorph.Set.univ (ComplexPoint X)).symm.continuous⟩)
        (relativeCohomologyToAbsolute ℚ
          (neighborhoodSupportComplementPair Set.univ (S : Set (ComplexPoint X))) n
          (supportedSingularClass X S n u)) := by
  let (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  apply (spec_singularToFieldCohomology_bijective ℚ X n).injective
  exact (congrArg (singularToFieldCohomology ℚ X n)
    (bh11_cupComparison_eq_raw X n (forgetSupport ℚ X S n u))).trans
    ((singularToFieldCohomology_rationalCohomologyLinearEquivSingular X n
      (forgetSupport ℚ X S n u)).trans
      (bh11_forget_support_singular_aux X S n u).symm)

end HodgeLean.Adapters
