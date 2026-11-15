import HodgeLean.Foundations.Program.G32Native.PELGenericGroupEndomorphisms

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable (A B : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
local instance : Module.Finite ℚ (HQ B 1) := (torusCohomology_cupProductOf B).finite

/-- The faithful contravariant End⁰ action in a specified rational basis.
Source: Mumford, Abelian Varieties, §§19, 22. -/
def end0MatrixAction {n : ℕ} (b : Module.Basis (Fin n) ℚ (HQ A 1)) :
    AbelianEnd0 A →ₐ[ℚ] (Matrix (Fin n) (Fin n) ℚ)ᵐᵒᵖ :=
  (LinearMap.toMatrixAlgEquiv b).op.toAlgHom.comp (abelianEnd0Action A)

/-- End⁰ has the same matrix image on fibres with the same marked Hodge group.
No action on the target fibre is required as an input.
Source: Mumford, Abelian Varieties, §§19, 22; Abdulali, Annals 155 (2002),
Proposition 2.3.1 and §§3.1–3.3. -/
theorem end0MatrixAction_range_eq {n : ℕ}
    (bA : Module.Basis (Fin n) ℚ (HQ A 1)) (bB : Module.Basis (Fin n) ℚ (HQ B 1))
    (hGroup : g2_hodgeGroup (latticeHodgePieces A)
        (spec_latticeHodgePieces_isInternal A) bA =
      g2_hodgeGroup (latticeHodgePieces B) (spec_latticeHodgePieces_isInternal B) bB) :
    (end0MatrixAction A bA).range = (end0MatrixAction B bB).range := by
  ext M
  have criterion (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
      [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
      (b : Module.Basis (Fin n) ℚ (HQ X 1)) :
      M ∈ (end0MatrixAction X b).range ↔
        ∀ N ∈ g1_lieOfSet (g2_hodgeGroup (latticeHodgePieces X)
          (spec_latticeHodgePieces_isInternal X) b),
          N * M.unop.map (algebraMap ℚ ℂ) = M.unop.map (algebraMap ℚ ℂ) * N := by
    letI := (torusCohomology_cupProductOf X).finite
    have hc := (end0_range_iff_commutant X (Matrix.toLin b b M.unop)).trans
      (commutant_iff_group_tangent (latticeHodgePieces X)
        (spec_latticeHodgePieces_isInternal X) b _)
    rw [LinearMap.toMatrix_toLin] at hc
    rw [← hc]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, ?_⟩
      apply (LinearMap.toMatrix b b).injective
      rw [LinearMap.toMatrix_toLin]
      exact congrArg MulOpposite.unop hd
    · rintro ⟨d, hd⟩
      refine ⟨d, ?_⟩
      apply MulOpposite.unop_injective
      change LinearMap.toMatrix b b (abelianEnd0Action X d).unop = M.unop
      change (abelianEnd0Action X d).unop = Matrix.toLin b b M.unop at hd
      rw [hd, LinearMap.toMatrix_toLin]
  rw [criterion A bA, criterion B bB, hGroup]

/-- Equality of marked Hodge groups transports the entire actual endomorphism
algebra, retaining its matrices in the specified bases.
Source: Mumford, Abelian Varieties, §§19, 22; Abdulali, Annals 155 (2002),
Proposition 2.3.1. -/
def referenceEnd0Equiv {n : ℕ}
    (bA : Module.Basis (Fin n) ℚ (HQ A 1)) (bB : Module.Basis (Fin n) ℚ (HQ B 1))
    (hGroup : g2_hodgeGroup (latticeHodgePieces A)
        (spec_latticeHodgePieces_isInternal A) bA =
      g2_hodgeGroup (latticeHodgePieces B) (spec_latticeHodgePieces_isInternal B) bB) :
    AbelianEnd0 B ≃ₐ[ℚ] AbelianEnd0 A :=
  (AlgEquiv.ofInjective (end0MatrixAction B bB)
    ((LinearMap.toMatrixAlgEquiv bB).op.injective.comp
      (spec_g4_abelianEnd0Action_injective B))).trans
    ((Subalgebra.equivOfEq _ _ (end0MatrixAction_range_eq A B bA bB hGroup).symm).trans
      (AlgEquiv.ofInjective (end0MatrixAction A bA)
        ((LinearMap.toMatrixAlgEquiv bA).op.injective.comp
          (spec_g4_abelianEnd0Action_injective A))).symm)

/-- The transported endomorphism retains the reference matrix exactly.
Source: Mumford, Abelian Varieties, §19. -/
theorem referenceEnd0Equiv_matrix {n : ℕ}
    (bA : Module.Basis (Fin n) ℚ (HQ A 1)) (bB : Module.Basis (Fin n) ℚ (HQ B 1))
    (hGroup : g2_hodgeGroup (latticeHodgePieces A)
        (spec_latticeHodgePieces_isInternal A) bA =
      g2_hodgeGroup (latticeHodgePieces B) (spec_latticeHodgePieces_isInternal B) bB)
    (d : AbelianEnd0 B) :
    LinearMap.toMatrix bA bA
      (abelianEnd0Action A (referenceEnd0Equiv A B bA bB hGroup d)).unop =
      LinearMap.toMatrix bB bB (abelianEnd0Action B d).unop := by
  have hh := (AlgEquiv.ofInjective (end0MatrixAction A bA)
    ((LinearMap.toMatrixAlgEquiv bA).op.injective.comp
      (spec_g4_abelianEnd0Action_injective A))).apply_symm_apply
    ((Subalgebra.equivOfEq _ _ (end0MatrixAction_range_eq A B bA bB hGroup).symm)
      ((AlgEquiv.ofInjective (end0MatrixAction B bB)
        ((LinearMap.toMatrixAlgEquiv bB).op.injective.comp
          (spec_g4_abelianEnd0Action_injective B))) d))
  exact congrArg (fun z => MulOpposite.unop z.val) hh

#print axioms end0MatrixAction
#print axioms end0MatrixAction_range_eq
#print axioms referenceEnd0Equiv
#print axioms referenceEnd0Equiv_matrix
end HodgeLean.Foundations.Program.GeneralTypeIII
