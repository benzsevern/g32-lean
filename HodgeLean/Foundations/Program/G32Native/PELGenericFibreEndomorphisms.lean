import HodgeLean.Foundations.Program.G32Native.PELEndomorphismCommutant
import HodgeLean.Adapters.AbelianCMData

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable (A B : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]

/-- If a marked fibre has the generic marked Lie algebra, its fixed action
exhausts End⁰ whenever it does on a reference fibre. The proof uses the actual
geometric endomorphism commutants of both fibres, rather than a fullness premise
on the target fibre.
Source: Mumford, Abelian Varieties, §§19, 22;
Abdulali, Annals 155 (2002), Proposition 2.3.1 and §§3.1–3.3. -/
theorem generic_fibre_action_surjective
    {D V : Type*} [Ring D] [Algebra ℚ D] [AddCommGroup V] [Module ℚ V]
    (mA : HQ A 1 ≃ₗ[ℚ] V) (mB : HQ B 1 ≃ₗ[ℚ] V)
    (rhoD : D →ₐ[ℚ] AbelianEnd0 A) (e : D ≃ₐ[ℚ] AbelianEnd0 B)
    (hfixed : ∀ d,
      (markedAction (abelianEnd0Action A) mA (rhoD d)).unop =
        (markedAction (abelianEnd0Action B) mB (e d)).unop)
    (hLie : (mA.conjAlgEquiv ℚ) ''
        (hodgeLieAlgebra (latticeHodgePieces A)
          (spec_latticeHodgePieces_isInternal A) : Set (Module.End ℚ (HQ A 1))) =
      (mB.conjAlgEquiv ℚ) ''
        (hodgeLieAlgebra (latticeHodgePieces B)
          (spec_latticeHodgePieces_isInternal B) : Set (Module.End ℚ (HQ B 1)))) :
    Function.Surjective rhoD := by
  intro a
  have hc := (marked_end0_range_iff_commutant A mA
    (markedAction (abelianEnd0Action A) mA a).unop).mp ⟨a, rfl⟩
  rw [hLie] at hc
  obtain ⟨b, hb⟩ := (marked_end0_range_iff_commutant B mB _).mpr hc
  refine ⟨e.symm b, ?_⟩
  apply spec_g4_abelianEnd0Action_injective A
  apply MulOpposite.unop_injective
  apply (mA.conjAlgEquiv ℚ).injective
  change (markedAction (abelianEnd0Action A) mA (rhoD (e.symm b))).unop =
    (markedAction (abelianEnd0Action A) mA a).unop
  rw [hfixed, e.apply_symm_apply]
  exact hb

/-- Equality of the retained marked actions with an exact reference action
also gives faithfulness, before any generic-group comparison.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.2, 5.5. -/
theorem fixed_fibre_action_injective
    {D V : Type*} [Ring D] [Algebra ℚ D] [AddCommGroup V] [Module ℚ V]
    (mA : HQ A 1 ≃ₗ[ℚ] V) (mB : HQ B 1 ≃ₗ[ℚ] V)
    (rhoD : D →ₐ[ℚ] AbelianEnd0 A) (e : D ≃ₐ[ℚ] AbelianEnd0 B)
    (hfixed : ∀ d,
      (markedAction (abelianEnd0Action A) mA (rhoD d)).unop =
        (markedAction (abelianEnd0Action B) mB (e d)).unop) :
    Function.Injective rhoD := by
  intro x y hxy
  apply e.injective
  apply spec_g4_abelianEnd0Action_injective B
  apply MulOpposite.unop_injective
  apply (mB.conjAlgEquiv ℚ).injective
  change (markedAction (abelianEnd0Action B) mB (e x)).unop =
    (markedAction (abelianEnd0Action B) mB (e y)).unop
  rw [← hfixed, ← hfixed, hxy]

#print axioms generic_fibre_action_surjective
#print axioms fixed_fibre_action_injective
end HodgeLean.Foundations.Program.GeneralTypeIII
