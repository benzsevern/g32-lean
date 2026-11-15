import HodgeLean.Foundations.PositivePolarizationRosati
import HodgeLean.Foundations.Program.G32Native.PELMarkedAction

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- The actual rational endomorphism action is the commutant of the
lattice-side Hodge Lie algebra, with analytic algebraization supplied internally.
Source: Mumford, Abelian Varieties, §§19, 22;
Birkenhake–Lange, Complex Abelian Varieties, §§1.2, 1.4. -/
theorem end0_range_iff_commutant
    (T : Module.End ℚ (HQ A 1)) :
    T ∈ Set.range (fun d : AbelianEnd0 A => (abelianEnd0Action A d).unop) ↔
      T ∈ Subalgebra.centralizer ℚ
        (hodgeLieAlgebra (latticeHodgePieces A)
          (spec_latticeHodgePieces_isInternal A) : Set (Module.End ℚ (HQ A 1))) := by
  rw [p1r_mem_range_iff]
  exact (spec_mem_centralizer_hodgeLieAlgebra_iff A _ T).symm

/-- A rational marking transports the exact geometric endomorphism commutant.
This does not assume that the fixed order action already exhausts End⁰.
Source: Mumford, Abelian Varieties, §§19, 22; Birkenhake–Lange, §§1.2, 5.5. -/
theorem marked_end0_range_iff_commutant
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (m : HQ A 1 ≃ₗ[ℚ] V) (T : Module.End ℚ V) :
    T ∈ Set.range (fun d : AbelianEnd0 A =>
      (markedAction (abelianEnd0Action A) m d).unop) ↔
      T ∈ Subalgebra.centralizer ℚ
        ((m.conjAlgEquiv ℚ) ''
          (hodgeLieAlgebra (latticeHodgePieces A)
            (spec_latticeHodgePieces_isInternal A) : Set (Module.End ℚ (HQ A 1)))) := by
  have hc : T ∈ Subalgebra.centralizer ℚ
      ((m.conjAlgEquiv ℚ) ''
        (hodgeLieAlgebra (latticeHodgePieces A)
          (spec_latticeHodgePieces_isInternal A) : Set (Module.End ℚ (HQ A 1)))) ↔
      (m.conjAlgEquiv ℚ).symm T ∈ Subalgebra.centralizer ℚ
        (hodgeLieAlgebra (latticeHodgePieces A)
          (spec_latticeHodgePieces_isInternal A) : Set (Module.End ℚ (HQ A 1))) := by
    simp only [Subalgebra.mem_centralizer_iff, Set.forall_mem_image]
    constructor
    · intro h X hX
      apply (m.conjAlgEquiv ℚ).injective
      simpa only [map_mul, AlgEquiv.apply_symm_apply] using h hX
    · intro h X hX
      simpa only [map_mul, AlgEquiv.apply_symm_apply] using
        congrArg (m.conjAlgEquiv ℚ) (h X hX)
  rw [hc, ← end0_range_iff_commutant]
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d, by simp only [markedAction_generator, AlgEquiv.symm_apply_apply]⟩
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    change (markedAction (abelianEnd0Action A) m d).unop = T
    rw [markedAction_generator]
    simpa only [AlgEquiv.apply_symm_apply] using congrArg (m.conjAlgEquiv ℚ) hd

#print axioms end0_range_iff_commutant
#print axioms marked_end0_range_iff_commutant
end HodgeLean.Foundations.Program.GeneralTypeIII
