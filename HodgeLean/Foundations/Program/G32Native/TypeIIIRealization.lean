import HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData
import HodgeLean.Foundations.Program.G32Native.TypeIIIDiagonalRealization

noncomputable section
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program.G32Native

/-- The ordinary polarized setting before G32 Lemma 8.1, retaining the chosen
presentation `D = (−3,b)` and its identification with the whole endomorphism
algebra. No homology basis, trace presentation, Weil type, Rosati equation, or
discriminant comparison is an input.
Source: G32 v0.16, section 8, opening paragraph;
Birkenhake–Lange, Complex Abelian Varieties, second edition, sections 5.2 and 9.6. -/
structure TypeIIIPolarizedSixfold (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
    [IsProjective A.hom] (pol : HQ A 2) where
  b : ℚ
  b_neg : b < 0
  endomorphisms : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A
  dim_eq : dim A.left = 6
  nondegenerate : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol)
  positive : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) nondegenerate

variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}

/-- Quaternionic homology and the diagonal trace presentation of the given
polarization, retaining the specified quaternion algebra and its endomorphisms.
The definite endomorphism algebra has canonical positive Rosati involution;
the homology representation is a rank-three left module, and the associated
nondegenerate skew-Hermitian form has a diagonal quaternionic basis.
Source: G32 v0.16, section 8, opening paragraph;
Birkenhake–Lange, Complex Abelian Varieties, second edition, sections 1.2, 5.2,
9.4–9.6 (rational representation, type III and quaternionic polarizations). -/
theorem typeIII_homology_realization_aux (G : TypeIIIPolarizedSixfold A pol) :
    ∃ Q : TypeIIISixfoldData A pol,
      Q.b = G.b ∧ HEq Q.endomorphisms G.endomorphisms := by
  obtain ⟨e, l1, l2, l3, he, hdiag, htrace⟩ := typeIII_diagonal_trace_realization
    G.b G.b_neg G.endomorphisms G.dim_eq G.nondegenerate G.positive
  refine ⟨{ b := G.b, b_neg := G.b_neg, endomorphisms := G.endomorphisms
            pullback := abelianEnd0Action A
            pullback_integral := ?_
            homology := e, homology_action := he
            l1 := l1, l2 := l2, l3 := l3, diagonal_nonzero := hdiag
            nondegenerate := G.nondegenerate, positive := G.positive, trace_eq := htrace },
    rfl, HEq.rfl⟩
  intro f
  simpa only [one_smul] using spec_g4_abelianEnd0Action_tmul A 1 f

/-- The retained diagonal presentation supplied by the quaternionic realization.
Source: G32 v0.16, section 8, opening paragraph. -/
def TypeIIIPolarizedSixfold.realization (G : TypeIIIPolarizedSixfold A pol) :
    TypeIIISixfoldData A pol :=
  Classical.choose (typeIII_homology_realization_aux G)

/-- The quaternion parameter is retained by the realization. -/
theorem TypeIIIPolarizedSixfold.realization_b (G : TypeIIIPolarizedSixfold A pol) :
    G.realization.b = G.b :=
  (Classical.choose_spec (typeIII_homology_realization_aux G)).1

/-- The endomorphism identification, hence the specified Eisenstein embedding,
is retained by the realization. -/
theorem TypeIIIPolarizedSixfold.realization_endomorphisms
    (G : TypeIIIPolarizedSixfold A pol) :
    HEq G.realization.endomorphisms G.endomorphisms :=
  (Classical.choose_spec (typeIII_homology_realization_aux G)).2

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_homology_realization_aux
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIIPolarizedSixfold.realization_b
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIIPolarizedSixfold.realization_endomorphisms
