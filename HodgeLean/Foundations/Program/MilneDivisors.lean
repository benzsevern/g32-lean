import HodgeLean.Foundations.Program.MilneDivisorsProofs

/-! # Milne M2: rational divisors and scalar extension

Implication from a positive nondegenerate polarization to the identification of
rational degree-two invariants through End⁰ and Rosati, and scalar extension
for the full complex centralizer. All self-products, including the zeroth, occur.
Higher-degree invariant generation belongs to M1; cup-product integration to M3.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

/-- Contraction coordinates detect every rational degree-two class.
Source: Bourbaki, Algebra, Chapter III, §7; Milne (1999), §1, Proposition 1.3. -/
theorem m2_operator_injective (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) :
    Function.Injective (m2_operator J pol hη) :=
  m2_operator_injective_aux J pol hη

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) :
    Function.Injective (m2_operator J pol hη) :=
  m2_operator_injective J pol hη

/-- Alternating bivectors give self-adjoint comparison operators.
Source: Milne (1999), §1, Proposition 1.3, dual cohomology convention. -/
theorem m2_operator_selfadjoint (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (d : HQ J 2) :
    p1_adjoint (polarizationVec (torusCohomology_cupProductOf J) pol) hη
      (m2_operator J pol hη d) = m2_operator J pol hη d :=
  m2_operator_selfadjoint_aux J pol hη d

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (d : HQ J 2) :
    p1_adjoint (polarizationVec (torusCohomology_cupProductOf J) pol) hη
      (m2_operator J pol hη d) = m2_operator J pol hη d :=
  m2_operator_selfadjoint J pol hη d

/-- Divisor classes correspond to rational Rosati-symmetric endomorphisms.
Source: Milne (1999), §1, Proposition 1.3; Birkenhake–Lange, §5.1; Lefschetz (1,1). -/
theorem m2_divisor_rosati (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (d : HQ J 2) :
    let hP : p1_IsPolarization J pol := (p1_isPolarization_iff J pol).2 ⟨hη, hpos⟩
    d ∈ algebraicCycleClassSpan J 1 ↔
      ∃ φ : AbelianEnd0 J, (abelianEnd0Action J φ).unop = m2_operator J pol hη d ∧
        p1_rosati J pol (p1_isNondegenerate J hP) (p1_adjoint_mem_range J hP) φ = φ :=
  m2_divisor_rosati_aux J pol hη hpos d

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (d : HQ J 2) :
    let hP : p1_IsPolarization J pol := (p1_isPolarization_iff J pol).2 ⟨hη, hpos⟩
    d ∈ algebraicCycleClassSpan J 1 ↔
      ∃ φ : AbelianEnd0 J, (abelianEnd0Action J φ).unop = m2_operator J pol hη d ∧
        p1_rosati J pol (p1_isNondegenerate J hP) (p1_adjoint_mem_range J hP) φ = φ :=
  m2_divisor_rosati J pol hη hpos d

/-- Rational degree-two fixed vectors give geometric endomorphisms.
Source: Milne (1999), Proposition 1.3 and proof of Proposition 3.3, using Lemma 3.5. -/
theorem m2_fixed_endomorphism (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (d : HQ J 2) :
    (∀ u ∈ g32p_lefschetz J pol,
      exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d)) =
      HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d)) ↔
      ∃ φ : AbelianEnd0 J, (abelianEnd0Action J φ).unop = m2_operator J pol hη d :=
  m2_fixed_endomorphism_aux J pol hη hpos d

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (d : HQ J 2) :
    (∀ u ∈ g32p_lefschetz J pol,
      exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d)) =
      HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d)) ↔
      ∃ φ : AbelianEnd0 J, (abelianEnd0Action J φ).unop = m2_operator J pol hη d :=
  m2_fixed_endomorphism J pol hη hpos d

/-- Rational divisors are exactly the rational degree-two fixed vectors.
Source: Milne (1999), Proposition 3.3, Betti specialization; Lefschetz (1,1). -/
theorem m2_divisor_fixed (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (d : HQ J 2) :
    d ∈ algebraicCycleClassSpan J 1 ↔
    ∀ u ∈ g32p_lefschetz J pol,
      exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d)) =
      HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d) :=
  m2_divisor_fixed_aux J pol hη hpos d

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (d : HQ J 2) :
    d ∈ algebraicCycleClassSpan J 1 ↔
    ∀ u ∈ g32p_lefschetz J pol,
      exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d)) =
      HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d) :=
  m2_divisor_fixed J pol hη hpos d

/-- The full complex invariant space is the scalar extension of its rational part.
Source: Milne (1999), Lemma 3.1, applied to the rational Betti centralizer and its exterior representations. -/
theorem m2_invariants_baseChange (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (r n : ℕ) :
    g32p_invariants J pol r n =
      (((g32p_invariants J pol r n).restrictScalars ℚ).comap
        (TensorProduct.mk ℚ ℂ (HQ (g3_power J r) n) 1)).baseChange ℂ :=
  m2_invariants_baseChange_aux J pol hη hpos r n

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (r n : ℕ) :
    g32p_invariants J pol r n =
      (((g32p_invariants J pol r n).restrictScalars ℚ).comap
        (TensorProduct.mk ℚ ℂ (HQ (g3_power J r) n) 1)).baseChange ℂ :=
  m2_invariants_baseChange J pol hη hpos r n

/-- Degree-two invariants on every self-product are spanned by rational divisors.
Source: Milne (1999), Proposition 3.3 and Proposition 1.5; Lemma 3.1. -/
theorem m2_power_divisors (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (r : ℕ) :
    g32p_invariants J pol r 2 =
      (algebraicCycleClassSpan (g3_power J r) 1).baseChange ℂ :=
  m2_power_divisors_aux J pol hη hpos r

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (r : ℕ) :
    g32p_invariants J pol r 2 =
      (algebraicCycleClassSpan (g3_power J r) 1).baseChange ℂ :=
  m2_power_divisors J pol hη hpos r

end HodgeLean.Foundations.Program
