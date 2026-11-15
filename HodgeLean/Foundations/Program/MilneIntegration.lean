import HodgeLean.Foundations.Program.MilneIntegrationProofs

/-! # Milne M3: cup and power integration (FROZEN SPEC)

Implication from the displayed complex abelian-variety instances and positive
nondegenerate polarization to the literal all-powers Milne input. The intermediate
statements connect M1 tensors and M2 divisors through homogeneous cup products.
The auxiliary bodies are open for review and the subsequent proving lane.
No assertion identifies arbitrary Hodge classes with these centralizer invariants.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

/-- The projection-induced exterior map respects homogeneous cup products on every power.
Source: Birkenhake–Lange, Complex Abelian Varieties, Lemma 1.3.1; Milne (1999), §1, cup algebra. -/
theorem m3_power_cup (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r i j : ℕ)
    (v : ⋀[ℂ]^i (Fin r → ℂ ⊗[ℚ] HQ J 1))
    (w : ⋀[ℂ]^j (Fin r → ℂ ⊗[ℚ] HQ J 1)) :
    g32p_powerClass J r (i + j)
      (exteriorPower.wedge ℂ (Fin r → ℂ ⊗[ℚ] HQ J 1) i j v w) =
    (cupProductOf (g3_power J r)).cupC rfl
      (g32p_powerClass J r i v) (g32p_powerClass J r j w) :=
  m3_power_cup_aux J r i j v w

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r i j : ℕ)
    (v : ⋀[ℂ]^i (Fin r → ℂ ⊗[ℚ] HQ J 1))
    (w : ⋀[ℂ]^j (Fin r → ℂ ⊗[ℚ] HQ J 1)) :
    g32p_powerClass J r (i + j)
      (exteriorPower.wedge ℂ (Fin r → ℂ ⊗[ℚ] HQ J 1) i j v w) =
    (cupProductOf (g3_power J r)).cupC rfl
      (g32p_powerClass J r i v) (g32p_powerClass J r j w) :=
  m3_power_cup J r i j v w

/-- The empty exterior product maps to the geometric unit, including the zeroth power.
Source: Birkenhake–Lange, Complex Abelian Varieties, Lemma 1.3.1; Milne (1999), introduction, empty intersection. -/
theorem m3_power_unit (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    g32p_powerClass J r 0 (exteriorPower.ιMulti ℂ 0 Fin.elim0) =
      (1 : ℂ) ⊗ₜ[ℚ] unitClass (g3_power J r) :=
  m3_power_unit_aux J r

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    g32p_powerClass J r 0 (exteriorPower.ιMulti ℂ 0 Fin.elim0) =
      (1 : ℂ) ⊗ₜ[ℚ] unitClass (g3_power J r) :=
  m3_power_unit J r

/-- Exterior fixed vectors are the alternating images of permuted quadratic tensor products.
Source: Milne (1999), Proposition 3.4 and Remark 3.7; m1b_centralizer_tensors and m0_tensor_lift_fixed. -/
theorem m3_exterior_products (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r n : ℕ) :
    (⨅ u ∈ g32p_lefschetz J pol,
      LinearMap.eqLocus (exteriorPower.map n (g32p_diag J u r)) LinearMap.id) =
    (m1b_products (m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2) n).map (InvariantsExterior.wedgeQuotient n) :=
  m3_exterior_products_aux J pol hη hpos r n

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r n : ℕ) :
    (⨅ u ∈ g32p_lefschetz J pol,
      LinearMap.eqLocus (exteriorPower.map n (g32p_diag J u r)) LinearMap.id) =
    (m1b_products (m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2) n).map (InvariantsExterior.wedgeQuotient n) :=
  m3_exterior_products J pol hη hpos r n

/-- The alternating cup image of each fixed quadratic tensor lies in the complex divisor span.
Source: Milne (1999), Proposition 3.3 and Lemma 3.1; m2_power_divisors. -/
theorem m3_quadratic_image (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r : ℕ) :
    ((m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2)).map
      ((g32p_powerClass J r 2).comp (InvariantsExterior.wedgeQuotient 2)) ≤
      (algebraicCycleClassSpan (g3_power J r) 1).baseChange ℂ :=
  m3_quadratic_image_aux J pol hη hpos r

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r : ℕ) :
    ((m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2)).map
      ((g32p_powerClass J r 2).comp (InvariantsExterior.wedgeQuotient 2)) ≤
      (algebraicCycleClassSpan (g3_power J r) 1).baseChange ℂ :=
  m3_quadratic_image J pol hη hpos r

/-- Permuted products of fixed quadratic tensors give algebraic classes in the stated codimension.
Source: Milne (1999), Theorem 3.2; Fulton, Intersection Theory, Corollary 19.2; g32c_cupC_span. -/
theorem m3_products_algebraic (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r p : ℕ) :
    (m1b_products (m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2) (2 * p)).map
      ((g32p_powerClass J r (2 * p)).comp (InvariantsExterior.wedgeQuotient (2 * p))) ≤
      (algebraicCycleClassSpan (g3_power J r) p).baseChange ℂ :=
  m3_products_algebraic_aux J pol hη hpos r p

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r p : ℕ) :
    (m1b_products (m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2) (2 * p)).map
      ((g32p_powerClass J r (2 * p)).comp (InvariantsExterior.wedgeQuotient (2 * p))) ≤
      (algebraicCycleClassSpan (g3_power J r) p).baseChange ℂ :=
  m3_products_algebraic J pol hη hpos r p

/-- The exact Milne input holds for every power and codimension, including zero.
Source: Milne (1999), Theorem 3.2 and Lemma 3.1; G32 v0.16, proof of Proposition 4.6. -/
theorem m3_milne_invariance (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) :
    g32p_MilneInvariance J pol hη hpos :=
  m3_milne_invariance_aux J pol hη hpos

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) :
    g32p_MilneInvariance J pol hη hpos :=
  m3_milne_invariance J pol hη hpos

end HodgeLean.Foundations.Program
