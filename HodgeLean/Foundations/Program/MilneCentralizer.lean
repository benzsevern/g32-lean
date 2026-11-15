import HodgeLean.Foundations.Program.MilneCentralizerProofs

/-! # Milne M0: complex centralizer and polarization comparison (FROZEN SPEC)

Implication from the displayed abelian-variety instances and, where needed, the exact
nondegeneracy and positivity inputs of `g32p_MilneInvariance`. The group is the full
complex centralizer preserving the polarization, with no connectedness restriction.
M1 receives the full group action and its tensor lift; M2 receives the bilinear Rosati
comparison and polarization independence. Classical-factor decomposition, invariant
generation, rational descent and divisor identification remain further work.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

/-- Commuting with integral geometric endomorphisms is equivalent to commuting with End⁰.
Source: Milne (1999), §1, definition of C(A); `spec_g4_abelianEnd0Action_tmul`. -/
theorem m0_centralizer_integral (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    u ∈ m0_endCentralizer J ↔
      ∀ f : J ⟶ J, IsMonHom f → u ∘ₗ (homPullback f 1).baseChange ℂ =
        (homPullback f 1).baseChange ℂ ∘ₗ u :=
  m0_centralizer_integral_aux J u

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    u ∈ m0_endCentralizer J ↔
      ∀ f : J ⟶ J, IsMonHom f → u ∘ₗ (homPullback f 1).baseChange ℂ =
        (homPullback f 1).baseChange ℂ ∘ₗ u :=
  m0_centralizer_integral J u

/-- An invertible map fixes the polarization bivector exactly when it preserves the dual form.
Source: Bourbaki, Algebra, Chapter IX, §4, dual nondegenerate alternating forms;
Milne (1999), §1, the symplectic description of S(A). -/
theorem m0_bivector_iff_form (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hu : IsUnit u) :
    exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) pol)) =
      HodgeBlocks.complexifyWedge 2 (polarizationVec (torusCohomology_cupProductOf J) pol) ↔
    ∀ x y, m0_form J pol hη (u x) (u y) = m0_form J pol hη x y :=
  m0_bivector_iff_form_aux J pol hη u hu

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hu : IsUnit u) :
    exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) pol)) =
      HodgeBlocks.complexifyWedge 2 (polarizationVec (torusCohomology_cupProductOf J) pol) ↔
    ∀ x y, m0_form J pol hη (u x) (u y) = m0_form J pol hη x y :=
  m0_bivector_iff_form J pol hη u hu

/-- The repository group is the full symplectic centralizer on complex H¹.
Source: Milne (1999), §1, definition of S(A), transported to the dual representation. -/
theorem m0_mem_lefschetz_iff (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    u ∈ g32p_lefschetz J pol ↔
      IsUnit u ∧ u ∈ m0_endCentralizer J ∧
        ∀ x y, m0_form J pol hη (u x) (u y) = m0_form J pol hη x y :=
  m0_mem_lefschetz_iff_aux J pol hη u

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    u ∈ g32p_lefschetz J pol ↔
      IsUnit u ∧ u ∈ m0_endCentralizer J ∧
        ∀ x y, m0_form J pol hη (u x) (u y) = m0_form J pol hη x y :=
  m0_mem_lefschetz_iff J pol hη u

/-- Rosati gives the complex bilinear adjoint for the exact positive class in the G32 input.
Source: Birkenhake–Lange, Complex Abelian Varieties, 2nd ed., §5.1;
`p1r_abelianEnd0Action_rosati`, `p1r_baseChange_adjoint`, `p1_isPolarization_iff`. -/
theorem m0_rosati_pairing (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (φ : AbelianEnd0 J) (x y : ℂ ⊗[ℚ] HQ J 1) :
    let hP : p1_IsPolarization J pol := (p1_isPolarization_iff J pol).2 ⟨hη, hpos⟩
    m0_form J pol hη (((abelianEnd0Action J φ).unop).baseChange ℂ x) y =
      m0_form J pol hη x
        (((abelianEnd0Action J (p1_rosati J pol (p1_isNondegenerate J hP)
          (p1_adjoint_mem_range J hP) φ)).unop).baseChange ℂ y) :=
  m0_rosati_pairing_aux J pol hη hpos φ x y

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (φ : AbelianEnd0 J) (x y : ℂ ⊗[ℚ] HQ J 1) :
    let hP : p1_IsPolarization J pol := (p1_isPolarization_iff J pol).2 ⟨hη, hpos⟩
    m0_form J pol hη (((abelianEnd0Action J φ).unop).baseChange ℂ x) y =
      m0_form J pol hη x
        (((abelianEnd0Action J (p1_rosati J pol (p1_isNondegenerate J hP)
          (p1_adjoint_mem_range J hP) φ)).unop).baseChange ℂ y) :=
  m0_rosati_pairing J pol hη hpos φ x y

/-- The full endomorphism centralizer has a unique adjoint for the polarization form.
Source: Milne (1999), §1, paragraph preceding Proposition 1.1; `p1r_mem_range_iff`,
`p1r_abelianEnd0Action_rosati` and nondegeneracy of `polarizationForm`. -/
theorem m0_centralizer_adjoint (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hu : u ∈ m0_endCentralizer J) :
    ∃! v : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1), v ∈ m0_endCentralizer J ∧
      ∀ x y, m0_form J pol hη (u x) y = m0_form J pol hη x (v y) :=
  m0_centralizer_adjoint_aux J pol hη hpos u hu

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hu : u ∈ m0_endCentralizer J) :
    ∃! v : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1), v ∈ m0_endCentralizer J ∧
      ∀ x y, m0_form J pol hη (u x) y = m0_form J pol hη x (v y) :=
  m0_centralizer_adjoint J pol hη hpos u hu

/-- The full group on H¹ is independent of the positive nondegenerate polarization.
Source: Milne (1999), §1, paragraphs defining C(A) and S(A);
`p1r_mem_range_iff` identifies the rational Hodge comparison operator with End⁰. -/
theorem m0_polarization_independent (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (pol' : HQ J 2)
    (hη' : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol'))
    (hpos' : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη') :
    g32p_lefschetz J pol = g32p_lefschetz J pol' :=
  m0_polarization_independent_aux J pol hη hpos pol' hη' hpos'

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (pol' : HQ J 2)
    (hη' : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol'))
    (hpos' : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη') :
    g32p_lefschetz J pol = g32p_lefschetz J pol' :=
  m0_polarization_independent J pol hη hpos pol' hη' hpos'

/-- The full group action on every exterior degree commutes with the diagonal End⁰ action.
Source: Milne (1999), §1 and §3; functoriality of exterior powers applied to the centralizer. -/
theorem m0_exterior_commutes (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1))
    (hu : u ∈ g32p_lefschetz J pol) (φ : AbelianEnd0 J) (r n : ℕ) :
    exteriorPower.map n (g32p_diag J u r) ∘ₗ
        exteriorPower.map n (g32p_diag J (((abelianEnd0Action J φ).unop).baseChange ℂ) r) =
      exteriorPower.map n (g32p_diag J (((abelianEnd0Action J φ).unop).baseChange ℂ) r) ∘ₗ
        exteriorPower.map n (g32p_diag J u r) :=
  m0_exterior_commutes_aux J pol u hu φ r n

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1))
    (hu : u ∈ g32p_lefschetz J pol) (φ : AbelianEnd0 J) (r n : ℕ) :
    exteriorPower.map n (g32p_diag J u r) ∘ₗ
        exteriorPower.map n (g32p_diag J (((abelianEnd0Action J φ).unop).baseChange ℂ) r) =
      exteriorPower.map n (g32p_diag J (((abelianEnd0Action J φ).unop).baseChange ℂ) r) ∘ₗ
        exteriorPower.map n (g32p_diag J u r) :=
  m0_exterior_commutes J pol u hu φ r n

/-- The normalized alternating lift preserves and detects invariance under every group element.
Source: Bourbaki, Algebra, Chapter III, §7; Milne (1999), Remark 3.7;
`InvariantsExterior.wedgeQuotient_toTensorPower`. This uses the group action, not derivations. -/
theorem m0_tensor_lift_fixed (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2) (r n : ℕ)
    (v : ⋀[ℂ]^n (Fin r → ℂ ⊗[ℚ] HQ J 1)) :
    (∀ u ∈ g32p_lefschetz J pol, exteriorPower.map n (g32p_diag J u r) v = v) ↔
      ∀ u ∈ g32p_lefschetz J pol,
        PiTensorProduct.map (fun _ : Fin n => g32p_diag J u r) (m0_tensorLift J r n v) =
          m0_tensorLift J r n v :=
  m0_tensor_lift_fixed_aux J pol r n v

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2) (r n : ℕ)
    (v : ⋀[ℂ]^n (Fin r → ℂ ⊗[ℚ] HQ J 1)) :
    (∀ u ∈ g32p_lefschetz J pol, exteriorPower.map n (g32p_diag J u r) v = v) ↔
      ∀ u ∈ g32p_lefschetz J pol,
        PiTensorProduct.map (fun _ : Fin n => g32p_diag J u r) (m0_tensorLift J r n v) =
          m0_tensorLift J r n v :=
  m0_tensor_lift_fixed J pol r n v

/-- Odd-degree invariant cup images vanish, including the zero-fold power.
Source: Milne (1999), §1, the scalar minus identity in S(A), and its exterior action. -/
theorem m0_odd_invariants (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2) (r n : ℕ) (hn : Odd n) :
    g32p_invariants J pol r n = ⊥ :=
  m0_odd_invariants_aux J pol r n hn

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2) (r n : ℕ) (hn : Odd n) :
    g32p_invariants J pol r n = ⊥ :=
  m0_odd_invariants J pol r n hn

/-- Milne's norm-one equation in the cohomological representation, without choosing an adjoint.
Source: Milne (1999), §1, definition S(A)(R) = {γ | γ†γ = 1};
finite dimensionality turns a left inverse into an inverse. -/
theorem m0_mem_lefschetz_norm_one (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    u ∈ g32p_lefschetz J pol ↔
      u ∈ m0_endCentralizer J ∧ ∃ v : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1),
        (∀ x y, m0_form J pol hη (u x) y = m0_form J pol hη x (v y)) ∧
        v ∘ₗ u = 1 :=
  m0_mem_lefschetz_norm_one_aux J pol hη u

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    u ∈ g32p_lefschetz J pol ↔
      u ∈ m0_endCentralizer J ∧ ∃ v : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1),
        (∀ x y, m0_form J pol hη (u x) y = m0_form J pol hη x (v y)) ∧
        v ∘ₗ u = 1 :=
  m0_mem_lefschetz_norm_one J pol hη u

end HodgeLean.Foundations.Program
