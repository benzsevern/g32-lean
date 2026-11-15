import HodgeLean.Foundations.Program.CycleFoundationsProofs

/-! # Cycle foundations for the G32 contraction (FROZEN SPEC)
Implication from the explicit smooth projective abelian-variety instances and a finite
product cone to Künneth, and to evaluation and the projection formula for projection
integration. Projection integration uses a supplied rational top-degree coordinate, rather
than a chosen orientation. Pullback and projection of the algebraic span, and correspondence
preservation, are set aside (see `docs/specs/CycleFoundations.md`). No geometric realization
or G32 contraction is supplied here.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
/-- Finite-product degree-one Künneth on the specified product cone.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §1.3. -/
theorem cfd_kunneth_one (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)]
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom] (P : Over (Spec ↧ℂ)) [GrpObj P] [IsCommMonObj P]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (π : ∀ i, P ⟶ A i)
    (hπ : Limits.IsLimit (Limits.Fan.mk P π)) :
    Function.Bijective (cfd_oneMap r A P π) :=
  cfd_kunneth_one_aux r A P π hπ

example (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)]
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom] (P : Over (Spec ↧ℂ)) [GrpObj P] [IsCommMonObj P]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (π : ∀ i, P ⟶ A i)
    (hπ : Limits.IsLimit (Limits.Fan.mk P π)) :
    Function.Bijective (cfd_oneMap r A P π) := cfd_kunneth_one r A P π hπ

/-- Finite-product Künneth in every degree, using the exterior algebra of H¹.
The map is the cup map after the exterior power of the sum of factor pullbacks.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §1.3. -/
theorem cfd_kunneth_exterior (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)]
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom] (P : Over (Spec ↧ℂ)) [GrpObj P] [IsCommMonObj P]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (π : ∀ i, P ⟶ A i)
    (hπ : Limits.IsLimit (Limits.Fan.mk P π)) (n : ℕ) :
    Function.Bijective ((cupProductOf P).cupWedgeMap n ∘ₗ
      exteriorPower.map n (cfd_oneMap r A P π)) :=
  cfd_kunneth_exterior_aux r A P π hπ n

example (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)]
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom] (P : Over (Spec ↧ℂ)) [GrpObj P] [IsCommMonObj P]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (π : ∀ i, P ⟶ A i)
    (hπ : Limits.IsLimit (Limits.Fan.mk P π)) (n : ℕ) :
    Function.Bijective ((cupProductOf P).cupWedgeMap n ∘ₗ
      exteriorPower.map n (cfd_oneMap r A P π)) := cfd_kunneth_exterior r A P π hπ n

/-- The specified top Künneth component integrates to the chosen coordinate.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §1.3; Fulton, Intersection Theory, §19.1. -/
theorem cfd_projection_cross (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (n : ℕ) (a : HQ A n) (b : HQ B (2 * d)) :
    cfd_projection A B d I n
      ((cupProductOf (A ⊗ B)).cup rfl
        (homPullback (fst A B) n a) (homPullback (snd A B) (2 * d) b)) = I b • a :=
  cfd_projection_cross_aux A B d hB I n a b

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (n : ℕ) (a : HQ A n) (b : HQ B (2 * d)) :
    cfd_projection A B d I n
      ((cupProductOf (A ⊗ B)).cup rfl
        (homPullback (fst A B) n a) (homPullback (snd A B) (2 * d) b)) = I b • a := cfd_projection_cross A B d hB I n a b

/-- Projection formula for integration in an arbitrary rational top coordinate.
Source: Fulton, Intersection Theory, second edition, Proposition 8.1.1(c) and §19.1. -/
theorem cfd_projection_formula (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (i j : ℕ) (a : HQ A i) (b : HQ (A ⊗ B) (j + 2 * d)) :
    cfd_projection A B d I (i + j)
      ((cupProductOf (A ⊗ B)).cup (Nat.add_assoc i j (2 * d)).symm
        (homPullback (fst A B) i a) b) =
      (cupProductOf A).cup rfl a (cfd_projection A B d I j b) :=
  cfd_projection_formula_aux A B d hB I i j a b

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (i j : ℕ) (a : HQ A i) (b : HQ (A ⊗ B) (j + 2 * d)) :
    cfd_projection A B d I (i + j)
      ((cupProductOf (A ⊗ B)).cup (Nat.add_assoc i j (2 * d)).symm
        (homPullback (fst A B) i a) b) =
      (cupProductOf A).cup rfl a (cfd_projection A B d I j b) := cfd_projection_formula A B d hB I i j a b

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (n : ℕ) (a : HQ A n) (ha : a ≠ 0) :
    cfd_projection A B d I n ≠ 0 := by
  have he := cfd_projection_cross A B d hB I n a (I.symm 1)
  rw [I.apply_symm_apply, one_smul] at he
  intro hz
  rw [hz, LinearMap.zero_apply] at he
  exact ha he.symm

end HodgeLean.Foundations.Program
