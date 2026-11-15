import HodgeLean.Foundations.Program.CompensationProduct

/-! Concrete cycle foundation maps. HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
/-- Sum of factor pullbacks in degree one.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §1.3. -/
def cfd_oneMap (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)]
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom] (P : Over (Spec ↧ℂ)) [GrpObj P] [IsCommMonObj P]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (π : ∀ i, P ⟶ A i) :
    (∀ i, HQ (A i) 1) →ₗ[ℚ] HQ P 1 :=
  ∑ i, (homPullback (π i) 1).comp (LinearMap.proj i)

example (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)]
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom] (P : Over (Spec ↧ℂ)) [GrpObj P] [IsCommMonObj P]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (π : ∀ i, P ⟶ A i) :
    cfd_oneMap r A P π 0 = 0 := map_zero _

/-- The existing algebraic cycle span transported to the HQ carrier.
This is a submodule, with the same generators as the upstream span.
Source: Fulton, Intersection Theory, second edition, §19.1; HQ.linearEquiv. -/
def cfd_cycleSpan (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) : Submodule ℚ (HQ X (2 * p)) :=
  (algebraicCycleClassSpan X p).comap (HQ.linearEquiv X (2 * p)).toLinearMap

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) : 0 ∈ cfd_cycleSpan X p := Submodule.zero_mem _

/-- Integration in a rational top-degree coordinate I, via Künneth.
Rescaling I rescales the map.
Source: Fulton, Intersection Theory, second edition, §19.1; Birkenhake–Lange, §1.3. -/
def cfd_projection (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (n : ℕ) :
    HQ (A ⊗ B) (n + 2 * d) →ₗ[ℚ] HQ A n := by
  classical
  let E := LinearEquiv.ofBijective (cp_kunnethMap A B (n + 2 * d))
    (cp_kunneth A B (n + 2 * d))
  let k : Finset.HasAntidiagonal.antidiagonal (n + 2 * d) :=
    ⟨(n, 2 * d), Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  exact ((TensorProduct.rid ℚ (HQ A n)).toLinearMap.comp
    (TensorProduct.map LinearMap.id I.toLinearMap)).comp
    ((DirectSum.component ℚ _ _ k).comp E.symm.toLinearMap)

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (n : ℕ) :
    cfd_projection A B d I n 0 = 0 := map_zero _

/-- Cohomological correspondence action, with the target factor first.
Source: Fulton, Intersection Theory, second edition, §16.1 and §19.1. -/
def cfd_corrAction (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ)
    (h : 2 * c + 2 * p = 2 * q + 2 * d) (ξ : HQ (A ⊗ B) (2 * c)) :
    HQ B (2 * p) →ₗ[ℚ] HQ A (2 * q) :=
  (cfd_projection A B d I (2 * q)).comp
    (((cupProductOf (A ⊗ B)).cup h ξ).comp (homPullback (snd A B) (2 * p)))

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ)
    (h : 2 * c + 2 * p = 2 * q + 2 * d) (ξ : HQ (A ⊗ B) (2 * c)) :
    cfd_corrAction A B d I c p q h ξ 0 = 0 := map_zero _

end HodgeLean.Foundations.Program
