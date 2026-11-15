import HodgeLean.Foundations.Program.G32Native.PositivePairNumericalNonzero
import Mathlib.CategoryTheory.Conj

/-! # Numerical detection in the literal final tower coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- The numerical criterion supplies T13's input on the same final normalization.
The final component, supported class and conjugating isomorphism are arguments. -/
theorem selected_final_primitive_nonzero
    (S : g32p_Supplier)
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} (P : g32p_Part J aut S)
    (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (K : Type) [Field K]
    (η : ∀ i, Spec ↧K ⟶ (B i).left)
    (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶
      s2b_normalizationOver (B i) (η i))
    (horder : (End.of (d (Fin.last r))) ^ S.m = 1)
    (W : Over (Spec ↧ℂ))
    (eWr : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) P.k)
    (hdis : ∀ s t : Fin S.m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom) ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom) ^ t.val).asHom).left))
    (degree : AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint Q)) (2 * P.k) →ₗ[ℚ] ℚ)
    (hdegree : degree (s2e_normalEuler ι P.k c) ≠ 0) :
    ∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
      let δ := eWr.inv ≫ d (Fin.last r) ≫ eWr.hom
      s2e_weightedSum S.m (fun t : ZMod S.m => ζ ^ t.val)
        (fun t : Fin S.m => TensorProduct.tmul ℚ (1 : ℂ)
          (s2e_pullback ℚ ((End.of δ ^ (S.m - t.val)).asHom) (2 * P.k)
            (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) P.k c))) ≠ 0 := by
  have hperiod : End.of (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom) ^ S.m = 1 := by
    have ho := congrArg eWr.conj horder
    rw [map_pow, map_one] at ho
    have he : eWr.conj (End.of (d (Fin.last r))) =
        End.of (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom) := by
      apply End.ext
      rw [Iso.conj_apply_asHom]
    rw [he] at ho
    exact ho
  exact numerical_normal_weighted_nonzero ι _ S.m
    (by have := S.three_le; omega) hperiod hdis P.k c degree hdegree

#print axioms selected_final_primitive_nonzero
end HodgeLean.Foundations.Program.G32Native
