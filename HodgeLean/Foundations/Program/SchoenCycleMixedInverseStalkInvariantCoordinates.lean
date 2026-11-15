import HodgeLean.Foundations.Program.SchoenCycleMixedStalkInvariantCoordinates
import HodgeLean.Foundations.Program.SchoenCycleInverseIndexedInvariants

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Mixed formal coefficients identify with the geometric stalk invariant algebra indexed by inverse tuple stabilizers.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
def s2e_mixed_inverse_formal_stalk_invariant_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n b : ℕ) (x : ComplexPoint (g3_power X n))
    (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint X) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj X n (ι ⟨a, i⟩)) x = p a) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    let H := s2e_powerPointStabilizer X n x
    let Q := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let β (σ : H) : R →ₐ[ℂ] R :=
      { toRingHom := s2e_fixed_point_stalkPullback (g3_power X n).left (s2_permute X n σ.val).left x.underlying
          (s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ.val) x σ.property)
        commutes' := s2e_fixed_point_stalkPullback_scalars (g3_power X n) (s2_permute X n σ.val) x.underlying
          (s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ.val) x σ.property) }
    let βhat (σ : H) : Q →ₐ[ℂ] Q := s2e_adic_algebra_map _ _ (β σ)
      (fun N r hr => s2e_fixed_point_stalkPullback_power (g3_power X n).left (s2_permute X n σ.val).left
        x.underlying (s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ.val) x σ.property) N r hr)
    AdicCompletion (idealOfVars (Σ a, Fin (m a)) ℂ)
      (MvPolynomial (Σ a, Fin (m a)) ℂ) ≃ₐ[ℂ]
      (⨅ σ : H, AlgHom.equalizer (βhat σ⁻¹) (AlgHom.id ℂ Q) : Subalgebra ℂ Q) := by
  dsimp only
  letI : Algebra ℂ ((g3_power X n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  exact (s2e_mixed_formal_stalk_invariant_coordinates X n b x m ι p hp hx).trans
    (s2e_inverse_indexed_invariant_equiv _)

#print axioms s2e_mixed_inverse_formal_stalk_invariant_coordinates
end HodgeLean.Foundations.Program
