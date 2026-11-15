import HodgeLean.Foundations.Program.SchoenCycleFormalStabilizerCoordinates
import HodgeLean.Foundations.Program.SchoenCycleIntertwiningInvariantAlgebras
import HodgeLean.Foundations.Program.SchoenCyclePowerPointStabilizer

/-! # Multiplicative invariants in actual formal tuple coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Formal parameter invariants and actual formal stalk invariants agree as complex algebras for the full tuple stabilizer.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_curve_power_formal_stabilizer_invariants_equiv
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    let H := s2e_powerPointStabilizer X n x
    let P := AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ)
    let Q := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let α (σ : H) : P →ₐ[ℂ] P := s2e_adic_algebra_map _ _ (rename σ.val.symm)
      (s2e_rename_preserves_origin_powers σ.val.symm)
    let β (σ : H) : R →ₐ[ℂ] R :=
      { toRingHom := s2e_fixed_point_stalkPullback (g3_power X n).left (s2_permute X n σ.val).left x.underlying
          (s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ.val) x σ.property)
        commutes' := s2e_fixed_point_stalkPullback_scalars (g3_power X n) (s2_permute X n σ.val) x.underlying
          (s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ.val) x σ.property) }
    let βhat (σ : H) : Q →ₐ[ℂ] Q := s2e_adic_algebra_map _ _ (β σ)
      (fun N r hr => s2e_fixed_point_stalkPullback_power (g3_power X n).left (s2_permute X n σ.val).left
        x.underlying (s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ.val) x σ.property) N r hr)
    (⨅ σ : H, AlgHom.equalizer (α σ) (AlgHom.id ℂ P) : Subalgebra ℂ P) ≃ₐ[ℂ]
      (⨅ σ : H, AlgHom.equalizer (βhat σ) (AlgHom.id ℂ Q) : Subalgebra ℂ Q) := by
  dsimp only
  letI : Algebra ℂ ((g3_power X n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  apply s2e_intertwining_invariant_algebras_equiv (s2e_curve_power_adic_equiv X n x)
  intro σ
  exact s2e_curve_power_adic_equiv_stabilizer X n x σ.val σ.property

#print axioms s2e_curve_power_formal_stabilizer_invariants_equiv
end HodgeLean.Foundations.Program
