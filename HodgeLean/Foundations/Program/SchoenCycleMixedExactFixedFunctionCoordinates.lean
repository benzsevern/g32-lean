import HodgeLean.Foundations.Program.SchoenCycleMixedExactFixedFunctionGerms
import HodgeLean.Foundations.Program.SchoenCycleMixedExactStalkInvariants
import HodgeLean.Foundations.Program.SchoenCycleComplexFixedFunctionLocalDescent
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric
import HodgeLean.Foundations.Program.SchoenCycleComplexLocalFixedFunctionFormalStalk
import HodgeLean.Foundations.Program.SchoenCycleMixedInverseStalkInvariantCoordinates
import HodgeLean.Foundations.Program.SchoenCycleMixedInverseStalkInvariantValues
import HodgeLean.Foundations.Program.SchoenCycleExactInvariantCotangentBasis

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Exact mixed elementary functions in the actual stabilizer local algebra retain their prescribed formal coordinate values.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_mixed_exact_fixed_function_coordinates
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z n ⟶ B) (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (U : B.left.Opens) (hW : IsAffineOpen (γ.left ⁻¹ᵁ U))
    (x : ComplexPoint (g3_power Z n)) (hxU : x.underlying ∈ γ.left ⁻¹ᵁ U)
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (hcx : IsClosed ({x.underlying} : Set (g3_power Z n).left)) :
    let H := s2e_powerPointStabilizer Z n x
    letI : Fintype H := Fintype.ofFinite H
    let a := fun σ : H => s2_permute Z n σ.val
    let ha1 : a 1 = 𝟙 (g3_power Z n) := s2e_step1_permute_one Z n
    let hamul : ∀ u v, a (u * v) = a v ≫ a u := fun u v => s2e_step1_permute_mul Z n u.val v.val
    let hinv := fun σ : H => hγ σ.val
    let hfix := fun σ : H => s2e_complex_point_fixed_underlying (g3_power Z n)
      (a σ) x σ.property
    let W := γ.left ⁻¹ᵁ U
    letI := s2e_step1_sectionAlgebra (g3_power Z n) W
    letI := s2e_step1_sectionAction (g3_power Z n) B H a ha1 hamul γ hinv U
    letI := s2e_step1_sectionAction_smulComm (g3_power Z n) B H a ha1 hamul γ hinv U
    let P := (hW.primeIdealOf ⟨x.underlying, hxU⟩).asIdeal
    let S := FixedPoints.subalgebra ℂ Γ((g3_power Z n).left, W) H
    let Q := P.under S
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ (D : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (Localization.AtPrime Q) ≃ₐ[ℂ]
        AdicCompletion (idealOfVars (Σ a, Fin (m a)) ℂ)
          (MvPolynomial (Σ a, Fin (m a)) ℂ))
      (c : (Σ a, Fin (m a)) → Localization.AtPrime Q),
      (∀ i, D (AdicCompletion.of _ _ (c i)) =
        AdicCompletion.of (idealOfVars (Σ a, Fin (m a)) ℂ)
          (MvPolynomial (Σ a, Fin (m a)) ℂ) (X i)) ∧
      (∀ i, s2e_complex_fixed_function_local_pullback (g3_power Z n) B H a ha1 hamul γ hinv
        U hW x.underlying hxU hfix (c i) =
        aeval (s2e_curvePowerParameter Z n x)
          (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m (X i)).val)) := by
  dsimp only
  let H := s2e_powerPointStabilizer Z n x
  letI : Fintype H := Fintype.ofFinite H
  let a := fun σ : H => s2_permute Z n σ.val
  let ha1 : a 1 = 𝟙 (g3_power Z n) := s2e_step1_permute_one Z n
  let hamul : ∀ u v, a (u * v) = a v ≫ a u := fun u v => s2e_step1_permute_mul Z n u.val v.val
  let hinv := fun σ : H => hγ σ.val
  let hfix := fun σ : H => s2e_complex_point_fixed_underlying (g3_power Z n) (a σ) x σ.property
  letI : IsLocallyNoetherian (g3_power Z n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z n).hom
  letI : Algebra ℂ ((g3_power Z n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  choose c hcval using fun i : Σ a, Fin (m a) =>
    s2e_mixed_exact_fixed_function_germ Z B n γ hγ U hW x hxU b m ι p hp hx (X i)
  obtain ⟨E, hE⟩ := s2e_complex_local_fixed_function_formal_stalk_invariants
    (g3_power Z n) B H a ha1 hamul γ hinv U hW x.underlying hxU hcx hfix
  let F := s2e_mixed_inverse_formal_stalk_invariant_coordinates Z n b x m ι p hp hx
  let D := E.trans F.symm
  have hD (i : Σ a, Fin (m a)) : D
      (AdicCompletion.of _ _ (c i)) =
      AdicCompletion.of (idealOfVars (Σ a, Fin (m a)) ℂ)
        (MvPolynomial (Σ a, Fin (m a)) ℂ) (X i) := by
    apply F.injective
    rw [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hE, hcval i]
    exact (s2e_mixed_inverse_formal_stalk_invariant_values Z n b x m ι p hp hx (X i)).symm
  exact ⟨D, c, hD, hcval⟩

#print axioms s2e_mixed_exact_fixed_function_coordinates
end HodgeLean.Foundations.Program
