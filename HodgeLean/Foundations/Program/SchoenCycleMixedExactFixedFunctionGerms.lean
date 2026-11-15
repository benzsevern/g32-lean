import HodgeLean.Foundations.Program.SchoenCycleMixedExactStalkInvariants
import HodgeLean.Foundations.Program.SchoenCycleComplexFixedFunctionLocalDescent
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every exact mixed coefficient polynomial in the native parameters descends to an actual local function on the retained tuple stabilizer fixed-function algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_mixed_exact_fixed_function_germ
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z n ⟶ B) (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (U : B.left.Opens) (hW : IsAffineOpen (γ.left ⁻¹ᵁ U))
    (x : ComplexPoint (g3_power Z n)) (hxU : x.underlying ∈ γ.left ⁻¹ᵁ U)
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (q : MvPolynomial (Σ a, Fin (m a)) ℂ) :
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
    ∃ t : Localization.AtPrime Q,
      s2e_complex_fixed_function_local_pullback (g3_power Z n) B H a ha1 hamul γ hinv
        U hW x.underlying hxU hfix t =
      aeval (s2e_curvePowerParameter Z n x)
        (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m q).val) := by
  dsimp only
  let H := s2e_powerPointStabilizer Z n x
  letI : Fintype H := Fintype.ofFinite H
  let a := fun σ : H => s2_permute Z n σ.val
  let ha1 : a 1 = 𝟙 (g3_power Z n) := s2e_step1_permute_one Z n
  let hamul : ∀ u v, a (u * v) = a v ≫ a u := fun u v => s2e_step1_permute_mul Z n u.val v.val
  let hinv := fun σ : H => hγ σ.val
  let hfix := fun σ : H => s2e_complex_point_fixed_underlying (g3_power Z n) (a σ) x σ.property
  letI : Algebra ℂ ((g3_power Z n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  apply s2e_complex_fixed_function_local_descent (g3_power Z n) B H a ha1 hamul γ hinv
    U hW x.underlying hxU hfix
  intro σ
  exact s2e_mixed_exact_stalk_invariants Z n b x m ι p hp hx q σ⁻¹

#print axioms s2e_mixed_exact_fixed_function_germ
end HodgeLean.Foundations.Program
