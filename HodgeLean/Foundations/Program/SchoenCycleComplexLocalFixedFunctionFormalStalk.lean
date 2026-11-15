import HodgeLean.Foundations.Program.SchoenCycleComplexFixedFunctionFormalStalk
import HodgeLean.Foundations.Program.SchoenCycleComplexFixedFunctionLocalValues
import HodgeLean.Foundations.Program.SchoenCycleLocalizedFormalComparisonValues
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineAdicValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual localized fixed-function formal algebra identifies with geometric formal stalk invariants and retains the exact actual pullback of every local function.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_complex_local_fixed_function_formal_stalk_invariants
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsLocallyNoetherian X.left]
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ g, a g ≫ q = q) (U : Y.left.Opens)
    (hW : IsAffineOpen (q.left ⁻¹ᵁ U)) (p : X.left) (hp : p ∈ q.left ⁻¹ᵁ U)
    (hclosed : IsClosed ({p} : Set X.left)) (hfix : ∀ g, (a g).left p = p) :
    let W := q.left ⁻¹ᵁ U
    letI := s2e_step1_sectionAlgebra X W
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
    let R := X.left.presheaf.stalk p
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    let P := (hW.primeIdealOf ⟨p, hp⟩).asIdeal
    let S := FixedPoints.subalgebra ℂ Γ(X.left, W) G
    let Q := P.under S
    let β : G → (R →ₐ[ℂ] R) := fun g =>
      { toRingHom := s2e_fixed_point_stalkPullback X.left (a g⁻¹).left p (hfix g⁻¹)
        commutes' := s2e_fixed_point_stalkPullback_scalars X (a g⁻¹) p (hfix g⁻¹) }
    let βhat g := s2e_adic_algebra_map _ _ (β g)
      (s2e_fixed_point_stalkPullback_power X.left (a g⁻¹).left p (hfix g⁻¹))
    ∃ F : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (Localization.AtPrime Q) ≃ₐ[ℂ]
      (⨅ g, AlgHom.equalizer (βhat g) (AlgHom.id ℂ
        (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
        Subalgebra ℂ (AdicCompletion (IsLocalRing.maximalIdeal R) R)),
      ∀ t, (F (AdicCompletion.of (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
          (Localization.AtPrime Q) t)).val =
        AdicCompletion.of (IsLocalRing.maximalIdeal R) R
          (s2e_complex_fixed_function_local_pullback X Y G a ha1 hamul q hinv U hW p hp hfix t) := by
  dsimp only
  let W := q.left ⁻¹ᵁ U
  let C := Γ(X.left, W)
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  let R := X.left.presheaf.stalk p
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  let P := (hW.primeIdealOf ⟨p, hp⟩).asIdeal
  let S := FixedPoints.subalgebra ℂ C G
  let Q := P.under S
  letI : P.IsMaximal := hW.primeIdealOf_isMaximal_of_isClosed ⟨p, hp⟩ hclosed
  letI : Algebra.IsIntegral S C := Algebra.IsInvariant.isIntegral S C G
  letI : Q.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  obtain ⟨hQ, E, hE⟩ := s2e_complex_fixed_function_formal_stalk_invariants
    X Y G a ha1 hamul q hinv U hW p hp hclosed hfix
  let f := (s2e_complex_section_germ X W p hp).comp S.val
  let l := s2e_complex_fixed_function_local_pullback X Y G a ha1 hamul q hinv U hW p hp hfix
  apply s2e_localized_formal_comparison_values Q _ E f l
  · intro s
    exact s2e_complex_fixed_function_local_pullback_of X Y G a ha1 hamul q hinv U hW p hp hfix s
  · intro s
    rw [hE, s2e_adic_algebra_map_of, s2e_complex_affine_adic_of_section]
    rfl

#print axioms s2e_complex_local_fixed_function_formal_stalk_invariants
end HodgeLean.Foundations.Program
