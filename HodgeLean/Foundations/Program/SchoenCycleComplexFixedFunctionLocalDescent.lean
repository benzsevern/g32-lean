import HodgeLean.Foundations.Program.SchoenCycleComplexFixedFunctionLocalPullback

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every exact geometric invariant local function is the actual pullback of a localized fixed function at the retained fixed point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_complex_fixed_function_local_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ g, a g ≫ q = q) (U : Y.left.Opens)
    (hW : IsAffineOpen (q.left ⁻¹ᵁ U)) (p : X.left) (hp : p ∈ q.left ⁻¹ᵁ U)
    (hfix : ∀ g, (a g).left p = p) :
    let W := q.left ⁻¹ᵁ U
    letI := s2e_step1_sectionAlgebra X W
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
    let P := (hW.primeIdealOf ⟨p, hp⟩).asIdeal
    let S := FixedPoints.subalgebra ℂ Γ(X.left, W) G
    let Q := P.comap S.val.toRingHom
    let R := X.left.presheaf.stalk p
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    ∀ r : R, (∀ g : G, s2e_fixed_point_stalkPullback X.left (a g⁻¹).left p (hfix g⁻¹) r = r) →
      ∃ t : Localization.AtPrime Q,
        s2e_complex_fixed_function_local_pullback X Y G a ha1 hamul q hinv U hW p hp hfix t = r := by
  dsimp only
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  letI : Algebra ℂ (X.left.presheaf.stalk p) :=
    (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  let E := s2e_complex_affine_fixed_prime_local_invariants X Y G a ha1 hamul q hinv U hW p hp hfix
  intro r hr
  obtain ⟨t, ht⟩ := E.surjective ⟨r, by
    simp only [Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    exact hr⟩
  refine ⟨t, ?_⟩
  exact congrArg Subtype.val ht

#print axioms s2e_complex_fixed_function_local_descent
end HodgeLean.Foundations.Program
