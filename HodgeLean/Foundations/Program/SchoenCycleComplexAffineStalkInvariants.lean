import HodgeLean.Foundations.Program.SchoenCycleComplexAffineFixedAction
import HodgeLean.Foundations.Program.SchoenCycleIntertwiningInvariantAlgebras

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual simultaneous formal section invariants identify with geometric formal stalk invariants over the complex numbers.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_complex_affine_stalk_invariants
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (G : Type*)
    (f : G → (X ⟶ X)) (p : X.left) (hfix : ∀ g, (f g).left p = p)
    (U : X.left.Opens) (hU : IsAffineOpen U) (hUP : ∀ g, U ≤ (f g).left ⁻¹ᵁ U)
    (hp : p ∈ U) (hclosed : IsClosed ({p} : Set X.left)) :
    letI := s2e_step1_sectionAlgebra X U
    let R := X.left.presheaf.stalk p
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    let I := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
    let α g := s2e_complex_section_pullback X X (f g) U U (hUP g)
    let β g : R →ₐ[ℂ] R :=
      { toRingHom := s2e_fixed_point_stalkPullback X.left (f g).left p (hfix g)
        commutes' := s2e_fixed_point_stalkPullback_scalars X (f g) p (hfix g) }
    let βhat g := s2e_adic_algebra_map _ _ (β g)
      (s2e_fixed_point_stalkPullback_power X.left (f g).left p (hfix g))
    ∃ hα : ∀ g n a, a ∈ I ^ n → α g a ∈ I ^ n,
      Nonempty ((⨅ g, AlgHom.equalizer (s2e_adic_algebra_map I I (α g) (hα g))
        (AlgHom.id ℂ (AdicCompletion I Γ(X.left, U))) :
          Subalgebra ℂ (AdicCompletion I Γ(X.left, U))) ≃ₐ[ℂ]
        (⨅ g, AlgHom.equalizer (βhat g) (AlgHom.id ℂ (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
          Subalgebra ℂ (AdicCompletion (IsLocalRing.maximalIdeal R) R))) := by
  dsimp only
  letI := s2e_step1_sectionAlgebra X U
  letI : Algebra ℂ (X.left.presheaf.stalk p) :=
    (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  choose hα hh using fun g =>
    s2e_complex_affine_formal_fixed_action X (f g) p (hfix g) U hU (hUP g) hp hclosed
  refine ⟨hα, ⟨?_⟩⟩
  exact s2e_intertwining_invariant_algebras_equiv
    (s2e_complex_affine_point_adic_equiv X U hU p hp hclosed) _ _ hh

#print axioms s2e_complex_affine_stalk_invariants
end HodgeLean.Foundations.Program
