import HodgeLean.Foundations.Program.SchoenCycleFixedPrimeLocalInvariantEquiv
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineFixedAction
import HodgeLean.Foundations.Program.SchoenCycleAffinePointStabilizer
import HodgeLean.Foundations.Program.SchoenCycleStep1SectionAction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual fixed functions localized at a retained fixed point identify with the exact geometric stalk invariants.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_complex_affine_fixed_prime_local_invariants
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
    let R := X.left.presheaf.stalk p
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    let P := (hW.primeIdealOf ⟨p, hp⟩).asIdeal
    let S := FixedPoints.subalgebra ℂ Γ(X.left, W) G
    let Q := P.comap S.val.toRingHom
    let β : G → (R →ₐ[ℂ] R) := fun g =>
      { toRingHom := s2e_fixed_point_stalkPullback X.left (a g⁻¹).left p (hfix g⁻¹)
        commutes' := s2e_fixed_point_stalkPullback_scalars X (a g⁻¹) p (hfix g⁻¹) }
    Localization.AtPrime Q ≃ₐ[ℂ]
      (⨅ g, AlgHom.equalizer (β g) (AlgHom.id ℂ R) : Subalgebra ℂ R) := by
  dsimp only
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  let R := X.left.presheaf.stalk p
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  letI : Nonempty W := ⟨⟨p, hp⟩⟩
  letI : Algebra Γ(X.left, W) R :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨p, hp⟩
  letI : IsScalarTower ℂ Γ(X.left, W) R :=
    IsScalarTower.of_algebraMap_eq (fun c => ((s2e_complex_section_germ X W p hp).commutes c).symm)
  let P := (hW.primeIdealOf ⟨p, hp⟩).asIdeal
  letI : IsLocalization.AtPrime R P := hW.isLocalization_stalk ⟨p, hp⟩
  let β : G → (R →ₐ[ℂ] R) := fun g =>
    { toRingHom := s2e_fixed_point_stalkPullback X.left (a g⁻¹).left p (hfix g⁻¹)
      commutes' := s2e_fixed_point_stalkPullback_scalars X (a g⁻¹) p (hfix g⁻¹) }
  have hP (g : G) (c : Γ(X.left, W)) : g • c ∈ P ↔ c ∈ P := by
    have he := (s2e_affine_point_fixed_iff_prime_comap X.left (a g⁻¹).left W hW
      (s2e_step1_action_preimage X Y q (a g⁻¹) (hinv g⁻¹) U) p hp).mp (hfix g⁻¹)
    change c ∈ P.comap ((a g⁻¹).left.appLE W W _).hom ↔ c ∈ P
    rw [he]
  have hβ (g : G) (c : Γ(X.left, W)) :
      β g (algebraMap Γ(X.left, W) R c) = algebraMap Γ(X.left, W) R (g • c) :=
    congrArg (fun k : Γ(X.left, W) ⟶ X.left.presheaf.stalk p => k.hom c)
      (s2e_fixed_point_germ_pullback X.left (a g⁻¹).left p (hfix g⁻¹) W
        (s2e_step1_action_preimage X Y q (a g⁻¹) (hinv g⁻¹) U) hp)
  exact s2e_fixed_prime_local_invariant_equiv ℂ Γ(X.left, W) R G P hP β hβ

#print axioms s2e_complex_affine_fixed_prime_local_invariants
end HodgeLean.Foundations.Program
