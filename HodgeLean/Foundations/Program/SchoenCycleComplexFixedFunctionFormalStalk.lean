import HodgeLean.Foundations.Program.SchoenCycleComplexFixedFunctionAdic
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineStalkInvariantValues
import HodgeLean.Foundations.Program.SchoenCycleComplexFixedPrimeLocal
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual fixed-function formal algebra identifies with geometric formal stalk invariants, retaining the canonical inclusion and affine germ values.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_complex_fixed_function_formal_stalk_invariants
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
    ∃ (hQ : ∀ n s, s ∈ Q ^ n → S.val s ∈ P ^ n)
      (E : AdicCompletion Q S ≃ₐ[ℂ]
        (⨅ g, AlgHom.equalizer (βhat g) (AlgHom.id ℂ
          (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
          Subalgebra ℂ (AdicCompletion (IsLocalRing.maximalIdeal R) R))),
      ∀ z, (E z).val = s2e_complex_affine_point_adic_equiv X W hW p hp hclosed
        (s2e_adic_algebra_map Q P S.val hQ z) := by
  dsimp only
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  let R := X.left.presheaf.stalk p
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  let P := (hW.primeIdealOf ⟨p, hp⟩).asIdeal
  let S := FixedPoints.subalgebra ℂ Γ(X.left, W) G
  letI : P.IsMaximal := hW.primeIdealOf_isMaximal_of_isClosed ⟨p, hp⟩ hclosed
  letI : IsNoetherianRing Γ(X.left, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hmem (g : G) (c : Γ(X.left, W)) : g • c ∈ P ↔ c ∈ P := by
    have he := (s2e_affine_point_fixed_iff_prime_comap X.left (a g⁻¹).left W hW
      (s2e_step1_action_preimage X Y q (a g⁻¹) (hinv g⁻¹) U) p hp).mp (hfix g⁻¹)
    change c ∈ P.comap ((a g⁻¹).left.appLE W W _).hom ↔ c ∈ P
    rw [he]
  have hP (g : G) : g • P = P := by
    ext c
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact hmem g⁻¹ c
  obtain ⟨hα, hQ, E, hE⟩ := s2e_complex_fixed_function_adic_invariants Γ(X.left, W) G P hP
  obtain ⟨hα', F, hF⟩ := s2e_complex_affine_stalk_invariant_values X G
    (fun g => a g⁻¹) p (fun g => hfix g⁻¹) W hW
    (fun g => s2e_step1_action_preimage X Y q (a g⁻¹) (hinv g⁻¹) U) hp hclosed
  refine ⟨hQ, E.trans F, ?_⟩
  intro z
  exact (hF (E z)).trans
    (congrArg (s2e_complex_affine_point_adic_equiv X W hW p hp hclosed) (hE z))

#print axioms s2e_complex_fixed_function_formal_stalk_invariants
end HodgeLean.Foundations.Program
