import HodgeLean.Foundations.Program.SchoenCycleComplexAffineAdic
import HodgeLean.Foundations.Program.SchoenCycleComplexSectionPullback
import HodgeLean.Foundations.Program.SchoenCycleFixedStalkScalars

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The canonical complex formal germ equivalence intertwines actual section pullback and geometric fixed-point stalk pullback.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_complex_affine_formal_fixed_action
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (f : X ⟶ X) (p : X.left) (hfix : f.left p = p)
    (U : X.left.Opens) (hU : IsAffineOpen U) (hUP : U ≤ f.left ⁻¹ᵁ U)
    (hp : p ∈ U) (hclosed : IsClosed ({p} : Set X.left)) :
    letI := s2e_step1_sectionAlgebra X U
    let R := X.left.presheaf.stalk p
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    let I := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
    let E := s2e_complex_affine_point_adic_equiv X U hU p hp hclosed
    let α := s2e_complex_section_pullback X X f U U hUP
    let β : R →ₐ[ℂ] R :=
      { toRingHom := s2e_fixed_point_stalkPullback X.left f.left p hfix
        commutes' := s2e_fixed_point_stalkPullback_scalars X f p hfix }
    ∃ hα : ∀ n a, a ∈ I ^ n → α a ∈ I ^ n,
      (s2e_adic_algebra_map _ _ β (s2e_fixed_point_stalkPullback_power X.left f.left p hfix)).comp
        E.toAlgHom = E.toAlgHom.comp (s2e_adic_algebra_map I I α hα) := by
  dsimp only
  letI := s2e_step1_sectionAlgebra X U
  let R := X.left.presheaf.stalk p
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  let I := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
  let α := s2e_complex_section_pullback X X f U U hUP
  let γ := s2e_complex_section_germ X U p hp
  let β : R →ₐ[ℂ] R :=
    { toRingHom := s2e_fixed_point_stalkPullback X.left f.left p hfix
      commutes' := s2e_fixed_point_stalkPullback_scalars X f p hfix }
  have hγ (a : Γ(X.left, U)) : β (γ a) = γ (α a) :=
    congrArg (fun k : Γ(X.left, U) ⟶ X.left.presheaf.stalk p => k.hom a)
      (s2e_fixed_point_germ_pullback X.left f.left p hfix U hUP hp)
  have hmem (n : ℕ) (a : Γ(X.left, U)) : γ a ∈ IsLocalRing.maximalIdeal R ^ n ↔ a ∈ I ^ n :=
    s2e_affine_stalk_power_jet_mem_iff X.left U hU p hp hclosed n a
  have hα (n : ℕ) (a : Γ(X.left, U)) (ha : a ∈ I ^ n) : α a ∈ I ^ n := by
    apply (hmem n (α a)).mp
    rw [← hγ]
    exact s2e_fixed_point_stalkPullback_power X.left f.left p hfix n (γ a) ((hmem n a).mpr ha)
  refine ⟨hα, ?_⟩
  apply AlgHom.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change Ideal.quotientMapₐ (IsLocalRing.maximalIdeal R ^ n • ⊤ : Ideal R) β _
      (Ideal.quotientMapₐ (IsLocalRing.maximalIdeal R ^ n • ⊤ : Ideal R) γ _ (x.val n)) =
    Ideal.quotientMapₐ (IsLocalRing.maximalIdeal R ^ n • ⊤ : Ideal R) γ _
      (Ideal.quotientMapₐ (I ^ n • ⊤ : Ideal Γ(X.left, U)) α _ (x.val n))
  refine Quotient.inductionOn' (x.val n) (fun a => ?_)
  change Ideal.Quotient.mk _ (β (γ a)) = Ideal.Quotient.mk _ (γ (α a))
  rw [hγ]

#print axioms s2e_complex_affine_formal_fixed_action
end HodgeLean.Foundations.Program
