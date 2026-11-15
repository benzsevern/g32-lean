import HodgeLean.Foundations.Program.SchoenCycleQuotientAdicStabilizerValues
import HodgeLean.Foundations.Program.SchoenCycleQuotientAdicStabilizer
import HodgeLean.Foundations.Program.SchoenCycleComplexSectionTower
import HodgeLean.Foundations.Program.SchoenCycleInvariantScalarRestriction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual complex quotient formal comparison retains canonical pullback values on all formal sections.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_complex_quotient_adic_stabilizer_values
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (p : Ideal Γ(Y.left, U)) [p.IsMaximal]
    (I : Ideal Γ(X.left, q.left ⁻¹ᵁ U)) [I.IsPrime] :
    letI := s2e_step1_sectionAlgebra Y U
    letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
    letI : Algebra Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := (q.left.app U).hom.toAlgebra
    letI : IsScalarTower ℂ Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := s2e_complex_section_app_tower X Y q U
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_quotient_sectionAction_base_smulComm X Y G a ha1 hamul q hinv U
    let α := MulSemiringAction.toAlgAut G Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U)
    let o : MulAction.orbit G I := ⟨I, MulAction.mem_orbit_self I⟩
    let β (g : MulAction.stabilizer G o) := s2e_adic_algebra_map I I ((α g.val).toAlgHom.restrictScalars ℂ)
      (s2e_orbit_ideal_stabilizer_preserves_powers G Γ(X.left, q.left ⁻¹ᵁ U) I g)
    ∀ hI : I.LiesOver p,
    letI := hI
    ∃ F : AdicCompletion p Γ(Y.left, U) ≃ₐ[ℂ]
      (⨅ g : MulAction.stabilizer G o, AlgHom.equalizer (β g)
        (AlgHom.id ℂ (AdicCompletion I Γ(X.left, q.left ⁻¹ᵁ U))) :
        Subalgebra ℂ (AdicCompletion I Γ(X.left, q.left ⁻¹ᵁ U))),
      ∀ x, (F x).val = s2e_adic_algebra_map p I
        ((Algebra.ofId Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U)).restrictScalars ℂ)
        (fun n a ha => (Ideal.pow_right_mono
          (Ideal.map_le_iff_le_comap.mpr (Ideal.over_def I p).le) n)
          (s2e_base_map_preserves_extended_ideal_powers p n a ha)) x := by
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X W
  letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (q.left.app U).hom.toAlgebra
  letI : IsScalarTower ℂ Γ(Y.left, U) Γ(X.left, W) := s2e_complex_section_app_tower X Y q U
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_quotient_sectionAction_base_smulComm X Y G a ha1 hamul q hinv U
  dsimp only
  intro hI
  obtain ⟨E, hE⟩ := s2e_quotient_adic_stabilizer_values X Y G a ha1 hamul q hinv hquot U hU p I hI
  refine ⟨(E.restrictScalars ℂ).trans (s2e_invariant_restrict_scalars_equiv (k := ℂ) _), ?_⟩
  intro x
  exact hE x

#print axioms s2e_complex_quotient_adic_stabilizer_values
end HodgeLean.Foundations.Program
