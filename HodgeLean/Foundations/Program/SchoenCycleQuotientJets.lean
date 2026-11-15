import HodgeLean.Foundations.Program.SchoenCycleInvariantJets
import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeLean.Foundations.Program.SchoenCycleStep1SectionAction

/-! # Infinitesimal section descent on actual finite quotient charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A section congruent modulo an ideal to all its translates on a quotient
inverse-image chart is congruent to the pullback of an actual section downstairs.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1,
finite group averaging and invariant affine section descent. -/
theorem s2e_quotient_affine_jet_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (I : Ideal Γ(X.left, q.left ⁻¹ᵁ U)) (b : Γ(X.left, q.left ⁻¹ᵁ U))
    (hb : letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
      ∀ g : G, g • b - b ∈ I) :
    ∃ c : Γ(Y.left, U), (q.left.app U).hom c - b ∈ I := by
  classical
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨b', hb', hcongr⟩ := s2e_invariant_jet_representative G Γ(X.left, W)
    (MulSemiringAction.toAlgAut G ℂ Γ(X.left, W)) I b hb
  have hi (u : G) : ((a u).left.appLE W W
      (s2e_step1_action_preimage X Y q (a u) (hinv u) U)).hom b' = b' := by
    have h := hb' u⁻¹
    change u⁻¹ • b' = b' at h
    change ((a ((u⁻¹)⁻¹)).left.appLE W W
      (s2e_step1_action_preimage X Y q (a ((u⁻¹)⁻¹)) (hinv ((u⁻¹)⁻¹)) U)).hom b' = b' at h
    simpa only [inv_inv] using h
  obtain ⟨c, hc, _⟩ := s2e_step1_invariant_affine_descent X Y G a ha1 hamul
    q hinv hquot U hU b' hi
  exact ⟨c, hc ▸ hcongr⟩

end HodgeLean.Foundations.Program
