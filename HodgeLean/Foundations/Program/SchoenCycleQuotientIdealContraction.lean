import HodgeLean.Foundations.Program.SchoenCycleInvariantIdealContraction
import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeLean.Foundations.Program.SchoenCycleStep1SectionAction

/-! # Ideal contraction on actual finite quotient charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every ideal on an affine chart of the retained finite categorical quotient
is recovered by contracting its extension to the inverse-image chart.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1,
§1, invariant sections and the averaging projection. -/
theorem s2e_quotient_affine_ideal_contraction
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U) (J : Ideal Γ(Y.left, U)) :
    (J.map (q.left.app U).hom).comap (q.left.app U).hom = J := by
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  letI : Fintype G := Fintype.ofFinite G
  letI := IsSchemeTheoreticallyDominant.of_isDominant q.left
  apply s2e_invariant_ring_ideal_contraction Γ(Y.left, U) Γ(X.left, W) G
    (MulSemiringAction.toAlgAut G ℂ Γ(X.left, W)) (q.left.app U).hom
    (q.left.app_injective U) _ _ J
  · intro g r
    let ρ := (a g⁻¹).left.appLE W W
      (s2e_step1_action_preimage X Y q (a g⁻¹) (hinv g⁻¹) U)
    have he : q.left.app U ≫ ρ = q.left.app U := by
      dsimp only [ρ]
      rw [q.left.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      have hg : (a g⁻¹).left ≫ q.left = q.left := congrArg Over.Hom.left (hinv g⁻¹)
      simp only [hg, W]
    exact congrArg (fun t : Γ(Y.left, U) ⟶ Γ(X.left, W) => t.hom r) he
  · intro b hb
    have hi (u : G) : ((a u).left.appLE W W
        (s2e_step1_action_preimage X Y q (a u) (hinv u) U)).hom b = b := by
      have h := hb u⁻¹
      change u⁻¹ • b = b at h
      change ((a ((u⁻¹)⁻¹)).left.appLE W W
        (s2e_step1_action_preimage X Y q (a ((u⁻¹)⁻¹)) (hinv ((u⁻¹)⁻¹)) U)).hom b = b at h
      simpa only [inv_inv] using h
    obtain ⟨r, hr, _⟩ := s2e_step1_invariant_affine_descent X Y G a ha1 hamul
      q hinv hquot U hU b hi
    exact ⟨r, hr⟩

#print axioms s2e_quotient_affine_ideal_contraction
end HodgeLean.Foundations.Program
