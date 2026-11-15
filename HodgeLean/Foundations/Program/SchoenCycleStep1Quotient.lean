import HodgeLean.Foundations.Program.SchoenCycleStep1Field

/-! # Reduced invariant factors of categorical quotients -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A reduced invariant surjective factor of a categorical quotient is an isomorphism. -/
theorem s2e_step1_quotient_reduced_factor_isIso
    (X B T : Over (Spec ↧ℂ)) (I : Type)
    (a : I → (X ⟶ X))
    (γ : X ⟶ B)
    (hγ : ∀ σ, a σ ≫ γ = γ)
    (hquot : ∀ (U : Over (Spec ↧ℂ)) (f : X ⟶ U),
      (∀ σ, a σ ≫ f = f) → ∃! u : B ⟶ U, γ ≫ u = f)
    (f : X ⟶ T) (t : T ⟶ B)
    [Surjective f.left] [IsReduced T.left] [IsSeparated t.left]
    (hf : ∀ σ, a σ ≫ f = f) (hfac : f ≫ t = γ) :
    IsIso t.left := by
  obtain ⟨s, hs, _⟩ := hquot T f hf
  have hst : s ≫ t = 𝟙 B := by
    apply (hquot B γ hγ).unique
    · rw [← Category.assoc, hs, hfac]
    · exact Category.comp_id γ
  have hst' : s.left ≫ t.left = 𝟙 B.left := congrArg Over.Hom.left hst
  letI : IsClosedImmersion (s.left ≫ t.left) := by rw [hst']; infer_instance
  letI : IsClosedImmersion s.left := IsClosedImmersion.of_comp s.left t.left
  letI : Surjective s.left := ⟨by
    intro y
    obtain ⟨x, hx⟩ := f.left.surjective y
    refine ⟨γ.left x, ?_⟩
    change (γ ≫ s).left x = y
    rw [hs]
    exact hx⟩
  letI : IsIso s.left := isIso_of_isClosedImmersion_of_surjective s.left
  have ht : t.left = inv s.left := by
    apply (cancel_epi s.left).mp
    rw [hst', IsIso.hom_inv_id]
  rw [ht]
  infer_instance

end HodgeLean.Foundations.Program
