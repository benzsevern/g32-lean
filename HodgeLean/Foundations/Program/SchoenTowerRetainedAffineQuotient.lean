import HodgeLean.Foundations.Program.SchoenTowerAffineQuotientDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations.Program

/-- A retained categorical quotient of an affine integral complex scheme agrees over
the coefficient scheme with its actual invariant spectrum. -/
theorem s2t_retainedAffineQuotient_iso (X : Over (Spec ↧ℂ))
    [IsAffine X.left] [IsIntegral X.left]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (B : Over (Spec ↧ℂ)) (γ : X ⟶ B)
    (hinv : ∀ g : G, (ρ g).asIso.hom ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ g : G, (ρ g).asIso.hom ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f) :
    ∃ e : s2t_affineQuotientOver X G ρ ≅ B,
      s2t_affineQuotientOverMap X G ρ ≫ e.hom = γ := by
  exact s2_invariantQuotient_iso (fun g => (ρ g).asIso.hom) γ
    (s2t_affineQuotientOverMap X G ρ) hinv hquot
    (s2t_affineQuotientOverMap_invariant X G ρ)
    (s2t_affineQuotientOverDesc X G ρ)

end HodgeLean.Foundations.Program
