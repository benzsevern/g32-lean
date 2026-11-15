import HodgeLean.Foundations.Program.SchoenTowerOverSections
import HodgeLean.Foundations.Program.SchoenAffineTargetDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- The actual affine invariant spectrum with its induced complex structure morphism. -/
def s2t_affineQuotientOver (X : Over (Spec ↧ℂ))
    (G : Type) [Group G] (ρ : G →* Aut X) : Over (Spec ↧ℂ) := by
  let a := ((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ
  letI := s2_schemeSectionAction X.left G a
  letI := s2t_overSectionAction_smulCommClass X G ρ
  exact Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (FixedPoints.subalgebra ℂ Γ(X.left, ⊤) G))))

/-- The actual affine invariant-spectrum projection is a morphism over the complex base. -/
def s2t_affineQuotientOverMap (X : Over (Spec ↧ℂ)) [IsAffine X.left]
    (G : Type) [Group G] (ρ : G →* Aut X) : X ⟶ s2t_affineQuotientOver X G ρ := by
  let a := ((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ
  letI := s2_schemeSectionAction X.left G a
  letI := s2t_overSectionAction_smulCommClass X G ρ
  refine Over.homMk (s2_affineSchemeQuotientMap X.left G a) ?_
  change (X.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
    (algebraMap (FixedPoints.subalgebra ℂ Γ(X.left, ⊤) G) Γ(X.left, ⊤)))) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (FixedPoints.subalgebra ℂ Γ(X.left, ⊤) G))) = X.hom
  rw [Category.assoc, ← Spec.map_comp]
  exact s2t_toSpecΓ_over X

/-- The actual affine projection over the coefficient scheme is invariant. -/
theorem s2t_affineQuotientOverMap_invariant (X : Over (Spec ↧ℂ)) [IsAffine X.left]
    (G : Type) [Group G] (ρ : G →* Aut X) (g : G) :
    (ρ g).asIso.hom ≫ s2t_affineQuotientOverMap X G ρ =
      s2t_affineQuotientOverMap X G ρ := by
  apply Over.OverMorphism.ext
  exact s2_affineSchemeQuotientMap_invariant X.left G
    (((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ) g

end HodgeLean.Foundations.Program
