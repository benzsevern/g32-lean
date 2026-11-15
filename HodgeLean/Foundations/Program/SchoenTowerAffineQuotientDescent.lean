import HodgeLean.Foundations.Program.SchoenTowerAffineQuotientOver
import HodgeLean.Foundations.Program.SchoenInvariantQuotientComparison

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations.Program

/-- Invariant morphisms of complex schemes descend through the actual affine invariant
projection as morphisms over the coefficient scheme. -/
theorem s2t_affineQuotientOverDesc (X : Over (Spec ↧ℂ))
    [IsAffine X.left] [IsIntegral X.left]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (T : Over (Spec ↧ℂ)) (f : X ⟶ T)
    (hf : ∀ g : G, (ρ g).asIso.hom ≫ f = f) :
    ∃! d : s2t_affineQuotientOver X G ρ ⟶ T,
      s2t_affineQuotientOverMap X G ρ ≫ d = f := by
  let a := ((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ
  let q := s2t_affineQuotientOverMap X G ρ
  haveI : Epi q.left := s2_affineSchemeQuotientMap_epi X.left G a
  obtain ⟨d, hd, hu⟩ := s2_affineSchemeQuotientDesc_arbitrary X.left G a f.left
    (fun g => congrArg (fun k : X ⟶ T => k.left) (hf g))
  change q.left ≫ d = f.left at hd
  have hw : d ≫ T.hom = (s2t_affineQuotientOver X G ρ).hom := by
    apply (cancel_epi q.left).mp
    rw [← Category.assoc, hd, Over.w, Over.w]
  let e : s2t_affineQuotientOver X G ρ ⟶ T := Over.homMk d hw
  refine ⟨e, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact hd
  · intro e' he'
    apply Over.OverMorphism.ext
    exact hu e'.left (congrArg (fun k : X ⟶ T => k.left) he')

end HodgeLean.Foundations.Program
