import HodgeLean.Foundations.Program.SchoenQuotientOver
import HodgeLean.Foundations.Program.SchoenGlobalTargetDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Invariant morphisms to arbitrary schemes over the base descend as morphisms over that base. -/
theorem s2_gluedQuotientOverDesc_arbitrary {S : Scheme.{0}} [IsAffine S]
    (X : Over S) [IsIntegral X.left]
    [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X.left)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ X.hom = X.hom)
    (hcover : ∀ x : X.left, ∃ U : s2_InvariantAffineOpen X.left G ρ, x ∈ U.val)
    (T : Over S) (f : X ⟶ T)
    (hf : ∀ g : G, (ρ g).asIso.hom ≫ f.left = f.left) :
    ∃! d : s2_gluedQuotientOver X G ρ hover hcover ⟶ T,
      s2_gluedQuotientOverMap X G ρ hover hcover ≫ d = f := by
  obtain ⟨d, hd, _⟩ := s2_gluedQuotientDesc_arbitrary X.left G ρ hcover T.left f.left hf
  haveI := s2_gluedQuotientMap_epi X.left G ρ hcover
  have hw : d ≫ T.hom = s2_gluedQuotientStructure X.hom G ρ hover hcover := by
    apply (cancel_epi (s2_gluedQuotientMap X.left G ρ hcover)).mp
    rw [← Category.assoc, hd, Over.w, s2_gluedQuotientStructure_fac]
  let e : s2_gluedQuotientOver X G ρ hover hcover ⟶ T := Over.homMk d hw
  have he : s2_gluedQuotientOverMap X G ρ hover hcover ≫ e = f := by
    apply Over.OverMorphism.ext
    exact hd
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Over.OverMorphism.ext
  apply (cancel_epi (s2_gluedQuotientMap X.left G ρ hcover)).mp
  exact congrArg (fun k : X ⟶ T => k.left) (he'.trans he.symm)

end HodgeLean.Foundations.Program
