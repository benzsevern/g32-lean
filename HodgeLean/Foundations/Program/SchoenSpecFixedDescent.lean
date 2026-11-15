import HodgeLean.Foundations.Program.SchoenSpecFixedSections
import HodgeLean.Foundations.Program.SchoenAffineTargetDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Invariant morphisms from an actual ring spectrum descend uniquely through its fixed-ring spectrum. -/
theorem s2_specFixedQuotientDesc (A G : Type) [CommRing A] [IsDomain A]
    [Group G] [Finite G] [MulSemiringAction G A] {T : Scheme.{0}}
    (f : Spec (CommRingCat.of A) ⟶ T)
    (hf : ∀ g : G, Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)) ≫ f = f) :
    ∃! d : Spec (CommRingCat.of (FixedPoints.subring A G)) ⟶ T,
      Spec.map (CommRingCat.ofHom (FixedPoints.subring A G).subtype) ≫ d = f := by
  letI := s2_schemeSectionAction (Spec (CommRingCat.of A)) G (s2_specAction A G)
  obtain ⟨d, hd, _⟩ := s2_affineSchemeQuotientDesc_arbitrary
    (Spec (CommRingCat.of A)) G (s2_specAction A G) f (fun g => hf g⁻¹)
  let e := (s2_specFixedSectionsIso A G).hom ≫ d
  have he : Spec.map (CommRingCat.ofHom (FixedPoints.subring A G).subtype) ≫ e = f := by
    dsimp only [e]
    rw [← Category.assoc, s2_specFixedSectionsIso_quotient, hd]
  haveI : Epi (Spec.map (CommRingCat.ofHom (FixedPoints.subring A G).subtype)) :=
    s2_affineQuotient_epi ℤ A G
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (cancel_epi (Spec.map (CommRingCat.ofHom (FixedPoints.subring A G).subtype))).mp
    (he'.trans he.symm)

end HodgeLean.Foundations.Program
