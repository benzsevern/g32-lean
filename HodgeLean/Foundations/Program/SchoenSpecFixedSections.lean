import HodgeLean.Foundations.Program.SchoenSpecAction
import HodgeLean.Foundations.Program.SchoenFixedSubringEquiv
import HodgeLean.Foundations.Program.SchoenAffineSchemeQuotient

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- The canonical spectrum-section isomorphism intertwines the actual section and ring actions. -/
theorem s2_specAction_ΓSpecIso (A G : Type) [CommRing A] [Group G] [MulSemiringAction G A]
    (g : G) (s : Γ(Spec (CommRingCat.of A), ⊤)) :
    letI := s2_schemeSectionAction (Spec (CommRingCat.of A)) G (s2_specAction A G)
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom (g • s) =
      g • (Scheme.ΓSpecIso (CommRingCat.of A)).hom s := by
  letI := s2_schemeSectionAction (Spec (CommRingCat.of A)) G (s2_specAction A G)
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    ((Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A (g⁻¹)⁻¹))).appTop s) = _
  rw [inv_inv]
  exact congrArg (fun k : Γ(Spec (CommRingCat.of A), ⊤) ⟶ CommRingCat.of A => k s)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)))

/-- The concrete fixed-ring spectrum identifies with the quotient built from spectrum sections. -/
def s2_specFixedSectionsIso (A G : Type) [CommRing A] [Group G] [MulSemiringAction G A] :
    letI := s2_schemeSectionAction (Spec (CommRingCat.of A)) G (s2_specAction A G)
    Spec (CommRingCat.of (FixedPoints.subring A G)) ≅
      Spec (CommRingCat.of (FixedPoints.subring Γ(Spec (CommRingCat.of A), ⊤) G)) := by
  letI := s2_schemeSectionAction (Spec (CommRingCat.of A)) G (s2_specAction A G)
  exact Scheme.Spec.mapIso (s2_fixedSubringEquiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
    (s2_specAction_ΓSpecIso A G)).toCommRingCatIso.op

/-- The fixed-section spectrum comparison preserves the actual quotient projection. -/
theorem s2_specFixedSectionsIso_quotient (A G : Type) [CommRing A] [Group G]
    [MulSemiringAction G A] :
    letI := s2_schemeSectionAction (Spec (CommRingCat.of A)) G (s2_specAction A G)
    Spec.map (CommRingCat.ofHom (FixedPoints.subring A G).subtype) ≫
      (s2_specFixedSectionsIso A G).hom =
      s2_affineSchemeQuotientMap (Spec (CommRingCat.of A)) G (s2_specAction A G) := by
  letI := s2_schemeSectionAction (Spec (CommRingCat.of A)) G (s2_specAction A G)
  change Spec.map _ ≫ Spec.map _ = (Spec (CommRingCat.of A)).isoSpec.hom ≫ Spec.map _
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  rfl

end HodgeLean.Foundations.Program
