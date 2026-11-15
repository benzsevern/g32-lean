import HodgeLean.Foundations.Curves.CurvePoints
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual affine scheme stalk and its prime localization identify over the prescribed native complex scalar structures.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_complex_spec_stalk_equiv
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] (x : PrimeSpectrum S) :
    let X := Over.mk (ComplexPoint.affineSpecStructureMap S)
    letI : Algebra ℂ (X.left.presheaf.stalk x) :=
      (HodgeLean.Foundations.Curves.stalkC (X := X) x).toAlgebra
    X.left.presheaf.stalk x ≃ₐ[ℂ] Localization.AtPrime x.asIdeal := by
  let X := Over.mk (ComplexPoint.affineSpecStructureMap S)
  letI : Algebra ℂ (X.left.presheaf.stalk x) :=
    (HodgeLean.Foundations.Curves.stalkC (X := X) x).toAlgebra
  refine { (Spec.stalkIso (CommRingCat.of S) x).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro c
  have he : CommRingCat.ofHom (HodgeLean.Foundations.Curves.stalkC (X := X) x) ≫
      (Spec.stalkIso (CommRingCat.of S) x).hom =
      CommRingCat.ofHom ((algebraMap S (Localization.AtPrime x.asIdeal)).comp (algebraMap ℂ S)) := by
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ S))).appTop ≫
      (Spec (CommRingCat.of S)).presheaf.germ ⊤ x trivial ≫ (Spec.stalkIso (CommRingCat.of S) x).hom = _
    rw [Spec.germ_stalkMapIso_hom]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ S))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom
        (algebraMap S (Localization.AtPrime x.asIdeal)) = _
    rw [Scheme.ΓSpecIso_naturality_assoc]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of (Localization.AtPrime x.asIdeal) => f.hom c) he

#print axioms s2e_complex_spec_stalk_equiv
end HodgeLean.Foundations.Program
