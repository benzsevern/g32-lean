import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineFlatIdeal

/-! # A typed source presentation for affine ideal pullback -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program AlgebraicGeometry.Conormal

/-- The source ideal after affine pullback is its associated scalar extension. -/
def unionConormalAffineIdealSourceIso
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
      (idealModule (Spec.map p)) ≅
      tilde ((ModuleCat.extendScalars (algebraMap R S)).obj
        (ModuleCat.of R (RingHom.ker p.hom))) :=
  (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapIso
      (affineIdealIso _ _ p) ≪≫
    (s2e_affine_pullback_tilde_iso _ _ (CommRingCat.ofHom (algebraMap R S))).app
      (ModuleCat.of R (RingHom.ker p.hom))

/-- The typed ideal-source presentation has the expected two map factors. -/
lemma unionConormalAffineIdealSourceIso_hom
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) :
    (unionConormalAffineIdealSourceIso (S := S) A p).hom =
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
          (affineIdealIso _ _ p).hom ≫
        (s2e_affine_pullback_tilde_iso _ _ (CommRingCat.ofHom (algebraMap R S))).hom.app
          (ModuleCat.of R (RingHom.ker p.hom)) := rfl

end HodgeLean.Foundations.Program.G32Native
