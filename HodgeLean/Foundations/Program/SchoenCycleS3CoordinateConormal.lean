import HodgeLean.Foundations.Program.SchoenCycleS3AffineIdealCotangent
import HodgeLean.Foundations.Program.SchoenCycleS3AffineConormalFree

/-! # Actual affine coordinate conormal sheaves -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The actual conormal of a quotient by distinct polynomial coordinates is free. -/
def s2e_affineCoordinateConormalIso {R σ τ : Type} [CommRing R] [Fintype τ]
    (e : τ ↪ σ) :
    let I := Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ R)))
    s2c_conormal (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      (SheafOfModules.free (R := (Spec (CommRingCat.of (MvPolynomial σ R ⧸ I))).ringCatSheaf)
        (Fin (Fintype.card τ)) : (Spec (CommRingCat.of (MvPolynomial σ R ⧸ I))).Modules) :=
  s2e_affineQuotientConormalIso (R := CommRingCat.of (MvPolynomial σ R))
      (Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ R)))) ≪≫ s2e_coordinateCotangentSheafFiniteIso e

end HodgeLean.Foundations.Program
