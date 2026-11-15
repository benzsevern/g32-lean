import HodgeLean.Foundations.Program.SchoenCycleS3CotangentBasis
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Free sheaves associated to affine coordinate conormal modules -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The sheaf associated to a coordinate conormal module is free on its coordinate classes. -/
def s2e_coordinateCotangentSheafIso {R σ τ : Type} [CommRing R]
    (e : τ ↪ σ) :
    let I := Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ R)))
    let Q := CommRingCat.of (MvPolynomial σ R ⧸ I)
    tilde (ModuleCat.of Q I.Cotangent) ≅
      (SheafOfModules.free (R := (Spec Q).ringCatSheaf) τ : (Spec Q).Modules) :=
  (tilde.functor _).mapIso (s2e_coordinateCotangentBasis (R := R) e).repr.toModuleIso ≪≫
    tildeFinsupp τ

/-- For finitely many distinct coordinates the associated conormal sheaf has that finite rank. -/
def s2e_coordinateCotangentSheafFiniteIso {R σ τ : Type} [CommRing R] [Fintype τ]
    (e : τ ↪ σ) :
    let I := Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ R)))
    let Q := CommRingCat.of (MvPolynomial σ R ⧸ I)
    tilde (ModuleCat.of Q I.Cotangent) ≅
      (SheafOfModules.free (R := (Spec Q).ringCatSheaf) (Fin (Fintype.card τ)) :
        (Spec Q).Modules) :=
  (tilde.functor _).mapIso
      ((s2e_coordinateCotangentBasis (R := R) e).reindex (Fintype.equivFin τ)).repr.toModuleIso ≪≫
    tildeFinsupp _

end HodgeLean.Foundations.Program
