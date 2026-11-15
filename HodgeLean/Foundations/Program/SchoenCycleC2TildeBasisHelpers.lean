import Mathlib.AlgebraicGeometry.Modules.Tilde

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual module basis gives an isomorphism from its associated sheaf
to the free scheme-module sheaf on the same index set. -/
def s2e_tilde_basis_iso
    (R : CommRingCat.{0}) (M : ModuleCat R) (ι : Type)
    (b : Module.Basis ι R M) :
    tilde M ≅ (SheafOfModules.free (R := (Spec R).ringCatSheaf) ι : (Spec R).Modules) :=
  (tilde.functor R).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp ι

end HodgeLean.Foundations.Program
