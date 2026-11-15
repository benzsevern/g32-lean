import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Recovering module frames from affine sheaf frames -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A frame of an associated sheaf gives a frame of its original module. -/
def unionAffineFrameEquiv
    (R : CommRingCat) (M : ModuleCat R) (p : ℕ)
    (e : tilde M ≅ (SheafOfModules.free (R := (Spec R).ringCatSheaf) (Fin p) :
      (Spec R).Modules)) : M ≃ₗ[R] (Fin p →₀ R) :=
  ((tilde.functor R).preimageIso (e ≪≫ (tildeFinsupp (R := R) (Fin p)).symm)).toLinearEquiv

/-- The original module is free whenever its associated sheaf has a finite frame. -/
lemma unionAffineFrame_free
    (R : CommRingCat) (M : ModuleCat R) (p : ℕ)
    (e : tilde M ≅ (SheafOfModules.free (R := (Spec R).ringCatSheaf) (Fin p) :
      (Spec R).Modules)) : Module.Free R M :=
  Module.Free.of_equiv (unionAffineFrameEquiv R M p e).symm

/-- A finite frame of an associated sheaf gives finite generation of its module. -/
lemma unionAffineFrame_finite
    (R : CommRingCat) (M : ModuleCat R) (p : ℕ)
    (e : tilde M ≅ (SheafOfModules.free (R := (Spec R).ringCatSheaf) (Fin p) :
      (Spec R).Modules)) : Module.Finite R M :=
  Module.Finite.equiv (unionAffineFrameEquiv R M p e).symm

/-- The rank of the module is the size of the affine sheaf frame. -/
lemma unionAffineFrame_finrank
    (R : CommRingCat) [Nontrivial R] (M : ModuleCat R) (p : ℕ)
    (e : tilde M ≅ (SheafOfModules.free (R := (Spec R).ringCatSheaf) (Fin p) :
      (Spec R).Modules)) : Module.finrank R M = p := by
  rw [(unionAffineFrameEquiv R M p e).finrank_eq]
  simp only [Module.finrank_finsupp, Module.finrank_self, Fintype.card_fin, mul_one]

#print axioms unionAffineFrameEquiv
#print axioms unionAffineFrame_free
#print axioms unionAffineFrame_finite
#print axioms unionAffineFrame_finrank
end HodgeLean.Foundations.Program.G32Native
