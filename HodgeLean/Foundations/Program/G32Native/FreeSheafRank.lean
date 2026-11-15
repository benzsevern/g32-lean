import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.LinearAlgebra.Dimension.Free

/-! Finite free sheaf ranks detected at a scheme point. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Isomorphic finite free sheaves on a nonzero affine scheme have equal ranks. -/
theorem g32l4_affine_free_rank_unique (R : CommRingCat) [Nontrivial R]
    {m n : ℕ}
    (e : (SheafOfModules.free (R := (Spec R).ringCatSheaf) (Fin m) :
      (Spec R).Modules) ≅ SheafOfModules.free (Fin n)) : m = n := by
  let e' := (tildeFinsupp (R := R) (Fin m)) ≪≫ e ≪≫
    (tildeFinsupp (R := R) (Fin n)).symm
  let e'' := (tilde.fullyFaithfulFunctor (R := R)).preimageIso e'
  have h := e''.toLinearEquiv.finrank_eq
  simpa only [Module.finrank_finsupp, Fintype.card_fin, Module.finrank_self, mul_one] using h

/-- A point detects equality of the ranks of two finite free sheaves. -/
theorem g32l4_free_rank_unique_at {X : Scheme} (x : X) {m n : ℕ}
    (e : (SheafOfModules.free (R := X.ringCatSheaf) (Fin m) : X.Modules) ≅
      SheafOfModules.free (Fin n)) : m = n := by
  let f := X.fromSpecResidueField x
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let e' := (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Fin m)).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫
    SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Fin n)
  exact g32l4_affine_free_rank_unique (X.residueField x) e'

end HodgeLean.Foundations.Program
