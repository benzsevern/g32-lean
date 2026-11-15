import HodgeLean.Foundations.Program.G32Native.PairedConormalModuleFibres
import HodgeLean.Foundations.Program.G32Native.PairedConormalFibreRankObstruction

/-! # Nonzero relations from actual finite frames -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Different ranks of the framed middle and quotient modules prevent the relation
from vanishing after pullback to any complex point. -/
theorem conormal_relation_pullback_ne_zero_of_fixedFrames
    {Q : Over (Spec ↧ℂ)} {I A M : Q.left.Modules} (a : I ⟶ A)
    (e : cokernel a ≅ M) (m n : ℕ) (hnm : n ≠ m)
    (hA : ∀ y : Q.left, ∃ U : Q.left.Opens, y ∈ U ∧
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin m) ≅
        (Scheme.Modules.pullback U.ι).obj A))
    (hM : ∀ y : Q.left, ∃ U : Q.left.Opens, y ∈ U ∧
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin n) ≅
        (Scheme.Modules.pullback U.ι).obj M)) (x : ComplexPoint Q) :
    (Scheme.Modules.pullback x.left).map a ≠ 0 := by
  apply conormal_relation_pullback_ne_zero_of_fibre_rank
  have hA' := (paired_module_fibre_rank_of_fixedFrames A m hA x).2
  have hM' := (paired_module_fibre_rank_of_fixedFrames M n hM x).2
  have he := ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    ((Scheme.Modules.pullback x.left).mapIso e)).toLinearEquiv.finrank_eq
  rw [he, hM', hA']
  exact hnm

end HodgeLean.Foundations.Program.G32Native
