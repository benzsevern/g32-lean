import HodgeLean.Foundations.Program.G32Native.PELPeriodGeneratedSubgroup
import HodgeLean.Foundations.HodgeGroupAlgebraicDescent

noncomputable section
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Complex Zariski closure stays inside any rational algebraic subgroup
containing the original set. -/
theorem pelComplexClosure_subset_ratGroup {n : ℕ}
    (S G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (hG : g2_IsRatAlgSubgroup G) (hSG : S ⊆ G) :
    @closure _ (g1_zariski ℂ n) S ⊆ G := by
  letI : TopologicalSpace (Matrix.GeneralLinearGroup (Fin n) ℂ) := g1_zariski ℂ n
  obtain ⟨E, hE⟩ := hG.1
  have hGal : g2h_GaloisStable G := by
    rw [hE]
    exact g2h_galoisStable_ratZeroSet E
  have hbound : g2_ratClosure G ⊆ G := by
    intro x hx
    rw [hE]
    intro f hf
    exact hx f (fun y hy => (hE ▸ hy) f hf)
  have hclosure : @closure _ (g1_zariski ℂ n) G ⊆ G := by
    rw [← g2h_ratClosure_eq_closure hGal]
    exact hbound
  exact (closure_mono hSG).trans hclosure

/-- The complex hull of the period-generated subgroup satisfies every
rational algebraic subgroup constraint satisfied by its generators. -/
theorem pelPeriodComplexClosure_subset (R : PELSplitReference)
    (G : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (hG : g2_IsRatAlgSubgroup G)
    (hperiod : ∀ z : PELSplitComponent R, pelPeriodMatrix R z.val ∈ G) :
    @closure _ (g1_zariski ℂ 12) (pelPeriodGeneratedSubgroup R : Set _) ⊆ G :=
  pelComplexClosure_subset_ratGroup _ _ hG
    (pelPeriodGeneratedSubgroup_subset R G hG hperiod)

#print axioms pelComplexClosure_subset_ratGroup
#print axioms pelPeriodComplexClosure_subset
end HodgeLean.Foundations.Program.GeneralTypeIII
