import HodgeLean.Foundations.Program.CompensationAssemblyTraceCup

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

theorem cq_circleTrace_cup_pullback (X : TopCat.{0}) (i j : ℕ)
    (a : Cohomology ℚ X i)
    (b : Cohomology ℚ (TopCat.of (X × UnitAddCircle)) (j + 1)) :
    cq_circleTrace X (i + j)
      (cup (TopCat.of (X × UnitAddCircle)) (Nat.add_assoc i j 1).symm
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) b) =
      cup X rfl a (cq_circleTrace X j b) := by
  obtain ⟨⟨u, v⟩, rfl⟩ := (prodCircleCohomologyEquiv X j).surjective b
  have ht : cq_circleTrace X j (prodCircleCohomologyEquiv X j (u, v)) = v := by
    change ((prodCircleCohomologyEquiv X j).symm
      (prodCircleCohomologyEquiv X j (u, v))).2 = v
    rw [LinearEquiv.symm_apply_apply]
  rw [ht, prodCircleCohomologyEquiv_apply, map_add, map_add]
  have hp := cohomologyMap_cup X
    (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ X) (Nat.add_assoc i j 1).symm a u
  rw [← hp, cq_circleTrace_pullback, zero_add]
  rw [← cup_assoc (Y := TopCat.of (X × UnitAddCircle))
    rfl rfl rfl (Nat.add_assoc i j 1).symm]
  rw [← cohomologyMap_cup, cq_circleTrace_cup_circleClass]

theorem cq_circleTrace_cup_pullback_of_eq (X : TopCat.{0}) (i j m : ℕ)
    (h : i + j = m) (a : Cohomology ℚ X i)
    (b : Cohomology ℚ (TopCat.of (X × UnitAddCircle)) (j + 1)) :
    cq_circleTrace X m
      (cup (TopCat.of (X × UnitAddCircle))
        ((Nat.add_assoc i j 1).symm.trans (congrArg (· + 1) h))
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) b) =
      cup X h a (cq_circleTrace X j b) := by
  subst m
  exact cq_circleTrace_cup_pullback X i j a b

end HodgeLean.Foundations.Program
