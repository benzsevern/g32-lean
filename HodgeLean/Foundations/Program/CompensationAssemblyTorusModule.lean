import HodgeLean.Foundations.Program.CompensationAssemblyTraceModule
import HodgeLean.Foundations.Program.CompensationAssemblyTorusTrace

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

def cq_circleTowerProjection (X : TopCat.{0}) :
    (k : ℕ) → cq_circleTower X k ⟶ X
  | 0 => 𝟙 X
  | k + 1 => (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) ≫ cq_circleTowerProjection X k

theorem cq_torusTrace_cup_pullback (X : TopCat.{0}) (k i j : ℕ)
    (a : Cohomology ℚ X i) (b : Cohomology ℚ (cq_circleTower X k) (j + k)) :
    cq_torusTrace X k (i + j)
      (cup (cq_circleTower X k) (Nat.add_assoc i j k).symm
        (cohomologyMap ℚ i (cq_circleTowerProjection X k) a) b) =
      cup X rfl a (cq_torusTrace X k j b) := by
  induction k with
  | zero =>
    dsimp only [cq_circleTower, cq_torusTrace, cq_circleTowerProjection] at b ⊢
    rw [cohomologyMap_id]
    rfl
  | succ k ih =>
    change cq_torusTrace X k (i + j)
      (cq_circleTrace (cq_circleTower X k) ((i + j) + k)
        (cup (TopCat.of (cq_circleTower X k × UnitAddCircle)) _
          (cohomologyMap ℚ i
            ((TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) ≫ cq_circleTowerProjection X k) a) b)) =
      cup X rfl a
        (cq_torusTrace X k j (cq_circleTrace (cq_circleTower X k) (j + k) b))
    rw [cohomologyMap_comp, LinearMap.comp_apply]
    have ht := cq_circleTrace_cup_pullback_of_eq (cq_circleTower X k) i (j + k)
      ((i + j) + k) (Nat.add_assoc i j k).symm
      (cohomologyMap ℚ i (cq_circleTowerProjection X k) a) b
    exact (congrArg (cq_torusTrace X k (i + j)) ht).trans (ih _)

theorem cq_circleTowerProjection_homeomorph (X : TopCat.{0}) (k : ℕ)
    (p : cq_circleTower X k) :
    cq_circleTowerProjection X k p = (cq_circleTowerHomeomorph X k p).1 := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih p.1

theorem cq_productTorusTrace_cup_pullback (X : TopCat.{0}) (k i j : ℕ)
    (a : Cohomology ℚ X i)
    (b : Cohomology ℚ (TopCat.of (X × UnitAddTorus (Fin k))) (j + k)) :
    cq_productTorusTrace X k (i + j)
      (cup (TopCat.of (X × UnitAddTorus (Fin k))) (Nat.add_assoc i j k).symm
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) b) =
      cup X rfl a (cq_productTorusTrace X k j b) := by
  let f : cq_circleTower X k ⟶ TopCat.of (X × UnitAddTorus (Fin k)) :=
    TopCat.ofHom ⟨cq_circleTowerHomeomorph X k, (cq_circleTowerHomeomorph X k).continuous⟩
  have hf : f ≫ (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) =
      cq_circleTowerProjection X k := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (cq_circleTowerProjection_homeomorph X k p).symm
  change cq_torusTrace X k (i + j)
    (cohomologyMap ℚ ((i + j) + k) f
      (cup (TopCat.of (X × UnitAddTorus (Fin k))) _
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) b)) =
    cup X rfl a (cq_torusTrace X k j (cohomologyMap ℚ (j + k) f b))
  have hp : cohomologyMap ℚ i f
      (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) =
      cohomologyMap ℚ i (cq_circleTowerProjection X k) a := by
    change (cohomologyMap ℚ i f ∘ₗ
      cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩)) a = _
    rw [← cohomologyMap_comp, hf]
  rw [cohomologyMap_cup, hp]
  exact cq_torusTrace_cup_pullback X k i j a _

end HodgeLean.Foundations.Program
