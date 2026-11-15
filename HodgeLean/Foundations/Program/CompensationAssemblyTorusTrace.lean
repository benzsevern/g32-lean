import HodgeLean.Foundations.Program.CompensationAssemblyCircleTrace

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

def cq_circleTower (X : TopCat.{0}) : ℕ → TopCat.{0}
  | 0 => X
  | k + 1 => TopCat.of (cq_circleTower X k × UnitAddCircle)

def cq_circleTowerMap {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (k : ℕ) → cq_circleTower X k ⟶ cq_circleTower Y k
  | 0 => f
  | k + 1 => cq_circleProductMap (cq_circleTowerMap f k)

def cq_torusTrace (X : TopCat.{0}) :
    (k n : ℕ) → Cohomology ℚ (cq_circleTower X k) (n + k) →ₗ[ℚ] Cohomology ℚ X n
  | 0, n => LinearMap.id
  | k + 1, n => cq_torusTrace X k n ∘ₗ cq_circleTrace (cq_circleTower X k) (n + k)

theorem cq_torusTrace_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (k n : ℕ)
    (c : Cohomology ℚ (cq_circleTower Y k) (n + k)) :
    cq_torusTrace X k n (cohomologyMap ℚ (n + k) (cq_circleTowerMap f k) c) =
      cohomologyMap ℚ n f (cq_torusTrace Y k n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (congrArg (cq_torusTrace X k n)
      (cq_circleTrace_naturality (cq_circleTowerMap f k) (n + k) c)).trans (ih _)

def cq_circleTowerHomeomorph (X : TopCat.{0}) :
    (k : ℕ) → cq_circleTower X k ≃ₜ X × UnitAddTorus (Fin k)
  | 0 => (Homeomorph.prodUnique X (UnitAddTorus (Fin 0))).symm
  | k + 1 => ((cq_circleTowerHomeomorph X k).prodCongr (Homeomorph.refl UnitAddCircle)).trans
      ((Homeomorph.prodAssoc X (UnitAddTorus (Fin k)) UnitAddCircle).trans
        ((Homeomorph.refl X).prodCongr (unitAddTorusSuccHomeomorph k).symm))

def cq_productTorusTrace (X : TopCat.{0}) (k n : ℕ) :
    Cohomology ℚ (TopCat.of (X × UnitAddTorus (Fin k))) (n + k) →ₗ[ℚ] Cohomology ℚ X n :=
  cq_torusTrace X k n ∘ₗ
    (cohomologyHomeomorphEquiv (cq_circleTowerHomeomorph X k).symm (n + k)).toLinearMap

theorem cq_circleTowerHomeomorph_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (k : ℕ) (p : cq_circleTower X k) :
    cq_circleTowerHomeomorph Y k (cq_circleTowerMap f k p) =
      (f (cq_circleTowerHomeomorph X k p).1, (cq_circleTowerHomeomorph X k p).2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((cq_circleTowerHomeomorph Y k (cq_circleTowerMap f k p.1)).1,
      (unitAddTorusSuccHomeomorph k).symm
        ((cq_circleTowerHomeomorph Y k (cq_circleTowerMap f k p.1)).2, p.2)) =
      (f (cq_circleTowerHomeomorph X k p.1).1,
        (unitAddTorusSuccHomeomorph k).symm ((cq_circleTowerHomeomorph X k p.1).2, p.2))
    rw [ih]

def cq_productTorusMap {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) :
    TopCat.of (X × UnitAddTorus (Fin k)) ⟶ TopCat.of (Y × UnitAddTorus (Fin k)) :=
  TopCat.ofHom ⟨fun p => (f p.1, p.2),
    (f.hom.continuous.comp continuous_fst).prodMk continuous_snd⟩

theorem cq_productTorusTrace_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (k n : ℕ)
    (c : Cohomology ℚ (TopCat.of (Y × UnitAddTorus (Fin k))) (n + k)) :
    cq_productTorusTrace X k n (cohomologyMap ℚ (n + k) (cq_productTorusMap f k) c) =
      cohomologyMap ℚ n f (cq_productTorusTrace Y k n c) := by
  let hX : cq_circleTower X k ⟶ TopCat.of (X × UnitAddTorus (Fin k)) :=
    TopCat.ofHom ⟨cq_circleTowerHomeomorph X k, (cq_circleTowerHomeomorph X k).continuous⟩
  let hY : cq_circleTower Y k ⟶ TopCat.of (Y × UnitAddTorus (Fin k)) :=
    TopCat.ofHom ⟨cq_circleTowerHomeomorph Y k, (cq_circleTowerHomeomorph Y k).continuous⟩
  have hcomm : cq_circleTowerMap f k ≫ hY = hX ≫ cq_productTorusMap f k := by
    apply ConcreteCategory.hom_ext
    intro p
    exact cq_circleTowerHomeomorph_naturality f k p
  have heq : cohomologyMap ℚ (n + k) hX
      (cohomologyMap ℚ (n + k) (cq_productTorusMap f k) c) =
      cohomologyMap ℚ (n + k) (cq_circleTowerMap f k)
        (cohomologyMap ℚ (n + k) hY c) := by
    change (cohomologyMap ℚ (n + k) hX ∘ₗ
      cohomologyMap ℚ (n + k) (cq_productTorusMap f k)) c =
      (cohomologyMap ℚ (n + k) (cq_circleTowerMap f k) ∘ₗ
        cohomologyMap ℚ (n + k) hY) c
    rw [← cohomologyMap_comp, ← cohomologyMap_comp, hcomm]
  exact (congrArg (cq_torusTrace X k n) heq).trans
    (cq_torusTrace_naturality f k n _)

theorem cq_productTorusTrace_restrict_eq_zero {U X : TopCat.{0}} (i : U ⟶ X)
    (k n : ℕ) (c : Cohomology ℚ (TopCat.of (X × UnitAddTorus (Fin k))) (n + k))
    (hc : cohomologyMap ℚ (n + k) (cq_productTorusMap i k) c = 0) :
    cohomologyMap ℚ n i (cq_productTorusTrace X k n c) = 0 := by
  rw [← cq_productTorusTrace_naturality, hc, map_zero]

theorem cq_torusTrace_surjective (X : TopCat.{0}) (k n : ℕ) :
    Function.Surjective (cq_torusTrace X k n) := by
  induction k with
  | zero => exact Function.surjective_id
  | succ k ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    refine ⟨prodCircleCohomologyEquiv (cq_circleTower X k) (n + k) (0, b), ?_⟩
    change cq_torusTrace X k n
      ((prodCircleCohomologyEquiv (cq_circleTower X k) (n + k)).symm
        (prodCircleCohomologyEquiv (cq_circleTower X k) (n + k) (0, b))).2 = a
    rw [LinearEquiv.symm_apply_apply]
    exact hb

theorem cq_productTorusTrace_surjective (X : TopCat.{0}) (k n : ℕ) :
    Function.Surjective (cq_productTorusTrace X k n) :=
  (cq_torusTrace_surjective X k n).comp
    (cohomologyHomeomorphEquiv (cq_circleTowerHomeomorph X k).symm (n + k)).surjective

end HodgeLean.Foundations.Program
