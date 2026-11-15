import HodgeLean.Foundations.Program.CompensationAssemblyTorusTrace

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

def cq_fibreProductMap {U X : TopCat.{0}} (f : U ⟶ X) (Y : TopCat.{0}) :
    TopCat.of (U × Y) ⟶ TopCat.of (X × Y) :=
  TopCat.ofHom ⟨fun p => (f p.1, p.2),
    (f.hom.continuous.comp continuous_fst).prodMk continuous_snd⟩

def cq_fibreTrace (X Y : TopCat.{0}) (k n : ℕ) (e : Y ≃ₜ UnitAddTorus (Fin k)) :
    Cohomology ℚ (TopCat.of (X × Y)) (n + k) →ₗ[ℚ] Cohomology ℚ X n :=
  cq_productTorusTrace X k n ∘ₗ
    (cohomologyHomeomorphEquiv ((Homeomorph.refl X).prodCongr e) (n + k)).toLinearMap

theorem cq_fibreTrace_naturality {U X : TopCat.{0}} (f : U ⟶ X)
    (Y : TopCat.{0}) (k n : ℕ) (e : Y ≃ₜ UnitAddTorus (Fin k))
    (c : Cohomology ℚ (TopCat.of (X × Y)) (n + k)) :
    cq_fibreTrace U Y k n e (cohomologyMap ℚ (n + k) (cq_fibreProductMap f Y) c) =
      cohomologyMap ℚ n f (cq_fibreTrace X Y k n e c) := by
  let hU : TopCat.of (U × UnitAddTorus (Fin k)) ⟶ TopCat.of (U × Y) :=
    TopCat.ofHom ⟨((Homeomorph.refl U).prodCongr e).symm,
      ((Homeomorph.refl U).prodCongr e).symm.continuous⟩
  let hX : TopCat.of (X × UnitAddTorus (Fin k)) ⟶ TopCat.of (X × Y) :=
    TopCat.ofHom ⟨((Homeomorph.refl X).prodCongr e).symm,
      ((Homeomorph.refl X).prodCongr e).symm.continuous⟩
  have hcomm : cq_productTorusMap f k ≫ hX = hU ≫ cq_fibreProductMap f Y := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  have heq : cohomologyMap ℚ (n + k) hU
      (cohomologyMap ℚ (n + k) (cq_fibreProductMap f Y) c) =
      cohomologyMap ℚ (n + k) (cq_productTorusMap f k)
        (cohomologyMap ℚ (n + k) hX c) := by
    change (cohomologyMap ℚ (n + k) hU ∘ₗ
      cohomologyMap ℚ (n + k) (cq_fibreProductMap f Y)) c =
      (cohomologyMap ℚ (n + k) (cq_productTorusMap f k) ∘ₗ
        cohomologyMap ℚ (n + k) hX) c
    rw [← cohomologyMap_comp, ← cohomologyMap_comp, hcomm]
  exact (congrArg (cq_productTorusTrace U k n) heq).trans
    (cq_productTorusTrace_naturality f k n _)

theorem cq_fibreTrace_eq_zero_of_injective_restriction {U X : TopCat.{0}} (f : U ⟶ X)
    (Y : TopCat.{0}) (k n : ℕ) (e : Y ≃ₜ UnitAddTorus (Fin k))
    (hi : Function.Injective (cohomologyMap ℚ n f))
    (c : Cohomology ℚ (TopCat.of (X × Y)) (n + k))
    (hc : cohomologyMap ℚ (n + k) (cq_fibreProductMap f Y) c = 0) :
    cq_fibreTrace X Y k n e c = 0 := by
  apply hi
  rw [← cq_fibreTrace_naturality, hc, map_zero, map_zero]

end HodgeLean.Foundations.Program
