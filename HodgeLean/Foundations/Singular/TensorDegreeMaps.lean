import HodgeLean.Foundations.Singular.TensorDegreeSum

/-! Naturality of actual tensor-degree inclusions for arbitrary rational chain maps. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace HodgeLean.Foundations.Singular

/-- Actual tensor-degree inclusions intertwine arbitrary chain maps on their two factors.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the total tensor complex. -/
theorem tensorDegreeInclusion_naturality
    {K K' L L' : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ K') (g : L ⟶ L')
    (p q n : ℕ) (hpq : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n hpq ≫ (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj K' L' p q n hpq := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc]
  exact HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor (ModuleCat ℚ))
    (ComplexShape.down ℕ) p q n hpq

#print axioms tensorDegreeInclusion_naturality
end HodgeLean.Foundations.Singular
