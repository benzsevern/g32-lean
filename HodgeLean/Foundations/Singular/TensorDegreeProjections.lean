import HodgeLean.Foundations.Singular.TensorDegreeMaps

/-! Actual bidegree projections for arbitrary rational tensor complexes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Projection from the total tensor chain group to a specified bidegree.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
def tensorDegreeProjection (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n ⟶
      ModuleCat.of ℚ ((K).X p ⊗[ℚ] (L).X q) :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := K) (K₂ := L)
    (F := curriedTensor (ModuleCat ℚ)) (c := ComplexShape.down ℕ)
    (fun r s _ => if h : r = p ∧ s = q then by
      rcases h with ⟨rfl, rfl⟩
      exact 𝟙 _
    else 0)

/-- Inclusion followed by its own bidegree projection is the identity.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
theorem tensorDegreeInclusion_projection_self (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q n : ℕ)
    (hpq : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n hpq ≫ tensorDegreeProjection K L p q n = 𝟙 _ := by
  unfold tensorDegreeProjection
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp

/-- Distinct tensor bidegrees have zero projection composite.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
theorem tensorDegreeInclusion_projection_other (K L : ChainComplex (ModuleCat ℚ) ℕ)
    (p q r s n : ℕ) (hrs : r + s = n) (h : ¬ (r = p ∧ s = q)) :
    HomologicalComplex.ιTensorObj K L r s n hrs ≫ tensorDegreeProjection K L p q n = 0 := by
  unfold tensorDegreeProjection
  rw [HomologicalComplex.ι_mapBifunctorDesc, dif_neg h]

#print axioms tensorDegreeInclusion_projection_other
#print axioms tensorDegreeProjection
#print axioms tensorDegreeInclusion_projection_self
end HodgeLean.Foundations.Singular
