import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ComplexClassLinearInvariance

/-! # The complex scalar change in the signed normal coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual complex matrix multiplying every normal coordinate by `I`. -/
def normalIMatrix (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := Complex.I • 1

/-- The scalar change is invertible also in rank zero. -/
theorem normalIMatrix_det_ne_zero (k : ℕ) : (normalIMatrix k).det ≠ 0 := by
  rw [normalIMatrix, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ Complex.I_ne_zero

#print axioms normalIMatrix_det_ne_zero

/-- The actual punctured pair map multiplying every complex normal coordinate by `I`. -/
def normalScalarIPair (k : ℕ) : puncturedPair ℂ k ⟶ puncturedPair ℂ k :=
  complexMatrixPuncturedPairMap k (normalIMatrix k) (normalIMatrix_det_ne_zero k)

/-- The pair map retains the specified scalar formula on actual vectors. -/
theorem normalScalarIPair_apply (k : ℕ) (z : Fin k → ℂ) :
    (TopPair.Hom.fst (normalScalarIPair k)) z = fun j => Complex.I * z j := by
  change (normalIMatrix k).mulVec z = _
  rw [normalIMatrix, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

#print axioms normalScalarIPair_apply

/-- The specified complex scalar change acts identically on actual supported cohomology in every degree. -/
theorem normalScalarIPair_cohomology (k n : ℕ)
    (α : RelativeCohomology ℚ (puncturedPair ℂ k) n) :
    relativeCohomologyMap ℚ n (normalScalarIPair k) α = α := by
  obtain ⟨H⟩ := Matrix.nonempty_complexIsotopyToOne (normalIMatrix k) (normalIMatrix_det_ne_zero k)
  have he : relativeCohomologyMap ℚ n (𝟙 (puncturedPair ℂ k)) =
      relativeCohomologyMap ℚ n (normalScalarIPair k) :=
    congrArg ModuleCat.Hom.hom
      ((HomologicalComplex.linearDualHomotopy
        (TopPair.Homotopy.relativeChainHomotopy (R := ℚ)
          (complexMatrixPuncturedPairHomotopy k (normalIMatrix_det_ne_zero k) H))).homologyMap_eq n)
  rw [relativeCohomologyMap_id] at he
  exact (congrArg (fun f => f α) he).symm

#print axioms normalScalarIPair_cohomology
end HodgeLean.Foundations.Program.G32Native.EulerModel
