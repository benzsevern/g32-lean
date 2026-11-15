import HodgeLean.Foundations.Program.G32Native.PELPeriodGenerationSteps

noncomputable section
open HodgeLean.Foundations
open scoped Quaternion
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The entire connected rank-three quaternionic period component generates
the connected quaternion-linear polarization-isometry group over the rationals.
Source: Abdulali, Annals of Mathematics 155 (2002), Proposition 2.3.1,
p. 919, §§3.2–3.3, pp. 920–921, and §4, p. 922. -/
theorem pel_period_matrix_generation_aux (R : PELSplitReference)
    (G : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (hG : g2_IsRatAlgSubgroup G)
    (hperiod : ∀ z : PELSplitComponent R, pelPeriodMatrix R z.val ∈ G) :
    pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) ⊆ G := by
  exact pel_period_matrix_generation_of_steps R G hG hperiod

#print axioms pel_period_matrix_generation_aux
end HodgeLean.Foundations.Program.GeneralTypeIII
