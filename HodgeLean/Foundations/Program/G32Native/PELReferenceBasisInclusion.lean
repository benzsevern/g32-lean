import HodgeLean.Foundations.Program.G32Native.PELPeriodComponentAction

noncomputable section
set_option maxHeartbeats 400000
open scoped Quaternion
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The rational reference operator is linear, before any scalar extension. -/
def pel_reference_operator_linear (R : PELSplitReference) :
    ℍ[ℚ, -3, 0, R.b] →ₗ[ℚ] Matrix (Fin 12) (Fin 12) ℚ where
  toFun := R.operator
  map_add' := by intro x y; simp [PELSplitReference.operator]
  map_smul' := by intro r x; simp [PELSplitReference.operator]

/-- Commutation with the four retained quaternion basis operators implies
commutation with every rational quaternion operator. -/
theorem pel_reference_real_commutes_all (R : PELSplitReference)
    (g : Matrix (Fin 12) (Fin 12) ℝ)
    (h : ∀ i : Fin 4, g *
      (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℝ) =
      (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℝ) * g) :
    ∀ d, g * (R.operator d).map (algebraMap ℚ ℝ) =
      (R.operator d).map (algebraMap ℚ ℝ) * g := by
  let f := (Algebra.linearMap ℚ ℝ).mapMatrix.comp (pel_reference_operator_linear R)
  let F := (LinearMap.mulRight ℚ g - LinearMap.mulLeft ℚ g).comp f
  have hF : F = 0 := by
    apply (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b).ext
    intro i
    exact sub_eq_zero.mpr (h i).symm
  intro d
  exact (sub_eq_zero.mp (LinearMap.congr_fun hF d)).symm

/-- The real group specified by the quaternion basis maps continuously into
the real group retaining every quaternion operator. -/
noncomputable def pel_reference_basis_inclusion (R : PELSplitReference) :
    pelIsometrySubgroup (R.form.map (algebraMap ℚ ℝ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℝ)) →*
      pelRealIsometries R where
  toFun g := ⟨g.val, g.property.1, fun T hT => by
    obtain ⟨d, rfl⟩ := hT
    exact pel_reference_real_commutes_all R g.val.val
      (fun i => (g.property.2 _ ⟨i, rfl⟩).eq) d⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The basis inclusion uses the inherited ordinary real topology. -/
theorem pel_reference_basis_inclusion_continuous (R : PELSplitReference) :
    Continuous (pel_reference_basis_inclusion R) :=
  continuous_induced_rng.mpr continuous_subtype_val

end HodgeLean.Foundations.Program.GeneralTypeIII
