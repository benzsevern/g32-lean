import HodgeLean.Foundations.Program.G32Native.PELReferenceLieCenter
import HodgeLean.Foundations.Program.G32Native.PELPeriodConnectedCircle
import HodgeLean.Foundations.Program.G32Native.PELNoncentralTangent

noncomputable section
set_option maxHeartbeats 200000
open scoped Quaternion
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Every compatible period matrix has a noncommuting element in the
connected reference isometry group. The zero Lie centre detects it without
a group-level almost-simplicity theorem.
Source: `pel_reference_lie_center_eq_zero` and `pel_noncentral_of_tangent`. -/
theorem pelPeriodMatrix_noncentral (R : PELSplitReference) (z : PELSplitDomain R) :
    ∃ g ∈ g1_identityComponent
      (pelIsometryGroup (R.form.map (algebraMap ℚ ℂ))
        (Set.range fun i : Fin 4 =>
          (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
            (algebraMap ℚ ℂ))), ¬ Commute (pelPeriodMatrix R z) g := by
  let Ω := R.form.map (algebraMap ℚ ℂ)
  let S := Set.range fun i : Fin 4 =>
    (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℂ)
  let j := pelPeriodMatrix R z
  let M : Matrix (Fin 12) (Fin 12) ℂ := j
  have hmem : j ∈ (pelIsometryGroup Ω S).carrier :=
    @connectedComponentIn_subset _ (g1_zariski ℂ 12) _ _ _ (pelPeriodMatrix_mem_component R z)
  obtain ⟨hiso, hcomm⟩ := (mem_pelIsometryGroup Ω S j).mp hmem
  have hsq : M * M = -1 := by
    change z.J.map (algebraMap ℝ ℂ) * z.J.map (algebraMap ℝ ℂ) = -1
    rw [← Matrix.map_mul, z.square, Matrix.map_neg, Matrix.map_one] <;> simp
  have hLie : M ∈ g1_lieOfSet (pelGenericGroup Ω S) :=
    (lie_pelGenericGroup Ω S M).mpr ⟨pel_square_isometry_skew M Ω hsq hiso, hcomm⟩
  by_contra! hn
  have hcenter : ∀ X ∈ g1_lieOfSet (pelGenericGroup Ω S), M * X = X * M := by
    intro X hX
    obtain ⟨hskew, hc⟩ := (lie_pelGenericGroup Ω S X).mp hX
    by_contra he
    obtain ⟨g, hg, hng⟩ := pel_noncentral_of_tangent Ω S j X hskew hc (Ne.symm he)
    exact hng (hn g hg)
  have hz := pel_reference_lie_center_eq_zero R M hLie hcenter
  apply pelPeriodMatrix_ne_complex_scalar R z 0
  simpa only [zero_smul] using hz

#print axioms pelPeriodMatrix_noncentral
end HodgeLean.Foundations.Program.GeneralTypeIII
