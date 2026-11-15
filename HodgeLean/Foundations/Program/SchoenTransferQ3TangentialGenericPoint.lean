import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms
import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialDominance

/-! Retention of support generic points through the common dense tangential base. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
namespace HodgeLean.Foundations.Program

/-- An actual nonempty etale support map sends its generic point into
every dense open of the integral tangential base. -/
theorem s4_q3_etale_support_generic_mem_dense_base
    {C T : Scheme.{0}} [IsIntegral C] [IsIntegral T]
    (f : C ⟶ T) [Etale f] (A : T.Opens) (hA : Dense (A : Set T)) :
    f (genericPoint C) ∈ A := by
  letI : IsDominant f :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace f f.isOpenMap⟩
  rw [s2_dominant_genericPoint f]
  obtain ⟨t, ht⟩ := hA.nonempty
  exact (genericPoint_specializes t).mem_open A.isOpen ht

end HodgeLean.Foundations.Program
