import HodgeLean.Foundations.Program.SchoenTransferQ3TransverseParameters
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Unramified.LocalRing

/-! Shared regular tangential parameters on the actual etale support map. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing RingTheory.Sequence
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- Target support parameters pull back to a regular system generating the
source support maximal ideal under the actual etale map. -/
theorem s4_q3_etale_support_shared_parameters
    {C D : Over (Spec ↧ℂ)} [IsIntegral D.left] [Smooth D.hom]
    (f : C ⟶ D) [Etale f.left] (p : C.left) (r : ℕ)
    (hr : Order.coheight (f.left p) = r) :
    ∃ rs : List (D.left.presheaf.stalk (f.left p)),
      rs.length = r ∧
      Ideal.ofList rs = maximalIdeal (D.left.presheaf.stalk (f.left p)) ∧
      IsRegular (D.left.presheaf.stalk (f.left p)) rs ∧
      IsRegular (C.left.presheaf.stalk p) (rs.map (f.left.stalkMap p).hom) ∧
      Ideal.ofList (rs.map (f.left.stalkMap p).hom) =
        maximalIdeal (C.left.presheaf.stalk p) := by
  obtain ⟨rs, hlen, hgen, hreg, hsource⟩ :=
    s4_q3_exists_regular_stalk_parameters f p r hr
  let R := D.left.presheaf.stalk (f.left p)
  let A := C.left.presheaf.stalk p
  letI : Algebra R A := (f.left.stalkMap p).hom.toAlgebra
  letI : IsLocalHom (algebraMap R A) := f.left.toLRSHom.prop p
  letI : Algebra.EssFiniteType R A := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f.left p
  letI : Algebra.FormallyUnramified R A := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f.left p
  refine ⟨rs, hlen, hgen, hreg, hsource, ?_⟩
  rw [← Ideal.map_ofList, hgen]
  exact Algebra.FormallyUnramified.map_maximalIdeal

end HodgeLean.Foundations.Program
