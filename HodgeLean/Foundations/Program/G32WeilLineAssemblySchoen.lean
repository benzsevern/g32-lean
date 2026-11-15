import HodgeLean.Foundations.Program.G32PropFourSixDefs
import HodgeLean.Foundations.Program.CyclotomicWeil

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false
open scoped TensorProduct
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Papers HodgeLean.Foundations HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem g32c_schoen_wedge_exists (A : g32t_Sixfold) (X : g32p_Cover A)
    (hS : g32p_SchoenSupplier X) (S : g32p_Supplier) (hAdm : g32p_Admissible X.aut S) :
    ∃ y : ⋀[ℚ]^(2 * (X.part S hAdm).k) (HQ (X.part S hAdm).P 1),
      y ∈ cyc_wedges (X.part S hAdm).act.cyc_coordinates ∧ y ≠ 0 ∧
      (cupProductOf (X.part S hAdm).P).cupWedgeMap _ y ∈
        algebraicCycleClassSpan (X.part S hAdm).P (X.part S hAdm).k := by
  letI := (torusCohomology_cupProductOf (X.part S hAdm).P).finite
  have hn : cyc_wedges (X.part S hAdm).act.cyc_coordinates ≠ ⊥ := by
    intro hh
    have hr := cyc_rational_rank S.three_le
      (Nat.mul_pos (by omega) (X.part S hAdm).act.cyc_positive)
      (X.part S hAdm).act.cyc_coordinates
    rw [hh, finrank_bot] at hr
    have := Nat.totient_pos.mpr (NeZero.pos S.m)
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  refine ⟨y, hy, hy0, ?_⟩
  have hs : cyc_Algebraic (cupProductOf (X.part S hAdm).P)
      (X.part S hAdm).act.cyc_coordinates := by
    by_cases hp : g32p_PrimeAvailable S
    · exact hS.schoen S hAdm hp
    · exact hS.withoutPrime S hAdm hp
  exact hs ⟨y, hy, rfl⟩

end HodgeLean.Foundations.Program
