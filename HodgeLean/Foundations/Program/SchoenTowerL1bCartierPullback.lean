import HodgeLean.Foundations.Program.SchoenTowerL1bPullbackEquations
import HodgeLean.Foundations.Program.SchoenTowerL1bRegularNeighborhoods

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A local rank-one ideal trivialization gives a nonzero equation after dominant pullback. -/
theorem s2v_l1b_cartier_pullback_equation
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [QuasiCompact f]
    (I : Y.IdealSheafData) (x : X)
    (hI : ∃ V : Y.affineOpens, f x ∈ V.1 ∧
      Nonempty (I.ideal V ≃ₗ[Γ(Y, V)] Γ(Y, V))) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ g : Γ(X, U), (I.comap f).ideal U = Ideal.span {g} ∧ g ≠ 0 := by
  apply s2v_l1b_local_nonzero_principal_pullback f I x
  obtain ⟨V, hxV, ⟨e⟩⟩ := hI
  let : Nonempty V.1 := ⟨⟨f x, hxV⟩⟩
  obtain ⟨g, hg, hreg⟩ := s2v_l1b_generator_of_ideal_trivialization (I.ideal V) e
  refine ⟨V, hxV, g, hg, ?_⟩
  intro hz
  have he : (0 : Γ(Y, V)) * g = 1 * g := by rw [hz, mul_zero, mul_zero]
  exact zero_ne_one (hreg he)

end HodgeLean.Foundations.Program
