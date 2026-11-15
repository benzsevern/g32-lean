import HodgeLean.Foundations.Program.SchoenCycleC11SchemeHelpers
import HodgeLean.Foundations.Program.SchoenPowerComplexPoints

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The original power-map square and the surjective symmetric quotient
make the actual finite initial projection surjective on scheme points. -/
theorem s2e_c1_retained_projection_surjective
    (Y Z W B : Over (Spec ↧ℂ)) [LocallyOfFiniteType B.hom]
    (p : Y ⟶ Z) (hp : Function.Surjective (Point.map p)) (N : ℕ)
    (q : g3_power Y N ⟶ W) (γ : g3_power Z N ⟶ B)
    (hγ : Function.Surjective (Point.map γ))
    (β : W ⟶ B) [IsFinite β.left]
    (hsq : q ≫ β = s2_powerMap p N ≫ γ) :
    Surjective β.left := by
  apply s2e_c11_surjective_of_point_surjective W B β
  intro b
  obtain ⟨v, hv⟩ := hγ b
  obtain ⟨x, hx⟩ := s2_powerMap_point_surjective p hp N v
  refine ⟨Point.map q x, ?_⟩
  calc
    Point.map β (Point.map q x) = Point.map (q ≫ β) x := rfl
    _ = Point.map (s2_powerMap p N ≫ γ) x := congrArg (fun f => Point.map f x) hsq
    _ = b := by change Point.map γ (Point.map (s2_powerMap p N) x) = b; rw [hx, hv]

end HodgeLean.Foundations.Program
