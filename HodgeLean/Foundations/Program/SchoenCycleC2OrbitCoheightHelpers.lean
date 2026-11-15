import HodgeLean.Foundations.Program.SchoenCycleC2DimensionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2CoheightHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2NeighbourhoodHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2SupportHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Every component in an orbit over a finite étale neighbourhood has the
coheight of the same projected component generic point. -/
theorem s2e_orbit_component_coheight_eq_projection
    {Q W B : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth B.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (β : W ⟶ B) (hd : δ ≫ β = β)
    (U : B.left.Opens) (hU : Set.range (ι ≫ β).left ⊆ U)
    (hfin : IsFinite (β.left ∣_ U)) (he : Etale (β.left ∣_ U)) (n : ℕ) :
    ∀ x ∈ (s2e_componentCycle (ι ≫ (End.of δ ^ n).asHom) ℚ).support,
      Order.coheight x = Order.coheight ((ι ≫ β).left (genericPoint Q.left)) := by
  intro x hx
  rw [s2e_componentCycle_support] at hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  have hp : (ι ≫ (End.of δ ^ n).asHom) ≫ β = ι ≫ β := by
    rw [Category.assoc, s2e_power_projection δ β hd n]
  have hpoint := congrArg (fun f : Q ⟶ B => f.left (genericPoint Q.left)) hp
  have hw : β.left ((ι ≫ (End.of δ ^ n).asHom).left (genericPoint Q.left)) ∈ U := by
    change ((ι ≫ (End.of δ ^ n).asHom) ≫ β).left (genericPoint Q.left) ∈ U
    rw [hp]
    exact hU ⟨genericPoint Q.left, rfl⟩
  exact (s2e_coheight_eq_of_finite_etale_near β U hfin he _ hw).trans
    (congrArg Order.coheight hpoint)

/-- A finite étale orbit over a fixed immersed smooth subscheme has the
codimension determined by the source and base dimensions. -/
theorem s2e_orbit_component_coheight_of_dimensions
    {Q W B : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom]
    [IsIntegral B.left] [Smooth B.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (β : W ⟶ B) (hd : δ ≫ β = β)
    [IsClosedImmersion (ι ≫ β).left]
    (U : B.left.Opens) (hU : Set.range (ι ≫ β).left ⊆ U)
    (hfin : IsFinite (β.left ∣_ U)) (he : Etale (β.left ∣_ U))
    (n k : ℕ) (hQ : dim Q.left = n) (hB : dim B.left = n + k)
    (t : ℕ) :
    ∀ x ∈ (s2e_componentCycle (ι ≫ (End.of δ ^ t).asHom) ℚ).support,
      Order.coheight x = k := by
  intro x hx
  exact (s2e_orbit_component_coheight_eq_projection ι δ β hd U hU hfin he t x hx).trans
    (s2e_immersion_generic_coheight_of_dimensions (ι ≫ β) n k hQ hB)

end HodgeLean.Foundations.Program
