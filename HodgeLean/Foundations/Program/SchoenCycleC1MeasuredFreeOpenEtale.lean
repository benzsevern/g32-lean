import HodgeLean.Foundations.Program.SchoenCycleC1MeasuredFreeEtaleSource
import HodgeLean.Foundations.Program.SchoenCycleC1ComplexFibreEtaleBase
import HodgeLean.Foundations.Program.SchoenCycleC1ComplexEtaleOpenDetection

/-! # Actual etaleness over the measured free deck locus -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A measured faithful deck action that is free above a specified base open
gives etaleness of the actual cover over that entire open. -/
theorem s2e_c1_measured_cover_etale_over_free_open
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    [IsIntegral Y.left] [Smooth Y.hom]
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hmeas : ∀ V : Y.left.Opens, (V : Set Y.left).Nonempty →
      ∃ y : ComplexPoint Y, y.underlying ∈ V ∧ Nat.card ((Point.map q) ⁻¹' {y}) = Nat.card G)
    (W : Y.left.Opens)
    (hfree : ∀ x : ComplexPoint X, q.left x.underlying ∈ W →
      ∀ g, Point.map (a g) x = x → g = 1) : Etale (q.left ∣_ W) := by
  apply s2e_c1_etale_restriction_of_complex_neighbourhoods X.left Y q.left W
  intro y hy
  apply s2e_c1_etale_base_of_complex_fibre_neighbourhoods X Y q y
  intro x hx
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y.left) (x := y.underlying) (U := ⊤) (by trivial)
  have hxU : x.underlying ∈ q.left ⁻¹ᵁ U := by
    change q.left x.underlying ∈ U
    simpa only [← Point.underlying_map, hx] using hyU
  have hxW : q.left x.underlying ∈ W := by
    simpa only [← Point.underlying_map, hx] using hy
  obtain ⟨V, hV, _, _, het⟩ := s2e_c1_measured_free_etale_source_neighbourhood
    X Y G a ha1 hamul hinj q hinv hmeas U hU x hxU (hfree x hxW)
  exact ⟨V, hV, het⟩

end HodgeLean.Foundations.Program
