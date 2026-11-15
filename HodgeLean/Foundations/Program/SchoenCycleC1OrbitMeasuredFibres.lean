import HodgeLean.Foundations.Program.SchoenCycleC1FreeOpenPoints

/-! # Measuring actual fibres from faithful finite orbits -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The orbit description of the actual complex fibres supplies a fibre of
full group cardinality in every nonempty base open. -/
theorem s2e_c1_orbit_fibres_measured_in_every_open
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom]
    (G : Type) [Group G] [Finite G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (q : X ⟶ Y) [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z)
    (U : Y.left.Opens) (hU : (U : Set Y.left).Nonempty) :
    ∃ y : ComplexPoint Y, y.underlying ∈ U ∧
      Nat.card ((Point.map q) ⁻¹' {y}) = Nat.card G := by
  classical
  have hpre : ((q.left ⁻¹ᵁ U) : Set X.left).Nonempty := by
    obtain ⟨y, hy⟩ := hU
    obtain ⟨x, hx⟩ := q.left.surjective y
    exact ⟨x, by change q.left x ∈ U; rw [hx]; exact hy⟩
  obtain ⟨x, hx, hfree⟩ := s2e_c1_exists_free_complex_point_in_open
    X G a ha1 hamul hinj (q.left ⁻¹ᵁ U) hpre
  refine ⟨Point.map q x, ?_, ?_⟩
  · rw [Point.underlying_map]
    exact hx
  let F := (Point.map q) ⁻¹' {Point.map q x}
  have hpres (u : G) : Point.map q (Point.map (a u) x) = Point.map q x := by
    rw [← Point.map_comp_apply, hinv]
  let f : G → F := fun u => ⟨Point.map (a u) x, hpres u⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      exact hfree (congrArg Subtype.val huv)
    · intro z
      obtain ⟨u, hu⟩ := (horbit x z.val).mp z.property.symm
      exact ⟨u, Subtype.ext hu⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end HodgeLean.Foundations.Program
