import HodgeLean.Foundations.Program.SchoenTransferQ3OrbitParacompact
import HodgeLean.Foundations.Program.FiniteQuotientSingularComparison
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis

/-! Injectivity for the specified finite orbit pullback. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The actual singular pullback is injective using only finite point-orbit
fibres, rather than a categorical-quotient premise on schemes. -/
theorem s4_q3_orbit_pullback_injective
    (X W : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ W) (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ g, a g ≫ q = q)
    (horbit : ∀ x y, Point.map q x = Point.map q y → ∃ g, Point.map (a g) x = y)
    (n : ℕ) : Function.Injective (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap q))) := by
  let q' := TopCat.ofHom (Point.continuousMap q)
  let ah := s4_q3_pointHomeomorph X G a ha1 hamul
  have halaws (g h : G) (x : ComplexPoint X) : ah (g * h) x = ah g (ah h x) := by
    change Point.map (a (g * h)) x = Point.map (a g) (Point.map (a h) x)
    rw [hamul, Point.map_comp_apply]
  have hi (g : G) (x : ComplexPoint X) : q' (ah g x) = q' x := by
    change Point.map q (Point.map (a g) x) = Point.map q x
    rw [← Point.map_comp_apply, hinv]
  have ho (x y : TopCat.of (ComplexPoint X)) (hxy : q' x = q' y) : ∃ g, ah g x = y :=
    horbit x y hxy
  obtain ⟨L, hL⟩ := constantSheaf_pullback_sections q'
  obtain ⟨T, hT⟩ := finite_quotient_constantSheaf_trace G ah halaws q'
    (Topology.IsQuotientMap.of_surjective_continuous hsurj (Point.continuous_map q)) hi ho
  have hd := finite_quotient_constantSheaf_trace_degree G (fun g => ah g) q' hsurj hi L T hL hT
  letI : ∀ U : Opens (ComplexPoint W), ParacompactSpace U :=
    s4_q3_orbit_target_openParacompact X W G a ha1 hamul q hsurj hinv horbit
  letI := s4_q3_orbit_pushforward_resolution X W q hsurj G (fun g => Point.map (a g)) horbit
  exact singular_cohomology_injective_of_sheaf_trace q'
    (HodgeLean.Foundations.ComplexTopology.finiteType_basis W) L T
    (Fintype.card G) Fintype.card_ne_zero hd hL n

end HodgeLean.Foundations.Program
