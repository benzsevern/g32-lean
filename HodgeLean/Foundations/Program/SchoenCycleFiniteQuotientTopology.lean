import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric

/-! # Local topology of actual finite quotients
Scheme symmetries act by homeomorphisms on complex points.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A scheme group symmetry induces the homeomorphism with the actual inverse symmetry.
Source: Hartshorne, Algebraic Geometry, II.2; functoriality of complex points. -/
def s2e_quotientPointHomeomorph (X : Over (Spec ↧ℂ))
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (g : G) : ComplexPoint X ≃ₜ ComplexPoint X where
  toFun := Point.map (a g)
  invFun := Point.map (a g⁻¹)
  left_inv x := by
    rw [← Point.map_comp_apply, ← hamul, inv_mul_cancel, ha1, Point.map_id]
  right_inv x := by
    rw [← Point.map_comp_apply, ← hamul, mul_inv_cancel, ha1, Point.map_id]
  continuous_toFun := Point.continuous_map (a g)
  continuous_invFun := Point.continuous_map (a g⁻¹)

example (X : Over (Spec ↧ℂ))
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (g : G) (x : ComplexPoint X) :
    s2e_quotientPointHomeomorph X G a ha1 hamul g x = Point.map (a g) x := rfl

/-- A quotient whose fibres are orbits of homeomorphisms is open.
Source: Bredon, Introduction to Compact Transformation Groups, Chapter I,
section 3, orbit spaces and the quotient topology. -/
theorem s2e_orbit_quotient_isOpenMap
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (I : Type*) (a : I → (A ≃ₜ A)) (q : A → B)
    (hq : Topology.IsQuotientMap q)
    (hinv : ∀ g x, q (a g x) = q x)
    (horbit : ∀ x y, q x = q y → ∃ g, a g x = y) : IsOpenMap q := by
  intro U hU
  apply hq.isOpen_preimage.mp
  have he : q ⁻¹' (q '' U) = ⋃ g, a g '' U := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      obtain ⟨g, hg⟩ := horbit y x he
      exact Set.mem_iUnion.mpr ⟨g, y, hy, hg⟩
    · intro hx
      obtain ⟨g, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨y, hy, (hinv g y).symm⟩
  rw [he]
  exact isOpen_iUnion fun g => (a g).isOpenMap _ hU

/-- The actual categorical finite quotient is open on complex points.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition,
Chapter 1, section 1, finite-group quotients; quotient topology. -/
theorem s2e_finite_quotient_pointMap_isOpenMap
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f) :
    IsOpenMap (Point.map q) := by
  haveI : Surjective q.left :=
    s2e_step1_surjective_of_complexPoint_surjective X Y q hsurj
  apply s2e_orbit_quotient_isOpenMap G
    (s2e_quotientPointHomeomorph X G a ha1 hamul) (Point.map q)
    (Topology.IsQuotientMap.of_surjective_continuous hsurj (Point.continuous_map q))
  · intro g x
    change Point.map q (Point.map (a g) x) = Point.map q x
    rw [← Point.map_comp_apply, hinv g]
  · intro x y hxy
    exact s2e_step1_finite_quotient_point_orbits X Y G a ha1 hamul q hinv hquot x y hxy

end HodgeLean.Foundations.Program
