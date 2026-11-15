import HodgeLean.Foundations.Program.SchoenTransferQ3OrbitCohomology

/-! Open paracompactness from the literal point-orbit interface. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The actual scheme symmetries act by homeomorphisms with their specified inverses. -/
def s4_q3_pointHomeomorph (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (g : G) :
    ComplexPoint X ≃ₜ ComplexPoint X where
  toFun := Point.map (a g)
  invFun := Point.map (a g⁻¹)
  left_inv x := by
    rw [← Point.map_comp_apply, ← hamul, inv_mul_cancel, ha1, Point.map_id]
  right_inv x := by
    rw [← Point.map_comp_apply, ← hamul, mul_inv_cancel, ha1, Point.map_id]
  continuous_toFun := Point.continuous_map (a g)
  continuous_invFun := Point.continuous_map (a g⁻¹)

/-- The original orbit-fibre quotient is open. -/
theorem s4_q3_orbit_map_isOpenMap
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (I : Type*) (a : I → (A ≃ₜ A)) (q : A → B)
    (hq : Topology.IsQuotientMap q) (hinv : ∀ g x, q (a g x) = q x)
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

/-- Open subspaces of the actual orbit target are paracompact without a
scheme categorical-quotient premise. -/
theorem s4_q3_orbit_target_openParacompact
    (X W : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ W) (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ g, a g ≫ q = q)
    (horbit : ∀ x y, Point.map q x = Point.map q y → ∃ g, Point.map (a g) x = y)
    (U : Opens (ComplexPoint W)) : ParacompactSpace U := by
  let ah := s4_q3_pointHomeomorph X G a ha1 hamul
  have hopen : IsOpenMap (Point.map q) := by
    apply s4_q3_orbit_map_isOpenMap G ah (Point.map q)
      (Topology.IsQuotientMap.of_surjective_continuous hsurj (Point.continuous_map q))
    · intro g x
      change Point.map q (Point.map (a g) x) = Point.map q x
      rw [← Point.map_comp_apply, hinv]
    · exact horbit
  letI : SecondCountableTopology (ComplexPoint X) :=
    ChartedSpace.secondCountable_of_sigmaCompact (Fin (dim X.left) → ℂ) (ComplexPoint X)
  letI : LocallyCompactSpace (ComplexPoint X) :=
    ChartedSpace.locallyCompactSpace (Fin (dim X.left) → ℂ) (ComplexPoint X)
  have hq : IsOpenQuotientMap (Point.map q) := ⟨hsurj, Point.continuous_map q, hopen⟩
  letI : SecondCountableTopology (ComplexPoint W) := Topology.IsOpenQuotientMap.secondCountableTopology hq
  letI : LocallyCompactSpace (ComplexPoint W) := hq.locallyCompactSpace
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  letI : SigmaCompactSpace U := inferInstance
  infer_instance

end HodgeLean.Foundations.Program
