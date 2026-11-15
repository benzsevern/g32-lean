import HodgeLean.Foundations.Program.SchoenCycleC2ChartPullbackHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A complex scheme isomorphism induces its actual homeomorphism of complex points. -/
def s2e_pointHomeomorphOfIso {V W : Over (Spec ↧ℂ)} (e : V ≅ W) :
    ComplexPoint V ≃ₜ ComplexPoint W where
  toFun := Point.map e.hom
  invFun := Point.map e.inv
  left_inv z := by
    rw [← Point.map_comp_apply, e.hom_inv_id, Point.map_id]
  right_inv z := by
    rw [← Point.map_comp_apply, e.inv_hom_id, Point.map_id]
  continuous_toFun := (Point.continuousMap e.hom).continuous
  continuous_invFun := (Point.continuousMap e.inv).continuous

/-- A scheme isomorphism transports holomorphic charts forward with their
source images and coordinate values fixed. -/
theorem s2e_iso_holomorphicChart_forward
    (V W : Over (Spec ↧ℂ))
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (i : V ⟶ W) [IsIso i] (r k : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint V) ((Fin r → ℂ) × (Fin k → ℂ)))
    (he : HodgeLean.Adapters.a3b4_IsHolChart V.hom e) (z : ComplexPoint V) :
    ∃ E : OpenPartialHomeomorph (ComplexPoint W) ((Fin r → ℂ) × (Fin k → ℂ)),
      HodgeLean.Adapters.a3b4_IsHolChart W.hom E ∧ E.source = Point.map i '' e.source ∧
      ∀ y, E (Point.map i y) = e y := by
  letI : Nonempty (ComplexPoint W) := ⟨Point.map i z⟩
  have hfInv : Topology.IsOpenEmbedding (Point.map (inv i)) :=
    (s2e_pointHomeomorphOfIso (asIso i).symm).isOpenEmbedding
  obtain ⟨E, hE, hsource, hval⟩ :=
    s2e_holomorphicChart_openEmbedding_pullback W V (inv i) hfInv r k e he
  refine ⟨E, hE, ?_, ?_⟩
  · rw [hsource]
    ext y
    constructor
    · intro hy
      refine ⟨Point.map (inv i) y, hy, ?_⟩
      rw [← Point.map_comp_apply, IsIso.inv_hom_id, Point.map_id]
    · rintro ⟨y, hy, rfl⟩
      change Point.map (inv i) (Point.map i y) ∈ e.source
      simpa only [← Point.map_comp_apply, IsIso.hom_inv_id, Point.map_id] using hy
  · intro y
    rw [hval]
    rw [← Point.map_comp_apply, IsIso.hom_inv_id, Point.map_id]

end HodgeLean.Foundations.Program
