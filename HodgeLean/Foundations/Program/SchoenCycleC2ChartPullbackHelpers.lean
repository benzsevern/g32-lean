import HodgeLean.Adapters.NormalConeB4aClassChartPullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program

/-- A regular morphism that embeds complex points as an open subset pulls
holomorphic normal charts back with the same coordinate values. -/
theorem s2e_holomorphicChart_openEmbedding_pullback
    (X Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [Nonempty (ComplexPoint X)]
    (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding (Point.map f)) (r k : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint Y) ((Fin r → ℂ) × (Fin k → ℂ)))
    (he : a3b4_IsHolChart Y.hom e) :
    ∃ E : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)),
      a3b4_IsHolChart X.hom E ∧ E.source = Point.map f ⁻¹' e.source ∧
      ∀ x, E x = e (Point.map f x) := by
  let a := hf.toOpenPartialHomeomorph (Point.map f)
  let E := a.trans e
  have hsource : E.source = Point.map f ⁻¹' e.source := by
    ext x
    change (x ∈ a.source ∧ e.source (a x)) ↔ e.source (Point.map f x)
    rw [show a.source = Set.univ from rfl]
    exact ⟨fun h => h.2, fun h => ⟨Set.mem_univ _, h⟩⟩
  have hsub : E.source ⊆ Point.map f ⁻¹' e.source := hsource.le
  have hmap := f4_map_isHom f
  refine ⟨E, ?_, hsource, fun _ => rfl⟩
  constructor
  · intro j
    exact anrem_isHolFun_restrict (f4_analytification X) hsub
      (hmap.2 e.source e.open_source (fun x : e.source => (e x).1 j) (he.1 j))
  · intro j
    exact anrem_isHolFun_restrict (f4_analytification X) hsub
      (hmap.2 e.source e.open_source (fun x : e.source => (e x).2 j) (he.2 j))

end HodgeLean.Foundations.Program
