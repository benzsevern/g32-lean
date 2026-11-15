import HodgeLean.Foundations.Program.SchoenTransferQ3FibreCharts
import HodgeLean.Foundations.Program.SchoenTransferQ3FibrePoints
import HodgeLean.Adapters.NormalConeB4Defs

/-! Holomorphic point charts on actual embedded tangential fibres. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program

/-- The fibre point chart retains the ambient normal coordinates and their
holomorphic interpretation over the original complex base. -/
theorem s4_q3_holomorphic_fibre_normal_chart
    {S X : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsClosedImmersion j.left] (r k : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (a : Fin r → ℂ)
    (hlevel : ∀ m ∈ e.source, m ∈ Set.range (Point.map j) ↔ (e m).1 = a)
    (x : ComplexPoint S) (hx : Point.map j x ∈ e.source) :
    ∃ es : OpenPartialHomeomorph (ComplexPoint S) ((Fin 0 → ℂ) × (Fin k → ℂ)),
      es.source = Point.map j ⁻¹' e.source ∧ x ∈ es.source ∧
        a3b4_IsHolChart S.hom es ∧ ∀ y, (es y).2 = (e (Point.map j y)).2 := by
  obtain ⟨ZS, sq, rfl⟩ := Over.mk_surjective S
  obtain ⟨ZX, xq, rfl⟩ := Over.mk_surjective X
  let S : Over (Spec ↧ℂ) := Over.mk sq
  let X : Over (Spec ↧ℂ) := Over.mk xq
  obtain ⟨es, hsource, hxes, hnormal⟩ := s4_q3_embedded_fibre_normal_chart
    (Point.map j) (ComplexPoint.isClosedEmbedding_map_of_closedImmersion j).isEmbedding
    e a hlevel x hx
  let H : (Fin k → ℂ) ≃ₜ ((Fin 0 → ℂ) × (Fin k → ℂ)) :=
    (Homeomorph.uniqueProd (Fin 0 → ℂ) (Fin k → ℂ)).symm
  let es' := es.trans H.toOpenPartialHomeomorph
  have hs : es'.source = Point.map j ⁻¹' e.source := by
    simpa only [es', OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ] using hsource
  have hn (y : ComplexPoint S) : (es' y).2 = (e (Point.map j y)).2 := by
    change (H (es y)).2 = _
    exact hnormal y
  refine ⟨es', hs, hs ▸ hx, ?_, hn⟩
  constructor
  · intro i
    exact Fin.elim0 i
  · intro i
    have hg := (f4_map_isHom j).2 e.source e.open_source
      (fun z : e.source => (e z).2 i) (he.2 i)
    have hg' : (f4_analytification S).IsHolFun
        (fun y : es'.source => (e (Point.map j y)).2 i) := by
      rw [hs]
      exact hg
    have hfun : (fun y : es'.source => (es' y).2 i) =
        (fun y : es'.source => (e (Point.map j y)).2 i) := by
      funext y
      exact congrFun (hn y) i
    change (f4_analytification S).IsHolFun (fun y : es'.source => (es' y).2 i)
    rw [hfun]
    exact hg'

end HodgeLean.Foundations.Program
