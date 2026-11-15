import HodgeLean.Adapters.NormalConeB4aClassChartTransport
import HodgeLean.Foundations.Program.SchoenSelectedGeometryOpenPoints

/-! Holomorphic chart transport through the actual algebraic open immersion. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program

/-- An algebraic isomorphism transports the actual holomorphic coordinates
and chart source to its target analytic space. -/
theorem s4_q3_holomorphic_chart_iso_transport
    {Y Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (a : Y ≅ Z) (r c : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint Y) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart Y.hom e) :
    ∃ E : OpenPartialHomeomorph (ComplexPoint Z) ((Fin r → ℂ) × (Fin c → ℂ)),
      a3b4_IsHolChart Z.hom E ∧ E.source = Point.map a.hom '' e.source ∧
      ∀ y, E (Point.map a.hom y) = e y := by
  let E := (Point.isoMapHomeomorph a).symm.toOpenPartialHomeomorph.trans e
  have hsource : E.source = Point.map a.inv ⁻¹' e.source := by
    ext z
    change (z ∈ Set.univ ∧ Point.map a.inv z ∈ e.source) ↔ _
    exact and_iff_right (Set.mem_univ _)
  have heval : ∀ y, E (Point.map a.hom y) = e y := by
    intro y
    change e (Point.map a.inv (Point.map a.hom y)) = e y
    rw [← Point.map_comp_apply, Iso.hom_inv_id, Point.map_id]
  have hsource' : E.source = Point.map a.hom '' e.source := by
    rw [hsource]
    ext z
    constructor
    · intro hz
      refine ⟨Point.map a.inv z, hz, ?_⟩
      rw [← Point.map_comp_apply, Iso.inv_hom_id, Point.map_id]
    · rintro ⟨y, hy, rfl⟩
      change Point.map a.inv (Point.map a.hom y) ∈ e.source
      rw [← Point.map_comp_apply, Iso.hom_inv_id, Point.map_id]
      exact hy
  have hmap := f4_map_isHom a.inv
  refine ⟨E, ?_, hsource', heval⟩
  constructor
  · intro j
    change (f4_analytification Z).IsHolFun
      (fun y : E.source => (e (Point.map a.inv y)).1 j)
    rw [hsource]
    exact hmap.2 e.source e.open_source (fun y : e.source => (e y).1 j) (he.1 j)
  · intro j
    change (f4_analytification Z).IsHolFun
      (fun y : E.source => (e (Point.map a.inv y)).2 j)
    rw [hsource]
    exact hmap.2 e.source e.open_source (fun y : e.source => (e y).2 j) (he.2 j)

/-- Every actual algebraic open immersion transports holomorphic charts,
including the composed ambient restrictions in the tangential construction. -/
theorem s4_q3_holomorphic_chart_openImmersion_transport
    {Y X : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [Nonempty (ComplexPoint Y)] (j : Y ⟶ X) [IsOpenImmersion j.left] (r c : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint Y) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart Y.hom e) :
    ∃ E : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)),
      a3b4_IsHolChart X.hom E ∧ E.source = Point.map j '' e.source ∧
      ∀ y, E (Point.map j y) = e y := by
  let U := j.left.opensRange
  have hr : Set.range j.left = Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  let a₀ := IsOpenImmersion.isoOfRangeEq j.left U.ι hr
  have ha₀ : a₀.hom ≫ U.ι = j.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let a : Y ≅ ComplexPoint.openScheme X U := Over.isoMk a₀ (by
    change a₀.hom ≫ (U.ι ≫ X.hom) = Y.hom
    rw [← Category.assoc, ha₀, Over.w j])
  let Z := ComplexPoint.openScheme X U
  have hj : j = a.hom ≫ ComplexPoint.openInclusion X U :=
    Over.OverMorphism.ext ha₀.symm
  letI : LocallyOfFiniteType Z.hom := by rw [← Over.w a.inv]; infer_instance
  letI : QuasiCompact Z.hom := by rw [← Over.w a.inv]; infer_instance
  letI : IsSeparated Z.hom := by rw [← Over.w a.inv]; infer_instance
  letI : Nonempty (ComplexPoint Z) := ⟨Point.map a.hom (Classical.choice inferInstance)⟩
  obtain ⟨E, hE, hsourceE, hvalueE⟩ := s4_q3_holomorphic_chart_iso_transport a r c e he
  obtain ⟨F, hF, hsourceF, hvalueF⟩ :=
    a3b4a_classHolomorphicChart_openTransport X U r c E hE
  refine ⟨F, hF, ?_, ?_⟩
  · rw [hsourceF, hsourceE, Set.image_image]
    have hf : (Point.map (ComplexPoint.openInclusion X U) ∘ Point.map a.hom) = Point.map j := by
      funext y
      rw [hj, Point.map_comp_apply]
      rfl
    change (Point.map (ComplexPoint.openInclusion X U) ∘ Point.map a.hom) '' e.source = _
    rw [hf]
  · intro y
    rw [hj, Point.map_comp_apply, hvalueF, hvalueE]

end HodgeLean.Foundations.Program
