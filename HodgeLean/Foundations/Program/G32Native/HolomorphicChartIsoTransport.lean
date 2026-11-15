import HodgeLean.Adapters.NormalConeB4aClassChartPullback

/-! # Holomorphic chart transport through the specified scheme isomorphism

The transported chart retains its whole source and all original coordinate values.
-/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Set Topology
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.TubularEuler

theorem holomorphic_chart_iso_transport
    (X Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (I : X ≅ Y) (r c : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) :
    ∃ a : OpenPartialHomeomorph (ComplexPoint Y) ((Fin r → ℂ) × (Fin c → ℂ)),
      a3b4_IsHolChart Y.hom a ∧
      a.source = Point.map I.hom '' e.source ∧
      ∀ y, a (Point.map I.hom y) = e y := by
  let H := Point.isoMapHomeomorph I
  let a := H.symm.toOpenPartialHomeomorph.trans e
  have heval (y : ComplexPoint X) : a (Point.map I.hom y) = e y := by
    change e (H.symm (H y)) = e y
    rw [H.symm_apply_apply]
  have hsource : a.source = Point.map I.hom '' e.source := by
    ext y
    change (y ∈ univ ∧ H.symm y ∈ e.source) ↔ _
    constructor
    · intro hy
      exact ⟨H.symm y, hy.2, H.apply_symm_apply y⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨mem_univ _, ?_⟩
      change H.symm (H z) ∈ e.source
      rwa [H.symm_apply_apply]
  have hsub : a.source ⊆ Point.map I.inv ⁻¹' e.source := fun _ hy => hy.2
  have hmap := f4_map_isHom I.inv
  refine ⟨a, ?_, hsource, heval⟩
  constructor
  · intro j
    exact anrem_isHolFun_restrict (f4_analytification Y) hsub
      (hmap.2 e.source e.open_source (fun y : e.source => (e y).1 j) (he.1 j))
  · intro j
    exact anrem_isHolFun_restrict (f4_analytification Y) hsub
      (hmap.2 e.source e.open_source (fun y : e.source => (e y).2 j) (he.2 j))

#print axioms holomorphic_chart_iso_transport
end HodgeLean.Foundations.TubularEuler
