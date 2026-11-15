import HodgeLean.Foundations.Program.SchoenTransferQ3SliceNormalCoclass

/-! Restriction of the actual point coclass to its normal neighbourhood. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicGeometry.SingularCycles
attribute [local irreducible] localClassOfChart normalizedRelativeCoclass
namespace HodgeLean.Foundations.Program

/-- Open excision restricts the specified point coclass to the exact
normal-projection coclass, preserving the ordered complex normalization. -/
theorem s4_q3_point_coclass_restrict_to_normal
    {M : Type} [TopologicalSpace M] [T1Space M] (d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (x : M) (hx : x ∈ e.source) (he : e x = 0) :
    relativeCohomologyMap ℚ (2 * d)
      (neighborhoodPointComplementPairMap
        (flattenedSupportNeighborhood (Fin 0 → ℂ) d e x hx) x)
      (normalizedRelativeCoclass
        (localClassOfChart d (pointChart e) x ⟨hx, Set.mem_univ _⟩)
        (s4_q3_centred_point_class_ne_zero d e x hx he)) =
      chartNormalProjectionCoclass (Fin 0 → ℂ) d e {x}
        (s4_q3_zero_tangent_chart_flattens_point d e x hx he)
        (flattenedSupportNeighborhood (Fin 0 → ℂ) d e x hx)
        (flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d e x hx) := by
  apply chartNormalProjectionCoclass_unique (Fin 0 → ℂ) d e {x}
    (s4_q3_zero_tangent_chart_flattens_point d e x hx he) x hx (congrArg Prod.snd he)
  let J := neighborhoodPointComplementPairMap
    (flattenedSupportNeighborhood (Fin 0 → ℂ) d e x hx) x
  let α := normalizedRelativeCoclass
    (localClassOfChart d (pointChart e) x ⟨hx, Set.mem_univ _⟩)
    (s4_q3_centred_point_class_ne_zero d e x hx he)
  let v := flattenedSupportNormalClass (Fin 0 → ℂ) d e x hx {x}
    (s4_q3_zero_tangent_chart_flattens_point d e x hx he) (congrArg Prod.snd he)
  have hnat := relativeCohomologyEquivDualHomology_relativeCohomologyMap ℚ (2 * d) J α v
  have hclass := s4_q3_point_normal_class_to_local_class d e x hx he
    (s4_q3_zero_tangent_chart_flattens_point d e x hx he)
  have heval := congrArg (fun w => relativeCohomologyEquivDualHomology ℚ
    (pointComplementPair x) (2 * d) α w) hclass
  exact hnat.trans (heval.trans (by
    simp only [α, relativeCohomologyEquivDualHomology_normalizedRelativeCoclass,
      normalizedDual_apply_self]))

end HodgeLean.Foundations.Program
