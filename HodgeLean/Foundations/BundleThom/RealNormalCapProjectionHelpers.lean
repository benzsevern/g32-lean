import HodgeLean.Foundations.BundleThom.ProductSecondSubsetHelpers

/-! # Projection from actual product cap domains

HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Projection from either actual product cap is a rational chain quasi-isomorphism over every base.
Source: Hatcher, Algebraic Topology, §2.2, contraction of hemisphere domains in Mayer–Vietoris. -/
theorem i1_realNormalCapProjection_quasiIso (B : Type) [TopologicalSpace B]
    (d : ℕ) (positive : Bool) :
    QuasiIso
      ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ))).map
        (TopCat.ofHom (⟨fun p : {p : B × (Fin (d + 1) → ℝ) |
          p.2 ∈ i1_realNormalCap d positive} => p.1.1,
          continuous_fst.comp continuous_subtype_val⟩))) := by
  letI := i1_realNormalCap_contractible d positive
  exact i1_productSecondSubsetProjection_quasiIso B (Fin (d + 1) → ℝ)
    (i1_realNormalCap d positive)

end HodgeLean.Foundations.BundleThom
