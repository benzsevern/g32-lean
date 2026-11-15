import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-! # Evaluation on neighbourhood orientation generators

Open excision transports the chart generator to the neighbourhood. Evaluation
naturality then determines pullback on normalized coclasses.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace AlgebraicGeometry.SingularCycles

 theorem span_neighborhoodOrientation_eq_top
    {M : Type} [TopologicalSpace M] [T1Space M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (U : Set M) (hU : IsOpen U) (hxU : x ∈ U) :
    Submodule.span ℚ {neighborhoodOrientation d e x hx U hU hxU} = ⊤ := by
  let E := neighborhoodPointComplementRelativeHomologyIso U x hU hxU (2 * d)
  have hsurj : Function.Surjective E.inv.hom :=
    (ConcreteCategory.isIso_iff_bijective E.inv).mp inferInstance |>.2
  calc
    Submodule.span ℚ {neighborhoodOrientation d e x hx U hU hxU} =
        (Submodule.span ℚ {localClassOfChart d e x hx}).map E.inv.hom := by
      rw [Submodule.map_span, Set.image_singleton]
      rfl
    _ = (⊤ : Submodule ℚ _).map E.inv.hom := by
      rw [span_localClassOfChart_eq_top]
    _ = ⊤ := (Submodule.map_top _).trans (LinearMap.range_eq_top.mpr hsurj)

 theorem normalizedCoclass_pullback_of_generator
    {P Q : TopPair} (n : ℕ) (f : P ⟶ Q)
    (z : RelativeHomology ℚ P n) (hz : z ≠ 0)
    (w : RelativeHomology ℚ Q n) (hw : w ≠ 0)
    (hspan : Submodule.span ℚ {z} = ⊤) (a : ℚ)
    (hmap : relativeHomologyMap ℚ n f z = a • w) :
    relativeCohomologyMap ℚ n f (normalizedRelativeCoclass w hw) =
      a • normalizedRelativeCoclass z hz := by
  apply (relativeCohomologyEquivDualHomology ℚ P n).injective
  apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _ hspan).mpr
  rintro ⟨v, hv⟩
  obtain rfl := Set.mem_singleton_iff.mp hv
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    hmap, map_smul, normalizedRelativeCoclass_pairing_self,
    map_smul, LinearMap.smul_apply, normalizedRelativeCoclass_pairing_self]

end AlgebraicGeometry.SingularCycles
