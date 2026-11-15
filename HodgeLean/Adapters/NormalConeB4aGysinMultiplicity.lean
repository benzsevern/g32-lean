import HodgeLean.Adapters.NormalConeB4aGysinSupport
import HodgeLean.Adapters.NormalConeB4aClassMultiplicity

/-! # Generic lengths in the local fibre multiplicity

At a point on just one component, the analytic normalization coefficient is
the length of the generic local ring of the scheme-theoretic image.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The local image-cycle multiplicity retains the full generic local-ring length. -/
theorem a3b4a_gysin_multiplicity_eq_genericLength
    {Z K : Scheme.{0}} [IsNoetherian Z]
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q] (i : K ⟶ Z)
    (y : genericPoints i.ker.subscheme) (x : ComplexPoint (Over.mk q))
    (hx : x.underlying ∈ closure ({i.ker.subschemeι y.1} : Set Z))
    (hother : ∀ η ∈ (a3b3_imageCycle i inferInstance).support,
      η ≠ i.ker.subschemeι y.1 → x.underlying ∉ closure ({η} : Set Z)) :
    a3b4_multiplicity q (a3b3_imageCycle i inferInstance) x =
      (a3b2_genericLength i.ker (a3b2_length_ne_top_of_isLocallyNoetherian _) y : ℚ) := by
  have hy : i.ker.subschemeι y.1 ∈ (a3b3_imageCycle i inferInstance).support := by
    rw [a3b3_imageCycle, a3b4a_gysin_idealCycle_support]
    exact ⟨y.1, y.2, rfl⟩
  rw [a3b4a_classMultiplicity_eq_component q _ _ hy x hx hother]
  exact a3b2_idealCycle_apply i.ker _ _ y

end HodgeLean.Adapters
