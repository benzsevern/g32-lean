import HodgeLean.RealDefs.ComplexFundamentalClassParts.C_OpenLift
import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs

/-! Local representatives of an arbitrary point-local singular class. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TopologicalSpace AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

theorem point_class_open_lift (X : TopCat.{0}) [T2Space X] (n : ℕ) (x : X)
    (α : orientationGroup X n x) :
    ∃ (U : Opens X) (hx : x ∈ U),
      ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n,
        relativeHomologyMap ℚ n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) c = α := by
  obtain ⟨W, hW, hxW, hlift⟩ := C_exists_open_lift ({x} : Set X) n α
  obtain ⟨c, hc⟩ := hlift W hxW Set.Subset.rfl
  exact ⟨⟨W, hW⟩, hxW rfl, c, hc⟩

#print axioms point_class_open_lift
end HodgeLean.Foundations.QuotientDuality
