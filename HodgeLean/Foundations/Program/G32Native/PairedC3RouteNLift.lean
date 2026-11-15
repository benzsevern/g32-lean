import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSplittingMaps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- N.1: the quotient's unit section lifts through the original projection.
Source: Hartshorne, Algebraic Geometry, III.5.1 and the cohomology sequence. -/
theorem paired_c3_route_n_lift_aux
    (k a b : ℕ) (hk : 0 < k) (hrank : a + (b + 1) = k)
    (j : Fin (k + 1)) (E : ShortComplex (pairedC3Proj k).Modules)
    (hE : E.ShortExact) (hqc : E.X₂.IsQuasicoherent)
    (hframes : ∀ x : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E.X₂ ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) :
          U.toScheme.Modules)))
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a (b + 1))
    (e₃ : E.X₃ ≅ pairedC3HyperplaneQuotient k j) :
    ∃ (q : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₃),
      Epi q ∧ ∃ s, s ≫ E.g = q := by
  letI : Epi (pairedC3HyperplaneUnit k j) := paired_c3_hyperplane_unit_epi k j
  obtain ⟨s, hs⟩ := paired_c3_modification_unit_lift k a (b + 1) hk j E hE hqc e₁ e₃
  exact ⟨pairedC3HyperplaneUnit k j ≫ e₃.inv, inferInstance, s, hs⟩

end HodgeLean.Foundations.Program.G32Native
