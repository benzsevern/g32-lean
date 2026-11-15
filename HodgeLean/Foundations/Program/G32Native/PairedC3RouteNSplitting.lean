import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Foundations.Program.G32Native.PairedC3LinearCommonZero
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSplittingSteps

/-! # A single hyperplane modification of a split projective bundle -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A rank-k bundle obtained by a hyperplane modification trades exactly
one negative summand for a trivial summand when the trivial rank is below k.
The quotient is the actual untwisted structure module of the hyperplane.
Source: Hartshorne, Algebraic Geometry, III.5.1; the hyperplane sequence
and the presentation by a lift of its constant section.
Open: negative-twist first-cohomology vanishing, lifting, and elimination
of a nonzero constant coefficient using the common zero of a linear system. -/
theorem paired_c3_route_n_splitting_aux
    (k a b : ℕ) (hk : 0 < k) (hrank : a + (b + 1) = k)
    (j : Fin (k + 1)) (E : ShortComplex (pairedC3Proj k).Modules)
    (hE : E.ShortExact) (hqc : E.X₂.IsQuasicoherent)
    (hframes : ∀ x : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E.X₂ ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) :
          U.toScheme.Modules)))
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a (b + 1))
    (e₃ : E.X₃ ≅ pairedC3HyperplaneQuotient k j) :
    Nonempty (E.X₂ ≅ pairedC3SplitBundle k (a + 1) b) := by
  obtain ⟨q, hq, s, hs⟩ := paired_c3_route_n_lift_aux
    k a b hk hrank j E hE hqc hframes e₁ e₃
  obtain ⟨T, hT, h₁, h₂, hf, hlocal⟩ := paired_c3_route_n_injection_aux
    k a b hk hrank j E hE hqc hframes e₁ e₃ q hq s hs
  obtain ⟨eQ⟩ := paired_c3_route_n_quotient_aux
    k a b hk hrank j E hE hqc hframes e₁ e₃ q hq s hs T hT h₁ h₂ hf
  obtain ⟨e⟩ := paired_c3_route_n_extension_split_aux k a b hk T hT
    (eqToIso h₁) eQ
  exact ⟨(eqToIso h₂).symm ≪≫ e⟩

end HodgeLean.Foundations.Program.G32Native
