import HodgeLean.Foundations.QuotientDuality.OrientationDescent

/-! Neighborhoods of finite quotient fibres. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem orbit_saturated_neighborhood (G : Type) [Group G] [Finite G]
    (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]
    (y : orbitSpace G X) (U : Opens X)
    (hU : ∀ x : X, orbitMap G X x = y → x ∈ U) :
    ∃ V : Opens (orbitSpace G X), y ∈ V ∧
      ∀ x : X, orbitMap G X x ∈ V → x ∈ U := by
  let V : Opens (orbitSpace G X) :=
    ⟨(orbitMap G X '' (U : Set X)ᶜ)ᶜ,
      ((orbitMap_isClosedMap G X) _ U.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hU x hxy)
  · intro x hx
    by_contra hxu
    exact hx ⟨x, hxu, rfl⟩

#print axioms orbit_saturated_neighborhood
end HodgeLean.Foundations.QuotientDuality
