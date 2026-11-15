import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.SingularMultiplicityLocal
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.PrimeComponentSeparation
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.CycleSeparatedPoints
import HodgeLean.Adapters.NormalConeB4aClassMultiplicity

/-! # Local multiplicity one in étale inverse-image charts

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace HodgeLean.Adapters
open HodgeLean.Foundations.Analytic Set Filter Topology
namespace AlgebraicGeometry.SingularCycles

/-- The local multiplicity of an étale inverse-image prime is one in every tested holomorphic chart.
Source: Fulton, Intersection Theory, second edition, §1.7; local constancy and separated component points. -/
theorem etale_prime_chart_multiplicity_one {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [Etale f.left] (ξ : Z.left) {r k : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (he : a3b4_IsHolChart X.hom e)
    (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom (ccm3_flatPullbackPrime f.left ξ) ↔
      (e y).2 = 0)
    (x : ComplexPoint X) (hx : x ∈ e.source)
    (hxS : x ∈ a3b4_cycleSupport X.hom (ccm3_flatPullbackPrime f.left ξ)) :
    a3b4_multiplicity X.hom (ccm3_flatPullbackPrime f.left ξ) x = 1 := by
  let γ := ccm3_flatPullbackPrime f.left ξ
  obtain ⟨W, _, hxW, hmult⟩ := singular_chart_multiplicity_locally_constant
    X.hom γ e he hS x hx hxS
  have hanti : ∀ a ∈ γ.support, ∀ b ∈ γ.support,
      a ∈ closure ({b} : Set X.left) → a = b := by
    intro a ha b hb hab
    exact prime_pullback_support_no_specialization f ξ a b ha hb hab
  obtain ⟨a, y, ha, hyW, hya, hother⟩ :=
    cycle_exists_separated_point_in_open X γ hanti
      (W : Set (ComplexPoint (Over.mk X.hom))) W.isOpen x hxW hxS
  have hyS : y ∈ a3b4_cycleSupport X.hom γ := Set.mem_iUnion₂.mpr ⟨a, ha, hya⟩
  have hyM := a3b4a_classMultiplicity_eq_component X.hom γ a ha y hya hother
  have hcoeff : γ a = 1 := etale_prime_coefficient_one f ξ a ha
  exact (hmult y hyW hyS).symm.trans (hyM.trans hcoeff)

end AlgebraicGeometry.SingularCycles
