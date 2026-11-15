import HodgeLean.Adapters.SupportedCycleClasses
import HodgeLean.Foundations.Program.SchoenCycleC2WeightedRestrictionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2OrbitNeighbourhoodHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Finite disjoint normalized component representatives give a normalized
representative of every rational weighted orbit cycle. -/
theorem s2e_rationalOrbitCycle_normalized_sum
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (k m : ℕ)
    (himm : ∀ t : Fin m, IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left)
    (hdisj : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of δ ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of δ ^ t.val).asHom).left))
    (c : ∀ t : Fin m,
      s2e_supportedClass W (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k)
    (hc : ∀ t : Fin m, a3b4_IsCycleClass W.hom
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k (c t))
    (a : Fin m → ℚ) :
    ∃ b : s2e_supportedClass W (s2e_rationalOrbitCycle ι δ m a) k,
      a3b4_IsCycleClass W.hom (s2e_rationalOrbitCycle ι δ m a) k b ∧
      s2e_classToAbsolute W (s2e_rationalOrbitCycle ι δ m a) k b =
        ∑ t : Fin m, a t • s2e_classToAbsolute W
          (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k (c t) := by
  let X := a3b4_an W.hom
  let S : Fin m → Set X := fun t => a3b4_cycleSupport W.hom
    (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ)
  have hS (t : Fin m) : S t = Point.underlying ⁻¹'
      Set.range (ι ≫ (End.of δ ^ t.val).asHom).left := by
    let := himm t
    exact s2e_componentCycle_analytic_support _
  have hclosed (t : Fin m) : IsClosed (S t) := by
    let := himm t
    rw [hS]
    exact (ι ≫ (End.of δ ^ t.val).asHom).left.isClosedEmbedding.isClosed_range.preimage
      (ComplexPoint.continuous_underlying_to_zariski W)
  have hsd : ∀ s t, s ≠ t → Disjoint (S s) (S t) := by
    intro s t hst
    rw [hS, hS]
    exact Set.disjoint_left.mpr fun _ hx hy => Set.disjoint_left.mp (hdisj s t hst) hx hy
  unfold s2e_supportedClass s2e_classToAbsolute s2e_rationalOrbitCycle
  exact SupportedCycleClasses.normalized_sum (ι := Fin m) (Z := W.left) W.hom k
    (fun t => s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ)
    hclosed hsd c hc a

end HodgeLean.Foundations.Program
