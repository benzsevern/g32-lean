import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPointCoclassRestriction
import HodgeLean.Adapters.NormalConeB4aClassHolomorphicOverlap
import HodgeLean.Adapters.NormalConeB4aClassMultiplicity

/-! # Native cycle normalization of the actual coordinate-point coclass -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual selected native point chart contains the entire literal coordinate-point cycle support. -/
theorem normalComponentPointChart_support_subset_source
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    a3b4_cycleSupport Q.hom (s2e_componentCycle (s2c_subschemeι Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) ⊆
      (normalComponentPointChart k eQ).source := by
  intro q hq
  obtain ⟨p, rfl⟩ := (normalComponentHomeomorph k eQ).surjective q
  have hp := (normalComponentHomeomorph_cycle_support k eQ p).mp hq
  rw [hp]
  exact normalComponentPointChart_param_mem k eQ 0

#print axioms normalComponentPointChart_support_subset_source
/-- Every actual single-component cycle has coefficient-one multiplicity at each point of its analytic support. -/
theorem componentCycle_multiplicity_one
    {Z Q : Over (Spec ↧ℂ)} [IsIntegral Z.left] [QuasiCompact Q.hom]
    (ι : Z ⟶ Q) (x : ComplexPoint Q)
    (hx : x ∈ a3b4_cycleSupport Q.hom (s2e_componentCycle ι ℚ)) :
    a3b4_multiplicity Q.hom (s2e_componentCycle ι ℚ) x = 1 := by
  classical
  let γ := s2e_componentCycle ι ℚ
  let p := ι.left (genericPoint Z.left)
  have hs : γ.support = {p} := s2e_componentCycle_support ι
  have hp : p ∈ γ.support := by rw [hs]; exact Set.mem_singleton p
  have hxp : x.underlying ∈ closure ({p} : Set Q.left) := by
    change x.underlying ∈ ⋃ ξ ∈ γ.support, closure ({ξ} : Set Q.left) at hx
    simpa only [hs, Set.biUnion_singleton] using hx
  have hother : ∀ η ∈ γ.support, η ≠ p →
      x.underlying ∉ closure ({η} : Set Q.left) := by
    intro η hη hne
    rw [hs] at hη
    exact (hne (Set.mem_singleton_iff.mp hη)).elim
  rw [a3b4a_classMultiplicity_eq_component Q.hom γ p hp x hxp hother]
  change (s2e_componentCycle ι ℚ) (ι.left (genericPoint Z.left)) = 1
  simp only [s2e_componentCycle, Function.locallyFinsuppWithin.single_apply, ite_true]

#print axioms componentCycle_multiplicity_one
/-- The constructed global coordinate-point coclass is a normalized representative of its literal actual component cycle. -/
theorem normalComponentPointCoclass_isCycleClass
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    a3b4_IsCycleClass Q.hom (s2e_componentCycle (s2c_subschemeι Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
        (normalComponentPointCoclass k eQ) := by
  intro r e' hS' x hx' hxS he'
  have hx := normalComponentPointChart_support_subset_source k eQ hxS
  obtain ⟨W, hW, hW', hxW, hnorm⟩ :=
    a3b4a_classHolomorphicChart_normalCoclass_overlap Q
      (normalComponentPointChart k eQ) e' (normalComponentPointChart_holomorphic k eQ) he'
      _ (normalComponentPointChart_support k eQ) hS' x hx hx' hxS
  refine ⟨(W : Set (ComplexPoint Q)), hW', W.isOpen, hxW, ?_⟩
  apply (normalComponentPointCoclass_neighborhood k eQ W hW).trans
  rw [componentCycle_multiplicity_one (s2c_subschemeι Q
    ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) x hxS, one_smul]
  exact hnorm

#print axioms normalComponentPointCoclass_isCycleClass
end HodgeLean.Foundations.Program.G32Native.EulerModel
