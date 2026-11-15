import HodgeLean.Foundations.QuotientDuality.LocalOrbitOrientationNeighborhood
import HodgeLean.Foundations.QuotientDuality.LocalOrbitRelativeGenerator
import HodgeLean.Foundations.QuotientDuality.LocalOrbitSupportMap

/-! Coherent rational orientations on finite orbit spaces without an absolute source class. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

theorem finite_orbit_coherent_orientation
    (G : Type) [Group G] [Fintype G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] [T2Space X] [PseudoMetrizableSpace X]
    [T2Space (orbitSpace G X)] [PseudoMetrizableSpace (orbitSpace G X)]
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (x : orbitSpace G X) (U : Opens (orbitSpace G X)), x ∈ U →
      ∃ V : Opens (orbitSpace G X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) (o : LocalRationalOrientation X n)
    (hp : ∀ (g : G) (x : X), relativeHomologyMap ℚ n
      (pointDeckMap G X g x) (o.generator x) = o.generator (g⁻¹ • x)) :
    Nonempty (LocalRationalOrientation (orbitSpace G X) n) := by
  choose c hc hfixed using orbit_relative_orientation_class G X n o hp
  refine ⟨{
    generator := fun y => relativeHomologyMap ℚ n (orbitComplementPairMap G X y) (c y)
    generates := fun y => orbit_relative_class_generates G X hX hY n o y (c y) (hc y) (hfixed y)
    vanishes := fun y i hi => orbit_local_homology_concentrated G X hX hY n o.vanishes y i hi
    coherent := ?_ }⟩
  intro y
  obtain ⟨V, hyV, w, hw⟩ := orbit_orientation_neighborhood G X n o y (c y) (hc y)
  let v := relativeHomologyMap ℚ n (orbitSupportPairMap G X (V : Set (orbitSpace G X))) w
  refine ⟨V, hyV, v, fun z hz => ?_⟩
  have hpre : {x : X | orbitMap G X x = z} ⊆
      orbitMap G X ⁻¹' (V : Set (orbitSpace G X)) := by
    intro x hx
    change orbitMap G X x ∈ V
    rw [show orbitMap G X x = z from hx]
    exact hz
  let Rz : TopPair.ofSubset (X := X)
      (orbitMap G X ⁻¹' (V : Set (orbitSpace G X)))ᶜ ⟶ orbitComplementPair G X z :=
    supportInclusionPairMap X hpre
  have hcw : relativeHomologyMap ℚ n Rz w = c z := by
    apply sub_eq_zero.mp
    apply finite_support_detects_zero X {x : X | orbitMap G X x = z}
      (orbit_fiber_finite G X z) n
    intro x hx
    have he : relativeHomologyMap ℚ n (orbitPointRestriction G X z x hx)
        (relativeHomologyMap ℚ n Rz w) = o.generator x := by
      exact (relativeHomologyMap_supportInclusion_trans
        (M := X) (Set.singleton_subset_iff.mpr hx) hpre n w).trans (hw x (hpre hx))
    change relativeHomologyMap ℚ n (orbitPointRestriction G X z x hx)
      (relativeHomologyMap ℚ n Rz w - c z) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (he.trans (hc z x hx).symm)
  have hsquare := congrArg (fun f => relativeHomologyMap ℚ n f w)
    (orbit_support_restriction_square G X (V : Set (orbitSpace G X)) z hz)
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at hsquare
  exact hsquare.symm.trans ((congrArg
    (relativeHomologyMap ℚ n (orbitComplementPairMap G X z)) hcw))

#print axioms finite_orbit_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
