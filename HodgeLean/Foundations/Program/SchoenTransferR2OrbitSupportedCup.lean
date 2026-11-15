import HodgeLean.Foundations.Program.SchoenTransferR2FiniteComponentCup
import HodgeLean.Foundations.Program.SchoenTransferR2ComponentFlatCharts
import HodgeLean.Adapters.NormalConeB4aClassSupport
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact

/-! # Supported cup annihilation on the actual finite component orbit

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program

/-- Zero restriction on every actual orbit component annihilates the supported
orbit class; normalization of that class is not needed for this implication.
Source: Hatcher, Algebraic Topology, §0 and §§3.1–3.2; actual flat component charts.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_orbit_supported_cup_eq_zero
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (k m : ℕ)
    (himm : ∀ t : Fin m, IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left)
    (hdisj : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of δ ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of δ ^ t.val).asHom).left))
    (hgeometry : ∀ t : Fin m,
      (∃ U : W.left.Opens, Set.range (ι ≫ (End.of δ ^ t.val).asHom).left ⊆ U ∧
        Smooth (U.ι ≫ W.hom)) ∧
      ∀ x ∈ (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ).support,
        Order.coheight x = k)
    (coeff : Fin m → ℚ)
    (cr : s2e_supportedClass W (s2e_rationalOrbitCycle ι δ m coeff) k)
    (u : Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * k))
    (hu : ∀ t : Fin m, s2e_pullback ℚ (ι ≫ (End.of δ ^ t.val).asHom) (2 * k) u = 0) :
    HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W))
      (show 2 * k + 2 * k = 2 * (2 * k) by omega)
      (s2e_classToAbsolute W (s2e_rationalOrbitCycle ι δ m coeff) k cr) u = 0 := by
  let X := TopCat.of (ComplexPoint W)
  letI : T2Space (ComplexPoint W) := f4_t2Space W
  letI : LocallyCompactSpace (ComplexPoint W) := an_locallyCompactSpace (f4_analytification W)
  let ρ (t : Fin m) := ι ≫ (End.of δ ^ t.val).asHom
  let j (t : Fin m) : TopCat.of (ComplexPoint Q) ⟶ X := TopCat.ofHom (Point.continuousMap (ρ t))
  have hj (t : Fin m) : Topology.IsClosedEmbedding (j t) := by
    letI := himm t
    exact ComplexPoint.isClosedEmbedding_map_of_closedImmersion (ρ t)
  have hdis : Pairwise (fun i l => Disjoint (Set.range (j i)) (Set.range (j l))) := by
    intro i l hil
    letI := himm i
    letI := himm l
    change Disjoint (Set.range (Point.map (ρ i))) (Set.range (Point.map (ρ l)))
    rw [ComplexPoint.range_map_of_isImmersion_of_comm W Q (ρ i),
      ComplexPoint.range_map_of_isImmersion_of_comm W Q (ρ l)]
    exact Set.disjoint_left.mpr fun _ hx hy => Set.disjoint_left.mp (hdisj i l hil) hx hy
  have hcharts (i : Fin m) : ∀ x ∈ Set.range (j i), ∃ r c : ℕ,
      ∃ e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin c → ℂ)),
        x ∈ e.source ∧ ∀ y ∈ e.source, y ∈ Set.range (j i) ↔ (e y).2 = 0 := by
    letI := himm i
    obtain ⟨U, hU, hsm⟩ := (hgeometry i).1
    exact s4_assembly_component_flat_charts (ρ i) k U hU hsm (hgeometry i).2
  let T : Closeds X := ⟨a3b4_cycleSupport W.hom (s2e_rationalOrbitCycle ι δ m coeff),
    a3b4a_classSupport_isClosed W.hom _⟩
  have hT : (T : Set X) ⊆ ⋃ i, Set.range (j i) := by
    intro x hx
    change x.underlying ∈ ⋃ ξ ∈ (s2e_rationalOrbitCycle ι δ m coeff).support, closure {ξ} at hx
    obtain ⟨ξ, hξ, hxξ⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (s2e_rationalOrbitCycle_support_subset ι δ m coeff hξ)
    rw [s2e_componentCycle_support] at hi
    obtain rfl := Set.mem_singleton_iff.mp hi
    letI := himm i
    have hr : x ∈ Set.range (j i) := by
      change x ∈ Set.range (Point.map (ρ i))
      rw [ComplexPoint.range_map_of_isImmersion_of_comm W Q (ρ i)]
      rwa [s2e_componentCycle_closure] at hxξ
    exact Set.mem_iUnion.mpr ⟨i, hr⟩
  have hz := s4_assembly_finite_component_cup_eq_zero X
    (fun _ : Fin m => TopCat.of (ComplexPoint Q)) j hj hdis hcharts T hT
    (2 * k) (2 * k) cr u hu
  have hzero (N : ℕ) (hN : 2 * k + 2 * k = N) :
      HodgeLean.Foundations.Singular.cup X hN
        (s2e_classToAbsolute W (s2e_rationalOrbitCycle ι δ m coeff) k cr) u = 0 := by
    subst N
    exact hz
  exact hzero _ _

#print axioms s4_assembly_orbit_supported_cup_eq_zero
end HodgeLean.Foundations.Program
