import HodgeLean.Foundations.Program.SchoenTransferR2DisjointFlatCharts
import HodgeLean.Foundations.Program.SchoenTransferR2DeformationCup
import HodgeLean.Foundations.Program.SchoenTransferR2SigmaCohomology
import HodgeLean.Foundations.Program.SchoenCycleC2SupportedSumHelpers

/-! # Cup annihilation for finite disjoint compact components

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Topology
namespace HodgeLean.Foundations.Program

/-- Zero restriction to each disjoint compact flat component annihilates every
class supported on a subset of their union. The disjoint union and neighbourhood
factor are the actual topological maps.
Source: Hatcher, Algebraic Topology, §0 and §§3.1–3.2.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_finite_component_cup_eq_zero
    {A : Type} [Finite A] (X : TopCat.{0}) [T2Space X] [LocallyCompactSpace X]
    (Q : A → TopCat.{0}) [∀ i, CompactSpace (Q i)]
    (j : ∀ i, Q i ⟶ X) (hj : ∀ i, IsClosedEmbedding (j i))
    (hdisj : Pairwise (fun i l => Disjoint (Set.range (j i)) (Set.range (j l))))
    (hcharts : ∀ i x, x ∈ Set.range (j i) → ∃ r c : ℕ,
      ∃ e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin c → ℂ)),
        x ∈ e.source ∧ ∀ y ∈ e.source, y ∈ Set.range (j i) ↔ (e y).2 = 0)
    (T : Closeds X) (hT : (T : Set X) ⊆ ⋃ i, Set.range (j i)) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (T : Set X)ᶜ) p)
    (u : Cohomology ℚ X q) (hu : ∀ i, cohomologyMap ℚ q (j i) u = 0) :
    HodgeLean.Foundations.Singular.cup X rfl
      (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (T : Set X)ᶜ) p a) u = 0 := by
  classical
  letI := Fintype.ofFinite A
  let K : A → Closeds X := fun i => ⟨Set.range (j i), (hj i).isClosed_range⟩
  let S : Closeds X := ⟨⋃ i, Set.range (j i),
    isClosed_iUnion_of_finite (fun i => (hj i).isClosed_range)⟩
  let J : TopCat.of (Σ i, Q i) ⟶ X := TopCat.ofHom
    ⟨fun x => j x.1 x.2, continuous_sigma (fun i => (j i).hom.continuous)⟩
  have hJinj : Function.Injective J := by
    rintro ⟨i, x⟩ ⟨l, y⟩ he
    by_cases hil : i = l
    · subst l
      exact congrArg (Sigma.mk i) ((hj i).injective he)
    · exact (Set.disjoint_left.mp (hdisj hil) ⟨x, rfl⟩ ⟨y, he.symm⟩).elim
  have hJ : IsClosedEmbedding J := J.hom.continuous.isClosedEmbedding hJinj
  have hS : (S : Set X) = Set.range J := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i, y⟩, hy⟩
    · rintro ⟨⟨i, y⟩, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, y, rfl⟩
  have hcompact : IsCompact (S : Set X) := by
    rw [hS]
    exact isCompact_range J.hom.continuous
  have hflat := s4_assembly_disjoint_union_flat_charts K hdisj hcharts
  obtain ⟨F, ⟨H⟩, _, V, hV, hF⟩ :=
    s4_assembly_compact_flat_deformation (S : Set X) hcompact hflat
  have huJ : cohomologyMap ℚ q J u = 0 := by
    apply s4_assembly_sigma_cohomology_eq_zero Q q
    intro i
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    change cohomologyMap ℚ q (j i) u = 0
    exact hu i
  have hz := s4_assembly_deformation_cup_eq_zero X (TopCat.of (Σ i, Q i)) J hJ.isEmbedding
    S hS V hV F H hF p q (enlargeSupport ℚ X hT p a) u huJ
  change HodgeLean.Foundations.Singular.cup X rfl
    (forgetSupport ℚ X (S : Set X) p (enlargeSupport ℚ X hT p a)) u = 0 at hz
  have he : forgetSupport ℚ X (S : Set X) p (enlargeSupport ℚ X hT p a) =
      relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (T : Set X)ᶜ) p a :=
    s2e_enlargeSupport_absolute X hT p a
  exact (congrArg (fun z => HodgeLean.Foundations.Singular.cup X rfl z u) he).symm.trans hz

#print axioms s4_assembly_finite_component_cup_eq_zero
end HodgeLean.Foundations.Program
