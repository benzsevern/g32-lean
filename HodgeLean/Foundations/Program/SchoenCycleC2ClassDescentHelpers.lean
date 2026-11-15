import HodgeLean.Foundations.Program.SchoenCycleC2ComponentPairHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2EmbeddingPairHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ChartPullbackHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2MultiplicityHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A component class transferred from an open immersion retains its local
complex normal projection normalization. -/
theorem s2e_componentCycle_normalized_open_descent
    {Q V W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (j : Q ⟶ V) (i : V ⟶ W)
    [IsClosedImmersion j.left] [IsOpenImmersion i.left]
    [IsClosedImmersion (j ≫ i).left]
    (hf : Topology.IsOpenEmbedding (Point.map i))
    (hcover : a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ) ⊆
      Set.range (Point.map i)) (k : ℕ)
    (cV : s2e_supportedClass V (s2e_componentCycle j ℚ) k)
    (cW : s2e_supportedClass W (s2e_componentCycle (j ≫ i) ℚ) k)
    (hcV : a3b4_IsCycleClass V.hom (s2e_componentCycle j ℚ) k cV)
    (hres : relativeCohomologyMap ℚ (2 * k) (s2e_componentOpenPairMap j i) cW = cV) :
    a3b4_IsCycleClass W.hom (s2e_componentCycle (j ≫ i) ℚ) k cW := by
  let X := a3b4_an V.hom
  let Y := a3b4_an W.hom
  let f : X ⟶ Y := TopCat.ofHom (Point.continuousMap i)
  let S : Set X := a3b4_cycleSupport V.hom (s2e_componentCycle j ℚ)
  let T : Set Y := a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ)
  have hST : ∀ z, f z ∈ T ↔ z ∈ S := fun z =>
    (Set.ext_iff.mp (s2e_componentCycle_support_open_preimage j i) z).symm
  intro r e hflat x hx hxT he
  obtain ⟨z, hz⟩ := hcover hxT
  have hzS : z ∈ S := (hST z).mp (by
    change Point.map i z ∈ T
    rw [hz]
    exact hxT)
  letI : Nonempty (ComplexPoint V) := ⟨z⟩
  obtain ⟨E, hE, hsource, hval⟩ :=
    s2e_holomorphicChart_openEmbedding_pullback V W i hf r k e he
  have hflatS : ∀ y ∈ E.source, y ∈ S ↔ (E y).2 = 0 := by
    intro y hy
    rw [hval y]
    apply (hST y).symm.trans
    apply hflat
    rwa [hsource] at hy
  have hzE : z ∈ E.source := by
    rw [hsource]
    change Point.map i z ∈ e.source
    rw [hz]
    exact hx
  obtain ⟨N', hNE, hN'o, hzN, hnorm⟩ := hcV r E hflatS z hzE hzS hE
  have hzrange : z.underlying ∈ Set.range j.left := by
    have h := hzS
    change z ∈ a3b4_cycleSupport V.hom (s2e_componentCycle j ℚ) at h
    rw [s2e_componentCycle_analytic_support] at h
    exact h
  rw [s2e_componentCycle_multiplicity (W := V) j z hzrange, one_smul] at hnorm
  let N : Set Y := f '' N'
  have hNe : N ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hNE hy
    rwa [hsource] at h
  have hNo : IsOpen N := hf.isOpenMap _ hN'o
  have hxN : x ∈ N := ⟨z, hzN, hz⟩
  refine ⟨N, hNe, hNo, hxN, ?_⟩
  have hxrange : x.underlying ∈ Set.range (j ≫ i).left := by
    have h := hxT
    rw [s2e_componentCycle_analytic_support] at h
    exact h
  rw [s2e_componentCycle_multiplicity (W := W) (j ≫ i) x hxrange, one_smul]
  let I := s2e_embeddingNeighbourhoodPairIso f hf.isEmbedding S T hST N'
  have hI : Function.Injective (relativeCohomologyMap ℚ (2 * k) I.hom) :=
    (s2e_relativeCohomologyMap_bijective_of_homology I.hom (2 * k)
      (ConcreteCategory.bijective_of_isIso ((relativeHomologyFunctor ℚ (2 * k)).map I.hom))).1
  apply hI
  have hlocal : relativeCohomologyMap ℚ (2 * k) I.hom
      (relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap N T) cW) =
      relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap N' S) cV := by
    dsimp only [I, N]
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      s2e_embeddingNeighbourhoodPairIso_naturality,
      relativeCohomologyMap_comp, LinearMap.comp_apply]
    exact congrArg (relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap N' S)) hres
  rw [hlocal]
  exact hnorm.trans (s2e_embeddingNeighbourhoodPairIso_normalCoclass f hf.isEmbedding S T hST
    r k E e hflatS hflat N' hNE hNe (fun y _ => hval y)).symm

end HodgeLean.Foundations.Program
