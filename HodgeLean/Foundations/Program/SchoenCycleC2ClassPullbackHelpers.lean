import HodgeLean.Foundations.Program.SchoenCycleC2ClassDescentHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Component class pullback retains normalization when holomorphic charts
transport to the image with unchanged coordinates. -/
theorem s2e_componentCycle_normalized_open_pullback
    {Q V W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (j : Q ⟶ V) (i : V ⟶ W)
    [IsClosedImmersion j.left] [IsOpenImmersion i.left]
    [IsClosedImmersion (j ≫ i).left]
    (hf : Topology.IsOpenEmbedding (Point.map i)) (k : ℕ)
    (hcharts : ∀ (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint V) ((Fin r → ℂ) × (Fin k → ℂ))),
      a3b4_IsHolChart V.hom e → ComplexPoint V →
      ∃ E : OpenPartialHomeomorph (ComplexPoint W) ((Fin r → ℂ) × (Fin k → ℂ)),
        a3b4_IsHolChart W.hom E ∧ E.source = Point.map i '' e.source ∧
        ∀ z, E (Point.map i z) = e z)
    (cV : s2e_supportedClass V (s2e_componentCycle j ℚ) k)
    (cW : s2e_supportedClass W (s2e_componentCycle (j ≫ i) ℚ) k)
    (hcW : a3b4_IsCycleClass W.hom (s2e_componentCycle (j ≫ i) ℚ) k cW)
    (hres : relativeCohomologyMap ℚ (2 * k) (s2e_componentOpenPairMap j i) cW = cV) :
    a3b4_IsCycleClass V.hom (s2e_componentCycle j ℚ) k cV := by
  let X := a3b4_an V.hom
  let Y := a3b4_an W.hom
  let f : X ⟶ Y := TopCat.ofHom (Point.continuousMap i)
  let S : Set X := a3b4_cycleSupport V.hom (s2e_componentCycle j ℚ)
  let T : Set Y := a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ)
  have hST : ∀ z, f z ∈ T ↔ z ∈ S := fun z =>
    (Set.ext_iff.mp (s2e_componentCycle_support_open_preimage j i) z).symm
  intro r e hflat x hx hxS he
  obtain ⟨E, hE, hsource, hval⟩ := hcharts r e he x
  have hflatT : ∀ y ∈ E.source, y ∈ T ↔ (E y).2 = 0 := by
    intro y hy
    rw [hsource] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [hval z]
    exact (hST z).trans (hflat z hz)
  have hfxE : Point.map i x ∈ E.source := by
    rw [hsource]
    exact ⟨x, hx, rfl⟩
  have hfxT : Point.map i x ∈ T := (hST x).mpr hxS
  obtain ⟨N, hNE, hNo, hfxN, hnorm⟩ := hcW r E hflatT (Point.map i x) hfxE hfxT hE
  have hfxrange : (Point.map i x).underlying ∈ Set.range (j ≫ i).left := by
    have h := hfxT
    change Point.map i x ∈ a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ) at h
    rw [s2e_componentCycle_analytic_support] at h
    exact h
  rw [s2e_componentCycle_multiplicity (W := W) (j ≫ i) (Point.map i x) hfxrange,
    one_smul] at hnorm
  let N' : Set X := f ⁻¹' N
  have hN'e : N' ⊆ e.source := by
    intro y hy
    have h := hNE hy
    rw [hsource] at h
    obtain ⟨z, hz, hzy⟩ := h
    exact hf.injective hzy ▸ hz
  have hN'o : IsOpen N' := hNo.preimage (Point.continuousMap i).continuous
  have hxN' : x ∈ N' := hfxN
  have hImage : f '' N' = N := Set.image_preimage_eq_of_subset (by
    intro y hy
    have h := hNE hy
    rw [hsource] at h
    obtain ⟨z, _, rfl⟩ := h
    exact ⟨z, rfl⟩)
  have hImageE : f '' N' ⊆ E.source := fun _ hy => hNE (hImage.le hy)
  have hxrange : x.underlying ∈ Set.range j.left := by
    have h := hxS
    rw [s2e_componentCycle_analytic_support] at h
    exact h
  refine ⟨N', hN'e, hN'o, hxN', ?_⟩
  rw [s2e_componentCycle_multiplicity (W := V) j x hxrange, one_smul]
  let I := s2e_embeddingNeighbourhoodPairIso f hf.isEmbedding S T hST N'
  have hlocal : relativeCohomologyMap ℚ (2 * k) I.hom
      (relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap (f '' N') T) cW) =
      relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap N' S) cV := by
    dsimp only [I]
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      s2e_embeddingNeighbourhoodPairIso_naturality,
      relativeCohomologyMap_comp, LinearMap.comp_apply]
    exact congrArg (relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap N' S)) hres
  have hnorm' : relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap (f '' N') T) cW =
      chartNormalProjectionCoclass (Fin r → ℂ) k E T hflatT (f '' N') hImageE := by
    have hm := a3b4a_classLocal_normalization_mono E T hflatT hImage.le hNE cW 1
      (by rw [one_smul]; exact hnorm)
    rw [one_smul] at hm
    exact hm
  exact hlocal.symm.trans ((congrArg (relativeCohomologyMap ℚ (2 * k) I.hom) hnorm').trans
    (s2e_embeddingNeighbourhoodPairIso_normalCoclass f hf.isEmbedding S T hST
      r k e E hflat hflatT N' hN'e hImageE (fun y _ => (hval y).symm)))

end HodgeLean.Foundations.Program
