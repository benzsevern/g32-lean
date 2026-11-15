import HodgeLean.Foundations.TubularEuler.NormalBundleDataHelpers
import HodgeLean.Foundations.TubularEuler.TransportRestrictionHelpers
import HodgeLean.Foundations.TubularEuler.TransverseCohomologyHelpers
import HodgeLean.Foundations.BundleResolution.ComplexBundleThomFibreHelpers

/-! # Local transverse computation for the supplied transported class

The maps of pairs retain both the original tube map and the supplied local coclass.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle Topology AlgebraicTopology.Singular
open HodgeLean.Foundations.Program HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.TubularEuler
open BundleThom BundleResolution

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
variable [SmoothOfRelativeDimension k Q.hom]
variable [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]

private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k
theorem transportedClass_fibre_of_local_normalization :
    let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
    letI := N.fiberBundle
    letI := N.vectorBundle
    ∀ (t : NormalTube ι k v j hj)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j))) [e.IsLinear ℂ]
    (x : ComplexPoint Q) (hx : x ∈ e.baseSet)
    (a : OpenPartialHomeomorph (ComplexPoint W) ((Fin k → ℂ) × (Fin k → ℂ)))
    (hs : ∀ y ∈ a.source, y ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔ (a y).2 = 0)
    (O : Set (ComplexPoint W)) (hO : IsOpen O) (hOa : O ⊆ a.source)
    (h0O : t.ambient (zeroSection (Fin k → ℂ) (i1_normalFibre j) x) ∈ O)
    (hnorm : relativeCohomologyMap ℚ (2 * k)
      (a3b4_neighborhoodPairMap O (a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ))) c =
      chartNormalProjectionCoclass (Fin k → ℂ) k a
        (a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ)) hs O hOa)
    (D : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ))
    (hD : HasFDerivAt (fun w : Fin k → ℂ =>
      (a (t.ambient (⟨x, (e.continuousLinearEquivAt ℂ x hx).symm w⟩ :
        TotalSpace (Fin k → ℂ) (i1_normalFibre j)))).2) D.toContinuousLinearMap 0),
    let E := analyticNormalComplexBundle j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
    relativeCohomologyMap ℚ (2 * k) (i1_complexBundleFibrePairMap E e x hx)
      (transportedClass ι k v j hj t c) = normalizedPointCoclass k := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  dsimp only
  intro t c e he x hx a hs O hO hOa h0O hnorm D hD
  letI := he
  let E := analyticNormalComplexBundle j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  let S := a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ)
  let J : C((Fin k → ℂ), TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
    ⟨fun w => ⟨x, (e.continuousLinearEquivAt ℂ x hx).symm w⟩,
      (FiberBundle.continuous_totalSpaceMk (Fin k → ℂ) (i1_normalFibre j) x).comp
        (e.continuousLinearEquivAt ℂ x hx).symm.continuous⟩
  have hJ0 : J 0 = zeroSection (Fin k → ℂ) (i1_normalFibre j) x := by
    change (⟨x, (e.continuousLinearEquivAt ℂ x hx).symm 0⟩ :
      TotalSpace (Fin k → ℂ) (i1_normalFibre j)) = ⟨x, 0⟩
    rw [map_zero]
  have hJne (w : Fin k → ℂ) (hw : w ≠ 0) : (J w).2 ≠ 0 := by
    intro h
    apply hw
    exact (e.continuousLinearEquivAt ℂ x hx).symm.injective (h.trans (map_zero _).symm)
  let U : Set (Fin k → ℂ) := J ⁻¹' (t.ambient.source ∩ t.ambient ⁻¹' O)
  have hU : IsOpen U := (t.ambient.isOpen_inter_preimage hO).preimage J.continuous
  have h0U : 0 ∈ U := by
    rw [show U = J ⁻¹' (t.ambient.source ∩ t.ambient ⁻¹' O) from rfl]
    rw [Set.mem_preimage, hJ0]
    exact ⟨t.ambient_source.symm ▸ t.contains_zero x, h0O⟩
  let f (w : Fin k → ℂ) := (a (t.ambient (J w))).2
  have hf : ContinuousOn f U :=
    (a.continuousOn.comp (t.ambient.continuousOn.comp J.continuous.continuousOn
      (fun w hw => hw.1)) (fun w hw => hOa hw.2)).snd
  have hf0 : f 0 = 0 := by
    have hz : J 0 ∈ t.source := by rw [hJ0]; exact t.contains_zero x
    have hS : t.ambient (J 0) ∈ S := by
      rw [t.ambient_map ⟨J 0, hz⟩]
      apply (t.support ⟨J 0, hz⟩).mpr
      change (J 0).2 = 0
      rw [hJ0]
      rfl
    exact (hs _ (hOa h0U.2)).mp hS
  obtain ⟨B, hBU, hne, hBo, h0B, hcoh⟩ :=
    complexDerivative_local_relativeCohomologyMap k U hU h0U f hf hf0 D hD
  let P := neighborhoodPointComplementPair B 0
  have hBsource (w : ↥B) : J w.val ∈ t.source := by
    change J w.val ∈ (t.source : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
    rw [← t.ambient_source]
    exact (hBU w.property).1
  let JN : P ⟶ i1_neighbourhoodPair k (i1_normalFibre j) t.source :=
    TopPair.ofSubsetHom (TopCat.ofHom
      ⟨fun w => ⟨J w.val, hBsource w⟩,
        (J.continuous.comp continuous_subtype_val).subtype_mk hBsource⟩)
      (fun w hw => hJne w.val hw)
  let FA : C(↥B, ComplexPoint W) :=
    ⟨fun w => t.ambient (J w.val),
      t.ambient.continuousOn.comp_continuous (J.continuous.comp continuous_subtype_val)
        (fun w => (hBU w.property).1)⟩
  let JA : P ⟶ neighborhoodSupportComplementPair O S :=
    TopPair.ofSubsetHom (TopCat.ofHom
      ⟨fun w => ⟨FA w, (hBU w.property).2⟩, FA.continuous.subtype_mk (fun w : ↥B => (hBU w.property).2)⟩) (by
        intro w hw hS
        have hz : J w.val ∈ t.source := hBsource w
        apply hJne w.val hw
        apply (t.support ⟨J w.val, hz⟩).mp
        change i1_tubularAmbientMap v j k t.source t.target t.map ⟨J w.val, hz⟩ ∈ S
        rw [← t.ambient_map ⟨J w.val, hz⟩]
        exact hS)
  have hJfactor : JN ≫ i1_neighbourhoodInclusion k (i1_normalFibre j) t.source =
      neighborhoodPointComplementPairMap B 0 ≫ i1_complexBundleFibrePairMap E e x hx := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  have hAfactor : JN ≫ tubePairMap ι k v j hj t =
      JA ≫ a3b4_neighborhoodPairMap O S := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      exact Subtype.ext (t.ambient_map ⟨J w.val.val, hBsource w.val⟩).symm
    · ext w
      exact (t.ambient_map ⟨J w.val, hBsource w⟩).symm
  have hnormal : JA ≫ chartNormalProjectionPair (Fin k → ℂ) k a S hs O hOa =
      complexNeighborhoodPuncturedPairMapOf k B f (hf.mono hBU) hne := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  have hα := transportedClass_pair_pullback ι k v j hj t c
    (neighborhoodPointComplementPairMap B 0 ≫ i1_complexBundleFibrePairMap E e x hx) JN hJfactor
  dsimp only [E, analyticNormalComplexBundle, normalTotalTop] at hα ⊢
  rw [hAfactor] at hα
  have hlocal : relativeCohomologyMap ℚ (2 * k) (JA ≫ a3b4_neighborhoodPairMap O S) c =
      relativeCohomologyMap ℚ (2 * k) (neighborhoodPointComplementPairMap B 0)
        (normalizedPointCoclass k) := by
    rw [relativeCohomologyMap_comp, LinearMap.comp_apply]
    have hn : relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap O S) c =
        chartNormalProjectionCoclass (Fin k → ℂ) k a S hs O hOa := hnorm
    rw [hn, chartNormalProjectionCoclass, ← LinearMap.comp_apply,
      ← relativeCohomologyMap_comp, hnormal, hcoh]
  rw [hlocal, relativeCohomologyMap_comp, LinearMap.comp_apply] at hα
  exact (s2e_relativeCohomologyMap_bijective_of_homology
    (neighborhoodPointComplementPairMap B 0) (2 * k)
    (neighborhoodPointComplement_relativeHomologyMap_bijective B 0 hBo h0B (2 * k))).1 hα

#print axioms transportedClass_fibre_of_local_normalization

end HodgeLean.Foundations.TubularEuler
