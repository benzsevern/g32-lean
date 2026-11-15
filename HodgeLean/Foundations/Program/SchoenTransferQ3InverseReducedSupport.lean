import HodgeLean.Foundations.Program.SchoenTransferQ3ReducedComponentPiece
import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentMap

/-! The actual reduced ambient component inside the unreduced inverse support. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The original reduced ambient component embeds in the actual unreduced
inverse support, with exactly the corresponding component as its image. -/
theorem s4_q3_inverse_reduced_support_map
    {X W : Scheme} (q : X ⟶ W) (x : W)
    (η : (ccm3_inverseIdeal q x).subscheme) :
    ∃ ψ : (ccm3_primeIdeal X ((ccm3_inverseIdeal q x).subschemeι η)).subscheme ⟶
        (ccm3_inverseIdeal q x).subscheme,
      ψ ≫ (ccm3_inverseIdeal q x).subschemeι =
        (ccm3_primeIdeal X ((ccm3_inverseIdeal q x).subschemeι η)).subschemeι ∧
      IsClosedImmersion ψ ∧ Set.range ψ = closure ({η} : Set (ccm3_inverseIdeal q x).subscheme) := by
  let K := ccm3_inverseIdeal q x
  let p := K.subschemeι η
  let I := ccm3_primeIdeal X p
  have hp : p ∈ (K.support : Set X) := by
    rw [← K.range_subschemeι]
    exact Set.mem_range_self η
  have hle : K ≤ I :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
      (show (⟨closure ({p} : Set X), isClosed_closure⟩ : Closeds X) ≤ K.support from
        closure_minimal (Set.singleton_subset_iff.mpr hp) K.support.isClosed)
  let ψ := Scheme.IdealSheafData.inclusion hle
  have hψ : ψ ≫ K.subschemeι = I.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι hle
  letI : IsClosedImmersion (ψ ≫ K.subschemeι) := by rw [hψ]; infer_instance
  have hclosed : IsClosedImmersion ψ := IsClosedImmersion.of_comp ψ K.subschemeι
  letI := hclosed
  have hI : Set.range I.subschemeι = closure ({p} : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  refine ⟨ψ, hψ, hclosed, ?_⟩
  rw [K.subschemeι.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
  change Set.range ψ = K.subschemeι ⁻¹' closure ({p} : Set X)
  ext t
  constructor
  · rintro ⟨c, rfl⟩
    have hc := congrArg (fun k : I.subscheme ⟶ X => k c) hψ
    change K.subschemeι (ψ c) = I.subschemeι c at hc
    rw [Set.mem_preimage, hc]
    exact hI ▸ Set.mem_range_self c
  · intro ht
    obtain ⟨c, hc⟩ := hI.symm ▸ ht
    refine ⟨c, K.subschemeι.isClosedEmbedding.injective ?_⟩
    have he := congrArg (fun k : I.subscheme ⟶ X => k c) hψ
    exact he.trans hc

/-- A closed component embedding has an actual reduced-piece neighbourhood
that is open on the underlying inverse-support space. -/
theorem s4_q3_closed_component_open_piece
    {C K : Scheme} [IsNoetherian K] (ψ : C ⟶ K) [IsClosedImmersion ψ]
    (η : K) (hη : closure ({η} : Set K) ∈ irreducibleComponents K)
    (himage : Set.range ψ = closure ({η} : Set K)) :
    ∃ U : K.Opens, η ∈ U ∧
      IsOpenEmbedding (((ψ ⁻¹ᵁ U).ι ≫ ψ).base) ∧
      Set.range ((ψ ⁻¹ᵁ U).ι ≫ ψ) = (U : Set K) := by
  obtain ⟨O, hO, ⟨t, ht⟩, hOC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hη
  have hηO : η ∈ O :=
    (specializes_iff_mem_closure.mpr (hOC ht)).mem_open hO ht
  let U : K.Opens := ⟨O, hO⟩
  let ψU := (ψ ⁻¹ᵁ U).ι ≫ ψ
  have hrange : Set.range ψU = (U : Set K) := by
    ext w
    constructor
    · rintro ⟨s, rfl⟩
      exact s.2
    · intro hw
      obtain ⟨s, hs⟩ := himage.symm ▸ hOC hw
      refine ⟨⟨s, ?_⟩, ?_⟩
      · change ψ s ∈ U
        rwa [hs]
      · exact hs
  have hopen : IsOpenEmbedding ψU.base :=
    { toIsEmbedding := ψU.isEmbedding, isOpen_range := hrange.symm ▸ U.isOpen }
  exact ⟨U, hηO, hopen, hrange⟩

/-- The reduced-component morphism is the restriction of the specified
unreduced inverse-support map, with its actual scheme square retained. -/
theorem s4_q3_inverse_support_component_square
    {X W C : Scheme} (q : X ⟶ W) (I : W.IdealSheafData)
    (i : C ⟶ X) (ψ : C ⟶ (I.comap q).subscheme) (f : C ⟶ I.subscheme)
    (hψ : ψ ≫ (I.comap q).subschemeι = i) (hf : f ≫ I.subschemeι = i ≫ q) :
    ψ ≫ Scheme.IdealSheafData.subschemeMap (I.comap q) I q (I.le_map_comap q) = f := by
  apply (cancel_mono I.subschemeι).mp
  rw [Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
    ← Category.assoc, hψ, hf]

end HodgeLean.Foundations.Program
