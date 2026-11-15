import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryHelpers
import HodgeLean.Foundations.Mathlib.GenericFlatSmooth

noncomputable section
open CategoryTheory TopologicalSpace
open scoped Classical
namespace AlgebraicGeometry.SingularCycles

theorem boundary_flat_restrict {X Z : Scheme} (f : X ⟶ Z) (U : Z.Opens)
    (h : ∀ x : X, f x ∈ U → (f.stalkMap x).hom.Flat) : Flat (f ∣_ U) := by
  apply Flat.of_stalkMap
  intro x
  exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (morphismRestrictStalkMap f U x)).mpr (h x.1 x.2)

theorem boundary_smooth_restrict {Z : Scheme} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (U : Z.Opens) (h : U ≤ q.smoothLocus) :
    Smooth (U.ι ≫ q) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  apply top_unique
  intro x _
  exact h x.2

set_option backward.isDefEq.respectTransparency false in
theorem boundary_reduced_generic_flat {X Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] :
    ∃ U : Z.Opens, Dense (U : Set Z) ∧ Flat (f ∣_ U) := by
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian q
  letI : CompactSpace Z := HodgeLean.Adapters.a3b4_compactSpace q
  letI : IsNoetherian Z := {}
  let U : Z.Opens := ⨆ V : {V : Z.Opens // Flat (f ∣_ V)}, V.1
  have hflat : Flat (f ∣_ U) := by
    apply boundary_flat_restrict
    intro x hx
    obtain ⟨V, hxV⟩ := Opens.mem_iSup.mp hx
    letI := V.2
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f V.1 ⟨x, hxV⟩)).mp (Flat.stalkMap _ _)
  refine ⟨U, ?_, hflat⟩
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  let W : Z.Opens :=
    ⟨(⋃₀ (irreducibleComponents Z \ {irreducibleComponent z}))ᶜ, by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        fun C hC ↦ isClosed_of_mem_irreducibleComponents C hC.1⟩
  have hW : closure (W : Set Z) = irreducibleComponent z :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      _ (irreducibleComponent_mem_irreducibleComponents z)
  letI : IsIntegral W.toScheme :=
    have : IrreducibleSpace W := isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_iff_closure.mp (hW ▸ isIrreducible_irreducibleComponent))
    isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨V, hV, hVflat⟩ := gfs_exists_flat_over_dense_open (f ∣_ W)
  let T : Z.Opens := W.ι ''ᵁ V
  have hTflat : Flat (f ∣_ T) :=
    (MorphismProperty.arrow_mk_iso_iff @Flat (morphismRestrictRestrict f W V)).mp hVflat
  have hTU : T ≤ U := le_iSup (fun V : {V : Z.Opens // Flat (f ∣_ V)} => V.1) ⟨T, hTflat⟩
  have hT : closure (T : Set Z) = irreducibleComponent z := by
    calc
      closure (T : Set Z) = closure (W.ι '' closure (V : Set W)) :=
        (closure_image_closure W.ι.continuous).symm
      _ = closure (W : Set Z) := by rw [hV.closure_eq]; simp only [Set.image_univ, W.range_ι]
      _ = irreducibleComponent z := hW
  apply closure_mono (show (T : Set Z) ⊆ U from hTU)
  rw [hT]
  exact mem_irreducibleComponent

end AlgebraicGeometry.SingularCycles
