import HodgeLean.Foundations.RationalHomologyManifold.NaturalGlobalExtensionNaturality

/-! Actual global sections preserve quasi-isomorphisms of natural-degree soft complexes.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Extension by zero of an actual natural-degree soft complex has soft terms in every integer degree.
Source: Bredon, Sheaf Theory, second edition, II.9; softness retained under term isomorphisms and zero sheaves.
HC no distance; AV milestone no distance.
-/
theorem naturalSoftComplex_extend_terms (X : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    (hK : ∀ n, IsSoft (K.X n)) (i : ℤ) :
    IsSoft ((K.extend ComplexShape.embeddingUpNat).X i) := by
  by_cases hi : ∃ n, ComplexShape.embeddingUpNat.f n = i
  · obtain ⟨n, hn⟩ := hi
    exact isSoft_of_sheaf_iso (K.extendXIso ComplexShape.embeddingUpNat hn).symm (hK n)
  · exact isSoft_of_isZero_sheaf _ (K.isZero_extend_X ComplexShape.embeddingUpNat i
      (by simpa only [not_exists] using hi))

#print axioms naturalSoftComplex_extend_terms
/-- The actual global-section functor preserves quasi-isomorphisms between natural-degree complexes of soft sheaves on a compact Hausdorff space.
Source: Bredon, Sheaf Theory, second edition, II.9 and IV.2; bounded-below soft comparison under actual extension by zero.
HC no distance; AV milestone no distance.
-/
theorem natural_soft_global_quasiIso (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (f : K ⟶ L)
    (hf : QuasiIso f) (hK : ∀ n, IsSoft (K.X n)) (hL : ∀ n, IsSoft (L.X n)) :
    QuasiIso (((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map f) := by
  let E := subdivisionGlobalSectionsFunctor X
  let e := ComplexShape.embeddingUpNat
  let g := ((E.mapHomologicalComplex (.up ℕ)).map f)
  letI := hf
  have he : QuasiIso (HomologicalComplex.extendMap f e) := inferInstance
  letI := bounded_soft_global_quasiIso X (HomologicalComplex.extendMap f e) 0 0 he
    (naturalSoftComplex_extend_terms X K hK) (naturalSoftComplex_extend_terms X L hL)
  letI := naturalGlobalExtensionMap_isIso X K
  letI := naturalGlobalExtensionMap_isIso X L
  haveI : QuasiIso (naturalGlobalExtensionMap X K ≫ HomologicalComplex.extendMap g e) := by
    rw [← naturalGlobalExtensionMap_naturality X f]
    infer_instance
  have hg := quasiIso_of_comp_left (naturalGlobalExtensionMap X K) (HomologicalComplex.extendMap g e)
  exact (HomologicalComplex.quasiIso_extendMap_iff g e).mp hg

#print axioms natural_soft_global_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
