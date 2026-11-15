import HodgeLean.Foundations.RationalHomologyManifold.BoundedSoftOpcycles

/-! Exactness of global sections of bounded-below exact complexes of soft sheaves.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Global sections retain an exact short complex whose first map has a soft kernel.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.9; lifting global sections through a soft kernel.
HC no distance; AV milestone no distance.
-/
theorem global_exact_of_soft_kernel (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.Exact)
    (hs : IsSoft (kernel S.f)) :
    (S.map (subdivisionGlobalSectionsFunctor X)).Exact := by
  let E := subdivisionGlobalSectionsFunctor X
  let f := S.f
  let g := factorThruImage f
  let T := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hT : T.ShortExact := { exact := ShortComplex.exact_kernel g }
  have hk : IsSoft (kernel g) := isSoft_of_sheaf_iso (kernelFactorThruImage f).symm hs
  letI : Epi (E.map g) := (AddCommGrpCat.epi_iff_surjective _).mpr
    (spec_surjective_globalSections_of_isSoft hT hk)
  let U := ShortComplex.mk (image.ι f) S.g (image_ι_comp_eq_zero S.zero)
  have hU : (U.map E).Exact := ShortComplex.exact_of_f_is_kernel _
    (KernelFork.mapIsLimit _ hS.isLimitImage' E)
  let φ : S.map E ⟶ U.map E := {
    τ₁ := E.map g
    τ₂ := 𝟙 _
    τ₃ := 𝟙 _
    comm₁₂ := by
      change E.map g ≫ E.map (image.ι f) = E.map f ≫ 𝟙 _
      rw [Category.comp_id, ← E.map_comp, image.fac]
    comm₂₃ := by simp only [ShortComplex.map_g, Category.comp_id, Category.id_comp]; rfl }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hU

#print axioms global_exact_of_soft_kernel
/-- The zero lower tail extends the softness of opcycles to every integer degree.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.10; bounded-below induction for soft quotients.
HC no distance; AV milestone no distance.
-/
theorem bounded_soft_opcycles_all (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ) (b : ℤ)
    [K.IsStrictlyGE b] (hK : K.Acyclic) (hs : ∀ i, IsSoft (K.X i)) (i : ℤ) :
    IsSoft (K.opcycles i) := by
  by_cases hi : b ≤ i
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = b + m := ⟨(i - b).toNat, by omega⟩
    exact bounded_soft_opcycles X K b hK hs m
  · apply isSoft_of_isZero_sheaf
    rw [IsZero.iff_id_eq_zero]
    apply (cancel_epi (K.pOpcycles i)).mp
    rw [Category.comp_id, comp_zero]
    exact (K.isZero_of_isStrictlyGE b i (by omega)).eq_of_src _ _

#print axioms bounded_soft_opcycles_all
/-- Every differential kernel in a bounded-below exact complex of soft sheaves is soft.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.10; exactness identifies kernels with soft quotient images.
HC no distance; AV milestone no distance.
-/
theorem bounded_soft_differential_kernel (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ) (b : ℤ)
    [K.IsStrictlyGE b] (hK : K.Acyclic) (hs : ∀ i, IsSoft (K.X i)) (i j : ℤ) (hij : i + 1 = j) :
    IsSoft (kernel (K.d i j)) := by
  let g := K.fromOpcycles (i - 1) i
  letI : Mono g := Preadditive.mono_of_isZero_kernel' _
    (K.homologyIsKernel (i - 1) i (by rw [CochainComplex.next]; omega))
    (hK (i - 1)).isZero_homology
  letI : StrongEpi (K.pOpcycles (i - 1)) := strongEpi_of_epi _
  let e0 : K.opcycles (i - 1) ≅ image (K.d (i - 1) i) :=
    image.isoStrongEpiMono (K.pOpcycles (i - 1)) g (K.p_fromOpcycles (i - 1) i)
  have hS : (K.sc' (i - 1) i j).Exact :=
    (K.exactAt_iff' (i - 1) i j (by rw [CochainComplex.prev])
      (by rw [CochainComplex.next]; exact hij)).mp (hK i)
  let e1 : image (K.d (i - 1) i) ≅ kernel (K.d i j) :=
    hS.isLimitImage'.conePointUniqueUpToIso (limit.isLimit _)
  exact isSoft_of_sheaf_iso (e0 ≪≫ e1) (bounded_soft_opcycles_all X K b hK hs (i - 1))

#print axioms bounded_soft_differential_kernel
/-- Global sections of a bounded-below exact complex of soft sheaves are exact in every degree.
Source: Bredon, Sheaf Theory, second edition, Theorems II.9.9–10; exactness of the bounded soft model under global sections.
HC no distance; AV milestone no distance.
-/
theorem bounded_soft_global_acyclic (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ) (b : ℤ)
    [K.IsStrictlyGE b] (hK : K.Acyclic) (hs : ∀ i, IsSoft (K.X i)) :
    (((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff]
  change ((K.sc i).map (subdivisionGlobalSectionsFunctor X)).Exact
  apply global_exact_of_soft_kernel X (K.sc i) (hK i)
  change IsSoft (kernel (K.d ((ComplexShape.up ℤ).prev i) i))
  exact bounded_soft_differential_kernel X K b hK hs
    ((ComplexShape.up ℤ).prev i) i (by rw [CochainComplex.prev]; omega)

#print axioms bounded_soft_global_acyclic
end HodgeLean.Foundations.RationalHomologyManifold
