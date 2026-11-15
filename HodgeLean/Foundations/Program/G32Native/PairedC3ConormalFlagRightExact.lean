import HodgeLean.Foundations.Program.G32Native.PairedC3FlagIdentityTranspose

/-! # Right exactness of the natural conormal flag -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The flag sequence is the natural union sequence for Q union F = F
and Q intersection F = Q. Identity transport removes the pushforward.
Source: Hartshorne, Algebraic Geometry, II.8.12, ideal form. -/
theorem paired_c3_conormal_flag_right_exact
    {Q F X : Scheme.{0}} [IsLocallyNoetherian X]
    (i : F ⟶ X) (j : Q ⟶ F)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    let f := Conormal.comparisonMap i (j ≫ i) (𝟙 _) j (by rw [Category.comp_id])
    let g := ((Scheme.Modules.pullbackId _).app (Conormal.sheaf (j ≫ i))).inv ≫
      Conormal.comparisonMap (j ≫ i) j i (𝟙 _) (by rw [Category.id_comp])
    ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).Exact ∧ Epi g := by
  let f := Conormal.comparisonMap i (j ≫ i) (𝟙 _) j (by rw [Category.comp_id])
  let g := ((Scheme.Modules.pullbackId _).app (Conormal.sheaf (j ≫ i))).inv ≫
    Conormal.comparisonMap (j ≫ i) j i (𝟙 _) (by rw [Category.id_comp])
  have hk : i.ker ≤ (j ≫ i).ker := j.le_ker_comp i
  have hu : i.ker = (j ≫ i).ker ⊓ i.ker := (inf_eq_right.mpr hk).symm
  have hs : (𝟙 Q) ≫ (j ≫ i) = j ≫ i := Category.id_comp _
  have ht : ((𝟙 Q) ≫ (j ≫ i)).ker = (j ≫ i).ker ⊔ i.ker := by
    rw [Category.id_comp, sup_eq_left.mpr hk]
  let C := unionConormalComplex i (j ≫ i) i j (𝟙 Q) j rfl hs hu
  have he : C.Exact :=
    unionConormal_exact_of_locallyNoetherian i (j ≫ i) i j (𝟙 Q) j rfl hs hu ht
  haveI : Epi C.g := unionConormalLast_epi (j ≫ i) i (𝟙 Q) j hs ht
  let eR : C.X₃ ≅ Conormal.sheaf j :=
    (Scheme.Modules.pushforwardId Q).app (Conormal.sheaf j)
  have hg : C.g ≫ eR.hom = g := paired_c3_identity_pullback_transpose _
  have hw : f ≫ g = 0 := by
    rw [← hg, ← Category.assoc]
    change (C.f ≫ C.g) ≫ eR.hom = 0
    rw [C.zero, zero_comp]
  let D := ShortComplex.mk f g hw
  let e : C ≅ D := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) eR
    ((Category.id_comp f).trans (Category.comp_id f).symm)
    ((Category.id_comp g).trans hg.symm)
  haveI : Epi g := by rw [← hg]; infer_instance
  exact ⟨hw, ShortComplex.exact_of_iso e he, inferInstance⟩

#print axioms paired_c3_conormal_flag_right_exact
end HodgeLean.Foundations.Program.G32Native
