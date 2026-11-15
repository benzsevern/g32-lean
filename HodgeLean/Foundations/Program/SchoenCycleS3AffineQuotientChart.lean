import HodgeLean.Foundations.Program.SchoenCycleS3ConormalIsoTransport
import HodgeLean.Foundations.Program.SchoenCycleS3ResidueConormalCharts

/-! # Quotient charts of actual ideal subschemes -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A closed immersion identifies its source with the subscheme of its kernel ideal. -/
theorem s2e_closedImmersion_subschemeIso {Z X : Scheme} (f : Z ⟶ X) [IsClosedImmersion f]
    (I : X.IdealSheafData) (h : f.ker = I) :
    ∃ e : Z ≅ I.subscheme, e.hom ≫ I.subschemeι = f := by
  subst I
  exact ⟨asIso f.toImage, f.toImage_imageι⟩

/-- The quotient by the transported global ideal has exactly the given affine ideal sheaf kernel. -/
theorem s2e_affineQuotient_kernel {R : CommRingCat.{0}} (J : (Spec R).IdealSheafData) :
    let I := Ideal.map (Scheme.ΓSpecIso R).hom.hom (J.ideal ⟨⊤, isAffineOpen_top _⟩)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker = J := by
  dsimp only
  let I := Ideal.map (Scheme.ΓSpecIso R).hom.hom (J.ideal ⟨⊤, isAffineOpen_top _⟩)
  let f := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  let eQ := (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).commRingCatIsoToRingEquiv
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply]
  ext x
  change f.appTop x = 0 ↔ x ∈ J.ideal ⟨⊤, isAffineOpen_top _⟩
  have hn : eQ (f.appTop x) = Ideal.Quotient.mk I (e x) :=
    congrArg (fun q => q x) (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  calc
    f.appTop x = 0 ↔ eQ (f.appTop x) = 0 := by
      constructor
      · intro h
        rw [h, map_zero]
      · intro h
        apply eQ.injective
        simpa only [map_zero] using h
    _ ↔ Ideal.Quotient.mk I (e x) = 0 := by rw [hn]
    _ ↔ e x ∈ I := Ideal.Quotient.eq_zero_iff_mem
    _ ↔ x ∈ J.ideal ⟨⊤, isAffineOpen_top _⟩ :=
      Ideal.apply_mem_of_equiv_iff (f := e) (I := J.ideal ⟨⊤, isAffineOpen_top _⟩) (x := x)

/-- An affine open chart induces a quotient chart of the actual ideal subscheme. -/
theorem s2e_subschemeQuotientChart {X : Scheme} {R : CommRingCat.{0}}
    (I : X.IdealSheafData) (j : Spec R ⟶ X) [IsOpenImmersion j] :
    let A := Ideal.map (Scheme.ΓSpecIso R).hom.hom
      ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩)
    ∃ (q : Spec (CommRingCat.of (R ⧸ A)) ⟶ I.subscheme),
      ∃ hq : IsOpenImmersion q, letI := hq
      q ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk A)) ≫ j ∧
        q.opensRange = I.subschemeι ⁻¹ᵁ j.opensRange := by
  dsimp only
  let A := Ideal.map (Scheme.ΓSpecIso R).hom.hom
    ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩)
  let a := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk A))
  obtain ⟨e, he⟩ := s2e_closedImmersion_subschemeIso a (I.comap j)
    (s2e_affineQuotient_kernel (I.comap j))
  let q := e.hom ≫ (I.comapIso j).hom ≫ pullback.snd j I.subschemeι
  have hq : IsOpenImmersion q := by dsimp only [q]; infer_instance
  refine ⟨q, hq, ?_, ?_⟩
  · dsimp only [q]
    rw [Category.assoc, Category.assoc, ← pullback.condition,
      I.comapIso_hom_fst_assoc, ← Category.assoc, he]
  · dsimp only [q]
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Hom.opensRange_pullbackSnd]

end HodgeLean.Foundations.Program
