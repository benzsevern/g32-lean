import HodgeLean.Foundations.Program.SchoenCycleS3AffineQuotientChart
import HodgeLean.Foundations.Program.SchoenCycleS3ConormalFreeTransport

/-! # Local conormal freeness from actual affine quotient charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A free quotient conormal gives freeness on the inverse image of its ambient open chart. -/
theorem s2e_subschemeConormal_free_on_chart {X : Scheme.{0}} {R : CommRingCat.{0}}
    (I : X.IdealSheafData) (j : Spec R ⟶ X) [IsOpenImmersion j] (ι : Type)
    (h : let A := Ideal.map (Scheme.ΓSpecIso R).hom.hom
          ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩)
      Nonempty (s2c_conormal (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk A))) ≅
        (SheafOfModules.free (R := (Spec (CommRingCat.of (R ⧸ A))).ringCatSheaf) ι :
          (Spec (CommRingCat.of (R ⧸ A))).Modules))) :
    Nonempty (Scheme.Modules.restrict (s2c_conormal I.subschemeι)
        (I.subschemeι ⁻¹ᵁ j.opensRange).ι ≅
      (SheafOfModules.free (R := (I.subschemeι ⁻¹ᵁ j.opensRange).toScheme.ringCatSheaf) ι :
        (I.subschemeι ⁻¹ᵁ j.opensRange).toScheme.Modules)) := by
  let A := Ideal.map (Scheme.ΓSpecIso R).hom.hom
    ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩)
  let a := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk A))
  let U := j.opensRange
  let V := I.subschemeι ⁻¹ᵁ U
  obtain ⟨q, hq, hqa, hqr⟩ := s2e_subschemeQuotientChart I j
  letI := hq
  let eY := j.isoOpensRange
  have hr : Set.range q = Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact congrArg (fun W : I.subscheme.Opens => (W : Set I.subscheme)) hqr
  let eX := IsOpenImmersion.isoOfRangeEq q V.ι hr
  have hf : eX.hom ≫ (I.subschemeι ∣_ U) = a ≫ eY.hom := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
      Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    exact hqa
  obtain ⟨e⟩ := h
  refine ⟨s2e_freeOfPullbackIso eX _ ι ?_⟩
  exact (Scheme.Modules.pullback eX.hom).mapIso (s2e_restrictConormalIso I.subschemeι U) ≪≫
    s2e_conormalArrowIso eX.hom eY.hom (I.subschemeι ∣_ U) a hf ≪≫ e

end HodgeLean.Foundations.Program
