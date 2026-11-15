import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentation

/-! # Reconstruction retaining an arbitrary actual divisor quotient -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.NormalPresentation
variable {C : Type*} [Category* C] [Abelian C] {I A F M D : C}

/-- The reconstruction keeps the supplied divisor quotient rather than replacing it by a label. -/
theorem elementary_divisor_presentation_of_lift
    (a : I ⟶ A) (p : A ⟶ D) (hap : a ≫ p = 0)
    (ha : (ShortComplex.mk a p hap).ShortExact)
    (f : F ⟶ M) (g : M ⟶ D) (hfg : f ≫ g = 0)
    (hs : (ShortComplex.mk f g hfg).ShortExact)
    (l : A ⟶ M) (hl : l ≫ g = p) :
    ∃ (b : I ⟶ F) (e : quotient a b ≅ M) (d : cokernel a ≅ D),
      cokernel.π a ≫ d.hom = p ∧
      projection a b ≫ e.hom = biprod.desc l f ∧
      freeArrow a b ≫ e.hom = f ∧
      e.hom ≫ g = divisorArrow a b ≫ d.hom := by
  have : Mono a := ha.mono_f
  have : Epi p := ha.epi_g
  let v := cokernel.desc a p hap
  have : Mono v := ha.exact.mono_cokernelDesc
  have : Epi v := epi_of_epi_fac (show cokernel.π a ≫ v = p from cokernel.π_desc _ _ _)
  have : IsIso v := isIso_of_mono_of_epi v
  let d : cokernel a ≅ D := asIso v
  have hd : cokernel.π a ≫ d.hom = p := cokernel.π_desc _ _ _
  have hz : f ≫ (g ≫ d.inv) = 0 := by rw [← Category.assoc, hfg, zero_comp]
  let T := ShortComplex.mk f (g ≫ d.inv) hz
  let eT : ShortComplex.mk f g hfg ≅ T :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) d.symm
      (by change 𝟙 F ≫ f = f ≫ 𝟙 M; simp only [Category.id_comp, Category.comp_id])
      (by change 𝟙 M ≫ (g ≫ d.inv) = g ≫ d.inv; exact Category.id_comp _)
  have ht : T.ShortExact := ShortComplex.shortExact_of_iso eT hs
  have hl' : l ≫ (g ≫ d.inv) = cokernel.π a := by
    rw [← Category.assoc, hl, ← hd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨b, e, he, hf, hg⟩ := elementary_presentation_of_lift a f (g ≫ d.inv) hz ht l hl'
  refine ⟨b, e, d, hd, he, hf, ?_⟩
  apply (cancel_mono d.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact hg

end HodgeLean.Foundations.Program.G32Native
