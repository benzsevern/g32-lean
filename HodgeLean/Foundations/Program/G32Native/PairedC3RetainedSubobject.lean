import HodgeLean.Foundations.Program.G32Native.PairedC3RelationElimination
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Retaining specified generators under relation elimination -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program.G32Native
variable {C : Type*} [Category C] [Abelian C]
variable {L A B M : C}

/-- Eliminating an invertible relation coefficient retains the specified
remaining generators, including their original scale and order. -/
theorem paired_c3_retained_presentation_iso
    (r : L ⟶ L ⊞ (A ⊞ B)) [IsIso (r ≫ biprod.fst)]
    (v : L ⊞ (A ⊞ B) ⟶ M) (hrv : r ≫ v = 0)
    (hv : IsColimit (CokernelCofork.ofπ v hrv)) :
    ∃ e : M ≅ A ⊞ B, v ≫ e.hom = pairedC3RelationProjection r ∧
      (biprod.inl ≫ biprod.inr ≫ v) ≫ e.hom = biprod.inl ∧
      (biprod.inr ≫ biprod.inr ≫ v) ≫ e.hom = biprod.inr := by
  let e := hv.coconePointUniqueUpToIso (pairedC3RelationProjectionIsCokernel r)
  have he : v ≫ e.hom = pairedC3RelationProjection r :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hv
      (pairedC3RelationProjectionIsCokernel r) WalkingParallelPair.one
  refine ⟨e, he, ?_, ?_⟩ <;>
    simp only [Category.assoc, he, pairedC3RelationProjection,
      biprod.inr_desc, Category.comp_id]

/-- A specified inclusion identified with the first summand has a short
exact quotient sequence and an explicit retraction. -/
theorem paired_c3_retained_subobject_sequence
    (w : A ⟶ M) (e : M ≅ A ⊞ B) (hw : w ≫ e.hom = biprod.inl) :
    ∃ (T : ShortComplex C), T.ShortExact ∧
      ∃ (h₁ : T.X₁ = A) (h₂ : T.X₂ = M) (h₃ : T.X₃ = B),
        T.f = eqToHom h₁ ≫ w ≫ eqToHom h₂.symm ∧
        ∃ r : T.X₂ ⟶ T.X₁, T.f ≫ r = 𝟙 _ := by
  have hw' : w = biprod.inl ≫ e.inv := by
    rw [← hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  let S := ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) biprod.snd biprod.inl_snd
  let T := ShortComplex.mk w (e.hom ≫ biprod.snd) (by
    rw [← Category.assoc, hw, biprod.inl_snd])
  let es : S ≅ T := ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _)
    (by change 𝟙 A ≫ w = biprod.inl ≫ e.inv; rw [Category.id_comp, hw'])
    (by change e.inv ≫ (e.hom ≫ biprod.snd) = biprod.snd ≫ 𝟙 B
        rw [e.inv_hom_id_assoc, Category.comp_id])
  have hS : S.ShortExact := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
  refine ⟨T, ShortComplex.shortExact_of_iso es hS, rfl, rfl, rfl, ?_,
    e.hom ≫ biprod.fst, ?_⟩
  · change w = 𝟙 A ≫ w ≫ 𝟙 M
    rw [Category.id_comp, Category.comp_id]
  · change w ≫ (e.hom ≫ biprod.fst) = 𝟙 A
    rw [← Category.assoc, hw, biprod.inl_fst]

/-- The cokernel of the retained first summand is the other specified summand. -/
def pairedC3RetainedCokernelIso
    (w : A ⟶ M) (e : M ≅ A ⊞ B) (hw : w ≫ e.hom = biprod.inl) :
    cokernel w ≅ B :=
  cokernel.mapIso w (biprod.inl : A ⟶ A ⊞ B) (Iso.refl A) e
    (by simpa only [Iso.refl_hom, Category.id_comp] using hw) ≪≫
  (cokernelIsCokernel (biprod.inl : A ⟶ A ⊞ B)).coconePointUniqueUpToIso
    (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact.gIsCokernel

end HodgeLean.Foundations.Program.G32Native
