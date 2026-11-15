import HodgeLean.Foundations.Program.SchoenTransferC1a5RelativeDefs
import Mathlib.Algebra.Homology.QuasiIso

/-! Changing the source pair in an actual relative comparison by specified isomorphisms.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- Relative comparison transports from an isomorphic source pair without monomorphy assumptions.
Source: Hatcher §2.1, maps of pairs; Mathlib cokernel.map. -/
lemma c1a5_relative_comparison_source_iso
    (F : SSet.{0} ⥤ ChainComplex (ModuleCat ℤ) ℕ)
    {A B C D A' B' : SSet.{0}} (f : A ⟶ B) (g : C ⟶ D)
    (a : A ⟶ C) (b : B ⟶ D) (w : f ≫ b = a ≫ g)
    (eA : A' ≅ A) (eB : B' ≅ B) (f' : A' ⟶ B')
    (hf : f' ≫ eB.hom = eA.hom ≫ f)
    (h : QuasiIso (c1a5RelativeMap F f' g (eA.hom ≫ a) (eB.hom ≫ b) (by
      rw [← Category.assoc, hf, Category.assoc, w, ← Category.assoc]))) :
    QuasiIso (c1a5RelativeMap F f g a b w) := by
  let u := c1a5RelativeMap F f' f eA.hom eB.hom hf
  have hu : IsIso u := by
    dsimp [u, c1a5RelativeMap]
    infer_instance
  have he : u ≫ c1a5RelativeMap F f g a b w =
      c1a5RelativeMap F f' g (eA.hom ≫ a) (eB.hom ≫ b) (by
        rw [← Category.assoc, hf, Category.assoc, w, ← Category.assoc]) := by
    apply (cancel_epi (cokernel.π (F.map f'))).1
    simp only [u, c1a5RelativeMap, cokernel.map, cokernel.π_desc_assoc,
      cokernel.π_desc, Category.assoc, F.map_comp]
  have hc : QuasiIso (u ≫ c1a5RelativeMap F f g a b w) := by rwa [he]
  have := hu
  have := hc
  exact quasiIso_of_comp_left u _

end HodgeLean.Foundations.Program
