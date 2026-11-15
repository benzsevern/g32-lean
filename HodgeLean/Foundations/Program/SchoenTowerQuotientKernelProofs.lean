import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- A categorical symmetric quotient has trivial scheme kernel.
Source: SGA 1, Exposé V, §1, universal property and scheme-theoretic image. -/
theorem s2t_quotient_kernel_aux (C P : Over (Spec ↧ℂ)) (h : ℕ)
    (π : g3_power C h ⟶ P)
    (hinv : ∀ σ, s2_permute C h σ ≫ π = π)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
      (∀ σ, s2_permute C h σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f) :
    π.left.ker = ⊥ := by
  let I : Over (Spec ↧ℂ) := Over.mk (π.left.imageι ≫ P.hom)
  let j : I ⟶ P := Over.homMk π.left.imageι
  let f : g3_power C h ⟶ I := Over.homMk π.left.toImage (by
    dsimp [I]
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, Over.w])
  have hj : f ≫ j = π := by ext1; exact π.left.toImage_imageι
  have hf : ∀ σ, s2_permute C h σ ≫ f = f := by
    intro σ
    apply Over.OverMorphism.ext
    apply (cancel_mono π.left.imageι).mp
    change (s2_permute C h σ).left ≫ π.left.toImage ≫ π.left.imageι =
      π.left.toImage ≫ π.left.imageι
    rw [Scheme.Hom.toImage_imageι]
    exact congrArg (fun k : g3_power C h ⟶ P => k.left) (hinv σ)
  obtain ⟨d, hd, hu⟩ := hquot I f hf
  have hdj : d ≫ j = 𝟙 P := by
    obtain ⟨u, _, hu'⟩ := hquot P π hinv
    exact (hu' (d ≫ j) (by change π ≫ (d ≫ j) = π; rw [← Category.assoc, hd, hj])).trans
      (hu' (𝟙 P) (by change π ≫ 𝟙 P = π; rw [Category.comp_id])).symm
  have hleft : d.left ≫ π.left.imageι = 𝟙 P.left :=
    congrArg (fun k : P ⟶ P => k.left) hdj
  letI : IsIso π.left.imageι := ⟨⟨d.left,
    (cancel_mono π.left.imageι).mp (by rw [Category.assoc, hleft,
      Category.comp_id, Category.id_comp]), hleft⟩⟩
  exact (Scheme.isIso_subschemeι_iff_eq_bot π.left.ker).mp inferInstance

/-- A trivial source kernel preserves the kernel of every subsequent morphism.
Source: Mathlib, Scheme.Hom.ker_comp and Scheme.IdealSheafData.map_bot. -/
theorem s2t_kernel_comp_aux {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : f.ker = ⊥) : (f ≫ g).ker = g.ker := by
  rw [Scheme.Hom.ker_comp, hf, Scheme.IdealSheafData.map_bot]

end HodgeLean.Foundations.Program
