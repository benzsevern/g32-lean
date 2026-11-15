import HodgeLean.Foundations.Program.SheafOverPullback
import HodgeLean.Foundations.Program.FiniteQuotientSingularComparison

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- A map over the quotient base acts compatibly on the pushed constant augmentation.
Source: Bredon, Sheaf Theory, second edition, II.4, comparison of resolutions. -/
theorem singularOverPullback_augmentation {A B : TopCat.{0}}
    (q : A ⟶ B) (f : A ⟶ A) (hf : f ≫ q = q)
    (L : 𝓒(A; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj 𝓒(A; ℚ))
    (hL : ∀ (V : Opens A) (s : 𝓒(A; ℚ).obj.obj (op V)) (x : f ⁻¹' V),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map f).obj V)
        (L.hom.app (op V) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) V s ⟨f x, x.property⟩) :
    pushedSingularAugmentation q ≫
        cochainOverPullback q f hf (singularCochainSheafComplexPullback ℚ f) =
      (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat B)).map
        (sheafOverPullback q f hf L) ≫ pushedSingularAugmentation q := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  simp only [CochainComplex.fromSingle₀Equiv_apply_coe,
    HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    pushedSingularAugmentation_zero]
  exact sheafOverPullback_naturality q f hf L (singularCochainSheafPullback ℚ f 0)
    (constantsToSingularCochainZeroSheaf ℚ A) (constantsToSingularCochainZeroSheaf ℚ A)
    (constantSheaf_pullback_singular_augmentation f L hL).symm

/-- Orbit sums on constants induce the same orbit sums on the singular augmentation.
Source: Bredon, Sheaf Theory, second edition, II.4, comparison of resolutions. -/
theorem singularOverPullback_sum_augmentation {A B : TopCat.{0}}
    (G : Type) [Fintype G] (q : A ⟶ B) (a : G → (A ⟶ A))
    (ha : ∀ g, a g ≫ q = q)
    (La : ∀ g, 𝓒(A; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat (a g)).obj 𝓒(A; ℚ))
    (hLa : ∀ g (V : Opens A) (s : 𝓒(A; ℚ).obj.obj (op V)) (x : a g ⁻¹' V),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map (a g)).obj V)
        ((La g).hom.app (op V) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) V s ⟨a g x, x.property⟩) :
    pushedSingularAugmentation q ≫
        (∑ g : G, cochainOverPullback q (a g) (ha g) (singularCochainSheafComplexPullback ℚ (a g))) =
      (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat B)).map
        (∑ g : G, sheafOverPullback q (a g) (ha g) (La g)) ≫ pushedSingularAugmentation q := by
  rw [Preadditive.comp_sum, Functor.map_sum, Preadditive.sum_comp]
  exact Finset.sum_congr rfl (fun g _ => singularOverPullback_augmentation q (a g) (ha g) (La g) (hLa g))

/-- Global sections of a singular pullback over the base give the actual global singular pullback.
Source: Bredon, Sheaf Theory, second edition, I.3, global sections of direct images. -/
theorem singularOverPullback_global {A B : TopCat.{0}}
    (q : A ⟶ B) (f : A ⟶ A) (hf : f ≫ q = q) :
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor B).mapHomologicalComplex
      (.up ℕ)).map
        (cochainOverPullback q f hf (singularCochainSheafComplexPullback ℚ f)) =
      singularGlobalSheafPullback f := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact sheafOverPullback_top q f hf (singularCochainSheafPullback ℚ f n)

end HodgeLean.Foundations.Program
