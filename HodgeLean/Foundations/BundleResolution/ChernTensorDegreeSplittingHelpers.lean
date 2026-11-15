import HodgeLean.Foundations.BundleResolution.ChernTensorRightAdditiveHelpers
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Degreewise splittings after tensoring rational chain complexes

Splittings of the original degreewise sequences induce actual splittings
of every total tensor degree, without chain-compatible splitting choices.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory HomologicalComplex
namespace HodgeLean.Foundations.BundleResolution

def i1_tensorRightShortComplex (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ))
    (L : ChainComplex (ModuleCat ℚ) ℕ) : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) := by
  letI := i1_tensorRight_additive L
  exact S.map (tensorRight L)

def i1_tensorRightDegreeSplitting (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ))
    (L : ChainComplex (ModuleCat ℚ) ℕ)
    (d : ∀ p, (S.map (eval (ModuleCat ℚ) (ComplexShape.down ℕ) p)).Splitting) (n : ℕ) :
    ((i1_tensorRightShortComplex S L).map (eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)).Splitting where
  r := i1_tensorDegreeMapLeft S.X₂ S.X₁ L (fun p => (d p).r.hom) n
  s := i1_tensorDegreeMapLeft S.X₃ S.X₂ L (fun p => (d p).s.hom) n
  f_r := by
    change (S.f ▷ L).f n ≫ _ = 𝟙 _
    rw [i1_tensorRight_degree, i1_tensorDegreeMapLeft_comp]
    have h : (fun p => (d p).r.hom.comp (S.f.f p).hom) = fun _ => LinearMap.id := by
      funext p
      exact congrArg ModuleCat.Hom.hom (d p).f_r
    rw [h, i1_tensorDegreeMapLeft_id]
    rfl
  s_g := by
    change _ ≫ (S.g ▷ L).f n = 𝟙 _
    rw [i1_tensorRight_degree, i1_tensorDegreeMapLeft_comp]
    have h : (fun p => (S.g.f p).hom.comp (d p).s.hom) = fun _ => LinearMap.id := by
      funext p
      exact congrArg ModuleCat.Hom.hom (d p).s_g
    rw [h, i1_tensorDegreeMapLeft_id]
    rfl
  id := by
    change i1_tensorDegreeMapLeft S.X₂ S.X₁ L (fun p => (d p).r.hom) n ≫ (S.f ▷ L).f n +
      (S.g ▷ L).f n ≫ i1_tensorDegreeMapLeft S.X₃ S.X₂ L (fun p => (d p).s.hom) n =
        𝟙 ((HomologicalComplex.tensorObj S.X₂ L).X n)
    rw [i1_tensorRight_degree, i1_tensorRight_degree,
      i1_tensorDegreeMapLeft_comp, i1_tensorDegreeMapLeft_comp, ← i1_tensorDegreeMapLeft_add]
    have h : (fun p =>
        (show S.X₂.X p →ₗ[ℚ] S.X₂.X p from (S.f.f p).hom.comp (d p).r.hom) +
        (show S.X₂.X p →ₗ[ℚ] S.X₂.X p from (d p).s.hom.comp (S.g.f p).hom)) =
        fun _ => LinearMap.id := by
      funext p
      exact congrArg ModuleCat.Hom.hom (d p).id
    rw [h, i1_tensorDegreeMapLeft_id]

end HodgeLean.Foundations.BundleResolution
