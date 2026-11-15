import Mathlib.Algebra.Homology.Embedding.Splitting
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Exact rational chain sequences after integer extension

Degreewise vector-space splittings extend by zero along the specified
integer offset while retaining the original sequence maps.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex
namespace HodgeLean.Foundations.BundleResolution

theorem i1_rationalChainSequence_extend_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)) (hS : S.ShortExact) (p : ℤ) :
    (S.map ((ComplexShape.embeddingUpIntLE p).extendFunctor (ModuleCat ℚ))).ShortExact := by
  let d (n : ℕ) : (S.map (eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)).Splitting := by
    have hn : (S.map (eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)).ShortExact :=
      (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
    exact hn.splittingOfProjective
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact ((ComplexShape.embeddingUpIntLE p).splittingExtend d i).shortExact

end HodgeLean.Foundations.BundleResolution
