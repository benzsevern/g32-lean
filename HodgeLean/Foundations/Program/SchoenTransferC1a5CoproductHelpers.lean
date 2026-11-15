import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Finite coproduct transport for integral chain comparisons.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace HodgeLean.Foundations.Program

/-- A finite coproduct of integral chain comparisons preserves homology.
Source: Hatcher, Algebraic Topology, §2.1, direct sums of chain complexes. -/
lemma c1a5_finite_coproduct_comparison {I : Type} [Finite I]
    {A B : I → ChainComplex (ModuleCat ℤ) ℕ} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, QuasiIso (f i)) : QuasiIso (CategoryTheory.Limits.Sigma.map f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  have (i : I) : IsIso (F.map (f i)) := by
    have := hf i
    change IsIso (homologyMap (f i) n)
    infer_instance
  have w : sigmaComparison F A ≫ F.map (CategoryTheory.Limits.Sigma.map f) =
      CategoryTheory.Limits.Sigma.map (fun i ↦ F.map (f i)) ≫ sigmaComparison F B := by
    apply CategoryTheory.Limits.Sigma.hom_ext
    intro i
    simp only [ι_comp_sigmaComparison_assoc, CategoryTheory.Limits.Sigma.ι_map_assoc,
      ι_comp_sigmaComparison, ← F.map_comp, CategoryTheory.Limits.Sigma.ι_map]
  have : IsIso (sigmaComparison F A ≫ F.map (CategoryTheory.Limits.Sigma.map f)) := by
    rw [w]
    infer_instance
  exact (isIso_comp_left_iff (sigmaComparison F A) (F.map (CategoryTheory.Limits.Sigma.map f))).1 this

end HodgeLean.Foundations.Program
