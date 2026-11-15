import HodgeLean.Foundations.BundleThom.ChainSquareAugmentationHelpers
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Rational chain equivalences under binary direct sum

HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits HomologicalComplex
namespace HodgeLean.Foundations.BundleThom

/-- Binary direct sum preserves rational chain quasi-isomorphisms.
Source: Hatcher, Algebraic Topology, §2.1, additivity of singular homology. -/
theorem i1_biprodMap_quasiIso
    {A B C D : ChainComplex (ModuleCat ℚ) ℕ} (f : A ⟶ B) (g : C ⟶ D)
    [QuasiIso f] [QuasiIso g] : QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n
  letI : PreservesBinaryBiproduct A C F :=
    preservesBinaryBiproduct_of_preservesBinaryProduct F
  letI : PreservesBinaryBiproduct B D F :=
    preservesBinaryBiproduct_of_preservesBinaryProduct F
  haveI : IsIso (F.map f) := by
    change IsIso (homologyMap f n)
    infer_instance
  haveI : IsIso (F.map g) := by
    change IsIso (homologyMap g n)
    infer_instance
  haveI : IsIso (biprod.map (F.map f) (F.map g)) :=
    (biprod.mapIso (asIso (F.map f)) (asIso (F.map g))).isIso_hom
  have he : F.map (biprod.map f g) ≫ (F.mapBiprod B D).hom =
      (F.mapBiprod A C).hom ≫ biprod.map (F.map f) (F.map g) := by
    apply biprod.hom_ext <;> simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, biprod.lift_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      biprod.map_fst, biprod.map_snd, ← F.map_comp]
  have hf : F.map (biprod.map f g) =
      (F.mapBiprod A C).hom ≫ biprod.map (F.map f) (F.map g) ≫
        inv ((F.mapBiprod B D).hom) := by
    simpa [Category.assoc] using congrArg (fun m => m ≫ inv ((F.mapBiprod B D).hom)) he
  change IsIso (F.map (biprod.map f g))
  rw [hf]
  infer_instance

end HodgeLean.Foundations.BundleThom
