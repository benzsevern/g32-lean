import HodgeLean.Foundations.BundleResolution.ChernExtendedBinaryComparisonHelpers
import Mathlib.Algebra.Homology.QuasiIso

/-! # Binary sums of integer-indexed rational quasi-isomorphisms

The homology functor carries the actual binary sum map to the sum of its
homology maps under its additive biproduct isomorphism.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace HodgeLean.Foundations.BundleResolution

theorem i1_integerBiprodMap_quasiIso
    {A B C D : CochainComplex (ModuleCat.{0} ℚ) ℤ} (f : A ⟶ B) (g : C ⟶ D)
    [QuasiIso f] [QuasiIso g] : QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℤ) n
  letI : PreservesBinaryBiproduct A C F := preservesBinaryBiproduct_of_preservesBinaryProduct F
  letI : PreservesBinaryBiproduct B D F := preservesBinaryBiproduct_of_preservesBinaryProduct F
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
    apply biprod.hom_ext <;>
      simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, biprod.lift_snd,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.map_fst, biprod.map_snd, ← F.map_comp]
  have hf : F.map (biprod.map f g) =
      (F.mapBiprod A C).hom ≫ biprod.map (F.map f) (F.map g) ≫ (F.mapBiprod B D).inv := by
    have hh := congrArg (fun m => m ≫ (F.mapBiprod B D).inv) he
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh
  change IsIso (F.map (biprod.map f g))
  rw [hf]
  infer_instance

theorem i1_extendedBinaryComparison_quasiIso
    {A B C D : ChainComplex (ModuleCat.{0} ℚ) ℕ} (p : ℤ)
    (a : A.extend (ComplexShape.embeddingUpIntLE p) ⟶ B.extend (ComplexShape.embeddingUpIntLE 0))
    (c : C.extend (ComplexShape.embeddingUpIntLE p) ⟶ D.extend (ComplexShape.embeddingUpIntLE 0))
    [QuasiIso a] [QuasiIso c] : QuasiIso (i1_extendedBinaryComparison p a c) := by
  let Fp := (ComplexShape.embeddingUpIntLE p).extendFunctor (ModuleCat.{0} ℚ)
  let F0 := (ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{0} ℚ)
  letI : PreservesBinaryBiproduct A C Fp := preservesBinaryBiproduct_of_preservesBinaryProduct Fp
  letI : PreservesBinaryBiproduct B D F0 := preservesBinaryBiproduct_of_preservesBinaryProduct F0
  let m : (Fp.obj A ⊞ Fp.obj C) ⟶ (F0.obj B ⊞ F0.obj D) := biprod.map a c
  haveI : QuasiIso m := i1_integerBiprodMap_quasiIso a c
  haveI : QuasiIso (Fp.mapBiprod A C).hom := quasiIso_of_isIso _
  haveI : QuasiIso (F0.mapBiprod B D).inv := quasiIso_of_isIso _
  haveI : QuasiIso (m ≫ (F0.mapBiprod B D).inv) := quasiIso_comp m _
  change QuasiIso ((Fp.mapBiprod A C).hom ≫ m ≫ (F0.mapBiprod B D).inv)
  exact quasiIso_comp (Fp.mapBiprod A C).hom (m ≫ (F0.mapBiprod B D).inv)

end HodgeLean.Foundations.BundleResolution
