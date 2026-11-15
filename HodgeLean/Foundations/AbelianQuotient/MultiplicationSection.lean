import HodgeLean.Foundations.AbelianQuotient.SemisimpleInverse
import HodgeLean.Foundations.AbelianQuotient.Product

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

set_option maxRecDepth 2000 in
/-- A homomorphism has an algebraic inner inverse up to a positive multiplication factor. -/
theorem hom_inner_inverse {A B : Variety} (f : Hom A B) :
    ∃ (N : ℕ) (s : Hom B A), 0 < N ∧
      f.hom ≫ s.hom ≫ f.hom = f.hom ^ (N : ℤ) := by
  let R := product A B
  haveI : IsMonHom (1 : B.X ⟶ A.X) := by
    rw [Hom.one_def]
    infer_instance
  let j : B.X ⟶ R.X := lift (1 : B.X ⟶ A.X) (𝟙 B.X)
  let k : A.X ⟶ R.X := lift (𝟙 A.X) (1 : A.X ⟶ B.X)
  haveI : IsMonHom j := by
    change IsMonHom (lift (1 : B.X ⟶ A.X) (𝟙 B.X))
    infer_instance
  let u : AbelianEnd R.X := ⟨fst A.X B.X ≫ f.hom ≫ j, inferInstance⟩
  obtain ⟨N, v, hN, hu⟩ := algebraic_inner_inverse R u
  let s : Hom B A := ⟨j ≫ v.hom ≫ fst A.X B.X, inferInstance⟩
  refine ⟨N, s, hN, ?_⟩
  have h := congrArg (fun e : R.X ⟶ R.X => k ≫ e ≫ snd A.X B.X) hu
  have hleft : k ≫ (u.hom ≫ v.hom ≫ u.hom) ≫ snd A.X B.X =
      f.hom ≫ s.hom ≫ f.hom := by
    dsimp only [u, s, k, j]
    simp only [Category.assoc, lift_fst_assoc, lift_snd, Category.comp_id, Category.id_comp]
  have hright : k ≫ (u.hom ^ (N : ℤ)) ≫ snd A.X B.X = f.hom ^ (N : ℤ) := by
    rw [← Category.assoc, GrpObj.comp_zpow, GrpObj.zpow_comp]
    dsimp only [u, k, j]
    simp only [Category.assoc, lift_fst_assoc, lift_snd, Category.comp_id, Category.id_comp]
  exact hleft.symm.trans (h.trans hright)

end HodgeLean.Foundations.AbelianQuotient
