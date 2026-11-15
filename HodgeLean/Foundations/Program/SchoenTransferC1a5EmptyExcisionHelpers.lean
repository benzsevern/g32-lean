import HodgeLean.Foundations.Program.SchoenTransferC1a5CollarExcisionHelpers

/-! Singular relative excision for attachments along an empty space.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- An actual pushout along an empty attaching space gives integral singular relative comparison.
Source: Hatcher §2.1, Theorem 2.20, empty boundary case of neighborhood excision. -/
lemma c1a5_empty_attachment_singular_excision {A B C D : TopCat.{0}} [IsEmpty A]
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) :
    QuasiIso (c1a5RelativeMap c1a5Chains (TopCat.toSSet.map l) (TopCat.toSSet.map r)
      (TopCat.toSSet.map t) (TopCat.toSSet.map b) (by
        rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
        exact congrArg TopCat.toSSet.map sq.w.symm)) := by
  have sq' : IsPushout t (𝟙 A ≫ l) r b := by simpa only [Category.id_comp] using sq
  have hc : IsClosed (Set.range (𝟙 A ≫ l)) := by
    rw [Set.range_eq_empty]
    exact isClosed_empty
  let H : TopCat.Homotopy (𝟙 A) (𝟙 A ≫ 𝟙 A) :=
    { toFun := fun p ↦ p.2
      continuous_toFun := continuous_snd
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl }
  exact c1a5_collar_attachment_singular_excision sq'
    (Topology.IsOpenEmbedding.of_isEmpty l) (Function.injective_of_subsingleton _) hc
    (𝟙 A) (Category.id_comp _) H (fun _ _ ↦ rfl)

end HodgeLean.Foundations.Program
