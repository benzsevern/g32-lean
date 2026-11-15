import HodgeLean.Foundations.QuotientDuality.PersistenceOpenPointFibres
import HodgeLean.Foundations.QuotientDuality.PersistenceCentrePoints
import HodgeLean.Foundations.QuotientDuality.PersistenceSupport

/-! Unique complex fibres of the actual normalization transition off its centre. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_normalization_unique_complex_fibre
    {L : Type} [Field L] (B' B : Over (Spec ↧ℂ))
    [IsIntegral B'.left] [IsIntegral B.left] [IsSeparated B.hom]
    (η' : Spec ↧L ⟶ B'.left) (η : Spec ↧L ⟶ B.left)
    [QuasiCompact η'] [QuasiSeparated η'] [IsDominant η']
    [QuasiCompact η] [QuasiSeparated η] [IsDominant η]
    (b : B' ⟶ B) (hη : η' ≫ b.left = η) (I : B.left.IdealSheafData)
    (hblowup : ∀ (T : Scheme) (j : T ⟶ B.left),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap j).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ B'.left, u ≫ b.left = j)
    (w : s2b_normalizationOver B' η' ⟶ s2b_normalizationOver B η)
    (hw : η'.toNormalization ≫ w.left = η.toNormalization)
    (V : B.left.Opens) (hV : (V : Set B.left).Nonempty)
    (havoid : ∀ y ∈ V, y ∉ I.support)
    (y : ComplexPoint (s2b_normalizationOver B η))
    (hy : y ∈ Point.overOpen (η.fromNormalization ⁻¹ᵁ V)) :
    ∃! x : ComplexPoint (s2b_normalizationOver B' η'), Point.map w x = y := by
  have hwb := s2e_c1_normalization_transition_over B' B b η' η hη w hw
  have hwb' : w.left ≫ η.fromNormalization = η'.fromNormalization ≫ b.left :=
    congrArg (fun f => f.left) hwb
  obtain ⟨E, hE⟩ := persistence_normalization_off_centre_iso η' η b.left hη I
    hblowup w.left hw hwb' V hV havoid
  have hU : η'.fromNormalization ⁻¹ᵁ (b.left ⁻¹ᵁ V) =
      w.left ⁻¹ᵁ (η.fromNormalization ⁻¹ᵁ V) := by
    ext x
    change b.left (η'.fromNormalization x) ∈ V ↔
      η.fromNormalization (w.left x) ∈ V
    change (η'.fromNormalization ≫ b.left) x ∈ V ↔
      (w.left ≫ η.fromNormalization) x ∈ V
    rw [hwb']
    rfl
  exact persistence_unique_complex_fibre_of_open_iso w _ _ hU E hE y hy

lemma persistence_normalization_unique_complex_fibre_off_range
    {L : Type} [Field L] (B' B : Over (Spec ↧ℂ))
    [IsIntegral B'.left] [IsIntegral B.left] [IsSeparated B.hom]
    [LocallyOfFiniteType B.hom]
    (η' : Spec ↧L ⟶ B'.left) (η : Spec ↧L ⟶ B.left)
    [QuasiCompact η'] [QuasiSeparated η'] [IsDominant η']
    [QuasiCompact η] [QuasiSeparated η] [IsDominant η]
    (b : B' ⟶ B) (hη : η' ≫ b.left = η) (I : B.left.IdealSheafData)
    (hblowup : ∀ (T : Scheme) (j : T ⟶ B.left),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap j).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ B'.left, u ≫ b.left = j)
    (w : s2b_normalizationOver B' η' ⟶ s2b_normalizationOver B η)
    (hw : η'.toNormalization ≫ w.left = η.toNormalization)
    (y : ComplexPoint (s2b_normalizationOver B η))
    (hy : y ∉ Set.range (Point.map
      (s2b_toCover (s2b_normalizationMap B η) (s2c_subschemeι B I)))) :
    ∃! x : ComplexPoint (s2b_normalizationOver B' η'), Point.map w x = y := by
  dsimp only [s2b_toCover] at hy
  rw [persistence_pullback_point_range, persistence_subscheme_point_range B I] at hy
  have hnot : η.fromNormalization y.underlying ∉ I.support := by
    change (Point.map (s2b_normalizationMap B η) y).underlying ∉ I.support at hy
    rw [Point.underlying_map] at hy
    exact hy
  let V : B.left.Opens := ⟨(I.support : Set B.left)ᶜ, I.support.isClosed.isOpen_compl⟩
  exact persistence_normalization_unique_complex_fibre B' B η' η b hη I hblowup
    w hw V ⟨η.fromNormalization y.underlying, hnot⟩ (fun _ hy => hy) y hnot

end HodgeLean.Foundations.QuotientDuality
