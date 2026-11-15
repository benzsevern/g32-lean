import HodgeLean.Foundations.QuotientDuality.PersistenceDefs
import HodgeLean.Foundations.Program.SchoenTowerDefs
import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationMapHelpers

/-! Actual inverse-image supports in normalization squares. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_pullback_point_range
    {R : Type} [CommRing R] {W B K : Over (Spec ↧R)} (β : W ⟶ B) (k : K ⟶ B) :
    Set.range (Point.map (pullback.fst β k)) =
      Point.map β ⁻¹' Set.range (Point.map k) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨Point.map (pullback.snd β k) z, ?_⟩
    change (z ≫ pullback.snd β k) ≫ k = (z ≫ pullback.fst β k) ≫ β
    simp only [Category.assoc, pullback.condition]
  · rintro ⟨z, hz⟩
    exact ⟨pullback.lift x z hz.symm, pullback.lift_fst _ _ _⟩

lemma persistence_exceptional_support_square
    {R : Type} [CommRing R] {X Y B' B K : Over (Spec ↧R)}
    (β : X ⟶ B') (βprev : Y ⟶ B) (b : B' ⟶ B) (k : K ⟶ B)
    (w : X ⟶ Y) (hw : w ≫ βprev = β ≫ b) :
    Point.map w ⁻¹' Set.range (Point.map (pullback.fst βprev k)) =
      Set.range (Point.map (pullback.fst β (pullback.fst b k))) := by
  rw [persistence_pullback_point_range βprev k,
    persistence_pullback_point_range β (pullback.fst b k),
    persistence_pullback_point_range b k]
  ext x
  change (x ≫ w) ≫ βprev ∈ Set.range (Point.map k) ↔
    (x ≫ β) ≫ b ∈ Set.range (Point.map k)
  rw [Category.assoc, hw, Category.assoc]

lemma persistence_normalization_exceptional_support
    {L : Type} [Field L] {B' B : Over (Spec ↧ℂ)} [IsSeparated B.hom]
    (η' : Spec ↧L ⟶ B'.left) (η : Spec ↧L ⟶ B.left)
    [QuasiCompact η'] [QuasiSeparated η'] [QuasiCompact η] [QuasiSeparated η]
    (b : B' ⟶ B) (hη : η' ≫ b.left = η)
    (w : s2b_normalizationOver B' η' ⟶ s2b_normalizationOver B η)
    (hw : η'.toNormalization ≫ w.left = η.toNormalization)
    {K : Over (Spec ↧ℂ)} (k : K ⟶ B) :
    Point.map w ⁻¹' Set.range (Point.map
      (s2b_toCover (s2b_normalizationMap B η) k)) =
      Set.range (Point.map (s2b_toCover (s2b_normalizationMap B' η')
        (pullback.fst b k))) := by
  exact persistence_exceptional_support_square _ _ b k w
    (s2e_c1_normalization_transition_over B' B b η' η hη w hw)

lemma persistence_relative_bijective_of_equal_source_subset
    (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (A : Set Y) (B : Set X) (hAB : f ⁻¹' A = B)
    (hmap : ∀ x, x ∈ B → f x ∈ A) (n : ℕ)
    (hbij : Function.Bijective (persistenceRelativePullback K f A n)) :
    Function.Bijective (AlgebraicTopology.Singular.relativeCohomologyMap K n
      (TopPair.ofSubsetHom f hmap)) := by
  subst B
  exact hbij

end HodgeLean.Foundations.QuotientDuality
