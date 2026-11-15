import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageTwo.Defs

/-! # Retained affine restrictions and their actual deck maps
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageThree

/-- Coefficient evaluation through the specified original field point.
Source: Stacks Project, tag 035H, affine normalization.
HC no distance; AV milestone no distance. -/
def fieldCoeff {K : Type} [Field K] {V : Scheme} (η : Spec ↧K ⟶ V) :
    Γ(V, ⊤) →+* K := (η.appTop ≫ (Scheme.ΓSpecIso ↧K).hom).hom

/-- The original field point in the actual normalization restriction.
Source: Stacks Project, tag 035H, normalization factorization.
HC no distance; AV milestone no distance. -/
def restrictedFieldPoint {K : Type} [Field K] {Y V : Scheme}
    (f : Spec ↧K ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (u : V ⟶ Y) (η : Spec ↧K ⟶ V) (hη : η ≫ u = f) :
    Spec ↧K ⟶ pullback f.fromNormalization u :=
  pullback.lift f.toNormalization η
    (f.toNormalization_fromNormalization.trans hη.symm)

/-- Restriction of the actual deck morphism to the inverse image of a base chart.
Source: Hartshorne, Algebraic Geometry, II.3, fibre products.
HC no distance; AV milestone no distance. -/
def restrictedDeck {N Y V : Scheme} (β : N ⟶ Y) (d : N ⟶ N)
    (hd : d ≫ β = β) (u : V ⟶ Y) : pullback β u ⟶ pullback β u :=
  pullback.lift (pullback.fst β u ≫ d) (pullback.snd β u)
    (by rw [Category.assoc, hd, pullback.condition])

example {K : Type} [Field K] {V : Scheme} (η : Spec ↧K ⟶ V) :
    fieldCoeff η = (η.appTop ≫ (Scheme.ΓSpecIso ↧K).hom).hom := rfl

example {K : Type} [Field K] {Y V : Scheme}
    (f : Spec ↧K ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (u : V ⟶ Y) (η : Spec ↧K ⟶ V) (hη : η ≫ u = f) :
    restrictedFieldPoint f u η hη ≫ pullback.snd _ _ = η := by
  simp [restrictedFieldPoint]

example {N Y V : Scheme} (β : N ⟶ Y) (d : N ⟶ N)
    (hd : d ≫ β = β) (u : V ⟶ Y) :
    restrictedDeck β d hd u ≫ pullback.fst _ _ = pullback.fst β u ≫ d := by
  simp [restrictedDeck]

example : fieldCoeff (𝟙 (Spec ↧ℚ)) (3 : Γ(Spec ↧ℚ, ⊤)) = 3 := map_ofNat _ _

example : restrictedFieldPoint (𝟙 (Spec ↧ℚ)) (𝟙 _) (𝟙 _) (by simp) ≫
    pullback.snd _ _ = 𝟙 _ := by
  simp [restrictedFieldPoint]

example : restrictedDeck (𝟙 (Spec ↧ℚ)) (𝟙 _) (by simp) (𝟙 _) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [restrictedDeck]

end AlgebraicGeometry.RamifiedNormalization.StageThree
