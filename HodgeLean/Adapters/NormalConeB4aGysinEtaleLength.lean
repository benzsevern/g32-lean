import HodgeLean.Adapters.NormalConeB4aGysinFiniteNeighborhood
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Local lengths under étale changes of the finite model -/

noncomputable section
namespace HodgeLean.Adapters

/-- A flat unramified local extension of essentially finite type preserves the
self-length of the local ring, including nonreduced contributions. -/
theorem a3b4a_gysin_local_length_eq_of_flat_unramified
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Module.Flat A B] [Algebra.FormallyUnramified A B] :
    Module.length B B = Module.length A A := by
  have hr : Module.length B (B ⧸ IsLocalRing.maximalIdeal B) = 1 := by
    change Module.length B (IsLocalRing.ResidueField B) = 1
    rw [Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := B))]
    exact Module.length_eq_one _ _
  have h := IsLocalRing.length_baseChange A B A
  rw [(TensorProduct.AlgebraTensorModule.rid A B B).length_eq,
    Algebra.FormallyUnramified.map_maximalIdeal,
    hr, mul_one] at h
  exact h

open CategoryTheory AlgebraicGeometry

/-- Étale morphisms preserve the full self-length of each source stalk. -/
theorem a3b4a_gysin_etale_stalk_length
    {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] (x : X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) =
      Module.length (Y.presheaf.stalk (f x)) (Y.presheaf.stalk (f x)) := by
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.flat_algebraMap_iff, RingHom.algebraMap_toAlgebra]
    exact Flat.stalkMap f x
  exact a3b4a_gysin_local_length_eq_of_flat_unramified
    (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)

open CategoryTheory.Limits

/-- The finite flat neighborhood after étale base change preserves the exact
source stalk length at its chosen point. -/
theorem a3b4a_gysin_finite_flat_etale_neighborhood_length
    {X B : Scheme.{0}} (f : X ⟶ B) [LocallyOfFiniteType f] [IsSeparated f] [Flat f]
    (x : X) (hx : f.QuasiFiniteAt x) :
    ∃ (U : Scheme.{0}) (g : U ⟶ B), Etale g ∧ f x ∈ Set.range g ∧
      ∃ (V W : (pullback f g).Opens) (v : V), IsCompl V W ∧
        IsFinite (V.ι ≫ pullback.snd f g) ∧ Flat (V.ι ≫ pullback.snd f g) ∧
        pullback.fst f g v.1 = x ∧
        Module.length (V.toScheme.presheaf.stalk v) (V.toScheme.presheaf.stalk v) =
          Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  obtain ⟨U, g, hg, hxg, V, W, v, hVW, hfin, hflat, hv⟩ :=
    a3b4a_gysin_finite_flat_etale_neighborhood f x hx
  letI : Etale g := hg
  refine ⟨U, g, hg, hxg, V, W, v, hVW, hfin, hflat, hv, ?_⟩
  have h := a3b4a_gysin_etale_stalk_length (V.ι ≫ pullback.fst f g) v
  change Module.length (V.toScheme.presheaf.stalk v) (V.toScheme.presheaf.stalk v) =
    Module.length (X.presheaf.stalk (pullback.fst f g v.1))
      (X.presheaf.stalk (pullback.fst f g v.1)) at h
  rw [hv] at h
  exact h

end HodgeLean.Adapters
