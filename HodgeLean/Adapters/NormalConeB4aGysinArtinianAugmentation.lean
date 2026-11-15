import HodgeLean.Adapters.NormalConeB4aGysinSpreadSlice
import Mathlib.RingTheory.Artinian.Ring

/-! # Finiteness of augmented Artinian local fibres -/

noncomputable section
namespace HodgeLean.Adapters

/-- An Artinian local algebra augmented to its scalar field is finite over
that field, with no separate module-finiteness assumption. -/
theorem a3b4a_gysin_artinian_augmented_finite
    {k A : Type*} [Field k] [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [Algebra k A] (ε : A →ₐ[k] k) : Module.Finite k A := by
  have hε : Function.Surjective ε := fun x => ⟨algebraMap k A x, by simp⟩
  have hker : RingHom.ker ε = IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε
  have hnil : IsNilpotent (RingHom.ker ε) := by
    rw [hker]
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
  have hfg : (RingHom.ker ε).FG := (RingHom.ker ε).fg_of_isNoetherianRing
  exact Module.finite_of_surjective_of_ker_le_nilradical ε hε
    (hfg.isNilpotent_iff_le_nilradical.mp hnil) hfg

/-- An augmented Artinian special local fibre at a point of a finite type
algebra gives quasi-finiteness at that point. -/
theorem a3b4a_gysin_quasiFiniteAt_of_augmented_artinian_fibre
    {D R : Type*} [CommRing D] [IsLocalRing D] [CommRing R]
    [Algebra D R] [Algebra.FiniteType D R]
    (q : Ideal R) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal D)]
    [Nontrivial (Localization.AtPrime q ⧸
      (IsLocalRing.maximalIdeal D).map (algebraMap D (Localization.AtPrime q)))]
    [IsArtinianRing (Localization.AtPrime q ⧸
      (IsLocalRing.maximalIdeal D).map (algebraMap D (Localization.AtPrime q)))]
    :
    letI : Algebra (IsLocalRing.ResidueField D) (Localization.AtPrime q ⧸
        (IsLocalRing.maximalIdeal D).map (algebraMap D (Localization.AtPrime q))) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    ∀ (ε : (Localization.AtPrime q ⧸
      (IsLocalRing.maximalIdeal D).map (algebraMap D (Localization.AtPrime q)))
        →ₐ[IsLocalRing.ResidueField D] IsLocalRing.ResidueField D),
    Algebra.QuasiFiniteAt D q := by
  let I := (IsLocalRing.maximalIdeal D).map (algebraMap D (Localization.AtPrime q))
  let A := Localization.AtPrime q ⧸ I
  let k := IsLocalRing.ResidueField D
  letI : Algebra k A := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  intro ε
  letI : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have : Module.Finite k A := a3b4a_gysin_artinian_augmented_finite ε
  have : IsScalarTower D k A := IsScalarTower.of_algebraMap_eq fun d => rfl
  have hfinite : Algebra.QuasiFinite D A := Algebra.QuasiFinite.trans D k A
  have : Algebra.WeaklyQuasiFiniteAt D q := by
    rw [Algebra.weaklyQuasiFiniteAt_iff, ← q.over_def (IsLocalRing.maximalIdeal D)]
    exact hfinite
  exact Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt q

end HodgeLean.Adapters
