import HodgeLean.Foundations.QuotientDuality.MonomialFractionGalois
import HodgeLean.Foundations.QuotientDuality.MonomialGaloisInvariants
import HodgeLean.Foundations.QuotientDuality.MonomialFiniteNormalCover

/-! Galois invariant presentations from normal root-generated integral covers. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality
universe u v w

theorem normal_root_cover_invariant_presentation
    {R : Type u} {A : Type w} {K L : Type v}
    [CommRing R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [CharZero K] [Field L]
    [Algebra R K] [Algebra R A] [Algebra R L]
    [Algebra.IsIntegral R A] [Algebra.FiniteType R A]
    (n m : ℕ) (hm : 0 < m) (ζ : K) (hζ : IsPrimitiveRoot ζ m)
    (v : K) (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (f : K →ₐ[R] L) (σ : A →ₐ[R] L) (hσ : Function.Injective σ)
    (V : A) (hV : σ V = f v) (W : Fin n → A) (U : A)
    (hgenA : Algebra.adjoin R (Set.range W ∪ {U}) = ⊤)
    (z : Fin n → R) (ε : R)
    (hW : ∀ j, W j ^ m = algebraMap R A (z j)) (hU : U ^ m = algebraMap R A ε) :
    ∃ β : integralClosure R K →ₐ[R] A,
      Function.Injective β ∧ β.toRingHom.Finite ∧ (∀ b, σ (β b) = f (b : K)) ∧
      ∃ (G : Type w) (_ : Group G) (_ : Finite G),
        ∃ ρ : G →* (A ≃ₐ[R] A),
          ∀ a : A, (∃ b, β b = a) ↔ ∀ g, ρ g a = a := by
  let F := FractionRing A
  let σF : F →ₐ[R] L := IsFractionRing.liftAlgHom (g := σ) hσ
  have hσF (a : A) : σF (algebraMap A F a) = σ a :=
    IsFractionRing.lift_algebraMap (K := F) (g := σ.toRingHom) hσ a
  obtain ⟨fF, hfF⟩ := lift_generated_field v hgen f σF
    ⟨algebraMap A F V, (hσF V).trans hV⟩
  letI : Algebra K F := fF.toRingHom.toAlgebra
  letI : IsScalarTower R K F := IsScalarTower.of_algebraMap_eq' fF.comp_algebraMap.symm
  obtain ⟨hgalois, hfinite⟩ := power_root_fractionField_galois
    (R := R) (A := A) (K := K) (F := F) n m hm
    ζ hζ W U hgenA
    (fun j => ⟨algebraMap R K (z j), by
      rw [← map_pow, hW, ← IsScalarTower.algebraMap_apply R A F,
        ← IsScalarTower.algebraMap_apply R K F]⟩)
    ⟨algebraMap R K ε, by
      rw [← map_pow, hU, ← IsScalarTower.algebraMap_apply R A F,
        ← IsScalarTower.algebraMap_apply R K F]⟩
  letI : IsGalois K F := hgalois
  letI : FiniteDimensional K F := hfinite
  obtain ⟨ρ, β, hβ, hρ, hβF, hfixed⟩ :=
    galois_cover_normalization_invariants (R := R) (K := K) (A := A) (F := F)
  have hβσ (z : integralClosure R K) : σ (β z) = f (z : K) :=
    (hσF (β z)).symm.trans
      ((congrArg σF (hβF z)).trans (AlgHom.congr_fun hfF (z : K)))
  have hcomp : β.toRingHom.comp (algebraMap R (integralClosure R K)) = algebraMap R A :=
    β.comp_algebraMap
  have hβint : β.toRingHom.IsIntegral := RingHom.IsIntegral.tower_top _ _ (by
    rw [hcomp]
    exact algebraMap_isIntegral_iff.mpr inferInstance)
  have hβft : β.toRingHom.FiniteType := RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap R (integralClosure R K)) (by
      rw [hcomp]
      exact RingHom.finiteType_algebraMap.mpr inferInstance)
  exact ⟨β, hβ, hβint.to_finite hβft, hβσ,
    F ≃ₐ[K] F, inferInstance, inferInstance, ρ, hfixed⟩

#print axioms normal_root_cover_invariant_presentation
end HodgeLean.Foundations.QuotientDuality
