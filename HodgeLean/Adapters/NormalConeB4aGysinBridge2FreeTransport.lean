import HodgeLean.Adapters.NormalConeB4aGysinBridge2FreeSpread
import HodgeLean.Adapters.NormalConeB4aGysinBridge2LocalizedGraded
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! # Reformulated bridge of A3-B4a: freeness at the primes of a basic open

A finite module annihilated by a prime `P` of a Noetherian ring `S` is a module over the domain
`S ⧸ P`; at every prime `Q ⊇ P` outside the zero locus of one element `r ∉ P`, every localization
of it at `Q` is free of one rank over `S_Q ⧸ P S_Q`. Source: Matsumura, *Commutative Ring Theory*,
Theorem 4.10; Atiyah–Macdonald, *Introduction to Commutative Algebra*, Proposition 3.11. -/

noncomputable section
namespace HodgeLean.Adapters

/-- The image in `S ⧸ P` of the complement of a prime `Q ⊇ P` is the complement of `Q ⧸ P`. -/
theorem a3b4g_algebraMapSubmonoid_quotient {S : Type*} [CommRing S] (P Q : Ideal S)
    [Q.IsPrime] [(Q.map (Ideal.Quotient.mk P)).IsPrime] (hPQ : P ≤ Q) :
    Algebra.algebraMapSubmonoid (S ⧸ P) Q.primeCompl =
      (Q.map (Ideal.Quotient.mk P)).primeCompl := by
  have hcomap : (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hPQ]
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · rintro ⟨y, hy, hyx⟩ hx
    apply hy
    have h : Ideal.Quotient.mk P y ∈ Q.map (Ideal.Quotient.mk P) := by
      change algebraMap S (S ⧸ P) y ∈ _
      rw [hyx]
      exact hx
    rw [← hcomap]
    exact h
  · intro hx
    refine ⟨x, fun h => hx ?_, rfl⟩
    rw [← hcomap] at h
    exact h

/-- A finite module annihilated by a prime `P` of a Noetherian ring is free of one rank over
`S_Q ⧸ P S_Q`, in every localization at a prime `Q ⊇ P` outside the zero locus of one element
`r ∉ P`. Source: Matsumura, *Commutative Ring Theory*, Theorem 4.10. -/
theorem a3b4g_free_atPrime_of_torsion {S : Type*} [CommRing S] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] (M : Type*) [AddCommGroup M] [Module S M] [Module.Finite S M]
    (hM : Module.IsTorsionBySet S M (P : Set S)) :
    ∃ r : S, r ∉ P ∧ ∃ n : ℕ, ∀ (Q : Ideal S) [Q.IsPrime] (A : Type*) [CommRing A] [Algebra S A]
      [IsLocalization.AtPrime A Q], P ≤ Q → r ∉ Q →
      ∀ (M' : Type*) [AddCommGroup M'] [Module A M'] [Module S M']
        [IsScalarTower S A M'] (φ : M →ₗ[S] M'),
        IsLocalizedModule Q.primeCompl φ →
        Nonempty (M' ≃ₗ[A] (Fin n → A ⧸ P.map (algebraMap S A))) := by
  letI : Module (S ⧸ P) M := hM.module
  haveI : IsScalarTower S (S ⧸ P) M := hM.isScalarTower
  haveI : Module.Finite (S ⧸ P) M := Module.Finite.of_restrictScalars_finite S (S ⧸ P) M
  obtain ⟨r', hr', n, hfree⟩ := a3b4g_exists_free_rank_basicOpen (R := S ⧸ P) M
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r'
  refine ⟨r, fun h => hr' (Ideal.Quotient.eq_zero_iff_mem.mpr h), n,
    fun Q _ A _ _ _ hPQ hrQ M' _ _ _ _ φ hφ => ?_⟩
  set Q' := Q.map (Ideal.Quotient.mk P) with hQ'
  have hcomap : Q'.comap (Ideal.Quotient.mk P) = Q := by
    rw [hQ', Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hPQ]
  haveI : Q'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hPQ)
  have hr'Q : Ideal.Quotient.mk P r ∉ Q' := fun h => hrQ (by
    rw [← hcomap, Ideal.mem_comap]
    exact h)
  obtain ⟨e₁⟩ := hfree Q' hr'Q
  have hsub := a3b4g_algebraMapSubmonoid_quotient P Q hPQ
  let f₁ : M →ₗ[S ⧸ P] (Fin n → Localization.AtPrime Q') :=
    (e₁.restrictScalars (S ⧸ P)).toLinearMap ∘ₗ LocalizedModule.mkLinearMap Q'.primeCompl M
  haveI : IsLocalizedModule Q'.primeCompl f₁ :=
    IsLocalizedModule.of_linearEquiv _ _ (e₁.restrictScalars (S ⧸ P))
  haveI : IsLocalizedModule (Algebra.algebraMapSubmonoid (S ⧸ P) Q.primeCompl) f₁ := by
    rw [hsub]
    infer_instance
  haveI h₁ : IsLocalizedModule Q.primeCompl (f₁.restrictScalars S) :=
    IsLocalizedModule.restrictScalars _ f₁
  let g₁ := Algebra.linearMap (S ⧸ P) (Localization.AtPrime Q')
  haveI : IsLocalizedModule Q'.primeCompl g₁ := inferInstance
  haveI : IsLocalizedModule (Algebra.algebraMapSubmonoid (S ⧸ P) Q.primeCompl) g₁ := by
    rw [hsub]
    infer_instance
  haveI : IsLocalizedModule Q.primeCompl (g₁.restrictScalars S) :=
    IsLocalizedModule.restrictScalars _ g₁
  let q := a3b4g_quotientLocalizationMap (T := S) (T' := A) P (P.map (algebraMap S A)) rfl
  haveI : IsLocalizedModule Q.primeCompl q :=
    a3b4g_quotientLocalizationMap_isLocalizedModule Q.primeCompl P _ rfl
  let ι := IsLocalizedModule.linearEquiv Q.primeCompl (g₁.restrictScalars S) q
  let ιn := LinearEquiv.piCongrRight (fun _ : Fin n => ι)
  haveI : IsLocalizedModule Q.primeCompl (ιn.toLinearMap ∘ₗ f₁.restrictScalars S) :=
    IsLocalizedModule.of_linearEquiv _ _ ιn
  exact ⟨(IsLocalizedModule.linearEquiv Q.primeCompl φ
    (ιn.toLinearMap ∘ₗ f₁.restrictScalars S)).extendScalarsOfIsLocalization Q.primeCompl A⟩

end HodgeLean.Adapters
