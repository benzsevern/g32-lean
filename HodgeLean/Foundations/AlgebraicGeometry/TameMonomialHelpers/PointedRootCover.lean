import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.UniversalRootCover
import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.LocalizedRotations
import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.RootCoverEvaluations

/-! # Normal root covers at the specified evaluation
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.TameMonomialCover.Helpers
universe w
variable {κbase : Type w} [Field κbase] [IsAlgClosed κbase] [CharZero κbase]
universe u v

/-- The specified zero-root evaluation has a normal local root cover carrying its coordinate rotation and an injective ambient-field map.
Source: Mathlib, smooth local normality, integral minimal primes and localization at the evaluation kernel. -/
theorem pointed_normal_root_cover
    (n m : ℕ) (hm : 0 < m) (R : Type u) (L : Type v)
    [CommRing R] [Field L] [Algebra κbase R] [Algebra R L] [Algebra κbase L]
    [IsScalarTower κbase R L]
    (c : MvPolynomial (Fin n) κbase →ₐ[κbase] R) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap R L)) (ε : R) (hε : IsUnit ε)
    (w : Fin n → L) (hw : ∀ k, w k ^ m = algebraMap R L (c (MvPolynomial.X k)))
    (hwint : ∀ k, _root_.IsIntegral R (w k))
    (u : L) (hu : u ^ m = algebraMap R L ε)
    (p : integralClosure R L →+* κbase) (j : Fin n) (hpw : p ⟨w j, hwint j⟩ = 0)
    (ζ : κbase) (hζ : IsPrimitiveRoot ζ m) :
    ∃ (A : Type (max u w)) (hA : CommRing A), letI := hA
      ∃ (_ : IsDomain A) (_ : IsIntegrallyClosed A)
        (i : R →+* A) (σ : A →+* L) (q : A →+* κbase)
        (W : Fin n → A) (U : A) (G : A ≃+* A),
        Function.Injective σ ∧ σ.comp i = algebraMap R L ∧
        (∀ k, σ (W k) = w k) ∧ σ U = u ∧
        (∀ r, G (i r) = i r) ∧
        (∀ k, G (W k) = if k = j then i (c (MvPolynomial.C ζ)) * W k else W k) ∧
        G U = U ∧ q.comp G.toRingHom = q ∧
        (∀ x (b : integralClosure R L), σ x = (b : L) → q x = p b) := by
  let f : R →ₐ[κbase] L := IsScalarTower.toAlgHom κbase R L
  obtain ⟨A₀, hA₀, i₀, b₀, W₀, U₀, τ, hi₀, hb₀, hparam,
    hWpow, hUpow, hUunit, hτi, hτW, hτU, hWcan, hrot, hext⟩ :=
    universal_root_cover n m hm R L c hc f ε hε w hw u hu
  letI := hA₀
  have hτi' : τ.comp i₀ = algebraMap R L := RingHom.ext hτi
  obtain ⟨β, q₀, hβ, rfl, hβi⟩ := integral_cover_evaluation i₀ hi₀ τ hτi' p
  have hqW : (p.comp β) (W₀ j) = 0 := by
    have H : β (W₀ j) = ⟨w j, hwint j⟩ := Subtype.ext ((hβ _).trans (hτW j))
    change p (β (W₀ j)) = 0
    rw [H, hpw]
  let weights (k : Fin n) : κbaseˣ := if k = j then (hζ.isUnit hm.ne').unit else 1
  have hweights (k : Fin n) : (weights k : κbase) ^ m = 1 := by
    dsimp only [weights]
    split_ifs
    · simpa only [IsUnit.unit_spec] using hζ.pow_eq_one
    · simp
  obtain ⟨G₀, hG₀i, hG₀W, hG₀U⟩ := hrot weights hweights
  have hG₀W' (k : Fin n) : G₀ (W₀ k) =
      if k = j then i₀ (c (MvPolynomial.C ζ)) * W₀ k else W₀ k := by
    rw [hG₀W]
    by_cases hk : k = j
    · simp only [weights, if_pos hk, IsUnit.unit_spec]
    · simp only [weights, if_neg hk, Units.val_one, MvPolynomial.C_1, map_one, one_mul]
  have hqG : (p.comp β).comp G₀.toRingHom = p.comp β := by
    apply hext
    · intro r
      change (p.comp β) (G₀ (i₀ r)) = _
      rw [hG₀i]
    · intro k
      change (p.comp β) (G₀ (W₀ k)) = _
      rw [hG₀W']
      by_cases hk : k = j
      · rw [if_pos hk, hk, map_mul, hqW, mul_zero]
      · rw [if_neg hk]
    · change (p.comp β) (G₀ U₀) = _
      rw [hG₀U]
  let Q := RingHom.ker (p.comp β)
  haveI : Q.IsPrime := RingHom.ker_isPrime (p.comp β)
  let A := Localization.AtPrime Q
  obtain ⟨hdom, hnormal⟩ := etale_root_localization_normal n A₀ b₀ hb₀ Q
  letI : IsDomain A := hdom
  letI : IsIntegrallyClosed A := hnormal
  have hmin := integral_cover_kernel_minimal i₀ hi₀ τ (by rw [hτi']; exact hinj)
  have hsub : RingHom.ker τ ≤ Q := by
    intro a ha
    have H : β a = 0 := Subtype.ext ((hβ a).trans ha)
    change p (β a) = 0
    rw [H, map_zero]
  obtain ⟨σ, hσinj, hσ⟩ := localized_component_embedding Q τ hmin hsub (S := A)
  obtain ⟨G, q, hG, hq, hqG⟩ := localized_rotation (p.comp β) G₀ hqG (S := A)
  let i : R →+* A := (algebraMap A₀ A).comp i₀
  let W (k : Fin n) : A := algebraMap A₀ A (W₀ k)
  let U : A := algebraMap A₀ A U₀
  refine ⟨A, inferInstance, inferInstance, inferInstance, i, σ, q, W, U, G,
    hσinj, ?_, ?_, ?_, ?_, ?_, ?_, hqG, ?_⟩
  · rw [show σ.comp i = (σ.comp (algebraMap A₀ A)).comp i₀ from rfl, hσ, hτi']
  · intro k
    exact (RingHom.congr_fun hσ (W₀ k)).trans (hτW k)
  · exact (RingHom.congr_fun hσ U₀).trans hτU
  · intro r
    change G (algebraMap A₀ A (i₀ r)) = algebraMap A₀ A (i₀ r)
    rw [hG, hG₀i]
  · intro k
    change G (algebraMap A₀ A (W₀ k)) = _
    rw [hG, hG₀W']
    split_ifs
    · exact map_mul (algebraMap A₀ A) _ _
    · rfl
  · exact (hG U₀).trans (congrArg (algebraMap A₀ A) hG₀U)
  · intro x b hx
    apply localized_integral_evaluation β p σ (fun a => ?_) q hq x b hx
    exact (RingHom.congr_fun hσ a).trans (hβ a).symm

end AlgebraicGeometry.TameMonomialCover.Helpers
