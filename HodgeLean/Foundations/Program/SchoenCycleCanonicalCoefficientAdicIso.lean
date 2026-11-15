import HodgeLean.Foundations.Program.SchoenCycleFormalLocalCoordinates
import HodgeLean.Foundations.Program.SchoenCycleAdicFilteredMapExt
import HodgeLean.Foundations.Program.SchoenCycleAdicMapExtendedPowers
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The canonical adic map defined by actual cotangent representatives is bijective whenever the actual local algebra has a coefficient formal model.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 2, 7 and 10. -/
theorem s2e_canonical_coefficient_adic_map_bijective
    (k R σ : Type*) [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] [Finite σ]
    (E : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[k]
      AdicCompletion (idealOfVars σ k) (MvPolynomial σ k))
    (c : σ → IsLocalRing.maximalIdeal R)
    (b : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent)
    (hb : ∀ i, b i = (IsLocalRing.maximalIdeal R).toCotangent (c i)) :
    let f : MvPolynomial σ k →ₐ[k] R := aeval (fun i => (c i).val)
    ∃ h : ∀ n r, r ∈ idealOfVars σ k ^ n → f r ∈ IsLocalRing.maximalIdeal R ^ n,
      Function.Bijective (s2e_adic_algebra_map (idealOfVars σ k) (IsLocalRing.maximalIdeal R) f h) := by
  dsimp only
  let I := idealOfVars σ k
  let P := MvPolynomial σ k
  let D := AdicCompletion I P
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  letI : I.IsMaximal := s2e_coefficient_origin_isMaximal k σ
  letI : IsLocalRing D := s2e_maximal_adic_isLocalRing I (idealOfVars_fg σ k)
  let f : P →ₐ[k] R := aeval (fun i => (c i).val)
  have hI : I ≤ (IsLocalRing.maximalIdeal R).comap f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (aeval (R := k) (fun i => (c i).val)) (X i) ∈ IsLocalRing.maximalIdeal R
    rw [aeval_X]
    exact (c i).property
  have h : ∀ n r, r ∈ I ^ n → f r ∈ IsLocalRing.maximalIdeal R ^ n := by
    intro n r hr
    have hh : (I ^ n).map f.toRingHom ≤ IsLocalRing.maximalIdeal R ^ n := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hI) n
    exact hh (Ideal.mem_map_of_mem f.toRingHom hr)
  refine ⟨h, ?_⟩
  obtain ⟨F, hF⟩ := s2e_formal_local_coordinates_of_cotangent_basis k R σ E c b hb
  let G := s2e_adic_algebra_map I (IsLocalRing.maximalIdeal R) f h
  have hJ : I.map (algebraMap P D) = IsLocalRing.maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le I I le_rfl (idealOfVars_fg σ k))
  have hmap : (I.map (algebraMap P D)).map F.toRingHom =
      (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
    rw [hJ, ← AdicCompletion.maximalIdeal_eq_map]
    exact IsLocalRing.map_ringEquiv_maximalIdeal F.toRingEquiv
  have hFp : ∀ n r, r ∈ (I.map (algebraMap P D)) ^ n →
      F r ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) ^ n := by
    intro n r hr
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem F.toRingHom hr
  let ofP := IsScalarTower.toAlgHom k P D
  have he : G.comp ofP = F.toAlgHom.comp ofP := by
    apply MvPolynomial.algHom_ext
    intro i
    change G (AdicCompletion.of I P (X i)) = F (AdicCompletion.of I P (X i))
    rw [s2e_adic_algebra_map_of, hF]
    change AdicCompletion.of (IsLocalRing.maximalIdeal R) R
      ((aeval (R := k) (fun i => (c i).val)) (X i)) = _
    rw [aeval_X]
  have hGF : G = F.toAlgHom := s2e_adic_filtered_algHom_ext I (IsLocalRing.maximalIdeal R)
    (idealOfVars_fg σ k) (IsNoetherian.noetherian _) G F.toAlgHom
    (s2e_adic_algebra_map_preserves_extended_powers I _ (idealOfVars_fg σ k)
      (IsNoetherian.noetherian _) f h) hFp (fun r => DFunLike.congr_fun he r)
  rw [show s2e_adic_algebra_map I (IsLocalRing.maximalIdeal R) f h = G from rfl, hGF]
  exact F.bijective

#print axioms s2e_canonical_coefficient_adic_map_bijective
end HodgeLean.Foundations.Program
