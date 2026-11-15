import HodgeLean.Foundations.Program.SchoenCycleProductParameterExt
import HodgeLean.Foundations.Program.SchoenCycleTotalJetMaps
import HodgeLean.Foundations.Program.SchoenCycleMaximalPowerQuotients

/-! # The reverse composition for actual curve-power finite coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A local map realizing the polynomial coordinates is also a right inverse
to parameter evaluation on an actual curve-power finite neighbourhood.
Source: Hartshorne, Algebraic Geometry, II.2;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_curve_power_totalJet_eval_right_inverse
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    [IsIntegral (g3_power X n).left] (x : ComplexPoint (g3_power X n))
    (t : ∀ i, X.left.presheaf.stalk ((g3_proj X n i).left x.underlying))
    (ht : ∀ i, IsLocalRing.maximalIdeal
      (X.left.presheaf.stalk ((g3_proj X n i).left x.underlying)) = Ideal.span {t i})
    (N : ℕ) (hN : 0 < N)
    (l : (g3_power X n).left.presheaf.stalk x.underlying →+*
      (MvPolynomial (Fin n) ℂ ⧸ idealOfVars (Fin n) ℂ ^ N)) [IsLocalHom l]
    (hC : ∀ c, l (HodgeLean.Foundations.Curves.stalkC x.underlying c) = algebraMap ℂ _ c)
    (hcoord : ∀ i, l ((g3_proj X n i).left.stalkMap x.underlying (t i)) =
      Ideal.Quotient.mk (idealOfVars (Fin n) ℂ ^ N) (MvPolynomial.X i)) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    let A := MvPolynomial (Fin n) ℂ ⧸ idealOfVars (Fin n) ℂ ^ N
    letI := s2e_totalJet_isLocalRing (Fin n) N hN
    let s := fun i => (g3_proj X n i).left.stalkMap x.underlying (t i)
    ∀ hs : ∀ i, s i ∈ IsLocalRing.maximalIdeal R,
      (s2e_totalJet_eval (Fin n) R s hs N).comp
        (s2e_local_power_quotient_lift ℂ R A
          { toRingHom := l, commutes' := hC } N
          (s2e_totalJet_maximalIdeal_pow (Fin n) N hN)) = AlgHom.id ℂ _ := by
  let R := (g3_power X n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let A := MvPolynomial (Fin n) ℂ ⧸ idealOfVars (Fin n) ℂ ^ N
  letI := s2e_totalJet_isLocalRing (Fin n) N hN
  let B := R ⧸ IsLocalRing.maximalIdeal R ^ N
  letI := s2e_maximal_power_quotient_isLocalRing R N hN
  let s := fun i => (g3_proj X n i).left.stalkMap x.underlying (t i)
  dsimp only
  intro hs
  let φ : R →ₐ[ℂ] A := { toRingHom := l, commutes' := hC }
  let α := s2e_totalJet_eval (Fin n) R s hs N
  let β := s2e_local_power_quotient_lift ℂ R A φ N
    (s2e_totalJet_maximalIdeal_pow (Fin n) N hN)
  let q : R →ₐ[ℂ] B := Ideal.Quotient.mkₐ ℂ (IsLocalRing.maximalIdeal R ^ N)
  letI : IsLocalHom q.toRingHom := IsLocalHom.of_surjective q.toRingHom Ideal.Quotient.mk_surjective
  letI : IsLocalHom α.toRingHom := s2e_nilpotent_maximal_source_map_local A B α.toRingHom N
    (s2e_totalJet_maximalIdeal_pow (Fin n) N hN)
  letI : IsLocalHom φ.toRingHom := inferInstanceAs (IsLocalHom l)
  letI : IsLocalHom (α.comp φ).toRingHom :=
    inferInstanceAs (IsLocalHom (α.toRingHom.comp φ.toRingHom))
  have hm : q.toRingHom = (α.comp φ).toRingHom := by
    apply s2e_curve_power_nilpotent_parameter_ext X n x t ht B q.toRingHom (α.comp φ).toRingHom
    · intro c
      exact q.commutes c
    · intro c
      exact (α.comp φ).commutes c
    · intro i
      refine ⟨N, ?_⟩
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (s i) ^ N = 0
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (hs i) N
    · intro i
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (s i) = α (l (s i))
      rw [hcoord i]
      simpa only [aeval_X] using (s2e_totalJet_eval_mk (Fin n) R s hs N (MvPolynomial.X i)).symm
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro r
  change α (β (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) r)) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) r
  rw [s2e_local_power_quotient_lift_mk]
  exact (congrArg (fun k : R →+* B => k r) hm).symm

end HodgeLean.Foundations.Program
