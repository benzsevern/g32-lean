import HodgeLean.Foundations.Program.SchoenCycleProductJetInverse
import HodgeLean.Foundations.Program.SchoenCycleProductParameterExistence

/-! # Polynomial finite coordinates on actual curve-power stalks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual finite neighbourhood of a curve-power point has polynomial
coordinates given by the pulled-back regular parameters of all curve factors.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_curve_power_stalk_total_jet_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    [IsIntegral (g3_power X n).left] (x : ComplexPoint (g3_power X n))
    (t : ∀ i, X.left.presheaf.stalk ((g3_proj X n i).left x.underlying))
    (ht : ∀ i, IsLocalRing.maximalIdeal
      (X.left.presheaf.stalk ((g3_proj X n i).left x.underlying)) = Ideal.span {t i})
    (hreg : ∀ i, Function.Injective (fun z => t i * z)) (N : ℕ) (hN : 0 < N) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ e : (MvPolynomial (Fin n) ℂ ⧸ idealOfVars (Fin n) ℂ ^ N) ≃ₐ[ℂ]
        (R ⧸ IsLocalRing.maximalIdeal R ^ N),
      ∀ p : MvPolynomial (Fin n) ℂ,
        e (Ideal.Quotient.mk (idealOfVars (Fin n) ℂ ^ N) p) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)
            (aeval (fun i => (g3_proj X n i).left.stalkMap x.underlying (t i)) p) := by
  classical
  let R := (g3_power X n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let A := MvPolynomial (Fin n) ℂ ⧸ idealOfVars (Fin n) ℂ ^ N
  letI := s2e_totalJet_isLocalRing (Fin n) N hN
  let a : Fin n → A := fun i => Ideal.Quotient.mk (idealOfVars (Fin n) ℂ ^ N) (MvPolynomial.X i)
  have ha (i : Fin n) : IsNilpotent (a i) := ⟨N, s2e_totalJet_coordinate_pow (Fin n) N i⟩
  obtain ⟨l, hl, hC, hcoord⟩ := s2e_curve_power_nilpotent_stalk_map_exists X n x t ht hreg A
    (s2e_totalJetResidue (Fin n) N hN) a ha
  letI : IsLocalHom l := hl
  let s := fun i => (g3_proj X n i).left.stalkMap x.underlying (t i)
  have hs (i : Fin n) : s i ∈ IsLocalRing.maximalIdeal R := by
    have hi : t i ∈ IsLocalRing.maximalIdeal
        (X.left.presheaf.stalk ((g3_proj X n i).left x.underlying)) := by
      rw [ht i]
      exact Ideal.subset_span rfl
    exact (IsLocalRing.map_maximalIdeal_le ((g3_proj X n i).left.stalkMap x.underlying).hom)
      (Ideal.mem_map_of_mem _ hi)
  let φ : R →ₐ[ℂ] A := { toRingHom := l, commutes' := hC }
  letI : IsLocalHom φ.toRingHom := inferInstanceAs (IsLocalHom l)
  let α := s2e_totalJet_eval (Fin n) R s hs N
  let β := s2e_local_power_quotient_lift ℂ R A φ N
    (s2e_totalJet_maximalIdeal_pow (Fin n) N hN)
  let B := R ⧸ IsLocalRing.maximalIdeal R ^ N
  have hleft : β.comp α = AlgHom.id ℂ A :=
    s2e_totalJet_eval_left_inverse (Fin n) R s hs N hN φ hcoord
  have hright : α.comp β = AlgHom.id ℂ B :=
    s2e_curve_power_totalJet_eval_right_inverse X n x t ht N hN l hC hcoord hs
  have hinj : Function.Injective α := by
    intro a b hab
    have h := congrArg β hab
    change (β.comp α) a = (β.comp α) b at h
    rwa [hleft] at h
  have hsurj : Function.Surjective α := by
    intro b
    refine ⟨β b, ?_⟩
    exact congrArg (fun k : B →ₐ[ℂ] B => k b) hright
  refine ⟨AlgEquiv.ofBijective α ⟨hinj, hsurj⟩, ?_⟩
  intro p
  exact s2e_totalJet_eval_mk (Fin n) R s hs N p

end HodgeLean.Foundations.Program
