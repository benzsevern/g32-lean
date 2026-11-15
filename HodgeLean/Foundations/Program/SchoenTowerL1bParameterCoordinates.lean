import HodgeLean.Foundations.Program.SchoenTowerL1bParameterJetAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Ideal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Single-variable finite coordinates retain evaluation at the chosen
regular parameter and use the variable ideal required by adic series. -/
theorem s2v_l1b_parameter_finite_coordinates
    {k : Type*} [Field k] (R : Type*) [CommRing R] [Algebra k R] [IsLocalRing R]
    (φ : R →ₐ[k] k) (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hreg : Function.Injective (fun x : R => t * x)) (N : ℕ) :
    ∃ e : (MvPolynomial Unit k ⧸ MvPolynomial.idealOfVars Unit k ^ N) ≃+*
        (R ⧸ IsLocalRing.maximalIdeal R ^ N),
      ∀ p : MvPolynomial Unit k,
        e (Ideal.Quotient.mk (MvPolynomial.idealOfVars Unit k ^ N) p) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)
            (MvPolynomial.aeval (fun _ : Unit => t) p) := by
  let E := MvPolynomial.uniqueAlgEquiv k Unit
  let J := MvPolynomial.idealOfVars Unit k
  have hJ : Ideal.map E.toRingHom J = Ideal.span {Polynomial.X} := by
    have hset : E.toRingHom '' Set.range MvPolynomial.X = {Polynomial.X} := by
      ext p
      constructor
      · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
        simp [E, MvPolynomial.uniqueAlgEquiv_apply]
      · intro hp
        rcases Set.mem_singleton_iff.mp hp with rfl
        refine ⟨MvPolynomial.X (), ⟨(), rfl⟩, ?_⟩
        simp [E, MvPolynomial.uniqueAlgEquiv_apply]
    change Ideal.map E.toRingHom (MvPolynomial.idealOfVars Unit k) = _
    rw [MvPolynomial.idealOfVars, Ideal.map_span, hset]
  have hJn : Ideal.span {(Polynomial.X ^ N : Polynomial k)} =
      (J ^ N).map E.toRingHom := by
    rw [Ideal.map_pow, hJ, Ideal.span_singleton_pow]
  let e₁ := Ideal.quotientEquivAlg (J ^ N)
    (Ideal.span {(Polynomial.X ^ N : Polynomial k)}) E hJn
  let e₂ := s2v_l1b_parameter_jet_algEquiv R φ t ht hreg N
  have htn : Ideal.span {t ^ N} = IsLocalRing.maximalIdeal R ^ N := by
    rw [ht, Ideal.span_singleton_pow]
  let e₃ := Ideal.quotientEquivAlgOfEq k htn
  refine ⟨((e₁.trans e₂).trans e₃).toRingEquiv, ?_⟩
  intro p
  change e₃ (e₂ (e₁ (Ideal.Quotient.mk (J ^ N) p))) = _
  dsimp only [e₁, e₂, e₃]
  rw [Ideal.quotientEquivAlg_mk, s2v_l1b_parameter_jet_algEquiv_mk,
    Ideal.quotientEquivAlgOfEq_mk]
  congr 1
  exact MvPolynomial.eval₂_const_uniqueAlgEquiv

end HodgeLean.Foundations.Program
