import HodgeLean.Foundations.Program.SchoenTowerI2a

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A single vanishing etale binomial coordinate fixes every integral evaluation under its exponent iterate. -/
theorem single_branch_integral_evaluation_inertia
    (n m α : ℕ) (hm : 0 < m)
    (R L : Type) [CommRing R] [IsDomain R] [Field L]
    [Algebra ℂ R] [Algebra R L] [Algebra ℂ L] [IsScalarTower ℂ R L]
    (c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap R L)) (j : Fin n)
    (ε : R) (hε : IsUnit ε) (w : L)
    (hw : w ^ m = algebraMap R L ε * (algebraMap R L (c (MvPolynomial.X j))) ^ α)
    (hgen : Subfield.closure (Set.range (algebraMap R L) ∪ {w}) = ⊤)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (δ : L ≃ₐ[R] L) (hδ : δ w = algebraMap ℂ L ζ * w)
    (ev : integralClosure R L →ₐ[ℂ] ℂ)
    (hzero : ev (algebraMap R (integralClosure R L) (c (MvPolynomial.X j))) = 0) :
    ∀ b, ev ((δ.mapIntegralClosure ^ α) b) = ev b := by
  classical
  let exps : Fin n → ℕ := fun i => if i = j then α else 0
  have hw' : w ^ m = algebraMap R L ε *
      ∏ i, (algebraMap R L (c (MvPolynomial.X i))) ^ exps i := by
    simpa [exps] using hw
  have hi := HodgeLean.Foundations.Program.s2v_i2a_normalized_monomial_inertia n m hm R L
    c hc hinj exps ε hε w hw' hgen ζ hζ δ hδ ev j hzero
  have hf := hi (Subgroup.mem_zpowers (δ.mapIntegralClosure ^ exps j))
  change ∀ b, ev ((δ.mapIntegralClosure ^ (if j = j then α else 0)) b) = ev b at hf
  rw [if_pos rfl] at hf
  exact hf

end AlgebraicGeometry.RamifiedNormalization.StageFour
