import HodgeLean.Foundations.Program.SchoenTowerI2a
import HodgeLean.Foundations.Program.SchoenTowerI2bBranchCoordinates

/-! Integral-element inertia with the retained branch indexing.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The exponent of a retained vanishing branch fixes every integral-element evaluation.
Source: the frozen normalized monomial inertia interface and reindexing by the chart embedding. -/
theorem s2v_i2b_retained_branch_inertia
    {ι : Type} [Fintype ι] [DecidableEq ι] (n m : ℕ) (hm : 0 < m)
    (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra ℂ R] [Algebra R K] [Algebra ℂ K] [IsScalarTower ℂ R K]
    (c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap R K))
    (J : Finset ι) (κ : J ↪ Fin n) (z : ι → R) (α : ι → ℕ)
    (hz : ∀ t : J, z t = c (MvPolynomial.X (κ t)))
    (habsent : ∀ t, t ∉ J → z t = 1)
    (ε : R) (hε : IsUnit ε) (v : K)
    (hv : v ^ m = algebraMap R K ε * ∏ t, (algebraMap R K (z t)) ^ α t)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[R] K) (hd : d v = algebraMap ℂ K ζ * v)
    (p : integralClosure R K →ₐ[ℂ] ℂ) (t : J)
    (hp : p (algebraMap R (integralClosure R K) (z t)) = 0) :
    ∀ b, p ((d.mapIntegralClosure ^ α t) b) = p b := by
  obtain ⟨β, hβ, hprod⟩ := s2v_i2b_branch_exponents_reindex J κ α
    (fun t => algebraMap R K (z t)) (fun j => algebraMap R K (c (MvPolynomial.X j)))
    (fun t => by rw [hz t]) (fun t ht => by rw [habsent t ht, map_one])
  have hv' : v ^ m = algebraMap R K ε *
      ∏ j, (algebraMap R K (c (MvPolynomial.X j))) ^ β j :=
    hv.trans (congrArg (fun x => algebraMap R K ε * x) hprod)
  have hp' : p (algebraMap R (integralClosure R K) (c (MvPolynomial.X (κ t)))) = 0 := by
    rw [← hz t]
    exact hp
  have hi := s2v_i2a_normalized_monomial_inertia n m hm R K c hc hinj β ε hε v hv'
    hgen ζ hζ d hd p (κ t) hp'
  have hf : ∀ b, p ((d.mapIntegralClosure ^ β (κ t)) b) = p b :=
    hi (Subgroup.mem_zpowers _)
  rw [hβ t] at hf
  exact hf

end HodgeLean.Foundations.Program
