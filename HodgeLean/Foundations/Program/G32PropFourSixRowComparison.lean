import HodgeLean.Foundations.Program.G32PropFourSixCharacterPairing

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

theorem g32p_polynomialPairing_row {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (m : ℕ) (a : Fin 44 → ℤ) (b : Fin 4 → ℤ)
    (terms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ))
    (modulus : List ℤ) (quotients : Fin 48 → List ℤ) (z : ℂ)
    (hroot : g32p_coeffEval z modulus = 0)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((terms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (m / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((terms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (m / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hcheckFree : ∀ j : Fin 44,
      g32p_cyclotomicPairingCheck (Fintype.card H) (a j)
        (g32p_pairingCoefficients m (terms ⟨j.val, by omega⟩))
        modulus (quotients ⟨j.val, by omega⟩) = true)
    (hcheckQuat : ∀ j : Fin 4,
      g32p_cyclotomicPairingCheck (Fintype.card H) (b j)
        (g32p_pairingCoefficients m (terms ⟨44 + j.val, by omega⟩))
        modulus (quotients ⟨44 + j.val, by omega⟩) = true) :
    papersA τ τbar θ H χ = (a, fun j => (b j : ZMod 2)) := by
  apply Prod.ext
  · funext j
    exact g32p_polynomialPairing_free H (τ j) (τbar j) χ m (a j) _ modulus _ z
      hroot (hfree j) (hcheckFree j)
  · funext j
    have hh := g32p_polynomialPairing_mult H (θ j) χ m (b j) _ modulus _ z
      hroot (hquat j) (hcheckQuat j)
    change (papersMult H (θ j) χ : ZMod 2) = (b j : ZMod 2)
    have hc := congrArg (fun n : ℤ => (n : ZMod 2)) hh
    simpa only [Int.cast_natCast] using hc

end HodgeLean.Foundations.Program
