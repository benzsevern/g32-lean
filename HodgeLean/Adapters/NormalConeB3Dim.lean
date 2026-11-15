import HodgeLean.Adapters.NormalConeB3Diagonal
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula

/-! # Diagonal cone coefficient: the dimension of a smooth integral scheme

A nonzero algebra étale over `k[x₁, …, xₙ]` has Krull dimension `n`: it is flat and quasi-finite
over the polynomial ring, so heights of primes are heights of their contractions, and maximal
ideals contract to maximal ideals, which have height `n`. On an integral scheme smooth over `k`,
any two étale charts meet in a common basic open, so they have the same number of coordinates,
and that number is the dimension of the scheme, the height of its generic point.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry Topology
universe u

/-- A nonzero algebra étale over a polynomial ring in `d` variables over a field has Krull
dimension `d`.
Source: Matsumura, *Commutative Ring Theory*, Theorem 15.1 and Theorem 5.11; Mathlib,
`Algebra.QuasiFinite.height_eq_height_under` (HodgeConjecture) and
`MvPolynomial.height_eq_fin_of_isMaximal`. -/
theorem a3b3_ringKrullDim_of_etale {k S : Type*} [Field k] [CommRing S] [Nontrivial S] (d : ℕ)
    (g : MvPolynomial (Fin d) k →+* S) (hg : g.Etale) : ringKrullDim S = d := by
  let : Algebra (MvPolynomial (Fin d) k) S := g.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin d) k) S := RingHom.etale_algebraMap.mp hg
  obtain ⟨P, hP⟩ := Ideal.exists_maximal S
  have hfiniteType : (algebraMap (MvPolynomial (Fin d) k) S).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hunder : (P.under (MvPolynomial (Fin d) k)).IsMaximal :=
    hfiniteType.isMaximal_comap_of_isJacobsonRing P
  have hheight : P.height = d := by
    rw [Algebra.QuasiFinite.height_eq_height_under (R := MvPolynomial (Fin d) k)]
    exact MvPolynomial.height_eq_fin_of_isMaximal k d (P.under (MvPolynomial (Fin d) k))
  apply le_antisymm
  · calc ringKrullDim S ≤ ringKrullDim (MvPolynomial (Fin d) k) :=
          Algebra.QuasiFinite.ringKrullDim_le
      _ = d := by
          rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ENat.card_eq_coe_fintype_card,
            Fintype.card_fin, ringKrullDim_eq_zero_of_field]
          simp
  · change (↑(d : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim S
    rw [← hheight]
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

section dim
variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- Two étale charts of an integral scheme over a field have the same number of coordinates:
they share a basic open around the generic point, whose ring is étale over both polynomial rings.
Source: Mathlib, `exists_basicOpen_le_affine_inter` and `Algebra.Etale.of_isLocalizationAway`. -/
theorem a3b3_etale_chart_card_eq [IsIntegral Y] {V V' : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (hne : (V : Set Y).Nonempty) (hne' : (V' : Set Y).Nonempty)
    {m m' : ℕ} (g : MvPolynomial (Fin m) k →+* Γ(Y, V)) (hg : g.Etale)
    (g' : MvPolynomial (Fin m') k →+* Γ(Y, V')) (hg' : g'.Etale) : m = m' := by
  have hη : ∀ {U : Y.Opens}, (U : Set Y).Nonempty → genericPoint Y ∈ U := fun {U} hU =>
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  obtain ⟨f, f', hff', hx⟩ := exists_basicOpen_le_affine_inter hV hV' (genericPoint Y)
    ⟨hη hne, hη hne'⟩
  have : Nonempty (Y.basicOpen f) := ⟨⟨_, hx⟩⟩
  have key : ∀ {U : Y.Opens} (hU : IsAffineOpen U) (r : Γ(Y, U)) {n : ℕ}
      (h : MvPolynomial (Fin n) k →+* Γ(Y, U)), h.Etale → Nonempty (Y.basicOpen r) →
      ringKrullDim Γ(Y, Y.basicOpen r) = n := by
    intro U hU r n h hh hne
    let : Algebra Γ(Y, U) Γ(Y, Y.basicOpen r) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
    have : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hU.isLocalization_basicOpen r
    have hloc : (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen r)).Etale :=
      RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway r)
    exact a3b3_ringKrullDim_of_etale n _
      (RingHom.Etale.stableUnderComposition _ _ hh hloc)
  have h1 := key hV f g hg this
  rw [hff'] at this h1
  have h2 := key hV' f' g' hg' this
  rw [h1] at h2
  exact_mod_cast h2

/-- A smooth integral scheme over a field has dimension equal to the number of coordinates of any
étale chart: the height of the generic point is `n` for every nonempty affine open étale over
`k[x₁, …, xₙ]`.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 3.20 and Theorem 8.15; Matsumura,
*Commutative Ring Theory*, Theorem 15.1. -/
theorem a3b3_height_genericPoint_eq (p : Y ⟶ Spec (CommRingCat.of k)) [IsIntegral Y] [Smooth p]
    {V : Y.Opens} (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) {n : ℕ}
    (g : MvPolynomial (Fin n) k →+* Γ(Y, V)) (hg : g.Etale) :
    Order.height (genericPoint Y) = n := by
  have hdimV : ∀ {U : Y.Opens} (hU : IsAffineOpen U), (U : Set Y).Nonempty → ∀ {m : ℕ}
      (h : MvPolynomial (Fin m) k →+* Γ(Y, U)), h.Etale → Order.krullDim U = m := by
    intro U hU hUne m h hh
    have : Nonempty U := hUne.to_subtype
    rw [orderKrullDim_affineOpen_eq_ringKrullDim U hU, a3b3_ringKrullDim_of_etale m h hh]
  have htop : Order.height (genericPoint Y) = Order.krullDim Y :=
    Order.height_top_eq_krullDim (α := Y)
  have hle : Order.krullDim Y ≤ n := by
    apply Scheme.orderKrullDim_le_of_exists_open_orderKrullDim_le Y n
    intro x
    obtain ⟨U, hU, hxU, m, h, -, hh⟩ := a3b3_exists_etale_chart p x
    refine ⟨U, hxU, ?_⟩
    rw [hdimV hU ⟨x, hxU⟩ h hh, a3b3_etale_chart_card_eq hU hV ⟨x, hxU⟩ hne h hh g hg]
  have hge : Order.krullDim V ≤ Order.krullDim Y := by
    rw [← Scheme.topologicalKrullDim_eq_orderKrullDim V.toScheme,
      ← Scheme.topologicalKrullDim_eq_orderKrullDim Y]
    exact V.isOpenEmbedding.isInducing.topologicalKrullDim_le
  rw [hdimV hV hne g hg] at hge
  have := le_antisymm hle hge
  rw [this] at htop
  exact_mod_cast htop

end dim
end HodgeLean.Adapters
