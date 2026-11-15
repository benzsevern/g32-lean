import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.MvPolynomial.Basic

/-! Nonvanishing in the retained monomial chart.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- An etale map from a domain into a nonzero ring is injective.
Source: flat modules over a domain are torsion free. -/
theorem s2v_i2b_etale_injective_of_domain
    {A R : Type*} [CommRing A] [IsDomain A] [CommRing R] [Nontrivial R]
    (f : A →+* R) (hf : f.Etale) : Function.Injective f := by
  letI : Algebra A R := f.toAlgebra
  haveI : Module.Flat A R := (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1
  exact FaithfulSMul.algebraMap_injective A R

/-- The unit times parameter monomial in the actual coefficient field has a nonzero root.
Source: nonvanishing of independent polynomial parameters under injective ring maps. -/
theorem s2v_i2b_monomial_generator_ne_zero
    {F R K ι : Type*} [CommRing F] [Nontrivial F] [CommRing R] [Nontrivial R] [Field K]
    [Fintype ι] [DecidableEq ι] (n m : ℕ) (hm : 0 < m)
    (c : MvPolynomial (Fin n) F →+* R) (hc : Function.Injective c)
    (φ : R →+* K) (hφ : Function.Injective φ)
    (J : Finset ι) (κ : J → Fin n) (z : ι → R)
    (hz : ∀ t : J, z t = c (MvPolynomial.X (κ t)))
    (habsent : ∀ t, t ∉ J → z t = 1)
    (α : ι → ℕ) (ε : R) (hε : IsUnit ε) (v : K)
    (hv : v ^ m = φ ε * ∏ t, φ (z t) ^ α t) : v ≠ 0 := by
  have hmap : ∀ a : R, a ≠ 0 → φ a ≠ 0 := by
    intro a ha he
    exact ha (hφ (he.trans φ.map_zero.symm))
  have hz0 : ∀ t, φ (z t) ≠ 0 := by
    intro t
    apply hmap
    by_cases ht : t ∈ J
    · rw [hz ⟨t, ht⟩]
      intro he
      exact MvPolynomial.X_ne_zero (κ ⟨t, ht⟩) (hc (he.trans c.map_zero.symm))
    · rw [habsent t ht]
      exact one_ne_zero
  have hprod : (∏ t, φ (z t) ^ α t) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun t _ => pow_ne_zero _ (hz0 t))
  have hvpow : v ^ m ≠ 0 := by
    rw [hv]
    exact mul_ne_zero (hε.map φ).ne_zero hprod
  intro he
  apply hvpow
  rw [he, zero_pow (Nat.ne_of_gt hm)]

end HodgeLean.Foundations.Program
