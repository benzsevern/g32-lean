import HodgeLean.Foundations.Program.SchoenCycleFixedPrimeLocalizationAlgebra
import HodgeLean.Foundations.Program.SchoenCycleFixedPrimeLocalizationInjective
import HodgeLean.Foundations.Program.SchoenCycleFixedPrimeLocalizationValues
import HodgeLean.Foundations.Program.SchoenCycleExactFixedPrimeDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- At an actual fixed prime, localization of the actual fixed-function algebra identifies with all exact local invariants under the compatible local pullbacks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_fixed_prime_local_invariant_equiv
    (k C B G : Type*) [CommRing k] [CommRing C] [IsDomain C] [CommRing B]
    [Algebra k C] [Algebra C B] [Algebra k B] [IsScalarTower k C B]
    [Group G] [Fintype G] [MulSemiringAction G C] [SMulCommClass G k C]
    (P : Ideal C) [P.IsPrime] [IsLocalization.AtPrime B P]
    (hP : ∀ (g : G) (c : C), g • c ∈ P ↔ c ∈ P)
    (β : G → (B →ₐ[k] B))
    (hβ : ∀ (g : G) (c : C), β g (algebraMap C B c) = algebraMap C B (g • c)) :
    let S := FixedPoints.subalgebra k C G
    let Q := P.comap S.val.toRingHom
    Localization.AtPrime Q ≃ₐ[k]
      (⨅ g, AlgHom.equalizer (β g) (AlgHom.id k B) : Subalgebra k B) := by
  let S := FixedPoints.subalgebra k C G
  let Q := P.comap S.val.toRingHom
  let K : Subalgebra k B := ⨅ g, AlgHom.equalizer (β g) (AlgHom.id k B)
  let f := s2e_fixed_prime_localization_algHom k C B G P
  have hmem (t : Localization.AtPrime Q) : f t ∈ K := by
    simp only [K, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    intro g
    exact s2e_fixed_prime_localization_map_fixed k C B G P
      (fun g => (β g).toRingHom) hβ g t
  let fK := f.codRestrict K hmem
  have hinjCB : Function.Injective (algebraMap C B) := IsLocalization.injective B (M := P.primeCompl) (by
    intro c hc
    change c ∉ P at hc
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hz
    exact hc (hz ▸ P.zero_mem))
  apply AlgEquiv.ofBijective fK
  constructor
  · intro x y hxy
    apply s2e_fixed_prime_localization_map_injective k C B G P hinjCB
    exact congrArg (fun z : K => z.val) hxy
  · intro y
    have hy := y.property
    simp only [K, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply] at hy
    obtain ⟨t, ht⟩ := s2e_exact_fixed_prime_local_descent k C B G P hP
      (fun g => (β g).toRingHom) hβ y.val hy
    exact ⟨t, Subtype.ext ht⟩

#print axioms s2e_fixed_prime_local_invariant_equiv

/-- The exact local invariant algebra identification retains its canonical localization pullback on every local function.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_fixed_prime_local_invariant_equiv_val
    (k C B G : Type*) [CommRing k] [CommRing C] [IsDomain C] [CommRing B]
    [Algebra k C] [Algebra C B] [Algebra k B] [IsScalarTower k C B]
    [Group G] [Fintype G] [MulSemiringAction G C] [SMulCommClass G k C]
    (P : Ideal C) [P.IsPrime] [IsLocalization.AtPrime B P]
    (hP : ∀ (g : G) (c : C), g • c ∈ P ↔ c ∈ P)
    (β : G → (B →ₐ[k] B))
    (hβ : ∀ (g : G) (c : C), β g (algebraMap C B c) = algebraMap C B (g • c)) :
    let S := FixedPoints.subalgebra k C G
    let Q := P.comap S.val.toRingHom
    ∀ t : Localization.AtPrime Q,
      (s2e_fixed_prime_local_invariant_equiv k C B G P hP β hβ t).val =
        s2e_fixed_prime_localization_map k C B G P t := by
  dsimp only
  intro t
  rfl

#print axioms s2e_fixed_prime_local_invariant_equiv_val
end HodgeLean.Foundations.Program
