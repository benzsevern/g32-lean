import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs
import HodgeLean.Adapters.NormalConeB4aClassMultiplicity

/-! # Neighbourhoods and multiplicities for collected primes

A finite family of prime supports can be separated near a point belonging to
one member only. Multiplicity there reads the retained coefficient.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
open scoped Classical
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem primeSupport_mem_iff {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    (p : Z) (x : a3b4_an q) :
    x ∈ primeSupport q p ↔ x.underlying ∈ closure ({p} : Set Z) := by
  simp [primeSupport, a3b4_cycleSupport]

theorem separatedPrime_neighborhood {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] (b : Z →₀ ℚ) (p : b.support)
    (x : a3b4_an q) (hoff : ∀ t : b.support, t ≠ p → x ∉ primeSupport q t.1) :
    ∃ V : Opens (a3b4_an q), x ∈ V ∧
      ∀ t : b.support, t ≠ p → ∀ y ∈ V, y ∉ primeSupport q t.1 := by
  classical
  let A : Set (a3b4_an q) := ⋃ t : b.support, ⋃ (_ : t ≠ p), primeSupport q t.1
  have hAc : IsClosed A := by
    apply isClosed_iUnion_of_finite
    intro t
    apply isClosed_iUnion_of_finite
    intro _
    exact a3b4a_classSupport_isClosed q
      (Function.locallyFinsuppWithin.single t.1 (1 : ℚ))
  have hAo : IsOpen Aᶜ := hAc.isOpen_compl
  refine ⟨⟨Aᶜ, hAo⟩, ?_, ?_⟩
  · intro hxA
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hxA
    obtain ⟨hne, hxt⟩ := Set.mem_iUnion.mp ht
    exact hoff t hne hxt
  · intro t hne y hy hyt
    exact hy (Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨hne, hyt⟩⟩)

theorem prime_multiplicity_at {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (p : Z) (x : a3b4_an q) (hx : x ∈ primeSupport q p) :
    a3b4_multiplicity q (Function.locallyFinsuppWithin.single p (1 : ℚ)) x = 1 := by
  classical
  rw [a3b4a_classMultiplicity_eq_component q _ p (by simp) x
    ((primeSupport_mem_iff q p x).mp hx)]
  · simp
  · intro t ht hne
    have ht' : t = p := by simpa using ht
    exact (hne ht').elim

end AlgebraicGeometry.SingularCycles
