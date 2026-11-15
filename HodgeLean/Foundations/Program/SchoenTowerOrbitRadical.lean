import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.RingTheory.Ideal.GoingUp

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise

namespace HodgeLean.Foundations.Program

/-- Over a maximal invariant-base ideal, the radical of its extension is the intersection
of the actual orbit of a prime above it. -/
theorem s2t_radical_extended_under_eq_orbit {R A G : Type*}
    [CommRing R] [CommRing A] [Algebra R A] [Group G] [Finite G]
    [MulSemiringAction G A] [SMulCommClass G R A] [Algebra.IsInvariant R A G]
    (q : Ideal A) [q.IsPrime] (hp : (q.under R).IsMaximal) :
    ((q.under R).map (algebraMap R A)).radical = ⨅ g : G, g • q := by
  apply le_antisymm
  · apply le_iInf
    intro g
    apply (show (g • q).IsPrime from inferInstance).radical_le_iff.mpr
    rw [Ideal.map_le_iff_le_comap]
    change q.under R ≤ (g • q).under R
    rw [Ideal.under_smul]
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro P hP
    letI : P.IsPrime := hP.2
    have heq : q.under R = P.under R := hp.eq_of_le
      (Ideal.comap_ne_top (algebraMap R A) hP.2.ne_top)
      (Ideal.map_le_iff_le_comap.mp hP.1)
    obtain ⟨g, rfl⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R A G q P heq
    exact iInf_le _ g

/-- Every ideal in the actual orbit of a maximal ideal is maximal. -/
theorem s2t_orbit_isMaximal {A G : Type*}
    [CommRing A] [Group G] [MulSemiringAction G A] (q : Ideal A) [q.IsMaximal]
    (i : MulAction.orbit G q) : (i : Ideal A).IsMaximal := by
  obtain ⟨g, hg⟩ := i.property
  rw [← hg]
  change (q.map (MulSemiringAction.toRingHom G A g)).IsMaximal
  exact (Ideal.isMaximal_map_iff_of_bijective
    (f := MulSemiringAction.toRingHom G A g)
    (MulSemiringAction.toRingEquiv G A g).bijective).mpr inferInstance

/-- Distinct maximal ideals in the actual group orbit are pairwise coprime. -/
theorem s2t_orbit_maximal_pairwise_coprime {A G : Type*}
    [CommRing A] [Group G] [MulSemiringAction G A] (q : Ideal A) [q.IsMaximal] :
    Pairwise (fun i j : MulAction.orbit G q => IsCoprime (i : Ideal A) (j : Ideal A)) := by
  have hmax (i : MulAction.orbit G q) : (i : Ideal A).IsMaximal := by
    obtain ⟨g, hg⟩ := i.property
    rw [← hg]
    change (q.map (MulSemiringAction.toRingHom G A g)).IsMaximal
    exact (Ideal.isMaximal_map_iff_of_bijective
      (f := MulSemiringAction.toRingHom G A g)
      (MulSemiringAction.toRingEquiv G A g).bijective).mpr inferInstance
  intro i j hij
  letI := hmax i
  letI := hmax j
  exact Ideal.isCoprime_of_isMaximal (fun h => hij (Subtype.ext h))

/-- The radical over the image of a maximal ideal uses precisely its distinct orbit ideals. -/
theorem s2t_radical_extended_maximal_eq_distinctOrbit {R A G : Type*}
    [CommRing R] [CommRing A] [Algebra R A] [Group G] [Finite G]
    [MulSemiringAction G A] [SMulCommClass G R A] [Algebra.IsInvariant R A G]
    (q : Ideal A) [q.IsMaximal] :
    ((q.under R).map (algebraMap R A)).radical =
      ⨅ i : MulAction.orbit G q, (i : Ideal A) := by
  letI : Algebra.IsIntegral R A := Algebra.IsInvariant.isIntegral R A G
  have hp := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) q
  rw [s2t_radical_extended_under_eq_orbit (R := R) (G := G) q hp]
  apply le_antisymm
  · apply le_iInf
    intro i
    obtain ⟨g, hg⟩ := i.property
    rw [← hg]
    exact iInf_le _ g
  · apply le_iInf
    intro g
    exact iInf_le (fun i : MulAction.orbit G q => (i : Ideal A)) ⟨g • q, ⟨g, rfl⟩⟩

/-- The extended invariant-base ideal is contained in every actual orbit ideal. -/
theorem s2t_extended_under_le_orbit {R A G : Type*}
    [CommRing R] [CommRing A] [Algebra R A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (q : Ideal A) (i : MulAction.orbit G q) :
    (q.under R).map (algebraMap R A) ≤ (i : Ideal A) := by
  obtain ⟨g, hg⟩ := i.property
  rw [← hg]
  change (q.under R).map (algebraMap R A) ≤ g • q
  rw [Ideal.map_le_iff_le_comap]
  change q.under R ≤ (g • q).under R
  rw [Ideal.under_smul]

end HodgeLean.Foundations.Program
