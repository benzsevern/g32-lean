import HodgeLean.Foundations.Program.SchoenTowerJetDenominators

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- Finitely many localized first jets at distinct field-valued points have one global
representative, with arbitrary residue values and scalar translations of the local jets.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10 and Chapter 3. -/
theorem s2t_interpolate_localized_jets {K A ι : Type*}
    [Field K] [CommRing A] [Algebra K A] [Finite ι]
    (φ : ι → A →ₐ[K] K) (hinj : Function.Injective φ)
    [∀ i, (RingHom.ker (φ i).toRingHom).IsPrime]
    (t : (i : ι) → Localization.AtPrime (RingHom.ker (φ i).toRingHom)) (c : ι → K) :
    ∃ g : A, (∀ i, φ i g = c i) ∧ ∀ i, ∃ k : K,
      algebraMap A (Localization.AtPrime (RingHom.ker (φ i).toRingHom)) g -
        (t i + algebraMap K (Localization.AtPrime (RingHom.ker (φ i).toRingHom)) k) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (φ i).toRingHom)) ^ 2 := by
  classical
  have hex (i : ι) := s2t_localization_point_jet_lift (φ i) (t i)
  choose a ha using hex
  obtain ⟨g, hg⟩ := s2t_interpolate_point_jets φ hinj a c
  refine ⟨g, fun i => (hg i).1, fun i => ⟨c i - φ i (a i), ?_⟩⟩
  let B := Localization.AtPrime (RingHom.ker (φ i).toRingHom)
  let m := IsLocalRing.maximalIdeal B
  have hm : Ideal.map (algebraMap A B) (RingHom.ker (φ i).toRingHom) = m :=
    Localization.AtPrime.map_eq_maximalIdeal
  have hlocal : algebraMap A B (a i) - t i ∈ m ^ 2 := by
    have h := ha i
    change algebraMap A B (a i) - t i ∈
      (Ideal.map (algebraMap A B) (RingHom.ker (φ i).toRingHom)) ^ 2 at h
    rw [hm] at h
    exact h
  have hglobal : algebraMap A B (g - (a i + algebraMap K A (c i - φ i (a i)))) ∈ m ^ 2 := by
    rw [← hm, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hg i).2
  have heq : algebraMap A B g - (t i + algebraMap K B (c i - φ i (a i))) =
      algebraMap A B (g - (a i + algebraMap K A (c i - φ i (a i)))) +
        (algebraMap A B (a i) - t i) := by
    simp only [map_sub, map_add, IsScalarTower.algebraMap_apply K A B]
    ring
  rw [heq]
  exact (m ^ 2).add_mem hglobal hlocal

end HodgeLean.Foundations.Program
