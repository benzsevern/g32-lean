import HodgeLean.Foundations.Program.SchoenTowerPointJets
import Mathlib.RingTheory.Etale.Locus

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- A finitely presented algebra that is étale at finitely many distinct field-valued points
has a single principal étale neighborhood containing them all.
Source: Stacks Project, Tags 00U2 and 00DT; `Algebra.exists_etale_of_isEtaleAt`. -/
theorem s2t_common_principal_etale_neighborhood {R K A ι : Type*}
    [CommRing R] [Field K] [CommRing A] [Algebra R A] [Algebra K A]
    [Algebra.FinitePresentation R A] [Finite ι]
    (φ : ι → A →ₐ[K] K) (hinj : Function.Injective φ)
    [∀ i, (RingHom.ker (φ i).toRingHom).IsPrime]
    [∀ i, Algebra.IsEtaleAt R (RingHom.ker (φ i).toRingHom)] :
    ∃ g : A, (∀ i, φ i g = 1) ∧ Algebra.Etale R (Localization.Away g) := by
  classical
  have hex (i : ι) := Algebra.exists_etale_of_isEtaleAt (R := R)
    (RingHom.ker (φ i).toRingHom)
  choose r hr he using hex
  have hr' (i : ι) : φ i (r i) ≠ 0 := by
    simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hr i
  obtain ⟨g, hg, hvalue⟩ := s2t_unit_value_in_span φ hinj r hr'
  refine ⟨g, hvalue, Algebra.basicOpen_subset_etaleLocus_iff_etale.mp ?_⟩
  intro p hp
  change g ∉ p.asIdeal at hp
  by_contra hpE
  have hspan : Ideal.span (Set.range r) ≤ p.asIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_contra hri
    exact hpE ((Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr (he i)) hri)
  exact hp (hspan hg)

end HodgeLean.Foundations.Program
