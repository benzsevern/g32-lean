import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Scalars supplied by affine component noncontainment -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Noncontainment of affine component images gives a kernel section whose
restriction to the first component is nonzero. -/
lemma unionConormal_affine_nonzero_kernel_section
    (R A B : CommRingCat) (q : R ⟶ A) (r : R ⟶ B)
    (hq : Function.Surjective q) (hr : Function.Surjective r)
    (hnot : ¬ Set.range (Spec.map q) ⊆ Set.range (Spec.map r)) :
    ∃ a : RingHom.ker r.hom, q a.val ≠ 0 := by
  by_contra hn
  have hle : RingHom.ker r.hom ≤ RingHom.ker q.hom := by
    intro a ha
    change q a = 0
    by_contra hne
    exact hn ⟨⟨a, ha⟩, hne⟩
  apply hnot
  change Set.range (PrimeSpectrum.comap q.hom) ⊆ Set.range (PrimeSpectrum.comap r.hom)
  rw [range_comap_of_surjective A q.hom hq,
    range_comap_of_surjective B r.hom hr]
  exact PrimeSpectrum.zeroLocus_anti_mono_ideal hle

#print axioms unionConormal_affine_nonzero_kernel_section
end HodgeLean.Foundations.Program.G32Native
