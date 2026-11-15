import HodgeLean.Foundations.Program.G32Native.PairedC3CotangentImageGenerators
import HodgeLean.Foundations.Program.SchoenCycleProjCoordinateMaps
import HodgeLean.Foundations.Program.SchoenCycleS3AffineConormalFree

/-! # The actual ideal of arbitrary polynomial coordinate elimination -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Polynomial coordinate elimination has exactly the ideal generated
by the discarded variables, for arbitrary retained index types. -/
theorem paired_c3_coordinate_elimination_kernel {A ι κ : Type} [CommRing A] (e : κ ↪ ι) :
    RingHom.ker (MvPolynomial.killCompl (R := A) e.injective).toRingHom =
      Ideal.span (X '' (Set.range e)ᶜ) := by
  classical
  ext p
  rw [RingHom.mem_ker, MvPolynomial.mem_ideal_span_X_image]
  change MvPolynomial.killCompl (R := A) e.injective p = 0 ↔ _
  constructor
  · intro hp m hm
    by_contra h
    have hs : ↑m.support ⊆ Set.range e := by
      intro i hi
      by_contra hie
      exact h ⟨i, hie, Finsupp.mem_support_iff.mp hi⟩
    have hc := congrArg (fun q : MvPolynomial κ A =>
      q.coeff (m.comapDomain e e.injective.injOn)) hp
    rw [MvPolynomial.coeff_killCompl,
      Finsupp.mapDomain_comapDomain e e.injective m hs, AddMonoidAlgebra.coeff_zero] at hc
    exact (MvPolynomial.mem_support_iff.mp hm) hc
  · intro hp
    ext m
    rw [MvPolynomial.coeff_killCompl, AddMonoidAlgebra.coeff_zero]
    by_contra h
    obtain ⟨i, hie, hi⟩ := hp _ (MvPolynomial.mem_support_iff.mpr h)
    have hs := Finsupp.mapDomain_support (f := e) (s := m)
      (Finsupp.mem_support_iff.mpr hi)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hs
    exact hie ⟨j, hj⟩

/-- The discarded coordinate labels, with no duplication or reindexing. -/
def pairedC3DiscardedCoordinateEmbedding {ι κ : Type} (e : κ ↪ ι) :
    {j : ι // j ∉ Set.range e} ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩

/-- The affine conormal basis consists of exactly the discarded coordinate classes. -/
def pairedC3CoordinateEliminationConormalBasis {A ι κ : Type} [CommRing A] (e : κ ↪ ι) :
    let I := Ideal.span (X (R := A) '' (Set.range e)ᶜ)
    Module.Basis {j : ι // j ∉ Set.range e} (MvPolynomial ι A ⧸ I) I.Cotangent := by
  let I := Ideal.span (X (R := A) '' (Set.range e)ᶜ)
  exact Module.Basis.mk
    (s2e_coordinate_classes_independent I (pairedC3DiscardedCoordinateEmbedding e)
      (fun j => Ideal.subset_span ⟨j.val, j.property, rfl⟩))
    (paired_c3_cotangent_image_generators_span X (Set.range e)ᶜ)

/-- Every labelled vector of the elimination conormal basis is the
specified original coordinate class with coefficient one. -/
theorem paired_c3_coordinate_elimination_conormal_basis_apply
    {A ι κ : Type} [CommRing A] (e : κ ↪ ι)
    (j : {j : ι // j ∉ Set.range e}) :
    pairedC3CoordinateEliminationConormalBasis (A := A) e j =
      (Ideal.span (X (R := A) '' (Set.range e)ᶜ)).toCotangent
        ⟨X j.val, Ideal.subset_span ⟨j.val, j.property, rfl⟩⟩ :=
  Module.Basis.mk_apply
    (s2e_coordinate_classes_independent
      (Ideal.span (X (R := A) '' (Set.range e)ᶜ)) (pairedC3DiscardedCoordinateEmbedding e)
      (fun j => Ideal.subset_span ⟨j.val, j.property, rfl⟩))
    (paired_c3_cotangent_image_generators_span X (Set.range e)ᶜ) j

end HodgeLean.Foundations.Program.G32Native
