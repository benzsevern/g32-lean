import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Actual quotient sequences for nested relative chain pairs -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits
namespace HodgeLean.Foundations.QuotientDuality

variable {C : Type*} [Category C] [Abelian C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D)

/-- The actual three cokernels of a composable pair, with the canonical quotient maps.
Source: Weibel, An Introduction to Homological Algebra, section 1.3, quotient sequences.
HC no distance; AV milestone no distance. -/
def properCycle_cokernel_composition_sequence : ShortComplex C :=
  (kernelCokernelCompSequence.snakeInput f g).L₃

/-- A monomorphism in the second factor gives the actual short exact sequence of the three quotient objects.
Source: Weibel, An Introduction to Homological Algebra, section 1.3, the kernel-cokernel sequence.
HC no distance; AV milestone no distance. -/
lemma properCycle_cokernel_composition_sequence_shortExact [Mono g] :
    (properCycle_cokernel_composition_sequence f g).ShortExact where
  exact := (kernelCokernelCompSequence.snakeInput f g).L₃_exact
  mono_f := by
    have h := (kernelCokernelCompSequence_exact f g).exact 2
    apply h.mono_g
    change kernelCokernelCompSequence.δ f g = 0
    rw [kernelCokernelCompSequence.δ_fac]
    have hi : kernel.ι g = 0 := (cancel_mono g).mp (by simp)
    simp [hi]
  epi_g := by
    change Epi ((kernelCokernelCompSequence f g).map' 4 5)
    infer_instance

variable (k : A ⟶ D) (hk : f ≫ g = k)

/-- The same actual quotient sequence with a specified composite morphism.
Source: Weibel, An Introduction to Homological Algebra, section 1.3, quotient sequences.
HC no distance; AV milestone no distance. -/
def properCycle_cokernel_factorization_sequence : ShortComplex C where
  X₁ := cokernel f
  X₂ := cokernel k
  X₃ := cokernel g
  f := cokernel.map f k (𝟙 A) g (by simpa using hk)
  g := cokernel.map k g f (𝟙 D) (by simpa using hk.symm)
  zero := by
    apply (cancel_epi (cokernel.π f)).mp
    simp

/-- Equality of the specified composite retains the actual outer quotients and the canonical middle quotient transport.
Source: Weibel, An Introduction to Homological Algebra, section 1.3, functoriality of quotients.
HC no distance; AV milestone no distance. -/
def properCycle_cokernel_factorization_iso :
    properCycle_cokernel_composition_sequence f g ≅ properCycle_cokernel_factorization_sequence f g k hk := by
  subst k
  exact Iso.refl _

/-- The actual quotient sequence for a specified composite is short exact.
Source: Weibel, An Introduction to Homological Algebra, section 1.3, quotient sequences.
HC no distance; AV milestone no distance. -/
lemma properCycle_cokernel_factorization_sequence_shortExact [Mono g] :
    (properCycle_cokernel_factorization_sequence f g k hk).ShortExact :=
  ShortComplex.shortExact_of_iso (properCycle_cokernel_factorization_iso f g k hk)
    (properCycle_cokernel_composition_sequence_shortExact f g)

end HodgeLean.Foundations.QuotientDuality
