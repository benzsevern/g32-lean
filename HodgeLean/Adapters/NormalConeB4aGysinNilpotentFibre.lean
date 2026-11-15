import HodgeLean.Adapters.NormalConeB4aGysinSmoothThickening
import HodgeLean.Adapters.NormalConeB4aGysinAugmentedLength
import HodgeLean.Adapters.NormalConeB4aGysinLocalModelLength

/-! # Generic multiplicities in split finite nilpotent thickenings -/

noncomputable section
namespace HodgeLean.Adapters

/-- A nilpotent retraction identifies the unique source prime over each base prime. -/
theorem a3b4a_gysin_nilpotent_retraction_prime
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (π : A →ₐ[B] B) (hnil : IsNilpotent (RingHom.ker π))
    (p : Ideal B) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] :
    q = p.comap π.toRingHom := by
  obtain ⟨n, hn⟩ := hnil
  have hker : RingHom.ker π ≤ q := by
    intro a ha
    apply (inferInstance : q.IsPrime).mem_of_pow_mem n
    have hz : a ^ n = 0 := by simpa [hn] using Ideal.pow_mem_pow ha n
    rw [hz]
    exact q.zero_mem
  ext a
  change a ∈ q ↔ π a ∈ p
  have hk : a - algebraMap B A (π a) ∈ q := hker (by simp [RingHom.mem_ker])
  constructor
  · intro ha
    apply (Ideal.mem_of_liesOver q p (π a)).mpr
    simpa using q.sub_mem ha hk
  · intro ha
    have hm := (Ideal.mem_of_liesOver q p (π a)).mp ha
    simpa using q.add_mem hk hm

/-- Every fibre of a finite split nilpotent thickening is local. -/
theorem a3b4a_gysin_nilpotent_retraction_fibre_local
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A] [Module.Finite B A]
    (π : A →ₐ[B] B) (hnil : IsNilpotent (RingHom.ker π)) (p : Ideal B) [p.IsPrime] :
    IsLocalRing (p.Fiber A) := by
  have : p.LiesOver p := ⟨by ext x; rfl⟩
  let q := p.comap π
  have : q.LiesOver p := inferInstance
  apply a3b4a_gysin_fibre_local_of_unique_prime p q
  intro q' hq' hq'p
  exact a3b4a_gysin_nilpotent_retraction_prime π hnil p q'

/-- In a finite flat split nilpotent thickening of a domain, every fibre has
the full generic stalk length of the thickening, including all nilpotents. -/
theorem a3b4a_gysin_nilpotent_fibre_length_eq_generic_length
    {B A : Type*} [CommRing B] [IsDomain B] [CommRing A]
    [Algebra B A] [Module.Finite B A] [Module.Flat B A]
    (π : A →ₐ[B] B) (hnil : IsNilpotent (RingHom.ker π)) (p : Ideal B) [p.IsPrime] :
    letI : (RingHom.ker π).IsPrime := RingHom.ker_isPrime π
    Module.length (p.Fiber A) (p.Fiber A) =
      Module.length (Localization.AtPrime (RingHom.ker π))
        (Localization.AtPrime (RingHom.ker π)) := by
  have : (RingHom.ker π).IsPrime := RingHom.ker_isPrime π
  have : IsLocalRing (p.Fiber A) := a3b4a_gysin_nilpotent_retraction_fibre_local π hnil p
  have : IsLocalRing ((⊥ : Ideal B).Fiber A) :=
    a3b4a_gysin_nilpotent_retraction_fibre_local π hnil ⊥
  let ε (I : Ideal B) [I.IsPrime] : I.Fiber A →ₐ[I.ResidueField] I.ResidueField :=
    (Algebra.TensorProduct.rid B I.ResidueField I.ResidueField).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id I.ResidueField I.ResidueField) π)
  have hdim := a3b4a_gysin_augmented_fibre_lengths_equal p (⊥ : Ideal B) (ε p) (ε ⊥)
  have : (RingHom.ker π).LiesOver (⊥ : Ideal B) := ⟨by
    ext b
    change b = 0 ↔ π (algebraMap B A b) = 0
    simp⟩
  let F := (PrimeSpectrum.primesOverOrderIsoFiber B A (⊥ : Ideal B))
    (Ideal.primesOver.mk (⊥ : Ideal B) (RingHom.ker π))
  have hr : F.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = RingHom.ker π := by
    exact congrArg Subtype.val ((PrimeSpectrum.primesOverOrderIsoFiber B A (⊥ : Ideal B)).symm_apply_apply
      (Ideal.primesOver.mk (⊥ : Ideal B) (RingHom.ker π)))
  have hf := a3b4a_gysin_local_fibre_length_eq_source_quotient (⊥ : Ideal B) F.asIdeal
  dsimp only at hf
  rw [Ideal.map_bot] at hf
  let L := Localization.AtPrime (F.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom)
  have hbot := a3b2_length_eq_of_ringEquiv (RingEquiv.quotientBot L)
  have hmove := a3b2_length_eq_of_ringEquiv
    (Localization.localRingEquiv
      (F.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom)
      (RingHom.ker π) (RingEquiv.refl A) (hr.trans (by ext a; rfl)))
  exact hdim.trans (hf.trans (hbot.trans hmove))

end HodgeLean.Adapters
