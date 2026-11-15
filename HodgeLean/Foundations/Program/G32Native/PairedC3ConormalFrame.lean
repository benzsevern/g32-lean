import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalRelations

/-! # The quotient-ring conormal frame of regular chart equations -/
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
open RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native

/-- The original equations, mapped to their conormal classes.
Source: Hartshorne, Algebraic Geometry, II.8, conormal modules. -/
def pairedC3ConormalGenerators {A : Type*} [CommRing A] {n : ℕ} (f : Fin n → A) :
    (Fin n → A) →ₗ[A] (Ideal.span (Set.range f)).Cotangent :=
  ∑ i, (LinearMap.proj i).smulRight
    ((Ideal.span (Set.range f)).toCotangent ⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩)

/-- The generator map sends coefficients to the class of their linear
combination of the specified equations.
Source: Hartshorne, Algebraic Geometry, II.8. -/
theorem paired_c3_conormal_generators_apply
    {A : Type*} [CommRing A] {n : ℕ} (f c : Fin n → A) :
    pairedC3ConormalGenerators f c =
      (Ideal.span (Set.range f)).toCotangent
        ⟨∑ i, c i * f i, (Ideal.span (Set.range f)).sum_mem fun i _ =>
          Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)⟩ := by
  simp only [pairedC3ConormalGenerators, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, ← map_smul, ← map_sum]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, smul_eq_mul]

/-- The coefficient relations on regular equations are exactly their
coordinatewise ideal multiples.
Source: Hartshorne, Algebraic Geometry, II.8. -/
theorem paired_c3_conormal_generators_kernel
    {A : Type*} [CommRing A] {n : ℕ} (f : Fin n → A)
    (hreg : IsWeaklyRegular A (List.ofFn f)) :
    LinearMap.ker (pairedC3ConormalGenerators f) =
      Submodule.pi Set.univ (fun _ : Fin n => Ideal.span (Set.range f)) := by
  ext c
  rw [LinearMap.mem_ker, paired_c3_conormal_generators_apply, Ideal.toCotangent_eq_zero,
    paired_c3_regular_square_coefficients f c hreg]
  simp only [Submodule.mem_pi, Set.mem_univ, forall_const]

/-- The original equations generate the conormal module.
Source: Hartshorne, Algebraic Geometry, II.8. -/
theorem paired_c3_conormal_generators_surjective
    {A : Type*} [CommRing A] {n : ℕ} (f : Fin n → A) :
    Function.Surjective (pairedC3ConormalGenerators f) := by
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := (Ideal.span (Set.range f)).toCotangent_surjective x
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hx
  refine ⟨c, ?_⟩
  rw [paired_c3_conormal_generators_apply]
  congr 1
  exact Subtype.ext hc

/-- A weakly regular sequence supplies an actual rank-n frame of its
conormal over the quotient ring.
Source: Hartshorne, Algebraic Geometry, II.8, regular immersions. -/
def pairedC3RegularConormalFrame
    {A : Type*} [CommRing A] {n : ℕ} (f : Fin n → A)
    (hreg : IsWeaklyRegular A (List.ofFn f)) :
    (Fin n → A ⧸ Ideal.span (Set.range f)) ≃ₗ[A ⧸ Ideal.span (Set.range f)]
      (Ideal.span (Set.range f)).Cotangent := by
  let e := (Submodule.quotientPi (fun _ : Fin n => Ideal.span (Set.range f))).symm
  let e' := Submodule.quotEquivOfEq _ _ (paired_c3_conormal_generators_kernel f hreg).symm
  let e'' := (pairedC3ConormalGenerators f).quotKerEquivOfSurjective
    (paired_c3_conormal_generators_surjective f)
  exact (e.trans (e'.trans e'')).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

#print axioms pairedC3ConormalGenerators
#print axioms paired_c3_conormal_generators_apply
#print axioms paired_c3_conormal_generators_kernel
#print axioms paired_c3_conormal_generators_surjective
#print axioms pairedC3RegularConormalFrame
end HodgeLean.Foundations.Program.G32Native
