import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.Derivation.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- Prescribed first jets at distinct field-valued points can be translated to arbitrary values
and interpolated by a single algebra element.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10. -/
theorem s2t_interpolate_point_jets {K A ι : Type*} [Field K] [CommRing A]
    [Algebra K A] [Finite ι] (φ : ι → A →ₐ[K] K) (hinj : Function.Injective φ)
    (a : ι → A) (c : ι → K) :
    ∃ g : A, ∀ i, φ i g = c i ∧
      g - (a i + algebraMap K A (c i - φ i (a i))) ∈
        RingHom.ker (φ i).toRingHom ^ 2 := by
  have hmax (i : ι) : (RingHom.ker (φ i).toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun k => ⟨algebraMap K A k, (φ i).commutes k⟩)
  have hker : Function.Injective (fun i => RingHom.ker (φ i).toRingHom) := by
    intro i j hij
    apply hinj
    ext z
    have hz : z - algebraMap K A (φ i z) ∈ RingHom.ker (φ i).toRingHom := by
      simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    change RingHom.ker (φ i).toRingHom = RingHom.ker (φ j).toRingHom at hij
    rw [hij] at hz
    have hz' : φ j z - φ i z = 0 := by
      simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using hz
    exact (sub_eq_zero.mp hz').symm
  have hcop : Pairwise (fun i j => IsCoprime
      (RingHom.ker (φ i).toRingHom ^ 2) (RingHom.ker (φ j).toRingHom ^ 2)) := by
    intro i j hij
    letI := hmax i
    letI := hmax j
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact Ideal.pow_sup_pow_eq_top
      (Ideal.isCoprime_of_isMaximal (fun he => hij (hker he))).sup_eq
  obtain ⟨g, hg⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun i => a i + algebraMap K A (c i - φ i (a i)))
  refine ⟨g, fun i => ⟨?_, hg i⟩⟩
  have hle : RingHom.ker (φ i).toRingHom ^ 2 ≤ RingHom.ker (φ i).toRingHom :=
    Ideal.pow_le_self (by omega)
  have h := hle (hg i)
  have hz : φ i g - (φ i (a i) + (c i - φ i (a i))) = 0 := by
    simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      map_sub, map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using h
  rw [add_comm (φ i (a i)), sub_add_cancel] at hz
  exact sub_eq_zero.mp hz

/-- Translating a first jet by a scalar leaves every derivation into a module annihilated by
its point ideal unchanged.
Source: Hartshorne, Algebraic Geometry, II.8, definition of the cotangent space. -/
theorem s2t_derivation_eq_of_point_jet {K A M : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [AddCommGroup M] [Module K M] [Module A M]
    (I : Ideal A) (D : Derivation K A M)
    (hI : ∀ a ∈ I, ∀ m : M, a • m = 0)
    (g a : A) (c : K) (hjet : g - (a + algebraMap K A c) ∈ I ^ 2) :
    D g = D a := by
  rw [pow_two] at hjet
  have hz : D (g - (a + algebraMap K A c)) = 0 := by
    refine Submodule.mul_induction_on (C := fun z => D z = 0) hjet ?_ ?_
    · intro u hu v hv
      rw [D.leibniz, hI u hu, hI v hv, zero_add]
    · intro u v hu hv
      rw [map_add, hu, hv, zero_add]
  rw [map_sub, map_add, D.map_algebraMap, add_zero] at hz
  exact sub_eq_zero.mp hz

/-- Sections nonzero at their respective distinct field-valued points generate a section with
value one at every specified point.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10. -/
theorem s2t_unit_value_in_span {K A ι : Type*} [Field K] [CommRing A]
    [Algebra K A] [Finite ι] (φ : ι → A →ₐ[K] K) (hinj : Function.Injective φ)
    (r : ι → A) (hr : ∀ i, φ i (r i) ≠ 0) :
    ∃ g ∈ Ideal.span (Set.range r), ∀ i, φ i g = 1 := by
  classical
  letI := Fintype.ofFinite ι
  have hex (i : ι) : ∃ b : A, ∀ j, φ j b =
      if j = i then (φ i (r i))⁻¹ else 0 := by
    obtain ⟨b, hb⟩ := s2t_interpolate_point_jets φ hinj (fun _ => 0)
      (fun j => if j = i then (φ i (r i))⁻¹ else 0)
    exact ⟨b, fun j => (hb j).1⟩
  choose b hb using hex
  refine ⟨∑ i, b i * r i, ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _
      (Ideal.subset_span (Set.mem_range_self i)))
  · intro j
    rw [map_sum, Fintype.sum_eq_single j]
    · rw [map_mul, hb, ite_eq_left rfl, inv_mul_cancel₀ (hr j)]
    · intro i hij
      rw [map_mul, hb, ite_eq_right hij.symm, zero_mul]

end HodgeLean.Foundations.Program
