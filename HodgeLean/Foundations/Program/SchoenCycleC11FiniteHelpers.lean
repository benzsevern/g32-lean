import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped NNReal
namespace HodgeLean.Foundations.Program

/-- A complex evaluation of an integral element obeys the bound from its monic relation.
Source: Mathlib, Polynomial.IsRoot.norm_lt_cauchyBound; Atiyah–Macdonald, Chapter 5. -/
theorem s2e_c11_integral_evaluation_bound
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    (p : Polynomial A) (hp : p.Monic) (b : B) (hb : Polynomial.aeval b p = 0)
    (φ : B →ₐ[ℂ] ℂ) :
    ‖φ b‖₊ < Polynomial.cauchyBound
      (p.map (φ.toRingHom.comp (algebraMap A B))) := by
  apply Polynomial.IsRoot.norm_lt_cauchyBound (hp.map _).ne_zero
  rw [Polynomial.IsRoot.def, Polynomial.eval_map]
  calc
    _ = φ (Polynomial.eval₂ (algebraMap A B) b p) :=
      (Polynomial.hom_eval₂ (p := p) (f := algebraMap A B) (g := φ.toRingHom) b).symm
    _ = 0 := by
      change φ (Polynomial.aeval b p) = 0
      rw [hb, map_zero]

/-- Monic relations bound evaluations uniformly over a compact set of base points.
Source: Mathlib, Cauchy root bound and compact boundedness of continuous coefficient functions. -/
theorem s2e_c11_compact_base_integral_bound
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    (p : Polynomial A) (hp : p.Monic) (b : B) (hb : Polynomial.aeval b p = 0)
    (K : Set (A →ₐ[ℂ] ℂ)) (hK : IsCompact K) :
    ∃ R : ℝ≥0, ∀ φ : B →ₐ[ℂ] ℂ,
      φ.comp (IsScalarTower.toAlgHom ℂ A B) ∈ K → ‖φ b‖₊ ≤ R := by
  let c : (A →ₐ[ℂ] ℂ) → ℝ≥0 := fun ψ =>
    (Finset.range p.natDegree).sup (fun i => ‖ψ (p.coeff i)‖₊)
  have hc : Continuous c := by
    apply Continuous.finset_sup_apply
    intro i _
    exact (AlgebraicGeometry.ComplexPoint.continuous_affineAlgebraHom_apply
      A (p.coeff i)).nnnorm
  obtain ⟨R, hR⟩ := (hK.image hc).bddAbove
  refine ⟨R + 1, ?_⟩
  intro φ hφ
  have hbound := s2e_c11_integral_evaluation_bound p hp b hb φ
  have heq : Polynomial.cauchyBound (p.map (φ.toRingHom.comp (algebraMap A B))) =
      c (φ.comp (IsScalarTower.toAlgHom ℂ A B)) + 1 := by
    simp only [Polynomial.cauchyBound, hp.natDegree_map,
      (hp.map _).leadingCoeff, nnnorm_one, div_one, Polynomial.coeff_map]
    rfl
  rw [heq] at hbound
  exact hbound.le.trans (add_le_add (hR ⟨_, hφ, rfl⟩) le_rfl)

/-- Every element of a finite algebra has uniformly bounded evaluations over compact base sets.
Source: Atiyah–Macdonald, Chapter 5; Mathlib, IsIntegral.of_finite and Cauchy root bound. -/
theorem s2e_c11_finite_element_compact_bound
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Module.Finite A B] (b : B) (K : Set (A →ₐ[ℂ] ℂ)) (hK : IsCompact K) :
    ∃ R : ℝ≥0, ∀ φ : B →ₐ[ℂ] ℂ,
      φ.comp (IsScalarTower.toAlgHom ℂ A B) ∈ K → ‖φ b‖₊ ≤ R := by
  obtain ⟨p, hp, hb⟩ := IsIntegral.of_finite (R := A) b
  exact s2e_c11_compact_base_integral_bound p hp b hb K hK

/-- Algebra homomorphisms form a closed equation locus in the space of all functions.
Source: Hartshorne, Algebraic Geometry, Appendix B, affine analytification by equations. -/
theorem s2e_c11_algebraHom_isClosedEmbedding
    (B : Type) [CommRing B] [Algebra ℂ B] :
    Topology.IsClosedEmbedding (fun φ : B →ₐ[ℂ] ℂ => (φ : B → ℂ)) := by
  have hrange : Set.range (fun φ : B →ₐ[ℂ] ℂ => (φ : B → ℂ)) =
      {g : B → ℂ | g 0 = 0 ∧ g 1 = 1 ∧
        (∀ x y, g (x + y) = g x + g y) ∧
        (∀ x y, g (x * y) = g x * g y) ∧
        ∀ c : ℂ, g (algebraMap ℂ B c) = c} := by
    ext g
    constructor
    · rintro ⟨φ, rfl⟩
      exact ⟨φ.map_zero, φ.map_one, φ.map_add, φ.map_mul, φ.commutes⟩
    · rintro ⟨h0, h1, ha, hm, hc⟩
      let φ : B →ₐ[ℂ] ℂ :=
        { toFun := g
          map_zero' := h0
          map_one' := h1
          map_add' := ha
          map_mul' := hm
          commutes' := hc }
      exact ⟨φ, rfl⟩
  refine ⟨Topology.IsEmbedding.induced (fun φ ψ h => AlgHom.ext (congrFun h)), ?_⟩
  rw [hrange]
  have h0 : IsClosed {g : B → ℂ | g 0 = 0} :=
    isClosed_eq (continuous_apply 0) continuous_const
  have h1 : IsClosed {g : B → ℂ | g 1 = 1} :=
    isClosed_eq (continuous_apply 1) continuous_const
  have ha : IsClosed {g : B → ℂ | ∀ x y, g (x + y) = g x + g y} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
      isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))))
  have hm : IsClosed {g : B → ℂ | ∀ x y, g (x * y) = g x * g y} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
      isClosed_eq (continuous_apply (x * y)) ((continuous_apply x).mul (continuous_apply y))))
  have hc : IsClosed {g : B → ℂ | ∀ c : ℂ, g (algebraMap ℂ B c) = c} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun c => isClosed_eq (continuous_apply (algebraMap ℂ B c))
      continuous_const)
  exact h0.inter (h1.inter (ha.inter (hm.inter hc)))

/-- Finite algebra restriction has compact inverse images of compact base sets.
Source: Mathlib, Tychonoff compactness; Atiyah–Macdonald, Chapter 5, integral relations. -/
theorem s2e_c11_finite_affine_compact_preimage
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Module.Finite A B] (K : Set (A →ₐ[ℂ] ℂ)) (hK : IsCompact K) :
    IsCompact ((fun φ : B →ₐ[ℂ] ℂ =>
      φ.comp (IsScalarTower.toAlgHom ℂ A B)) ⁻¹' K) := by
  classical
  let r : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ) :=
    fun φ => φ.comp (IsScalarTower.toAlgHom ℂ A B)
  let eB : (B →ₐ[ℂ] ℂ) → (B → ℂ) := fun φ => φ
  let eA : (A →ₐ[ℂ] ℂ) → (A → ℂ) := fun φ => φ
  let rf : (B → ℂ) → (A → ℂ) := fun g a => g (algebraMap A B a)
  have hrf : Continuous rf := continuous_pi (fun a => continuous_apply (algebraMap A B a))
  have heB := s2e_c11_algebraHom_isClosedEmbedding B
  have heA := s2e_c11_algebraHom_isClosedEmbedding A
  have himage : eB '' (r ⁻¹' K) = Set.range eB ∩ rf ⁻¹' (eA '' K) := by
    ext g
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨⟨φ, rfl⟩, r φ, hφ, rfl⟩
    · rintro ⟨⟨φ, rfl⟩, ψ, hψ, h⟩
      refine ⟨φ, ?_, rfl⟩
      have heq : r φ = ψ := AlgHom.ext (fun a => (congrFun h a).symm)
      change r φ ∈ K
      rw [heq]
      exact hψ
  have hclosed : IsClosed (eB '' (r ⁻¹' K)) := by
    rw [himage]
    exact heB.isClosed_range.inter ((hK.image heA.continuous).isClosed.preimage hrf)
  choose R hR using fun b : B => s2e_c11_finite_element_compact_bound b K hK
  apply heB.isEmbedding.isCompact_iff.mpr
  apply (isCompact_pi_infinite (fun b => isCompact_closedBall (0 : ℂ) (R b : ℝ))).of_isClosed_subset
    hclosed
  rintro g ⟨φ, hφ, rfl⟩ b
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hR b φ hφ

/-- Each finite-algebra coordinate has a continuous bound depending only on the base point.
Source: Mathlib, Cauchy root bound; Atiyah–Macdonald, Chapter 5, integral relations. -/
theorem s2e_c11_finite_element_continuous_bound
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Module.Finite A B] (b : B) :
    ∃ c : (A →ₐ[ℂ] ℂ) → ℝ≥0, Continuous c ∧
      ∀ φ : B →ₐ[ℂ] ℂ, ‖φ b‖₊ ≤ c (φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
  obtain ⟨p, hp, hb⟩ := IsIntegral.of_finite (R := A) b
  let c : (A →ₐ[ℂ] ℂ) → ℝ≥0 := fun ψ =>
    (Finset.range p.natDegree).sup (fun i => ‖ψ (p.coeff i)‖₊) + 1
  refine ⟨c, ?_, ?_⟩
  · apply Continuous.add_const
    apply Continuous.finset_sup_apply
    intro i _
    exact (AlgebraicGeometry.ComplexPoint.continuous_affineAlgebraHom_apply A (p.coeff i)).nnnorm
  · intro φ
    have h := s2e_c11_integral_evaluation_bound p hp b hb φ
    have heq : Polynomial.cauchyBound (p.map (φ.toRingHom.comp (algebraMap A B))) =
        c (φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
      simp only [Polynomial.cauchyBound, hp.natDegree_map,
        (hp.map _).leadingCoeff, nnnorm_one, div_one, Polynomial.coeff_map]
      rfl
    exact heq ▸ h.le

end HodgeLean.Foundations.Program
