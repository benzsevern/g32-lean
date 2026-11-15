import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import HodgeLean.Foundations.Program.G32SelectedRealizationDefs

noncomputable section
open HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32x_projector_inverse_matrix :
    ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4b_toMatrix g⁻¹ =
      (b4b_projectorDenominator : ℂ) •
        (Matrix.single 0 0 1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [← b63l_projector_matrix]
  exact Fintype.sum_equiv (Equiv.inv b4b_Group) _ _
    (fun g ↦ by simp only [Equiv.inv_apply, b63l_projectorCoeff_inverse])

theorem g32x_central_projector_convolution (h : b4b_Group) :
    ∑ g : b4b_Group,
      ((b4b_toMatrix g).trace + star (b4b_toMatrix g).trace) *
        (b4b_projectorCoeff (g⁻¹ * h) : ℂ) =
      (38880 : ℂ) * (b4b_projectorCoeff h : ℂ) := by
  have hsum : ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) *
      (b4b_toMatrix (h * g⁻¹)).trace =
      (b4b_projectorDenominator : ℂ) * b4b_toMatrix h 0 0 := by
    have hm := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦
      (b4b_toMatrix h * M).trace) g32x_projector_inverse_matrix
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul] at hm
    simp only [map_mul]
    rw [hm]
    simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and,
      Finset.sum_ite_eq, @eq_comm _ (0 : Fin 4)]
  calc
    _ = ∑ k : b4b_Group, (b4b_projectorCoeff k : ℂ) *
        ((b4b_toMatrix (h * k⁻¹)).trace +
          star (b4b_toMatrix (h * k⁻¹)).trace) := by
      symm
      refine Fintype.sum_equiv ((Equiv.inv b4b_Group).trans (Equiv.mulLeft h))
        _ _ fun k ↦ ?_
      simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft,
        mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      ring
    _ = (b4b_projectorDenominator : ℂ) * b4b_toMatrix h 0 0 +
        star ((b4b_projectorDenominator : ℂ) * b4b_toMatrix h 0 0) := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [hsum]
      congr 1
      rw [← hsum, star_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [star_mul, star_intCast]
      ring
    _ = _ := by
      rw [b63l_projectorCoeff_complex]
      norm_num [b4b_projectorDenominator, map_mul]
      ring

theorem g32x_representation_convolution {K G V : Type} [CommSemiring K]
    [Group G] [Fintype G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (a b : G → K) :
    (∑ g, a g • ρ g) * (∑ h, b h • ρ h) =
      ∑ x, (∑ g, a g * b (g⁻¹ * x)) • ρ x := by
  calc
    _ = ∑ g, ∑ h, (a g * b h) • ρ (g * h) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, map_mul, mul_comm (b h) (a g)]
    _ = ∑ g, ∑ x, (a g * b (g⁻¹ * x)) • ρ x := by
      apply Finset.sum_congr rfl
      intro g _
      exact Fintype.sum_equiv (Equiv.mulLeft g) _ _
        (fun h ↦ by simp only [Equiv.coe_mulLeft, inv_mul_cancel_left])
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]

theorem g32x_representation_central_fixed {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ b4b_Group V) :
    (((4 : ℂ) / Fintype.card b4b_Group) • ∑ g,
      ((b4b_toMatrix g).trace + star (b4b_toMatrix g).trace) • ρ g) *
        (∑ h, (b4b_projectorCoeff h : ℂ) • ρ h) =
      ∑ h, (b4b_projectorCoeff h : ℂ) • ρ h := by
  rw [smul_mul_assoc, g32x_representation_convolution]
  simp_rw [g32x_central_projector_convolution]
  have hs : (∑ h : b4b_Group, ((38880 : ℂ) * (b4b_projectorCoeff h : ℂ)) • ρ h) =
      (38880 : ℂ) • ∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) • ρ h := by
    simp only [Finset.smul_sum, smul_smul]
  rw [hs, smul_smul]
  rw [b63l_card_group]
  norm_num

theorem g32x_baseChange_zsum {V Idx : Type} [AddCommGroup V] [Module ℚ V]
    [Fintype Idx] (n : Idx → ℤ) (f : Idx → Module.End ℚ V) :
    (∑ i, n i • f i).baseChange ℂ = ∑ i, (n i : ℂ) • (f i).baseChange ℂ := by
  change (Module.End.baseChangeHom ℚ ℂ V) (∑ i, n i • f i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, Int.cast_smul_eq_zsmul]
  rfl


theorem g32y_common_kernel_projector {A V : Type*} [Ring A] [IsSemisimpleRing A]
    [AddCommGroup V] [Module ℚ V] (ρ : A →+* Module.End ℚ V) (s : Set A) :
    ∃ p : A, p * p = p ∧ ∀ v : V,
      v ∈ LinearMap.range (ρ p) ↔ ∀ a ∈ s, ρ a v = 0 := by
  classical
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span s)
  have hk (v : V) : ρ e v = 0 ↔ ∀ a ∈ s, ρ a v = 0 := by
    constructor
    · intro hv a ha
      have haI : a ∈ Ideal.span ({e} : Set A) := hI ▸ Ideal.subset_span ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp haI
      rw [map_mul, Module.End.mul_apply, hv, map_zero]
    · intro hv
      let J : Ideal A := {
        carrier := {a | ρ a v = 0}
        zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero, LinearMap.zero_apply]
        add_mem' := by
          intro a b ha hb
          change ρ (a + b) v = 0
          rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
        smul_mem' := by
          intro a b hb
          change ρ (a * b) v = 0
          rw [map_mul, Module.End.mul_apply, hb, map_zero] }
      have hle : Ideal.span s ≤ J := Ideal.span_le.mpr hv
      have heI : e ∈ Ideal.span s := hI.symm ▸ Ideal.mem_span_singleton_self e
      exact hle heI
  refine ⟨1 - e, ?_, ?_⟩
  · change e * e = e at he
    calc
      (1 - e) * (1 - e) = 1 - e - e + e * e := by noncomm_ring
      _ = 1 - e := by rw [he]; abel
  · intro v
    rw [← hk]
    constructor
    · rintro ⟨w, rfl⟩
      have hzero : ρ e * ρ (1 - e) = 0 := by
        rw [← map_mul, mul_sub, mul_one, he.eq, sub_self, map_zero]
      exact LinearMap.congr_fun hzero w
    · intro hv
      refine ⟨v, ?_⟩
      rw [map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply, hv, sub_zero]

theorem g32y_group_kernel_projector {H V : Type*} [Group H] [Fintype H]
    [AddCommGroup V] [Module ℚ V] (R : Representation ℚ H V)
    (s : Set (MonoidAlgebra ℚ H)) :
    ∃ u : H → ℚ,
      let e : Module.End ℚ V := ∑ h, u h • R h
      e ∘ₗ e = e ∧ ∀ v, v ∈ LinearMap.range e ↔ ∀ a ∈ s, R.asAlgebraHom a v = 0 := by
  classical
  let : NeZero (Nat.card H : ℚ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨p, hp, hs⟩ := g32y_common_kernel_projector R.asAlgebraHom.toRingHom s
  have hsum : R.asAlgebraHom p = ∑ h : H, p.coeff h • R h := by
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
    exact Finsupp.sum_fintype _ _ (fun h ↦ zero_smul ℚ (R h))
  refine ⟨p.coeff, ?_, ?_⟩
  · rw [← hsum, ← Module.End.mul_eq_comp, ← map_mul, hp]
  · rw [← hsum]
    exact hs

theorem g32y_relation_projector {H V : Type*} [Group H] [Fintype H]
    [AddCommGroup V] [Module ℚ V] (R : Representation ℚ H V)
    (s₁ s₂ : Set H) (q : Polynomial ℚ) :
    ∃ u : H → ℚ,
      let e : Module.End ℚ V := ∑ h, u h • R h
      e ∘ₗ e = e ∧ LinearMap.range e =
        (⨅ h, ⨅ (_ : h ∈ s₁), LinearMap.eqLocus (R h) LinearMap.id) ⊓
        ⨅ h, ⨅ (_ : h ∈ s₂), LinearMap.ker (Polynomial.aeval (R h) q) := by
  classical
  let z : H → MonoidAlgebra ℚ H := MonoidAlgebra.of ℚ H
  let s : Set (MonoidAlgebra ℚ H) :=
    {a | ∃ h ∈ s₁, a = z h - 1} ∪
    {a | ∃ h ∈ s₂, a = Polynomial.aeval (z h) q}
  have hz (h : H) : R.asAlgebraHom (z h) = R h := R.asAlgebraHom_of h
  have hpoly (h : H) : R.asAlgebraHom (Polynomial.aeval (z h) q) =
      Polynomial.aeval (R h) q := by
    rw [← Polynomial.aeval_algHom_apply, hz]
  obtain ⟨u, hu, hs⟩ := g32y_group_kernel_projector R s
  refine ⟨u, hu, ?_⟩
  ext v
  rw [hs]
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_eqLocus,
    LinearMap.id_apply, LinearMap.mem_ker]
  constructor
  · intro hv
    constructor
    · intro h hh
      have hh' := hv (z h - 1) (Or.inl ⟨h, hh, rfl⟩)
      simpa only [map_sub, map_one, hz, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero] using hh'
    · intro h hh
      have hh' := hv (Polynomial.aeval (z h) q) (Or.inr ⟨h, hh, rfl⟩)
      rwa [hpoly] at hh'
  · rintro ⟨h₁, h₂⟩ a (⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩)
    · rw [map_sub, map_one, hz, LinearMap.sub_apply, Module.End.one_apply,
        h₁ h hh, sub_self]
    · rw [hpoly]
      exact h₂ h hh

theorem g32y_clear_denominators {H : Type*} [Fintype H] (u : H → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : H → ℤ, ∀ h, (N : ℚ) * u h = (z h : ℚ) := by
  classical
  let N := ∏ h, (u h).den
  have hN : 0 < N := Finset.prod_pos (fun h _ ↦ (u h).den_pos)
  have hd (h : H) : (u h).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ h)
  choose k hk using hd
  refine ⟨N, hN, fun h ↦ (k h : ℤ) * (u h).num, ?_⟩
  intro h
  calc
    (N : ℚ) * u h = (k h : ℚ) * ((u h).den : ℚ) * u h := by
      rw [hk h, Nat.cast_mul]
      ring
    _ = (k h : ℚ) * (u h).num := by rw [mul_assoc, Rat.den_mul_eq_num]
    _ = (((k h : ℤ) * (u h).num : ℤ) : ℚ) := by push_cast; rfl

theorem g32y_image_idempotent {A : Type*} [Ring A] [IsSemisimpleRing A] (p : A) :
    ∃ e : A, e * e = e ∧ ∃ a b : A, e = p * a ∧ p = e * b := by
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
    (Ideal.span ({MulOpposite.op p} : Set Aᵐᵒᵖ))
  have heI : e ∈ Ideal.span ({MulOpposite.op p} : Set Aᵐᵒᵖ) :=
    hI.symm ▸ Ideal.mem_span_singleton_self e
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp heI
  have hpI : MulOpposite.op p ∈ Ideal.span ({e} : Set Aᵐᵒᵖ) :=
    hI ▸ Ideal.mem_span_singleton_self (MulOpposite.op p)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hpI
  refine ⟨e.unop, congrArg MulOpposite.unop he.eq, a.unop, b.unop, ?_, ?_⟩
  · exact (congrArg MulOpposite.unop ha).symm
  · exact (congrArg MulOpposite.unop hb).symm

theorem g32y_projector_with_range {A V : Type*} [Ring A] [IsSemisimpleRing A]
    [AddCommGroup V] [Module ℚ V] (ρ : A →+* Module.End ℚ V) (p : A) :
    ∃ e : A, e * e = e ∧ LinearMap.range (ρ e) = LinearMap.range (ρ p) := by
  obtain ⟨e, he, a, b, hea, hpb⟩ := g32y_image_idempotent p
  refine ⟨e, he, ?_⟩
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨ρ a v, ?_⟩
    rw [hea, map_mul, Module.End.mul_apply]
  · rintro _ ⟨v, rfl⟩
    refine ⟨ρ b v, ?_⟩
    rw [hpb, map_mul, Module.End.mul_apply]

end HodgeLean.Foundations.Program
