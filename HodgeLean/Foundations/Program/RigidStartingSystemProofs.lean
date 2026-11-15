import HodgeLean.Foundations.Program.RigidStartingSystemSourcePresentation
import HodgeLean.Foundations.Program.RigidStartingSystemRegularMonodromy
import HodgeLean.Foundations.Program.RigidStartingSystemMonodromyRigidity
import HodgeLean.Foundations.Program.RigidStartingSystemPullbackMonodromy
import HodgeLean.Foundations.Program.RigidStartingSystemDefs
import HodgeLean.Foundations.Program.RigidStartingSystemRational
import HodgeLean.Foundations.Program.RigidStartingSystemChart
import HodgeLean.Foundations.Program.RigidStartingSystemNonresonance
import HodgeLean.Foundations.Program.RigidStartingSystemExponentialClasses
import HodgeLean.Foundations.Program.RigidStartingSystemFourPointCentralizers
import HodgeLean.Foundations.Program.RigidStartingSystemIrreducibility
import HodgeLean.Foundations.Program.RigidStartingSystemRigidity
import HodgeLean.Foundations.Program.FuchsianSystem

/-! # Starting-system proofs -/

noncomputable section
open Set Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65r_marked_comparison_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (R : ℂ → E →L[ℂ] E) :
    ∃ x : {z : ℂ // z ∉ b65r_marks},
      ∃ e : {z : ℂ // z ∉ b65r_marks} ≃ₜ b6t_punctured mr_base,
      ∃ hx : e x = b63gP_basePoint,
        (∀ z, (e z : OnePoint ℂ) = ((z.val : ℂ) : OnePoint ℂ)) ∧
        ∃ P : FundamentalGroup {z : ℂ // z ∉ b65r_marks} x →* (E →L[ℂ] E)ˣ,
        ∃ M : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* (E →L[ℂ] E)ˣ,
          (∀ γ : Path x x,
            (P (FundamentalGroup.fromPath ⟦γ⟧) : E →L[ℂ] E) =
              b65f_transport E (b65f_coefficient E b65r_marks R)
                (fun t ↦ (γ.extend t).val)) ∧
          (∀ c, M (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ hx c) = P c) ∧
          (∀ i, (M (b63gP_loops i) : E →L[ℂ] E) =
            b65f_transport E (b65f_coefficient E b65r_marks R) (b65r_curve i)) := by
  let e := b65r_chart
  let x := e.symm b63gP_basePoint
  have hx : e x = b63gP_basePoint := e.apply_symm_apply _
  have hxi : e.symm b63gP_basePoint = x := rfl
  obtain ⟨P, hP⟩ := b65f_monodromy_representation E b65r_marks R x
  let G := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ hxi
  refine ⟨x, e, hx, fun _ ↦ rfl, P, P.comp G, hP, ?_, ?_⟩
  · intro c
    change P (G (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ hx c)) = P c
    rw [show G (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ hx c) = c from
      b65r_mapOfEq_leftInverse e hx c]
  · intro i
    obtain ⟨p, hp, hclass⟩ :=
      (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
    change FundamentalGroup.fromPath ⟦p⟧ = b63gP_loops i at hclass
    rw [← hclass]
    change (P (G (FundamentalGroup.fromPath ⟦p⟧)) : E →L[ℂ] E) = _
    change (P (FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ hxi
      (FundamentalGroup.fromPath ⟦p⟧)) : E →L[ℂ] E) = _
    change (P (FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ hxi
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) : E →L[ℂ] E) = _
    rw [b65r_mapOfEq_fromPath, hP]
    apply b65r_transport_congr
    intro t ht
    dsimp only
    rw [Path.extend_apply _ ht]
    apply OnePoint.coe_injective
    change ((e.symm (p ⟨t, ht⟩)).val : OnePoint ℂ) = (b65r_curve i t : OnePoint ℂ)
    have he : ((e.symm (p ⟨t, ht⟩)).val : OnePoint ℂ) = (p ⟨t, ht⟩).val :=
      congrArg Subtype.val (e.apply_symm_apply (p ⟨t, ht⟩))
    rw [he, hp]
    simp only [mr_curve, b65r_curve]
    split_ifs <;> rfl


theorem b65r_infinity_residue_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (s : Finset ℂ) (R : ℂ → E →L[ℂ] E) :
    Filter.Tendsto
      (fun w : ℂ ↦ -w⁻¹ • b65f_coefficient E s R w⁻¹)
      (nhdsWithin 0 ({0}ᶜ)) (nhds (-∑ a ∈ s, R a)) := by
  classical
  have hlim : Tendsto (fun w : ℂ ↦ -∑ a ∈ s, (1 - a * w)⁻¹ • R a)
      (𝓝 (0 : ℂ)) (𝓝 (-∑ a ∈ s, R a)) := by
    have hc : ContinuousAt (fun w : ℂ ↦ -∑ a ∈ s, (1 - a * w)⁻¹ • R a) 0 := by
      apply ContinuousAt.neg
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.sum_empty] using
          (continuousAt_const : ContinuousAt (fun _ : ℂ ↦ (0 : E →L[ℂ] E)) 0)
      | @insert a s ha ih =>
          simp only [Finset.sum_insert ha]
          exact ((((continuousAt_const.mul continuousAt_id).const_sub 1).inv₀
            (by simp)).smul continuousAt_const).add ih
    simpa only [mul_zero, sub_zero, inv_one, one_smul] using hc.tendsto
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw0 : w ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hw
  simp only [b65f_coefficient, Finset.smul_sum, neg_smul, Finset.sum_neg_distrib,
    smul_smul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← neg_smul]
  congr 1
  rw [neg_mul, ← mul_inv]
  congr 2
  rw [mul_sub, mul_inv_cancel₀ hw0, mul_comm a w]



theorem b65r_residue_classes_aux  :
    ∀ i : Fin 4,
      (∀ k : ℕ, 0 < k → Function.Bijective
        (fun T : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦
          (k : ℂ) • T - (b65r_operator (b65r_residues i) * T -
            T * b65r_operator (b65r_residues i)))) ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
          NormedSpace.exp ((2 * Real.pi * Complex.I) • b65r_operator (b65r_residues i)) *
          ↑(C⁻¹) = b65r_operator (b4b_toMatrix (b4b_generators i)) := by
  intro i
  exact ⟨fun k hk ↦ b65r_residues_nonresonance i k hk,
    b65r_residue_exponential_class i⟩

theorem b65r_rigidity_aux (n r : ℕ) (hn : 0 < n)
    (T S : Fin r → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hT : (List.ofFn T).prod = 1) (hS : (List.ofFn S).prod = 1)
    (hirr : ∀ W : Submodule ℂ (Fin n → ℂ),
      (∀ i v, v ∈ W → (T i).val.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hidx : b65r_index (fun i ↦ (T i).val) = 2)
    (hloc : ∀ i, ∃ C : (Matrix (Fin n) (Fin n) ℂ)ˣ, C * T i * C⁻¹ = S i) :
    ∃ C : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ i, C * T i * C⁻¹ = S i := by
  exact b65r_simultaneous_conjugacy T S hT hS hirr hidx hloc

theorem b65r_four_point_data_aux  :
    (∀ i : Fin 4,
      Module.finrank ℂ (b65r_centralizer (b4b_toMatrix (b4b_generators i))) =
        (![10, 10, 6, 8] : Fin 4 → ℕ) i) ∧
      b65r_index (fun i ↦ b4b_toMatrix (b4b_generators i)) = 2 ∧
      (∀ W : Submodule ℂ (Fin 4 → ℂ),
        (∀ i v, v ∈ W → (b4b_toMatrix (b4b_generators i)).mulVec v ∈ W) →
          W = ⊥ ∨ W = ⊤) := by
  exact ⟨b65r_printed_centralizer_finrank, b65r_printed_index, b65r_four_point_irreducible⟩

theorem b65r_pullback_identity_aux (s : ℂ) (h0 : s ≠ 0) (h3 : s ≠ 3)
    (h1 : s ≠ 1) (hneg2 : s ≠ -2)
    (h5 : b65r_P 5 s ≠ 0) (hneg7 : b65r_P (-7) s ≠ 0) :
    deriv b65r_phi s = 3*s*(s-3)^3*(5*s^2-3*s+4) / ((s-1)^4*(s+2)^4) ∧
      b65r_pullback s = deriv b65r_phi s • b65r_A (b65r_phi s) := by
  exact ⟨(b65r_phi_hasDerivAt s h1 hneg2).deriv,
    b65r_pullback_formula s h0 h3 h1 hneg2 h5 hneg7⟩

theorem b65r_pullback_local_monodromy_aux (a : ℂ)
    (ha : a = 0 ∨ a = 3 ∨ a = 1 ∨ a = -2 ∨
      b65r_P 5 a = 0 ∨ b65r_P (-7) a = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (b65f_circle a ρ) =
          (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
            b65r_operator (b4b_toMatrix (b65r_localTarget a)) * ↑(C⁻¹) := by
  rcases ha with h | h | h | h | h | h
  · subst a; exact b65r_branch_local_conjugacy 0
  · subst a; exact b65r_branch_local_conjugacy 1
  · subst a; exact b65r_branch_local_conjugacy 2
  · subst a; exact b65r_branch_local_conjugacy 3
  · exact b65r_reflection_local_conjugacy 0 a h
  · exact b65r_reflection_local_conjugacy 1 a h

theorem b65r_four_point_monodromy_aux (x : {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7}) :
    ∃ ρ : FundamentalGroup {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} x →* b4b_Group,
      Function.Surjective ρ ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        ∀ γ : Path x x,
          b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
            (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
              b65r_operator (b4b_toMatrix (ρ (FundamentalGroup.fromPath ⟦γ⟧))) * ↑(C⁻¹) := by
  obtain ⟨M,hM⟩ := b65r_regular_monodromy (Fin 4 → ℂ) b65r_sourceDomain
    b65r_sourceDomain_open b65r_A b65r_A_analytic x
  obtain ⟨δ,hδ,hu,hclasses⟩ := b65r_source_peripheral_presentation x M hM
  obtain ⟨ρ,hsurj,C,hC⟩ := b65r_rigid_monodromy_factorization δ hδ hu M
    (fun i ↦ isConj_iff.mp (hclasses i))
  refine ⟨ρ,hsurj,C,fun γ ↦ ?_⟩
  exact (hM γ).symm.trans (hC (FundamentalGroup.fromPath ⟦γ⟧))

end HodgeLean.Foundations.Program
