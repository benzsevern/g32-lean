import HodgeLean.Foundations.Program.G32SelectedRealizationSupplierHodge

noncomputable section
open Manifold TopologicalSpace HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Foundations
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem g32y_form_character_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    {G : Type} [Group G] [Fintype G] [MulAction G C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) :
    ∑ g : G, (b4_formRepresentation hG).character g =
      (Nat.card G : ℂ) * Module.finrank ℂ (Representation.invariants (b4_formRepresentation hG)) := by
  let := Module.finite_of_finrank_eq_succ hE
  let := b3Forms_holForm_finiteDimensional (C := C) hE
  have hav := Representation.card_inv_mul_sum_char_eq_finrank (b4_formRepresentation hG)
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  calc
    _ = (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ *
        ∑ g : G, (b4_formRepresentation hG).character g) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    _ = _ := by rw [hav]

theorem g32y_holo_multiplicity_fixedKernel
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    {G : Type} [Group G] [Fintype G] [MulAction G C]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [FaithfulSMul G C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (ρ : Representation ℂ G V) (hρ : Representation.invariants ρ = ⊥) :
    (Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_formAct E (C := C) g)
      (b3_HolForm E C)) : ℂ) =
      (Module.finrank ℂ V : ℂ) *
        ((Module.finrank ℂ (Representation.invariants (b4_formRepresentation hG)) : ℂ) - 1) +
        (Nat.card G : ℂ)⁻¹ * ∑ g : G, (∑ᶠ x : C, b4_fixedKernel hE g x) *
          (ρ.character g - (Module.finrank ℂ V : ℂ)) := by
  classical
  let d : ℂ := Module.finrank ℂ V
  let χ := (b4_formRepresentation hG).character
  have hχ : ∑ g : G, χ g⁻¹ = (Nat.card G : ℂ) *
      Module.finrank ℂ (Representation.invariants (b4_formRepresentation hG)) := by
    calc
      _ = ∑ g : G, χ g := by simpa using Equiv.sum_comp (Equiv.inv G) χ
      _ = _ := g32y_form_character_sum hE hG
  have hρsum : ∑ g : G, ρ.character g = 0 := by
    have hav := Representation.card_inv_mul_sum_char_eq_finrank ρ
    rw [hρ, finrank_bot, Nat.cast_zero] at hav
    exact (mul_eq_zero.mp hav).resolve_left
      (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
  have heq (g : G) : χ g⁻¹ * (ρ.character g - d) =
      (ρ.character g - d) + (∑ᶠ x : C, b4_fixedKernel hE g x) *
        (ρ.character g - d) := by
    by_cases hg : g = 1
    · subst g
      simp [d, Representation.char_one]
    · have ht := b4_formRepresentation_character_of_ne_one hE hG g⁻¹
        (inv_ne_one.mpr hg)
      simp only [inv_inv] at ht
      have hkernel : (∑ᶠ x : C, b4_fixedKernel hE g x) =
          ∑ᶠ x : C, if (b4_actionHomeomorph hG g) x = x then
            b4c_rotation hE (b4_actionHomeomorph hG g) x /
              (1 - b4c_rotation hE (b4_actionHomeomorph hG g) x) else 0 := by
        apply finsum_congr
        intro x
        simp only [b4_fixedKernel, if_neg hg]
        rfl
      rw [hkernel, show χ g⁻¹ = _ from ht]
      ring
  have hsum := congrArg (fun f : G → ℂ ↦ ∑ g : G, f g) (funext heq)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub,
    ← Finset.sum_mul, hχ, hρsum, zero_mul, zero_sub, sub_zero,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [b4_homGForm_character_average hE hG ρ]
  have hchange : (∑ g : G, χ g * ρ.character g⁻¹) =
      ∑ g : G, χ g⁻¹ * ρ.character g := by
    simpa only [Equiv.inv_apply, inv_inv] using
      (Equiv.sum_comp (Equiv.inv G) (fun g ↦ χ g * ρ.character g⁻¹)).symm
  change (Nat.card G : ℂ)⁻¹ * (∑ g : G, χ g * ρ.character g⁻¹) = _
  rw [hchange]
  rw [Nat.card_eq_fintype_card] at hsum ⊢
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  dsimp only [d] at hsum ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  field_simp [hn]
  linear_combination hsum

theorem g32y_chevalleyWeil_holo
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    {G : Type} [Group G] [Fintype G] [MulAction G C]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [FaithfulSMul G C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (h : C → G) (hh : ∀ x, b4_IsRotGen E x (h x))
    (ρ : Representation ℂ G V) (hρ : Representation.invariants ρ = ⊥) :
    (Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_formAct E (C := C) g)
      (b3_HolForm E C)) : ℝ) =
      (Module.finrank ℂ V : ℝ) *
        ((Module.finrank ℂ (Representation.invariants (b4_formRepresentation hG)) : ℝ) - 1) +
        ∑ᶠ x : C, (Nat.card (MulAction.stabilizer G x) : ℝ) / Fintype.card G * b4_age (ρ (h x)) := by
  classical
  have hmult := g32y_holo_multiplicity_fixedKernel hE hG ρ hρ
  have hfin (g : G) : Function.HasFiniteSupport (fun x : C ↦
      b4_fixedKernel hE g x * (ρ.character g - (Module.finrank ℂ V : ℂ))) := by
    apply (b4_fixedKernel_finiteSupport hE hG g).subset
    intro x hx
    exact fun hz ↦ hx (by dsimp only; rw [hz, zero_mul])
  have hswap : (∑ g : G, (∑ᶠ x : C, b4_fixedKernel hE g x) *
      (ρ.character g - (Module.finrank ℂ V : ℂ))) =
      ∑ᶠ x : C, (Nat.card (MulAction.stabilizer G x) : ℂ) * (b4_age (ρ (h x)) : ℂ) := by
    simp_rw [finsum_mul]
    rw [← finsum_sum_comm Finset.univ _ (fun g _ ↦ hfin g)]
    apply finsum_congr
    intro x
    exact b4_fixedKernel_character_sum hE hG x (h x) (hh x) ρ
  rw [hswap, mul_finsum] at hmult
  have hcast := Complex.ofRealHom.toAddMonoidHom.map_finsum_of_injective
    Complex.ofReal_injective (fun x : C ↦
      (Nat.card (MulAction.stabilizer G x) : ℝ) / Fintype.card G * b4_age (ρ (h x)))
  change ((∑ᶠ x : C, (Nat.card (MulAction.stabilizer G x) : ℝ) /
    Fintype.card G * b4_age (ρ (h x)) : ℝ) : ℂ) = _ at hcast
  have hsum : (∑ᶠ x : C, (Nat.card G : ℂ)⁻¹ *
      ((Nat.card (MulAction.stabilizer G x) : ℂ) * (b4_age (ρ (h x)) : ℂ))) =
      ((∑ᶠ x : C, (Nat.card (MulAction.stabilizer G x) : ℝ) /
        Fintype.card G * b4_age (ρ (h x)) : ℝ) : ℂ) := by
    rw [hcast]
    apply finsum_congr
    intro x
    change _ = (((Nat.card (MulAction.stabilizer G x) : ℝ) /
      Fintype.card G * b4_age (ρ (h x)) : ℝ) : ℂ)
    push_cast
    rw [Nat.card_eq_fintype_card]
    ring
  rw [hsum] at hmult
  exact_mod_cast hmult

end HodgeLean.Foundations.Program
