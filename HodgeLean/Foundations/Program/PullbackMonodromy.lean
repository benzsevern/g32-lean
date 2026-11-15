import HodgeLean.Foundations.Program.PullbackMonodromyProofs

/-! # Pullback monodromy statements

Branch count, normalization and the small-index subgroup statement for the printed
rational pullback, and implication from finite signed words to Hurwitz-orbit certificates.
The surjective pullback representation is set aside to a later stage. The selected-component
comparison requires further geometric word data. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- The two reduced sextic fibres and zero give exactly thirteen branch points.
Source: G32 v0.16, §5.2, reduced fibres over 5 and −7 and Lemma surj. -/
theorem b65s_branch_count  :
    Nat.card ↥b65s_branch = 13 :=
  b65s_branch_count_aux 

example  :
    Nat.card ↥b65s_branch = 13 :=
  b65s_branch_count 

/-- An index-at-most-six subgroup containing a reflection of the first class is the whole group.
Source: G32 v0.16, §5.2, proof of Lemma surj; ATLAS, PSp₄(3), minimal proper subgroup index 27. -/
theorem b65s_small_index (H : Subgroup b4b_Group) (hindex : H.index ≤ 6)
    (href : ∃ g : b4b_Group, g * b4b_generators 0 * g⁻¹ ∈ H) :
    H = ⊤ :=
  b65s_small_index_aux H hindex href

example (H : Subgroup b4b_Group) (hindex : H.index ≤ 6)
    (href : ∃ g : b4b_Group, g * b4b_generators 0 * g⁻¹ ∈ H) :
    H = ⊤ :=
  b65s_small_index H hindex href

/-- Column transport converts opposite-valued covering monodromy by inverse-unop.
Source: MarkedRootCoverDefs, convention paragraph; MulOpposite.unop_mul; G32 v0.16, §5.3, action convention. -/
theorem b65s_opposite_conversion (Γ : Type*) [Group Γ] (κ : Γ →* b4b_Groupᵐᵒᵖ) :
    (Function.Surjective ((b65s_unopInv b4b_Group).comp κ) ↔ Function.Surjective κ) ∧
      ∀ c : Γ, (b65s_column κ c).val =
        b65r_operator (b4b_toMatrix (MulOpposite.unop (κ (c⁻¹)))) :=
  b65s_opposite_conversion_aux Γ κ

example (Γ : Type*) [Group Γ] (κ : Γ →* b4b_Groupᵐᵒᵖ) :
    (Function.Surjective ((b65s_unopInv b4b_Group).comp κ) ↔ Function.Surjective κ) ∧
      ∀ c : Γ, (b65s_column κ c).val =
        b65r_operator (b4b_toMatrix (MulOpposite.unop (κ (c⁻¹)))) :=
  b65s_opposite_conversion Γ κ

/-- The reversed inverse marked tuple is generating, has product one and retains the class multiset.
Source: b63d_root_nielsen; b63_root_positive_class; b63_root_negative_class; b63d_root_classes; mr_root_op_reverse_prod. -/
theorem b65s_column_root  :
    b4_Nielsen b65s_columnRoot ∧ b4_classes b65s_columnRoot = b4_classes b4b_root :=
  b65s_column_root_aux 

example  :
    b4_Nielsen b65s_columnRoot ∧ b4_classes b65s_columnRoot = b4_classes b4b_root :=
  b65s_column_root 

/-- Signed finite words evaluate inside the same Hurwitz orbit with the Nielsen and local-class conditions preserved.
Source: Völklein, Groups as Galois Groups, Chapters 9–10; b4_nielsen_of_sameComponent and b4_classes_of_sameComponent. -/
theorem b65s_word_orbit (w : List b65s_Move) (t : Fin 13 → b4b_Group) :
    b4_SameComponent t (b65s_word w t) ∧
      b4_classes (b65s_word w t) = b4_classes t ∧
      (b4_Nielsen (b65s_word w t) ↔ b4_Nielsen t) :=
  b65s_word_orbit_aux w t

example (w : List b65s_Move) (t : Fin 13 → b4b_Group) :
    b4_SameComponent t (b65s_word w t) ∧
      b4_classes (b65s_word w t) = b4_classes t ∧
      (b4_Nielsen (b65s_word w t) ↔ b4_Nielsen t) :=
  b65s_word_orbit w t

/-- Ordering the two sextic fibres permits a normalized ten-coordinate configuration with the involution at infinity.
Source: G32 v0.16, §5.2, the two reduced disjoint fibres; §3.1, normalization modulo PGL₂; b6_chart_coordinates. -/
theorem b65s_normalization  :
    ∃ p : Fin 13 → ℂ,
      Function.Injective p ∧
      Set.range (fun i ↦ (p i : OnePoint ℂ)) = b65s_branch ∧
      p 12 = 0 ∧ b65r_P 5 (p 10) = 0 ∧ b65r_P (-7) (p 11) = 0 ∧
      (fun i : Fin 10 ↦ b65s_normalize (p 10) (p 11) (p (Fin.castLE (by omega) i))) ∈ b6_chart :=
  b65s_normalization_aux 

example  :
    ∃ p : Fin 13 → ℂ,
      Function.Injective p ∧
      Set.range (fun i ↦ (p i : OnePoint ℂ)) = b65s_branch ∧
      p 12 = 0 ∧ b65r_P 5 (p 10) = 0 ∧ b65r_P (-7) (p 11) = 0 ∧
      (fun i : Fin 10 ↦ b65s_normalize (p 10) (p 11) (p (Fin.castLE (by omega) i))) ∈ b6_chart :=
  b65s_normalization 

/-- Field-type check from a continuous normalized parameter curve to the two path fields.
Source: HodgeLean/Papers/G32DominanceDefs.lean, curve_cont and curve_zero;
b6t_polydisc_neighbourhood. -/
example (c : C(ℂ, b6_chart)) :
    ContinuousAt (fun θ ↦ (c θ).val) 0 ∧
      (c 0).val ∈ b6t_polydisc (c 0).val := by
  exact ⟨(continuous_subtype_val.comp c.continuous).continuousAt,
    (b6t_polydisc_neighbourhood (c 0).val (c 0).property).1⟩

end HodgeLean.Foundations.Program
