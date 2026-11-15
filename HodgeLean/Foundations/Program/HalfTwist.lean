import HodgeLean.Foundations.Program.HalfTwistProofs

/-! # Half-twists and certified transport (FROZEN SPEC)
Implication from elementary configuration tracks to Hurwitz actions on the based column loops,
and from the arithmetic certificate to its ambient realization up to conjugation.
Endpoint permutations are retained in the word interface. The ordered normalized path and
radial monodromy comparison require an endpoint-label revision recorded in the route note. No new cohomology comparison or
Hodge-theoretic consequence is claimed here. HC no distance; AV milestone no distance.
-/
noncomputable section
open Complex Set Topology
namespace HodgeLean.Foundations.Program

/-- The elementary tracks depend continuously on time and mark.
Source: Völklein, Groups as Galois Groups, Chapters 9–10; continuity of the complex exponential. -/
theorem b66h_track_continuous (j : Fin 11) (ε : ℝ) :
    Continuous (fun q : ℝ × Fin 12 ↦ b66h_track j ε q.1 q.2) :=
  b66h_track_continuous_aux j ε

example := @b66h_track_continuous

/-- A signed half-turn exchanges exactly the two selected marks.
Source: Völklein, Groups as Galois Groups, Chapters 9–10, elementary braid endpoints. -/
theorem b66h_track_endpoints (j : Fin 11) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    b66h_track j ε 0 = mr_marks ∧
      b66h_track j ε 1 = mr_marks ∘ Equiv.swap j.castSucc j.succ :=
  b66h_track_endpoints_aux j ε hε

example := @b66h_track_endpoints

/-- The elementary half-turn has no collisions.
Source: Völklein, Groups as Galois Groups, Chapters 9–10, configuration-space half-twists. -/
theorem b66h_track_injective (j : Fin 11) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (t : unitInterval) :
    Function.Injective (b66h_track j ε t) :=
  b66h_track_injective_aux j ε hε t

example := @b66h_track_injective

/-- An elementary ambient half-twist acts on the based column loops by the Hurwitz formula.
Source: Völklein, Groups as Galois Groups, Chapters 9–10; b4_braid; b65s_columnRoot convention. -/
theorem b66h_half_twist (i : Fin 12) (hi : i ≠ 0) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ t k, H t (mr_marks k : OnePoint ℂ) =
        (b66h_track ⟨11 - i.val, by omega⟩ ε t k : OnePoint ℂ)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ k, MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop k))) =
            b4_braid i.castSucc i.succ b66h_loop k :=
  b66h_half_twist_aux i hi

example := @b66h_half_twist

/-- Finite signed words are realized by ambient isotopies with their endpoint permutation retained.
Source: Völklein, Groups as Galois Groups, Chapters 9–10; b65s_word, list-order composition. -/
theorem b66h_word_realization (w : List b65s_Move)
    (hw : ∀ m ∈ w, ∃ i : Fin 12, i ≠ 0 ∧ (m = .positive i ∨ m = .negative i)) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∃ σ : Equiv.Perm (Fin 12), ∀ k,
        H 1 (mr_marks k : OnePoint ℂ) = (mr_marks (σ k) : OnePoint ℂ)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group, ∀ k,
            ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop k)))) =
              b65s_word w (fun i ↦ ρ (b66h_loop i)) k :=
  b66h_word_realization_aux w hw

example := @b66h_word_realization

/-- The certificate word realizes the literal final column tuple up to its specified conjugation.
Source: B65-BRAIDCERT REPORT §1.5; b65b_word; b65b_replay; Völklein, Chapters 9–10. -/
theorem b66h_certificate_realization (ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group)
    (hρ : ∀ i, ρ (b66h_loop i) = b65s_columnRoot i) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∃ σ : Equiv.Perm (Fin 12), ∀ k,
        H 1 (mr_marks k : OnePoint ℂ) = (mr_marks (σ k) : OnePoint ℂ)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ i, ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop i)))) =
            b4_conjTuple (b4b_generators 1)⁻¹ b65b_final i :=
  b66h_certificate_realization_aux ρ hρ

example := @b66h_certificate_realization

end HodgeLean.Foundations.Program
