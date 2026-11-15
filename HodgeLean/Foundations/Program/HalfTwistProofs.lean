import HodgeLean.Foundations.Program.HalfTwistWord

/-! # Proof obligations for the half-twist interfaces -/
noncomputable section
open Complex Set Topology
namespace HodgeLean.Foundations.Program

theorem b66h_track_continuous_aux (j : Fin 11) (ε : ℝ) :
    Continuous (fun q : ℝ × Fin 12 ↦ b66h_track j ε q.1 q.2) :=
  b66h_track_continuous_body j ε

theorem b66h_track_endpoints_aux (j : Fin 11) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    b66h_track j ε 0 = mr_marks ∧
      b66h_track j ε 1 = mr_marks ∘ Equiv.swap j.castSucc j.succ :=
  b66h_track_endpoints_body j ε hε

theorem b66h_track_injective_aux (j : Fin 11) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (t : unitInterval) :
    Function.Injective (b66h_track j ε t) :=
  b66h_track_injective_body j ε t

theorem b66h_half_twist_aux (i : Fin 12) (hi : i ≠ 0) :
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
  b66h_half_twist_body i hi

theorem b66h_word_realization_aux (w : List b65s_Move)
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
  b66h_word_body w hw

theorem b66h_certificate_realization_aux (ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group)
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
  b66h_certificate_body ρ hρ

end HodgeLean.Foundations.Program
