import HodgeLean.Foundations.Program.RigidStartingSystemExponentialClasses

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

def b65r_printedUnitHom : b4b_Group →* (Matrix (Fin 4) (Fin 4) ℂ)ˣ where
  toFun g := {
    val := b4b_toMatrix g
    inv := b4b_toMatrix g⁻¹
    val_inv := by rw [← map_mul,mul_inv_cancel,map_one]
    inv_val := by rw [← map_mul,inv_mul_cancel,map_one] }
  map_one' := by apply Units.ext; exact map_one b4b_toMatrix
  map_mul' g h := by apply Units.ext; exact map_mul b4b_toMatrix g h

def b65r_operatorUnitsEquiv : (Matrix (Fin 4) (Fin 4) ℂ)ˣ ≃*
    ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ :=
  Units.mapEquiv (b65r_operatorEquiv 4).toMulEquiv

def b65r_printedOperatorHom : b4b_Group →*
    ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ :=
  b65r_operatorUnitsEquiv.toMonoidHom.comp b65r_printedUnitHom

theorem b65r_printedOperatorHom_val (g : b4b_Group) :
    (b65r_printedOperatorHom g).val = b65r_operator (b4b_toMatrix g) := rfl

theorem b65r_printed_generators_prod : (List.ofFn b4b_generators).prod = 1 := by
  apply Subtype.val_injective
  change ((List.ofFn (fun i ↦ b4b_toMatrix (b4b_generators i))).prod) = 1
  simp only [List.ofFn_succ,Fin.isValue,Fin.coe_ofNat_eq_mod,Fin.natCast_eq_last,
    List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]
  change g32R1 g32h_omega*(g32R2 g32h_omega*(g32X g32h_omega*g32Y g32h_omega)) = 1
  simpa only [mul_assoc] using papers_g32_tuple_prod g32h_omega g32h_omega_sq_add

theorem b65r_printed_generators_surjective {Γ : Type*} [Group Γ]
    (ρ : Γ →* b4b_Group) (γ : Fin 4 → Γ) (hρ : ∀ i, ρ (γ i) = b4b_generators i) :
    Function.Surjective ρ := by
  have hh : ∀ m, m ∈ g32h_G → ∃ x : Γ, b4b_toMatrix (ρ x) = m := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hm
      rcases hm with h | h | h | h
      · exact ⟨γ 0,by rw [hρ]; exact h.symm⟩
      · exact ⟨γ 1,by rw [hρ]; exact h.symm⟩
      · exact ⟨γ 2,by rw [hρ]; exact h.symm⟩
      · exact ⟨γ 3,by rw [hρ]; exact h.symm⟩
    | one => exact ⟨1,by simp⟩
    | mul m n hm hn hm' hn' =>
      obtain ⟨x,hx⟩ := hm'
      obtain ⟨y,hy⟩ := hn'
      exact ⟨x*y,by rw [map_mul,map_mul,hx,hy]⟩
  intro g
  obtain ⟨x,hx⟩ := hh g.val g.property
  exact ⟨x,Subtype.val_injective hx⟩

end HodgeLean.Foundations.Program
