import HodgeLean.Foundations.Program.G32PropFourSixDualMultiplicity
import HodgeLean.Foundations.Program.G32PropFourSixDeterminantRep
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0187

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_twistAction {G : Type} [Group G] (χ : G →* ℂˣ) (V : FDRep ℂ G) :
    Representation ℂ G V where
  toFun g := (χ g : ℂ) • V.ρ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm (χ g : ℂ) (χ h : ℂ)]

def g32p_twist {G : Type} [Group G] (χ : G →* ℂˣ) (V : FDRep ℂ G) : FDRep ℂ G :=
  FDRep.of (g32p_twistAction χ V)

theorem g32p_twist_character {G : Type} [Group G] (χ : G →* ℂˣ)
    (V : FDRep ℂ G) (g : G) :
    (g32p_twist χ V).character g = (χ g : ℂ) * V.character g := by
  change LinearMap.trace ℂ V ((χ g : ℂ) • V.ρ g) = _
  simp only [map_smul, smul_eq_mul]
  rfl

theorem g32p_twist_simple {G : Type} [Group G] [Fintype G]
    (χ : G →* ℂˣ) (V : FDRep ℂ G) (hV : Simple V) : Simple (g32p_twist χ V) := by
  apply (FDRep.simple_iff_char_is_norm_one _).mpr
  rw [← (FDRep.simple_iff_char_is_norm_one V).mp hV]
  apply Finset.sum_congr rfl
  intro g hg
  rw [g32p_twist_character, g32p_twist_character]
  calc
    _ = ((χ g : ℂ) * (χ g⁻¹ : ℂ)) * (V.character g * V.character g⁻¹) := by ring
    _ = _ := by simp

def g32p_naturalTwist (i : Fin 3) : FDRep ℂ g32p_G :=
  g32p_twist (g32p_determinant ^ i.val) g32p_rho

def g32p_naturalTwistDual (i : Fin 3) : FDRep ℂ g32p_G :=
  FDRep.of (Representation.dual (g32p_naturalTwist i).ρ)

theorem g32p_naturalTwist_simple (i : Fin 3) : Simple (g32p_naturalTwist i) :=
  g32p_twist_simple _ _ g32p_rho_simple

theorem g32p_naturalTwistDual_simple (i : Fin 3) : Simple (g32p_naturalTwistDual i) :=
  g32p_dual_simple _ (g32p_naturalTwist_simple i)

theorem g32p_naturalTwist_character (i : Fin 3) (g : g32p_G) :
    (g32p_naturalTwist i).character g =
      (g32p_determinant g : ℂ) ^ i.val * g32p_rho.character g := by
  rw [g32p_naturalTwist, g32p_twist_character]
  simp only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]

theorem g32p_naturalTwistDual_conjugate (i : Fin 3) (g : g32p_G) :
    (g32p_naturalTwistDual i).character g = star ((g32p_naturalTwist i).character g) := by
  change (FDRep.of (Representation.dual (g32p_naturalTwist i).ρ)).character g = _
  rw [FDRep.char_dual, g32p_naturalTwist_character, g32p_naturalTwist_character]
  have hr : g32p_rho.character g⁻¹ = star (g32p_rho.character g) :=
    (g32p_rhoDual_character g).symm.trans (g32p_rhoDual_conjugate g)
  have hd : (g32p_determinant g⁻¹ : ℂ) = star (g32p_determinant g : ℂ) := by
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact Complex.inv_eq_conj
      (((Units.coeHom ℂ).comp g32p_determinant).isOfFinOrder
        (isOfFinOrder_of_finite g)).norm_eq_one
  rw [hr, hd, star_mul, star_pow]
  ring

def g32p_naturalTwistReflection (i : Fin 3) : HurwitzPrymRex_Zw :=
  ![⟨3, 1⟩, ⟨-1, 2⟩, ⟨-2, -3⟩] i

theorem g32p_naturalTwist_character_reflection (i : Fin 3) :
    (g32p_naturalTwist i).character (g32p_classDatum 0) =
      HurwitzPrymRex_ev g32h_omega (g32p_naturalTwistReflection i) := by
  rw [g32p_naturalTwist_character, g32p_determinant_val, g32p_class_determinant,
    g32p_rho_character_reflection]
  norm_num
  fin_cases i <;>
    norm_num [g32p_naturalTwistReflection, HurwitzPrymRex_ev] <;>
    papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add

theorem g32p_naturalTwist_not_selfDual (i : Fin 3) :
    ¬ g32p_SelfDual (g32p_naturalTwist i) := by
  intro h
  have hi := congrArg Complex.im (h (g32p_classDatum 0))
  rw [g32p_naturalTwist_character_reflection] at hi
  have hn : g32h_omega.im ≠ 0 :=
    omega_im_ne_zero g32h_omega g32h_omega_sq_add
  fin_cases i <;>
    norm_num [g32p_naturalTwistReflection, HurwitzPrymRex_ev, Complex.conj_im] at hi <;>
    apply hn <;> linarith

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory HodgeLean.Papers
open scoped MonoidalCategory

set_option maxHeartbeats 400000

def g32p_recordedSupplierCharacterAt (i : Fin 51) (conjugate : Bool) :
    (g32p_recordedSuppliers i).H →* ℂˣ :=
  if conjugate then (g32p_recordedSupplierCharacters i)⁻¹
  else g32p_recordedSupplierCharacters i

def g32p_recordedCoinduced (i : Fin 51) (conjugate : Bool) : FDRep ℂ g32p_G :=
  g32p_coinduced (g32p_recordedSuppliers i).H (g32p_recordedSupplierCharacterAt i conjugate)

theorem g32p_recordedCoinduced_mult (i : Fin 51) (conjugate : Bool)
    (V : FDRep ℂ g32p_G) :
    Module.finrank ℂ (V ⟶ g32p_recordedCoinduced i conjugate) =
      papersMult (g32p_recordedSuppliers i).H V
        (g32p_recordedSupplierCharacterAt i conjugate) :=
  g32p_coinduced_mult _ _ _

def g32p_inductionGenerator (i : Fin 51) (conjugate : Bool) (variant : Fin 4) :
    FDRep ℂ g32p_G :=
  let V := g32p_recordedCoinduced i conjugate
  ![V, V ⊗ g32p_rho, g32p_twist g32p_determinant V,
    g32p_twist (g32p_determinant ^ 2) V] variant

theorem g32p_inductionGenerator_base (i : Fin 51) (conjugate : Bool) :
    g32p_inductionGenerator i conjugate 0 = g32p_recordedCoinduced i conjugate := rfl

theorem g32p_inductionGenerator_tensor_character (i : Fin 51) (conjugate : Bool)
    (g : g32p_G) :
    (g32p_inductionGenerator i conjugate 1).character g =
      (g32p_recordedCoinduced i conjugate).character g * g32p_rho.character g :=
  congrFun (FDRep.char_tensor _ _) g

theorem g32p_inductionGenerator_twist_character (i : Fin 51) (conjugate : Bool)
    (g : g32p_G) :
    (g32p_inductionGenerator i conjugate 2).character g =
      (g32p_determinant g : ℂ) * (g32p_recordedCoinduced i conjugate).character g :=
  g32p_twist_character _ _ _

theorem g32p_inductionGenerator_twist_sq_character (i : Fin 51) (conjugate : Bool)
    (g : g32p_G) :
    (g32p_inductionGenerator i conjugate 3).character g =
      (g32p_determinant g : ℂ) ^ 2 * (g32p_recordedCoinduced i conjugate).character g := by
  change (g32p_twist (g32p_determinant ^ 2) _).character g = _
  rw [g32p_twist_character]
  rfl

def g32p_recordedInductionGenerators (j : Fin 408) : FDRep ℂ g32p_G :=
  let k := if j.val < 102 then j.val else
    if j.val < 204 then j.val - 102 else (j.val - 204) / 2
  let i : Fin 51 := ⟨k % 51, Nat.mod_lt _ (by decide)⟩
  let variant : Fin 4 := if j.val < 102 then 0 else
    if j.val < 204 then 1 else ⟨(j.val - 204) % 2 + 2, by omega⟩
  g32p_inductionGenerator i (decide (51 ≤ k)) variant

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory
open scoped Classical

set_option maxHeartbeats 400000

theorem g32p_coinduced_character_direct {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) (g : G) :
    (g32p_coinduced H χ).character g =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G,
        if hx : x * g * x⁻¹ ∈ H then (χ ⟨x * g * x⁻¹, hx⟩ : ℂ) else 0 := by
  rw [g32p_coinduced_character]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have he : x * g⁻¹ * x⁻¹ = (x * g * x⁻¹)⁻¹ := by group
  by_cases hx : x * g * x⁻¹ ∈ H
  · have hi : x * g⁻¹ * x⁻¹ ∈ H := by
      rw [he]
      exact H.inv_mem hx
    rw [dite_eq_left hx, dite_eq_left hi]
    have hh : (⟨x * g⁻¹ * x⁻¹, hi⟩ : H) = (⟨x * g * x⁻¹, hx⟩ : H)⁻¹ :=
      Subtype.ext he
    rw [hh, map_inv, Units.val_inv_eq_inv_val, inv_inv]
  · have hi : x * g⁻¹ * x⁻¹ ∉ H := by
      rw [he, H.inv_mem_iff]
      exact hx
    rw [dite_eq_right hx, dite_eq_right hi]

theorem g32p_recordedCoinduced_character (i : Fin 51) (conjugate : Bool)
    (g : g32p_G) :
    (g32p_recordedCoinduced i conjugate).character g =
      (Nat.card (g32p_recordedSuppliers i).H : ℂ)⁻¹ * ∑ x : g32p_G,
        if hx : x * g * x⁻¹ ∈ (g32p_recordedSuppliers i).H then
          (g32p_recordedSupplierCharacterAt i conjugate ⟨x * g * x⁻¹, hx⟩ : ℂ)
        else 0 :=
  g32p_coinduced_character_direct _ _ _

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory
open scoped Classical

set_option maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false in
theorem g32p_inductionGenerator_character (i : Fin 51) (conjugate : Bool)
    (variant : Fin 4) (g : g32p_G) :
    (g32p_inductionGenerator i conjugate variant).character g =
      ![1, g32p_rho.character g, (g32p_determinant g : ℂ),
        (g32p_determinant g : ℂ) ^ 2] variant *
      ((Nat.card (g32p_recordedSuppliers i).H : ℂ)⁻¹ * ∑ x : g32p_G,
        if hx : x * g * x⁻¹ ∈ (g32p_recordedSuppliers i).H then
          (g32p_recordedSupplierCharacterAt i conjugate ⟨x * g * x⁻¹, hx⟩ : ℂ)
        else 0) := by
  have hc := g32p_recordedCoinduced_character i conjugate g
  fin_cases variant <;>
    simp [g32p_inductionGenerator, FDRep.char_tensor, g32p_twist_character, hc] <;> ring

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory
open scoped Classical
set_option maxHeartbeats 400000

theorem g32p_coinduced_top_character {G : Type} [Group G] [Fintype G]
    (χ : G →* ℂˣ) (g : G) :
    (g32p_coinduced (⊤ : Subgroup G) (χ.comp (⊤ : Subgroup G).subtype)).character g =
      (χ g : ℂ) := by
  rw [g32p_coinduced_character_direct]
  have hχ (x : G) : χ (x * g * x⁻¹) = χ g := by
    simp only [map_mul, map_inv]
    rw [mul_comm (χ x) (χ g), mul_assoc, mul_inv_cancel, mul_one]
  simp only [Subgroup.mem_top, dite_true, MonoidHom.comp_apply, Subgroup.coe_subtype,
    hχ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card]
  have hc : Nat.card (⊤ : Subgroup G) = Nat.card G :=
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv
  simp only [Subgroup.mem_top] at hc
  have hn : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  rw [hc, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem g32p_determinantSupplier_coinduced_character (conjugate : Bool) (g : g32p_G) :
    (g32p_recordedCoinduced 0 conjugate).character g =
      if conjugate then (g32p_determinant g : ℂ)⁻¹ else (g32p_determinant g : ℂ) := by
  cases conjugate
  · simp only [Bool.false_eq_true, ite_false]
    change (g32p_coinduced ⊤ (g32p_complexCharacter g32p_determinantSupplier)).character g = _
    rw [g32p_determinantSupplier_complexCharacter, g32p_coinduced_top_character]
  · simp only [ite_true]
    change (g32p_coinduced ⊤ (g32p_complexCharacter g32p_determinantSupplier)⁻¹).character g = _
    rw [g32p_determinantSupplier_complexCharacter]
    change (g32p_coinduced ⊤ ((g32p_determinant⁻¹).comp
      (⊤ : Subgroup g32p_G).subtype)).character g = _
    simpa only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val] using
      (g32p_coinduced_top_character (g32p_determinant⁻¹) g)

theorem g32p_determinantSupplier_generator_character
    (conjugate : Bool) (variant : Fin 4) (g : g32p_G) :
    (g32p_inductionGenerator 0 conjugate variant).character g =
      ![1, g32p_rho.character g, (g32p_determinant g : ℂ),
        (g32p_determinant g : ℂ) ^ 2] variant *
      (if conjugate then (g32p_determinant g : ℂ)⁻¹ else (g32p_determinant g : ℂ)) := by
  fin_cases variant <;>
    simp [g32p_inductionGenerator, FDRep.char_tensor, g32p_twist_character,
      g32p_determinantSupplier_coinduced_character] <;> ring

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_integralPower (M : HurwitzPrymRex_Mat) : ℕ → HurwitzPrymRex_Mat
  | 0 => HurwitzPrymRex_mone
  | n + 1 => HurwitzPrymRex_mmul (g32p_integralPower M n) M

def g32p_integralTrace (M : HurwitzPrymRex_Mat) : HurwitzPrymRex_Zw :=
  ⟨∑ i : Fin 4, (M i i).re, ∑ i : Fin 4, (M i i).om⟩

theorem g32p_integralPower_map (M : HurwitzPrymRex_Mat) (n : ℕ) :
    HurwitzPrymRex_evM g32h_omega (g32p_integralPower M n) =
      HurwitzPrymRex_evM g32h_omega M ^ n := by
  induction n with
  | zero => exact HurwitzPrymRex_evM_mone
  | succ n ih => rw [g32p_integralPower, HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
      ih, pow_succ]

theorem g32p_literalRepresentative_powerTrace (c : Fin 102) (n : ℕ) :
    g32p_rho.character (g32p_literalRepresentative c ^ n) =
      HurwitzPrymRex_ev g32h_omega
        (g32p_integralTrace (g32p_integralPower (g32p_literalRepresentativeMatrix c) n)) := by
  rw [g32p_rho_character, map_pow]
  change Matrix.trace (b4b_toMatrix
    (g32p_archiveWord (g32p_literalRepresentativeWord c)) ^ n) = _
  rw [g32p_archiveIntegralWord_map, g32p_literalRepresentative_integral,
    ← map_pow, ← g32p_integralPower_map, g32p_archive_trace, g32p_integral_trace]
  rfl

theorem g32p_powerTrace_eq_of_isConj {a b : g32p_G} (h : IsConj a b) (n : ℕ) :
    g32p_rho.character (a ^ n) = g32p_rho.character (b ^ n) := by
  obtain ⟨u, hu⟩ := isConj_iff.mp (IsConj.pow n h)
  rw [← hu, FDRep.char_conj]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_000 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨4, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩]

theorem g32p_literalPowerTrace_check_000 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_000 (k.val + 1)) =
      g32p_literalPowerTrace_000 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_001 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨3, 1⟩, ⟨2, -1⟩, ⟨4, 0⟩, ⟨3, 1⟩]

theorem g32p_literalPowerTrace_check_001 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_001 (k.val + 1)) =
      g32p_literalPowerTrace_001 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_002 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨2, -1⟩, ⟨3, 1⟩, ⟨4, 0⟩, ⟨2, -1⟩]

theorem g32p_literalPowerTrace_check_002 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_002 (k.val + 1)) =
      g32p_literalPowerTrace_002 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_003 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨2, 1⟩, ⟨3, 1⟩, ⟨0, 0⟩, ⟨2, -1⟩]

theorem g32p_literalPowerTrace_check_003 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_003 (k.val + 1)) =
      g32p_literalPowerTrace_003 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_004 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨2, 2⟩, ⟨0, -2⟩, ⟨4, 0⟩, ⟨2, 2⟩]

theorem g32p_literalPowerTrace_check_004 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_004 (k.val + 1)) =
      g32p_literalPowerTrace_004 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_005 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩]

theorem g32p_literalPowerTrace_check_005 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_005 (k.val + 1)) =
      g32p_literalPowerTrace_005 k := by
  fin_cases k <;> decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_006 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 0⟩, ⟨1, 0⟩, ⟨4, 0⟩, ⟨1, 0⟩]

theorem g32p_literalPowerTrace_check_006 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_006 (k.val + 1)) =
      g32p_literalPowerTrace_006 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_007 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 3⟩]

theorem g32p_literalPowerTrace_check_007 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_007 (k.val + 1)) =
      g32p_literalPowerTrace_007 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_008 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, -1⟩, ⟨2, -1⟩, ⟨0, 0⟩, ⟨3, 1⟩]

theorem g32p_literalPowerTrace_check_008 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_008 (k.val + 1)) =
      g32p_literalPowerTrace_008 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_009 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 3⟩, ⟨1, 0⟩]

theorem g32p_literalPowerTrace_check_009 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_009 (k.val + 1)) =
      g32p_literalPowerTrace_009 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_010 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨2, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩]

theorem g32p_literalPowerTrace_check_010 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_010 (k.val + 1)) =
      g32p_literalPowerTrace_010 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_011 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, -2⟩, ⟨2, 2⟩, ⟨4, 0⟩, ⟨0, -2⟩]

theorem g32p_literalPowerTrace_check_011 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_011 (k.val + 1)) =
      g32p_literalPowerTrace_011 k := by
  fin_cases k <;> decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_012 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 3⟩, ⟨-1, -1⟩]

theorem g32p_literalPowerTrace_check_012 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_012 (k.val + 1)) =
      g32p_literalPowerTrace_012 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_013 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨4, 4⟩, ⟨0, 0⟩, ⟨0, 4⟩]

theorem g32p_literalPowerTrace_check_013 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_013 (k.val + 1)) =
      g32p_literalPowerTrace_013 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_014 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-2, -3⟩, ⟨1, 0⟩]

theorem g32p_literalPowerTrace_check_014 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_014 (k.val + 1)) =
      g32p_literalPowerTrace_014 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_015 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]

theorem g32p_literalPowerTrace_check_015 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_015 (k.val + 1)) =
      g32p_literalPowerTrace_015 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_016 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩]

theorem g32p_literalPowerTrace_check_016 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_016 (k.val + 1)) =
      g32p_literalPowerTrace_016 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_017 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 0⟩, ⟨1, 2⟩, ⟨-2, 0⟩, ⟨-1, 2⟩]

theorem g32p_literalPowerTrace_check_017 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_017 (k.val + 1)) =
      g32p_literalPowerTrace_017 k := by
  fin_cases k <;> decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_018 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩]

theorem g32p_literalPowerTrace_check_018 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_018 (k.val + 1)) =
      g32p_literalPowerTrace_018 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_019 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨2, 1⟩, ⟨1, 3⟩, ⟨0, 0⟩, ⟨-2, -3⟩]

theorem g32p_literalPowerTrace_check_019 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_019 (k.val + 1)) =
      g32p_literalPowerTrace_019 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_020 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, -1⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨-2, -3⟩]

theorem g32p_literalPowerTrace_check_020 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_020 (k.val + 1)) =
      g32p_literalPowerTrace_020 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_021 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩]

theorem g32p_literalPowerTrace_check_021 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_021 (k.val + 1)) =
      g32p_literalPowerTrace_021 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_022 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]

theorem g32p_literalPowerTrace_check_022 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_022 (k.val + 1)) =
      g32p_literalPowerTrace_022 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_023 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, -1⟩, ⟨-2, -3⟩, ⟨0, 0⟩, ⟨1, 3⟩]

theorem g32p_literalPowerTrace_check_023 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_023 (k.val + 1)) =
      g32p_literalPowerTrace_023 k := by
  fin_cases k <;> decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_024 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨2, 0⟩, ⟨-2, 0⟩, ⟨-4, 0⟩, ⟨-2, 0⟩]

theorem g32p_literalPowerTrace_check_024 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_024 (k.val + 1)) =
      g32p_literalPowerTrace_024 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_025 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, -2⟩]

theorem g32p_literalPowerTrace_check_025 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_025 (k.val + 1)) =
      g32p_literalPowerTrace_025 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_026 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, -1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]

theorem g32p_literalPowerTrace_check_026 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_026 (k.val + 1)) =
      g32p_literalPowerTrace_026 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_027 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 0⟩, ⟨-1, -2⟩, ⟨-2, 0⟩, ⟨-3, -2⟩]

theorem g32p_literalPowerTrace_check_027 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_027 (k.val + 1)) =
      g32p_literalPowerTrace_027 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_028 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨3, 2⟩, ⟨-1, 2⟩, ⟨-4, 0⟩, ⟨-3, -2⟩]

theorem g32p_literalPowerTrace_check_028 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_028 (k.val + 1)) =
      g32p_literalPowerTrace_028 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_029 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨2, 2⟩]

theorem g32p_literalPowerTrace_check_029 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_029 (k.val + 1)) =
      g32p_literalPowerTrace_029 k := by
  fin_cases k <;> decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_030 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨2, 2⟩]

theorem g32p_literalPowerTrace_check_030 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_030 (k.val + 1)) =
      g32p_literalPowerTrace_030 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_031 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨2, 2⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-4, -4⟩]

theorem g32p_literalPowerTrace_check_031 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_031 (k.val + 1)) =
      g32p_literalPowerTrace_031 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_032 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-4, 0⟩, ⟨-1, -1⟩]

theorem g32p_literalPowerTrace_check_032 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_032 (k.val + 1)) =
      g32p_literalPowerTrace_032 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_033 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -3⟩, ⟨0, 1⟩]

theorem g32p_literalPowerTrace_check_033 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_033 (k.val + 1)) =
      g32p_literalPowerTrace_033 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_034 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨0, -4⟩, ⟨0, 0⟩, ⟨-4, -4⟩]

theorem g32p_literalPowerTrace_check_034 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_034 (k.val + 1)) =
      g32p_literalPowerTrace_034 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_035 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨4, 0⟩, ⟨-1, -1⟩]

theorem g32p_literalPowerTrace_check_035 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_035 (k.val + 1)) =
      g32p_literalPowerTrace_035 k := by
  fin_cases k <;> decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_036 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨1, 3⟩, ⟨0, 1⟩]

theorem g32p_literalPowerTrace_check_036 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_036 (k.val + 1)) =
      g32p_literalPowerTrace_036 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_037 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨4, 4⟩, ⟨0, 4⟩, ⟨-4, 0⟩, ⟨-4, -4⟩]

theorem g32p_literalPowerTrace_check_037 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_037 (k.val + 1)) =
      g32p_literalPowerTrace_037 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_038 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩]

theorem g32p_literalPowerTrace_check_038 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_038 (k.val + 1)) =
      g32p_literalPowerTrace_038 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_039 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, -3⟩, ⟨-1, -1⟩]

theorem g32p_literalPowerTrace_check_039 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_039 (k.val + 1)) =
      g32p_literalPowerTrace_039 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_040 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]

theorem g32p_literalPowerTrace_check_040 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_040 (k.val + 1)) =
      g32p_literalPowerTrace_040 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_041 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 1⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨-2, -3⟩]

theorem g32p_literalPowerTrace_check_041 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_041 (k.val + 1)) =
      g32p_literalPowerTrace_041 k := by
  fin_cases k <;> decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_042 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 3⟩, ⟨-1, -1⟩]

theorem g32p_literalPowerTrace_check_042 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_042 (k.val + 1)) =
      g32p_literalPowerTrace_042 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_043 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩]

theorem g32p_literalPowerTrace_check_043 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_043 (k.val + 1)) =
      g32p_literalPowerTrace_043 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_044 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨2, 3⟩, ⟨1, 3⟩, ⟨-4, 0⟩, ⟨-2, -3⟩]

theorem g32p_literalPowerTrace_check_044 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_044 (k.val + 1)) =
      g32p_literalPowerTrace_044 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_045 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨4, 0⟩, ⟨0, 1⟩]

theorem g32p_literalPowerTrace_check_045 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_045 (k.val + 1)) =
      g32p_literalPowerTrace_045 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_046 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩]

theorem g32p_literalPowerTrace_check_046 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_046 (k.val + 1)) =
      g32p_literalPowerTrace_046 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_047 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩]

theorem g32p_literalPowerTrace_check_047 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_047 (k.val + 1)) =
      g32p_literalPowerTrace_047 k := by
  fin_cases k <;> decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_048 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 1⟩, ⟨-2, -1⟩, ⟨2, 0⟩, ⟨3, 1⟩]

theorem g32p_literalPowerTrace_check_048 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_048 (k.val + 1)) =
      g32p_literalPowerTrace_048 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_049 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -4⟩]

theorem g32p_literalPowerTrace_check_049 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_049 (k.val + 1)) =
      g32p_literalPowerTrace_049 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_050 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, -2⟩]

theorem g32p_literalPowerTrace_check_050 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_050 (k.val + 1)) =
      g32p_literalPowerTrace_050 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_051 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 2⟩, ⟨-1, 2⟩, ⟨0, 0⟩, ⟨-3, -2⟩]

theorem g32p_literalPowerTrace_check_051 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_051 (k.val + 1)) =
      g32p_literalPowerTrace_051 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_052 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 2⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 4⟩]

theorem g32p_literalPowerTrace_check_052 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_052 (k.val + 1)) =
      g32p_literalPowerTrace_052 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_053 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -3⟩, ⟨1, 0⟩]

theorem g32p_literalPowerTrace_check_053 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_053 (k.val + 1)) =
      g32p_literalPowerTrace_053 k := by
  fin_cases k <;> decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_054 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨-2, -3⟩, ⟨-1, -1⟩]

theorem g32p_literalPowerTrace_check_054 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_054 (k.val + 1)) =
      g32p_literalPowerTrace_054 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_055 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨2, 0⟩, ⟨-3, -2⟩]

theorem g32p_literalPowerTrace_check_055 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_055 (k.val + 1)) =
      g32p_literalPowerTrace_055 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_056 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 2⟩, ⟨2, 2⟩, ⟨-4, 0⟩, ⟨0, -2⟩]

theorem g32p_literalPowerTrace_check_056 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_056 (k.val + 1)) =
      g32p_literalPowerTrace_056 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_057 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 4⟩]

theorem g32p_literalPowerTrace_check_057 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_057 (k.val + 1)) =
      g32p_literalPowerTrace_057 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_058 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, -1⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨2, -1⟩]

theorem g32p_literalPowerTrace_check_058 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_058 (k.val + 1)) =
      g32p_literalPowerTrace_058 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_059 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨2, 2⟩]

theorem g32p_literalPowerTrace_check_059 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_059 (k.val + 1)) =
      g32p_literalPowerTrace_059 k := by
  fin_cases k <;> decide +kernel


end HodgeLean.Foundations.Program

end
end
