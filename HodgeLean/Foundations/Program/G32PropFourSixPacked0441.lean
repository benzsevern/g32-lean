import HodgeLean.Foundations.Program.G32PropFourSixPacked0440
import HodgeLean.Foundations.Program.G32PropFourSixLiteralCharacterData
import HodgeLean.Foundations.Program.G32PropFourSixCharacterCheck

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory
open scoped Classical

set_option maxHeartbeats 400000

theorem g32p_realize_integral_reconstruction {G I K : Type} [Group G] [Fintype G]
    [Fintype I] [Fintype K] (V : K → FDRep ℂ G)
    (A : K → I → ℤ) (Q : I → K → ℤ) (f : I → G → ℂ)
    (hA : ∀ k g, (V k).character g = ∑ j, (A k j : ℂ) * f j g)
    (hQ : ∀ i j, ∑ k, Q i k * A k j = if i = j then 1 else 0)
    (hnorm : ∀ i, (Nat.card G : ℂ)⁻¹ * ∑ g, f i g * f i g⁻¹ = 1)
    (hpos : ∀ i, 0 < (f i 1).re) :
    ∃ W : I → FDRep ℂ G, (∀ i, Simple (W i)) ∧ ∀ i, (W i).character = f i := by
  have hf (i : I) (g : G) : f i g = ∑ k, (Q i k : ℂ) * (V k).character g := by
    simp_rw [hA, Finset.mul_sum]
    rw [Finset.sum_comm]
    have ht (j : I) : ∑ k, (Q i k : ℂ) * ((A k j : ℂ) * f j g) =
        (if i = j then (1 : ℂ) else 0) * f j g := by
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      congr 1
      exact_mod_cast hQ i j
    simp_rw [ht, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h (i : I) := g32p_realize_virtual_character V (Q i) (f i) (hf i)
    (hnorm i) (hpos i)
  choose W hS hW using h
  exact ⟨W, hS, hW⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory
open scoped Classical

set_option maxHeartbeats 400000

theorem g32p_sum_class_fibers {G I : Type} [Fintype G] [Fintype I]
    (classify : G → I) (sizes : I → ℕ) (values : I → ℂ) (f : G → ℂ)
    (hcard : ∀ i, Fintype.card {g : G // classify g = i} = sizes i)
    (hvalues : ∀ g, f g = values (classify g)) :
    ∑ g, f g = ∑ i, (sizes i : ℂ) * values i := by
  simp_rw [hvalues]
  rw [← Fintype.sum_fiberwise' classify values]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]

theorem g32p_virtual_norm_of_class_fibers {G I : Type} [Group G] [Fintype G] [Fintype I]
    (classify : G → I) (sizes : I → ℕ) (inverse : I → I) (values : I → ℂ)
    (f : G → ℂ)
    (hcard : ∀ i, Fintype.card {g : G // classify g = i} = sizes i)
    (hinv : ∀ g, classify g⁻¹ = inverse (classify g))
    (hvalues : ∀ g, f g = values (classify g))
    (hnorm : ∑ i, (sizes i : ℂ) * (values i * values (inverse i)) = Nat.card G) :
    (Nat.card G : ℂ)⁻¹ * ∑ g, f g * f g⁻¹ = 1 := by
  have hs := g32p_sum_class_fibers classify sizes
    (fun i => values i * values (inverse i)) (fun g => f g * f g⁻¹) hcard
    (fun g => by rw [hvalues g, hvalues g⁻¹, hinv g])
  rw [hs, hnorm, inv_mul_cancel₀ (NeZero.ne (Nat.card G : ℂ))]

theorem g32p_reconstruction_of_class_fibers {G I K J : Type} [Group G] [Fintype G]
    [Fintype I] [Fintype K] [Fintype J]
    (classify : G → J) (sizes : J → ℕ) (inverse : J → J)
    (values : I → J → ℂ) (V : K → FDRep ℂ G)
    (A : K → I → ℤ) (Q : I → K → ℤ)
    (hcard : ∀ j, Fintype.card {g : G // classify g = j} = sizes j)
    (hinv : ∀ g, classify g⁻¹ = inverse (classify g))
    (hA : ∀ k g, (V k).character g = ∑ i, (A k i : ℂ) * values i (classify g))
    (hQ : ∀ i j, ∑ k, Q i k * A k j = if i = j then 1 else 0)
    (hnorm : ∀ i, ∑ j, (sizes j : ℂ) * (values i j * values i (inverse j)) = Nat.card G)
    (hpos : ∀ i, 0 < (values i (classify 1)).re) :
    ∃ W : I → FDRep ℂ G, (∀ i, Simple (W i)) ∧
      ∀ i g, (W i).character g = values i (classify g) := by
  obtain ⟨W, hS, hW⟩ := g32p_realize_integral_reconstruction V A Q
    (fun i g => values i (classify g)) hA hQ
    (fun i => g32p_virtual_norm_of_class_fibers classify sizes inverse (values i) _
      hcard hinv (fun _ => rfl) (hnorm i)) hpos
  exact ⟨W, hS, fun i g => congrFun (hW i) g⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_000 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 0 (g32p_literalColumn c),
        g32p_literalCharacterValue 0 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_000 : ∀ c : Fin 102,
    g32p_literalCharacterValue 0 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 0 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_001 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 1 (g32p_literalColumn c),
        g32p_literalCharacterValue 1 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_001 : ∀ c : Fin 102,
    g32p_literalCharacterValue 1 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 1 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_002 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 2 (g32p_literalColumn c),
        g32p_literalCharacterValue 2 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_002 : ∀ c : Fin 102,
    g32p_literalCharacterValue 2 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 2 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_003 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 3 (g32p_literalColumn c),
        g32p_literalCharacterValue 3 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_003 : ∀ c : Fin 102,
    g32p_literalCharacterValue 3 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 3 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_004 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 4 (g32p_literalColumn c),
        g32p_literalCharacterValue 4 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_004 : ∀ c : Fin 102,
    g32p_literalCharacterValue 4 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 4 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_005 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 5 (g32p_literalColumn c),
        g32p_literalCharacterValue 5 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_005 : ∀ c : Fin 102,
    g32p_literalCharacterValue 5 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 5 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_006 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 6 (g32p_literalColumn c),
        g32p_literalCharacterValue 6 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_006 : ∀ c : Fin 102,
    g32p_literalCharacterValue 6 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 6 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_007 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 7 (g32p_literalColumn c),
        g32p_literalCharacterValue 7 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_007 : ∀ c : Fin 102,
    g32p_literalCharacterValue 7 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 7 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_008 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 8 (g32p_literalColumn c),
        g32p_literalCharacterValue 8 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_008 : ∀ c : Fin 102,
    g32p_literalCharacterValue 8 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 8 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_009 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 9 (g32p_literalColumn c),
        g32p_literalCharacterValue 9 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_009 : ∀ c : Fin 102,
    g32p_literalCharacterValue 9 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 9 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_010 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 10 (g32p_literalColumn c),
        g32p_literalCharacterValue 10 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_010 : ∀ c : Fin 102,
    g32p_literalCharacterValue 10 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 10 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_011 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 11 (g32p_literalColumn c),
        g32p_literalCharacterValue 11 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_011 : ∀ c : Fin 102,
    g32p_literalCharacterValue 11 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 11 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_012 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 12 (g32p_literalColumn c),
        g32p_literalCharacterValue 12 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_012 : ∀ c : Fin 102,
    g32p_literalCharacterValue 12 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 12 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_013 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 13 (g32p_literalColumn c),
        g32p_literalCharacterValue 13 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_013 : ∀ c : Fin 102,
    g32p_literalCharacterValue 13 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 13 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_014 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 14 (g32p_literalColumn c),
        g32p_literalCharacterValue 14 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_014 : ∀ c : Fin 102,
    g32p_literalCharacterValue 14 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 14 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_015 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 15 (g32p_literalColumn c),
        g32p_literalCharacterValue 15 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_015 : ∀ c : Fin 102,
    g32p_literalCharacterValue 15 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 15 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_016 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 16 (g32p_literalColumn c),
        g32p_literalCharacterValue 16 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_016 : ∀ c : Fin 102,
    g32p_literalCharacterValue 16 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 16 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_017 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 17 (g32p_literalColumn c),
        g32p_literalCharacterValue 17 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_017 : ∀ c : Fin 102,
    g32p_literalCharacterValue 17 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 17 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_018 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 18 (g32p_literalColumn c),
        g32p_literalCharacterValue 18 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_018 : ∀ c : Fin 102,
    g32p_literalCharacterValue 18 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 18 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_019 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 19 (g32p_literalColumn c),
        g32p_literalCharacterValue 19 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_019 : ∀ c : Fin 102,
    g32p_literalCharacterValue 19 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 19 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_020 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 20 (g32p_literalColumn c),
        g32p_literalCharacterValue 20 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_020 : ∀ c : Fin 102,
    g32p_literalCharacterValue 20 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 20 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_021 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 21 (g32p_literalColumn c),
        g32p_literalCharacterValue 21 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_021 : ∀ c : Fin 102,
    g32p_literalCharacterValue 21 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 21 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_022 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 22 (g32p_literalColumn c),
        g32p_literalCharacterValue 22 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_022 : ∀ c : Fin 102,
    g32p_literalCharacterValue 22 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 22 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_023 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 23 (g32p_literalColumn c),
        g32p_literalCharacterValue 23 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_023 : ∀ c : Fin 102,
    g32p_literalCharacterValue 23 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 23 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_024 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 24 (g32p_literalColumn c),
        g32p_literalCharacterValue 24 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_024 : ∀ c : Fin 102,
    g32p_literalCharacterValue 24 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 24 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_025 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 25 (g32p_literalColumn c),
        g32p_literalCharacterValue 25 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_025 : ∀ c : Fin 102,
    g32p_literalCharacterValue 25 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 25 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_026 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 26 (g32p_literalColumn c),
        g32p_literalCharacterValue 26 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_026 : ∀ c : Fin 102,
    g32p_literalCharacterValue 26 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 26 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_027 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 27 (g32p_literalColumn c),
        g32p_literalCharacterValue 27 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_027 : ∀ c : Fin 102,
    g32p_literalCharacterValue 27 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 27 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_028 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 28 (g32p_literalColumn c),
        g32p_literalCharacterValue 28 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_028 : ∀ c : Fin 102,
    g32p_literalCharacterValue 28 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 28 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_029 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 29 (g32p_literalColumn c),
        g32p_literalCharacterValue 29 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_029 : ∀ c : Fin 102,
    g32p_literalCharacterValue 29 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 29 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_030 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 30 (g32p_literalColumn c),
        g32p_literalCharacterValue 30 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_030 : ∀ c : Fin 102,
    g32p_literalCharacterValue 30 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 30 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_031 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 31 (g32p_literalColumn c),
        g32p_literalCharacterValue 31 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_031 : ∀ c : Fin 102,
    g32p_literalCharacterValue 31 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 31 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_032 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 32 (g32p_literalColumn c),
        g32p_literalCharacterValue 32 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_032 : ∀ c : Fin 102,
    g32p_literalCharacterValue 32 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 32 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_033 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 33 (g32p_literalColumn c),
        g32p_literalCharacterValue 33 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_033 : ∀ c : Fin 102,
    g32p_literalCharacterValue 33 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 33 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_034 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 34 (g32p_literalColumn c),
        g32p_literalCharacterValue 34 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_034 : ∀ c : Fin 102,
    g32p_literalCharacterValue 34 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 34 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_035 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 35 (g32p_literalColumn c),
        g32p_literalCharacterValue 35 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_035 : ∀ c : Fin 102,
    g32p_literalCharacterValue 35 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 35 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_036 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 36 (g32p_literalColumn c),
        g32p_literalCharacterValue 36 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_036 : ∀ c : Fin 102,
    g32p_literalCharacterValue 36 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 36 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_037 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 37 (g32p_literalColumn c),
        g32p_literalCharacterValue 37 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_037 : ∀ c : Fin 102,
    g32p_literalCharacterValue 37 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 37 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_038 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 38 (g32p_literalColumn c),
        g32p_literalCharacterValue 38 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_038 : ∀ c : Fin 102,
    g32p_literalCharacterValue 38 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 38 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_039 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 39 (g32p_literalColumn c),
        g32p_literalCharacterValue 39 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_039 : ∀ c : Fin 102,
    g32p_literalCharacterValue 39 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 39 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_040 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 40 (g32p_literalColumn c),
        g32p_literalCharacterValue 40 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_040 : ∀ c : Fin 102,
    g32p_literalCharacterValue 40 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 40 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_041 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 41 (g32p_literalColumn c),
        g32p_literalCharacterValue 41 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_041 : ∀ c : Fin 102,
    g32p_literalCharacterValue 41 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 41 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_042 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 42 (g32p_literalColumn c),
        g32p_literalCharacterValue 42 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_042 : ∀ c : Fin 102,
    g32p_literalCharacterValue 42 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 42 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_043 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 43 (g32p_literalColumn c),
        g32p_literalCharacterValue 43 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_043 : ∀ c : Fin 102,
    g32p_literalCharacterValue 43 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 43 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_044 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 44 (g32p_literalColumn c),
        g32p_literalCharacterValue 44 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_044 : ∀ c : Fin 102,
    g32p_literalCharacterValue 44 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 44 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_045 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 45 (g32p_literalColumn c),
        g32p_literalCharacterValue 45 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_045 : ∀ c : Fin 102,
    g32p_literalCharacterValue 45 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 45 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_046 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 46 (g32p_literalColumn c),
        g32p_literalCharacterValue 46 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_046 : ∀ c : Fin 102,
    g32p_literalCharacterValue 46 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 46 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_047 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 47 (g32p_literalColumn c),
        g32p_literalCharacterValue 47 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_047 : ∀ c : Fin 102,
    g32p_literalCharacterValue 47 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 47 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_048 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 48 (g32p_literalColumn c),
        g32p_literalCharacterValue 48 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_048 : ∀ c : Fin 102,
    g32p_literalCharacterValue 48 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 48 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_049 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 49 (g32p_literalColumn c),
        g32p_literalCharacterValue 49 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_049 : ∀ c : Fin 102,
    g32p_literalCharacterValue 49 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 49 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_050 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 50 (g32p_literalColumn c),
        g32p_literalCharacterValue 50 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_050 : ∀ c : Fin 102,
    g32p_literalCharacterValue 50 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 50 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_051 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 51 (g32p_literalColumn c),
        g32p_literalCharacterValue 51 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_051 : ∀ c : Fin 102,
    g32p_literalCharacterValue 51 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 51 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_052 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 52 (g32p_literalColumn c),
        g32p_literalCharacterValue 52 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_052 : ∀ c : Fin 102,
    g32p_literalCharacterValue 52 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 52 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_053 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 53 (g32p_literalColumn c),
        g32p_literalCharacterValue 53 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_053 : ∀ c : Fin 102,
    g32p_literalCharacterValue 53 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 53 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_054 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 54 (g32p_literalColumn c),
        g32p_literalCharacterValue 54 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_054 : ∀ c : Fin 102,
    g32p_literalCharacterValue 54 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 54 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_055 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 55 (g32p_literalColumn c),
        g32p_literalCharacterValue 55 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_055 : ∀ c : Fin 102,
    g32p_literalCharacterValue 55 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 55 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_056 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 56 (g32p_literalColumn c),
        g32p_literalCharacterValue 56 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_056 : ∀ c : Fin 102,
    g32p_literalCharacterValue 56 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 56 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_057 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 57 (g32p_literalColumn c),
        g32p_literalCharacterValue 57 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_057 : ∀ c : Fin 102,
    g32p_literalCharacterValue 57 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 57 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_058 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 58 (g32p_literalColumn c),
        g32p_literalCharacterValue 58 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_058 : ∀ c : Fin 102,
    g32p_literalCharacterValue 58 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 58 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_059 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 59 (g32p_literalColumn c),
        g32p_literalCharacterValue 59 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_059 : ∀ c : Fin 102,
    g32p_literalCharacterValue 59 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 59 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_060 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 60 (g32p_literalColumn c),
        g32p_literalCharacterValue 60 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_060 : ∀ c : Fin 102,
    g32p_literalCharacterValue 60 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 60 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_061 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 61 (g32p_literalColumn c),
        g32p_literalCharacterValue 61 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_061 : ∀ c : Fin 102,
    g32p_literalCharacterValue 61 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 61 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_062 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 62 (g32p_literalColumn c),
        g32p_literalCharacterValue 62 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_062 : ∀ c : Fin 102,
    g32p_literalCharacterValue 62 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 62 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_063 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 63 (g32p_literalColumn c),
        g32p_literalCharacterValue 63 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_063 : ∀ c : Fin 102,
    g32p_literalCharacterValue 63 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 63 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_064 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 64 (g32p_literalColumn c),
        g32p_literalCharacterValue 64 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_064 : ∀ c : Fin 102,
    g32p_literalCharacterValue 64 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 64 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_065 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 65 (g32p_literalColumn c),
        g32p_literalCharacterValue 65 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_065 : ∀ c : Fin 102,
    g32p_literalCharacterValue 65 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 65 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_066 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 66 (g32p_literalColumn c),
        g32p_literalCharacterValue 66 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_066 : ∀ c : Fin 102,
    g32p_literalCharacterValue 66 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 66 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_067 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 67 (g32p_literalColumn c),
        g32p_literalCharacterValue 67 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_067 : ∀ c : Fin 102,
    g32p_literalCharacterValue 67 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 67 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_068 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 68 (g32p_literalColumn c),
        g32p_literalCharacterValue 68 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_068 : ∀ c : Fin 102,
    g32p_literalCharacterValue 68 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 68 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_069 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 69 (g32p_literalColumn c),
        g32p_literalCharacterValue 69 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_069 : ∀ c : Fin 102,
    g32p_literalCharacterValue 69 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 69 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_070 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 70 (g32p_literalColumn c),
        g32p_literalCharacterValue 70 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_070 : ∀ c : Fin 102,
    g32p_literalCharacterValue 70 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 70 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_071 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 71 (g32p_literalColumn c),
        g32p_literalCharacterValue 71 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_071 : ∀ c : Fin 102,
    g32p_literalCharacterValue 71 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 71 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_072 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 72 (g32p_literalColumn c),
        g32p_literalCharacterValue 72 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_072 : ∀ c : Fin 102,
    g32p_literalCharacterValue 72 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 72 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_073 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 73 (g32p_literalColumn c),
        g32p_literalCharacterValue 73 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_073 : ∀ c : Fin 102,
    g32p_literalCharacterValue 73 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 73 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_074 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 74 (g32p_literalColumn c),
        g32p_literalCharacterValue 74 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_074 : ∀ c : Fin 102,
    g32p_literalCharacterValue 74 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 74 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_075 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 75 (g32p_literalColumn c),
        g32p_literalCharacterValue 75 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_075 : ∀ c : Fin 102,
    g32p_literalCharacterValue 75 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 75 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_076 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 76 (g32p_literalColumn c),
        g32p_literalCharacterValue 76 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_076 : ∀ c : Fin 102,
    g32p_literalCharacterValue 76 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 76 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_077 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 77 (g32p_literalColumn c),
        g32p_literalCharacterValue 77 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_077 : ∀ c : Fin 102,
    g32p_literalCharacterValue 77 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 77 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalCharacterNorm_078 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 78 (g32p_literalColumn c),
        g32p_literalCharacterValue 78 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_078 : ∀ c : Fin 102,
    g32p_literalCharacterValue 78 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 78 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_079 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 79 (g32p_literalColumn c),
        g32p_literalCharacterValue 79 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_079 : ∀ c : Fin 102,
    g32p_literalCharacterValue 79 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 79 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_080 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 80 (g32p_literalColumn c),
        g32p_literalCharacterValue 80 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_080 : ∀ c : Fin 102,
    g32p_literalCharacterValue 80 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 80 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_081 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 81 (g32p_literalColumn c),
        g32p_literalCharacterValue 81 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_081 : ∀ c : Fin 102,
    g32p_literalCharacterValue 81 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 81 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_082 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 82 (g32p_literalColumn c),
        g32p_literalCharacterValue 82 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_082 : ∀ c : Fin 102,
    g32p_literalCharacterValue 82 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 82 (g32p_literalColumn c)) := by
  decide +kernel

theorem g32p_literalCharacterNorm_083 :
    g32p_pairingCheck 155520 1 (List.ofFn fun c : Fin 102 =>
      (g32p_literalSize c, g32p_literalCharacterValue 83 (g32p_literalColumn c),
        g32p_literalCharacterValue 83 (g32p_literalColumn (g32p_literalInverseClass c)))) =
          true := by
  decide +kernel

theorem g32p_literalCharacterInverse_083 : ∀ c : Fin 102,
    g32p_literalCharacterValue 83 (g32p_literalColumn (g32p_literalInverseClass c)) =
      g32p_literalBar (g32p_literalCharacterValue 83 (g32p_literalColumn c)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
