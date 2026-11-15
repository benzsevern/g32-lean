import HodgeLean.Foundations.Program.G32PropFourSixRowComparison

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory
open scoped Classical

set_option maxHeartbeats 400000

def g32p_characterPairing {G : Type*} [Group G] [Fintype G] (W : FDRep ℂ G) :
    (G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Nat.card G : ℂ)⁻¹ * ∑ g, f g * W.character g⁻¹
  map_add' f h := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      ← Finset.mul_sum] <;> ring

theorem g32p_characterPairing_simple {G : Type*} [Group G] [Fintype G]
    (V W : FDRep ℂ G) [Simple V] [Simple W] :
    g32p_characterPairing W V.character = if Nonempty (V ≅ W) then 1 else 0 := by
  classical
  letI := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  exact FDRep.char_orthonormal V W

theorem g32p_characters_linearIndependent {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (V : I → FDRep ℂ G) (hS : ∀ i, Simple (V i))
    (hN : ∀ i j, i ≠ j → IsEmpty (V i ≅ V j)) :
    LinearIndependent ℂ (fun i => (V i).character) := by
  classical
  letI : ∀ i, Simple (V i) := hS
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hp (j : I) : g32p_characterPairing (V i) (V j).character =
      if j = i then 1 else 0 := by
    rw [g32p_characterPairing_simple]
    split_ifs with hji
    · subst j
      rfl
    · have : j = i := by
        by_contra hn
        exact (hN j i hn).false hji.some
      contradiction
    · have : Nonempty (V j ≅ V i) := by subst j; exact ⟨Iso.refl _⟩
      contradiction
    · rfl
  have hh := congrArg (g32p_characterPairing (V i)) hc
  simpa only [map_sum, map_smul, hp, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_zero] using hh

theorem g32p_simple_iso_of_character_span {G I : Type*} [Group G] [Fintype G]
    (V : I → FDRep ℂ G) (hS : ∀ i, Simple (V i))
    (σ : FDRep ℂ G) [Simple σ]
    (hspan : σ.character ∈ Submodule.span ℂ (Set.range fun i => (V i).character)) :
    ∃ i, Nonempty (σ ≅ V i) := by
  classical
  letI : ∀ i, Simple (V i) := hS
  by_contra hn
  have hz : Submodule.span ℂ (Set.range fun i => (V i).character) ≤
      LinearMap.ker (g32p_characterPairing σ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g32p_characterPairing σ (V i).character = 0
    rw [g32p_characterPairing_simple, ite_eq_right]
    intro hi
    exact hn ⟨i, hi.map Iso.symm⟩
  have hh := hz hspan
  change g32p_characterPairing σ σ.character = 0 at hh
  rw [g32p_characterPairing_simple, ite_eq_left ⟨Iso.refl σ⟩] at hh
  exact one_ne_zero hh

theorem g32p_simple_iso_of_character_eq {G : Type*} [Group G] [Fintype G]
    (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : V.character = W.character) : Nonempty (V ≅ W) := by
  classical
  have hh : g32p_characterPairing W V.character = 1 := by
    rw [h, g32p_characterPairing_simple, ite_eq_left ⟨Iso.refl W⟩]
  rw [g32p_characterPairing_simple] at hh
  by_contra hn
  rw [ite_eq_right hn] at hh
  exact zero_ne_one hh

def g32p_precomposeClasses {G : Type*} {n : ℕ} (classify : G → Fin n) :
    (Fin n → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := f ∘ classify
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem g32p_character_of_class_representatives {G : Type*} [Group G] {n : ℕ}
    (classify : G → Fin n) (reps : Fin n → G)
    (hconj : ∀ g, IsConj g (reps (classify g))) (V : FDRep ℂ G) :
    g32p_precomposeClasses classify (fun j => V.character (reps j)) = V.character := by
  funext g
  obtain ⟨u, hu⟩ := isConj_iff.mp (hconj g)
  change V.character (reps (classify g)) = V.character g
  rw [← hu, FDRep.char_conj]

theorem g32p_simple_coverage_of_class_count {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (classify : G → Fin n) (reps : Fin n → G)
    (hconj : ∀ g, IsConj g (reps (classify g)))
    (V : Fin n → FDRep ℂ G) (hS : ∀ i, Simple (V i))
    (hN : ∀ i j, i ≠ j → IsEmpty (V i ≅ V j))
    (σ : FDRep ℂ G) [Simple σ] : ∃ i, Nonempty (σ ≅ V i) := by
  let L := g32p_precomposeClasses classify
  let coords : Fin n → Fin n → ℂ := fun i j => (V i).character (reps j)
  have heq : L ∘ coords = fun i => (V i).character := by
    funext i
    exact g32p_character_of_class_representatives classify reps hconj (V i)
  have hli : LinearIndependent ℂ coords := by
    apply LinearIndependent.of_comp L
    rw [heq]
    exact g32p_characters_linearIndependent V hS hN
  have htop : Submodule.span ℂ (Set.range coords) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp only [Fintype.card_fin, Module.finrank_pi])
  have himage : (Submodule.span ℂ (Set.range coords)).map L =
      Submodule.span ℂ (Set.range fun i => (V i).character) := by
    rw [Submodule.map_span, ← Set.range_comp, heq]
  apply g32p_simple_iso_of_character_span V hS σ
  rw [← himage]
  refine ⟨(fun j => σ.character (reps j)), ?_, ?_⟩
  · rw [htop]
    trivial
  · exact g32p_character_of_class_representatives classify reps hconj σ

end HodgeLean.Foundations.Program
