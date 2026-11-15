import HodgeLean.Foundations.Program.SchoenTowerT11bHalfLineCoordinates

/-! One ambient coordinate map for finitely many ordered continuous sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Ordered continuous sections have one ambient straightening above a continuous lower section.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible cylindrical-coordinate step. -/
theorem s2v_t11b_ordered_sections_ambient_coordinates {X : Type*} [TopologicalSpace X]
    {m : ℕ} (l : X → ℝ) (hl : Continuous l)
    (ψ : Fin m → X → ℝ) (hψ : ∀ i, Continuous (ψ i))
    (hbelow : ∀ b i, l b < ψ i b) (hordered : ∀ b, StrictMono (fun i => ψ i b)) :
    ∃ E : (X × ℝ) ≃ₜ (X × ℝ),
      (∀ z, (E z).1 = z.1) ∧ (∀ b, E (b, l b) = (b, 0)) ∧
      (∀ b i, E (b, ψ i b) = (b, (i.val : ℝ) + 1)) ∧
      ∀ b, StrictMono (fun x => (E (b, x)).2) := by
  induction m with
  | zero =>
    let E : (X × ℝ) ≃ₜ (X × ℝ) :=
      { toFun := fun z => (z.1, z.2 - l z.1)
        invFun := fun z => (z.1, z.2 + l z.1)
        left_inv := fun z => Prod.ext rfl (sub_add_cancel z.2 (l z.1))
        right_inv := fun z => Prod.ext rfl (add_sub_cancel_right z.2 (l z.1))
        continuous_toFun := continuous_fst.prodMk (continuous_snd.sub (hl.comp continuous_fst))
        continuous_invFun := continuous_fst.prodMk (continuous_snd.add (hl.comp continuous_fst)) }
    refine ⟨E, fun _ => rfl, ?_, ?_, ?_⟩
    · intro b
      exact Prod.ext rfl (sub_self (l b))
    · intro b i
      exact Fin.elim0 i
    · intro b x y hxy
      exact sub_lt_sub_right hxy (l b)
  | succ m ih =>
    obtain ⟨E, hbase, hfloor, hroots, hmono⟩ := ih
      (fun i => ψ i.castSucc) (fun i => hψ i.castSucc)
      (fun b i => hbelow b i.castSucc)
      (fun b i j hij => hordered b (Fin.castSucc_lt_castSucc_iff.mpr hij))
    let ζ : X → ℝ := fun b => (E (b, ψ (Fin.last m) b)).2
    have hζ : Continuous ζ := (continuous_snd.comp E.continuous).comp
      (continuous_id.prodMk (hψ (Fin.last m)))
    have habove : ∀ b, (m : ℝ) < ζ b := by
      intro b
      cases m with
      | zero =>
        have h := hmono b (hbelow b (Fin.last 0))
        dsimp only at h
        rw [hfloor b] at h
        simpa only [ζ, Nat.cast_zero] using h
      | succ k =>
        have h := hmono b (hordered b (Fin.castSucc_lt_last (Fin.last k)))
        dsimp only at h
        rw [hroots b (Fin.last k)] at h
        simpa only [Fin.val_last, Nat.cast_add, Nat.cast_one] using h
    let H := s2v_t11b_upperSectionCoordinates (m : ℝ) ζ hζ habove
    obtain ⟨hHbase, hHfix, hHsection, hHmono⟩ :=
      s2v_t11b_upperSectionCoordinates_spec (m : ℝ) ζ hζ habove
    refine ⟨E.trans H, ?_, ?_, ?_, ?_⟩
    · intro z
      change (H (E z)).1 = z.1
      exact (hHbase (E z)).trans (hbase z)
    · intro b
      change H (E (b, l b)) = (b, 0)
      rw [hfloor b]
      exact hHfix b 0 (Nat.cast_nonneg m)
    · intro b i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · change H (E (b, ψ j.castSucc b)) = (b, (j.val : ℝ) + 1)
        rw [hroots b j]
        apply hHfix
        exact_mod_cast Nat.succ_le_iff.mpr j.isLt
      · have hpoint : E (b, ψ (Fin.last m) b) = (b, ζ b) :=
          Prod.ext (hbase _) rfl
        change H (E (b, ψ (Fin.last m) b)) = (b, (m : ℝ) + 1)
        rw [hpoint]
        exact hHsection b
    · intro b x y hxy
      have hxpoint : E (b, x) = (b, (E (b, x)).2) := Prod.ext (hbase _) rfl
      have hypoint : E (b, y) = (b, (E (b, y)).2) := Prod.ext (hbase _) rfl
      change (H (E (b, x))).2 < (H (E (b, y))).2
      rw [hxpoint, hypoint]
      exact hHmono b (hmono b hxy)

/-- Every finite ordered continuous family has one base-preserving ambient straightening map.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible cylindrical-coordinate step. -/
theorem s2v_t11b_finite_sections_ambient_straightening {X : Type*} [TopologicalSpace X]
    {m : ℕ} (ψ : Fin m → X → ℝ) (hψ : ∀ i, Continuous (ψ i))
    (hordered : ∀ b, StrictMono (fun i => ψ i b)) :
    ∃ E : (X × ℝ) ≃ₜ (X × ℝ),
      (∀ z, (E z).1 = z.1) ∧
      (∀ b i, E (b, ψ i b) = (b, (i.val : ℝ) + 1)) ∧
      ∀ b, StrictMono (fun x => (E (b, x)).2) := by
  by_cases hm : m = 0
  · subst m
    refine ⟨Homeomorph.refl _, fun _ => rfl, ?_, ?_⟩
    · intro b i
      exact Fin.elim0 i
    · intro b x y hxy
      exact hxy
  · let i₀ : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
    let l : X → ℝ := fun b => ψ i₀ b - 1
    have hl : Continuous l := (hψ i₀).sub continuous_const
    have hbelow : ∀ b i, l b < ψ i b := by
      intro b i
      have hle : ψ i₀ b ≤ ψ i b :=
        (hordered b).monotone (show i₀ ≤ i from Nat.zero_le i.val)
      dsimp only [l]
      linarith
    obtain ⟨E, hbase, _, hroots, hmono⟩ :=
      s2v_t11b_ordered_sections_ambient_coordinates l hl ψ hψ hbelow hordered
    exact ⟨E, hbase, hroots, hmono⟩

end HodgeLean.Foundations.Program
