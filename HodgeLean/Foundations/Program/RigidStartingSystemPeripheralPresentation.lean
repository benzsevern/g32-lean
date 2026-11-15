import HodgeLean.Foundations.Program.RiemannRochProofs

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65r_reorder_peripheral_presentation {α Γ H : Type} [Group Γ] [Group H]
    {r : ℕ} (e : Fin r ≃ α) (b : Fin 4 ≃ Option α) (γ : α → Γ)
    (hu : ∀ (G : Type) [Group G] (v : α → G), ∃! φ : Γ →* G, ∀ a, φ (γ a) = v a)
    (M : Γ →* H) (T : Fin 4 → H)
    (hloc : ∀ a : Option α, IsConj (T (b.symm a))
      (M (a.elim ((List.ofFn (fun i ↦ γ (e i))).prod)⁻¹ γ))) :
    ∃ δ : Fin 4 → Γ, (List.ofFn δ).prod = 1 ∧
      (∀ (G : Type) [Group G] (v : Fin 4 → G), (List.ofFn v).prod = 1 →
        ∃! φ : Γ →* G, ∀ i, φ (δ i) = v i) ∧
      ∀ i, IsConj (T i) (M (δ i)) := by
  have hu0 : ∀ (G : Type) [Group G] (v : Fin r → G),
      ∃! φ : Γ →* G, ∀ i, φ (γ (e i)) = v i := by
    intro G _ v
    obtain ⟨φ,hφ,huniq⟩ := hu G (fun a ↦ v (e.symm a))
    refine ⟨φ,fun i ↦ by simpa using hφ (e i),?_⟩
    intro ψ hψ
    apply huniq
    intro a
    simpa using hψ (e.symm a)
  let δ0 : Fin (r+1) → Γ := Fin.cases ((List.ofFn (fun i ↦ γ (e i))).prod)⁻¹ (fun i ↦ γ (e i))
  obtain ⟨hp,hu1⟩ := RiemannRochTop_adjoin_inverse_product (fun i ↦ γ (e i)) hu0
  let J : Fin (r+1) ≃ Option α := (finSuccEquiv r).trans (Equiv.optionCongr e)
  let g : Option α → Γ := fun a ↦ δ0 (J.symm a)
  have hg (a : Option α) : g a = a.elim ((List.ofFn (fun i ↦ γ (e i))).prod)⁻¹ γ := by
    cases a <;> simp [g,J,δ0,← Equiv.optionCongr_symm,Equiv.optionCongr]
  have hn : (List.ofFn J).Nodup := List.nodup_ofFn.mpr J.injective
  have hb : (List.ofFn b).Nodup := List.nodup_ofFn.mpr b.injective
  have hperm : (List.ofFn J).Perm (List.ofFn b) := by
    apply (List.perm_ext_iff_of_nodup hn hb).mpr
    intro a
    constructor
    · intro _; exact List.mem_ofFn.mpr ⟨b.symm a,b.apply_symm_apply a⟩
    · intro _; exact List.mem_ofFn.mpr ⟨J.symm a,J.apply_symm_apply a⟩
  have hgp : ((List.ofFn J).map g).prod = 1 := by
    simpa only [List.map_ofFn,Function.comp_def,g,J.symm_apply_apply] using hp
  have hgu : ∀ (G : Type) [Group G] (v : Option α → G), ((List.ofFn J).map v).prod = 1 →
      ∃! φ : Γ →* G, ∀ a, φ (g a) = v a := by
    intro G _ v hv
    obtain ⟨φ,hφ,huniq⟩ := hu1 G (fun i ↦ v (J i))
      (by simpa only [List.map_ofFn,Function.comp_def] using hv)
    refine ⟨φ,fun a ↦ by simpa only [g,J.apply_symm_apply] using hφ (J.symm a),?_⟩
    intro ψ hψ
    apply huniq
    intro i
    simpa only [g,J.symm_apply_apply] using hψ (J i)
  obtain ⟨δ,hδ,hconj,hδu⟩ := RiemannRochTop_presentation_reorder hperm hn g hgp hgu
  refine ⟨fun i ↦ δ (b i),?_,?_,?_⟩
  · simpa only [List.map_ofFn,Function.comp_def] using hδ
  · intro G _ v hv
    obtain ⟨φ,hφ,huniq⟩ := hδu G (fun a ↦ v (b.symm a))
      (by simpa only [List.map_ofFn,Function.comp_def,b.symm_apply_apply] using hv)
    refine ⟨φ,fun i ↦ by simpa using hφ (b i),?_⟩
    intro ψ hψ
    apply huniq
    intro a
    simpa using hψ (b.symm a)
  · intro i
    have hc := M.map_isConj (hconj (b i))
    rw [hg] at hc
    have h := (hloc (b i)).trans hc
    simpa only [b.symm_apply_apply] using h

end HodgeLean.Foundations.Program
