import HodgeLean.Foundations.Program.CoverDictionaryForms

/-! # B6-5 stage 5d, geometric part: multiplicities and transfer through the dictionary

The Chevalley–Weil count `dim Hom_G(σ, H⁰(K_C)) = 3` on every fibre of a family at the G32 centre,
for `σ = b65g_rep false` (`ρ`) and `σ = b65g_rep true` (`ρ̄`, identified with the conjugate
representation by entrywise conjugation); evaluation of the r- and q-vectors away from the poles,
linearity of the represented forms in the coefficient vectors, and the transfer of dimensions and
bases through a bijective representation relation. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial Manifold
open scoped Topology ContDiff ComplexConjugate
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- `Hom_G` spaces of intertwined representations have the same dimension. -/
theorem b65g_homG_congr {G : Type} [Group G] {V V' M : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (e : V ≃ₗ[ℂ] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (act : G → M →ₗ[ℂ] M) (W : Submodule ℂ M) :
    Module.finrank ℂ (b4_HomG ρ' act W) = Module.finrank ℂ (b4_HomG ρ act W) := by
  have he' : ∀ g v, e.symm (ρ' g v) = ρ g (e.symm v) := fun g v ↦ by
    apply e.injective; rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let f : b4_HomG ρ' act W →ₗ[ℂ] b4_HomG ρ act W :=
    ((LinearMap.lcomp ℂ M e.toLinearMap).comp (b4_HomG ρ' act W).subtype).codRestrict _
      fun φ ↦ ⟨fun v ↦ φ.2.1 _, fun g v ↦ by
        simp only [LinearMap.comp_apply, LinearMap.lcomp_apply, Submodule.subtype_apply,
          LinearEquiv.coe_coe, he]
        exact φ.2.2 g (e v)⟩
  let f' : b4_HomG ρ act W →ₗ[ℂ] b4_HomG ρ' act W :=
    ((LinearMap.lcomp ℂ M e.symm.toLinearMap).comp (b4_HomG ρ act W).subtype).codRestrict _
      fun φ ↦ ⟨fun v ↦ φ.2.1 _, fun g v ↦ by
        simp only [LinearMap.comp_apply, LinearMap.lcomp_apply, Submodule.subtype_apply,
          LinearEquiv.coe_coe, he']
        exact φ.2.2 g (e.symm v)⟩
  refine (LinearEquiv.ofLinearMap f f' ?_ ?_).finrank_eq
  · refine LinearMap.ext fun φ ↦ Subtype.ext (LinearMap.ext fun v ↦ ?_)
    change φ.1 (e.symm (e v)) = φ.1 v
    rw [LinearEquiv.symm_apply_apply]
  · refine LinearMap.ext fun φ ↦ Subtype.ext (LinearMap.ext fun v ↦ ?_)
    change φ.1 (e (e.symm v)) = φ.1 v
    rw [LinearEquiv.apply_symm_apply]

/-- Chevalley–Weil on a fibre: `ρ` and `ρ̄` occur three times in `H⁰(K_C)` (G32 Lemma 3.6). -/
theorem b65g_holo_multiplicities {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) :
    Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun a ↦ b4_formAct ℂ (C := b65z_fibre c D.C t) a)
      (b3_HolForm ℂ (b65z_fibre c D.C t))) = 3 ∧
    Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
      (fun a ↦ b4_formAct ℂ (C := b65z_fibre c D.C t) a)
      (b3_HolForm ℂ (b65z_fibre c D.C t))) = 3 := by
  have hq : Function.Injective (b6_branch t.val) :=
    (b6t_polydisc_neighbourhood c D.atlas.hb).2.2.2 t.property
  have hrank : (∑ i : Fin 13, ((b4b_toMatrix (g i) - 1).rank : ℝ)) = 14 := by
    have h := g32h_multCW_of_nielsen _ hg
    unfold g32h_multCW at h
    have hz : (∑ i : Fin 13, ((b4b_toMatrix (g i) - 1).rank : ℤ)) = 14 := by
      linarith
    exact_mod_cast hz
  have hbar : (∑ i : Fin 13,
      b4_age (HurwitzPrymRex_barRep b63d_naturalRep (g i))) = 7 := by
    simp only [b63d_conjugateRep_age]
    have h := g32h_holoCW_of_nielsen _ hg
    unfold g32h_holoCW at h
    linarith
  have hnat : (∑ i : Fin 13, b4_age (b63d_naturalRep (g i))) = 7 := by
    have hsum : (∑ i : Fin 13,
        b4_age (HurwitzPrymRex_barRep b63d_naturalRep (g i))) +
        (∑ i : Fin 13, b4_age (b63d_naturalRep (g i))) = 14 := by
      rw [← Finset.sum_add_distrib, ← hrank]
      apply Finset.sum_congr rfl
      intro i hi
      rw [HurwitzPrymRex_age_add_bar, b63d_naturalRep_rank]
    linarith
  constructor
  · have h := b63d_finite_holoCW (b65z_fibre c D.C t) (D.hG t)
      (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t)
      (D.hk t) (D.hsurj t) (D.hgal t) (b6_branch t.val) hq g
      (D.hbranch t) (D.hrot t) b63d_naturalRep b63d_naturalRep_nontrivial
    rw [hnat, b63d_naturalRep_finrank] at h
    norm_num at h
    exact_mod_cast h
  · have h := b63d_finite_holoCW (b65z_fibre c D.C t) (D.hG t)
      (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t)
      (D.hk t) (D.hsurj t) (D.hgal t) (b6_branch t.val) hq g
      (D.hbranch t) (D.hrot t) (HurwitzPrymRex_barRep b63d_naturalRep)
      b63d_conjugateRep_nontrivial
    rw [hbar, b63d_conjugateRep_finrank] at h
    norm_num at h
    exact_mod_cast h

/-- Entrywise conjugation identifies `ρ̄` on the conjugate space with `b65g_rep true`.
Source: Fulton–Harris, *Representation Theory*, GTM 129, §3.5; `HurwitzPrymRex_Bar`. -/
def b65g_barEquiv : HurwitzPrymRex_Bar (Fin 4 → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun x := fun i ↦ conj (x.val i)
  invFun v := HurwitzPrymRex_Bar.of fun i ↦ conj (v i)
  map_add' x y := by funext i; simp
  map_smul' c x := by funext i; simp
  left_inv x := by ext i; simp
  right_inv v := by funext i; simp

/-- **The multiplicity three** of `σ ∈ {ρ, ρ̄}` in the holomorphic forms of every fibre. -/
theorem b65g_homG_finrank {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (cj : Bool) : Module.finrank ℂ (b65g_homG D t cj) = 3 := by
  obtain ⟨h1, h2⟩ := b65g_holo_multiplicities hg D t
  cases cj
  · have : b65g_rep false = b63d_naturalRep := by ext h v i; rfl
    rw [b65g_homG, this, h1]
  · rw [b65g_homG, ← h2]
    refine b65g_homG_congr _ _ b65g_barEquiv (fun h x ↦ ?_) _ _
    funext i
    simp [b65g_barEquiv, b65g_rep, b65g_mat, HurwitzPrymRex_barRep, b63d_naturalRep,
      Matrix.mulVec, dotProduct, map_sum]

section Transfer
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] (Rep : (Fin n → ℂ) → M → Prop)

/-- A linear relation passes to finite linear combinations. -/
theorem b65g_rep_finsum (h0 : Rep 0 0) (hadd : ∀ c c' φ φ', Rep c φ → Rep c' φ' → Rep (c + c') (φ + φ'))
    (hsmul : ∀ (l : ℂ) c φ, Rep c φ → Rep (l • c) (l • φ)) {ι : Type*} (S : Finset ι)
    (l : ι → ℂ) (cs : ι → Fin n → ℂ) (φ : ι → M) (h : ∀ a ∈ S, Rep (cs a) (φ a)) :
    Rep (∑ a ∈ S, l a • cs a) (∑ a ∈ S, l a • φ a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h0
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact hadd _ _ _ _ (hsmul _ _ _ (h a (Finset.mem_insert_self _ _)))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- A bijective linear relation between a kernel and a space of maps carries a basis of the
kernel to a basis of the space. -/
theorem b65g_basis_transfer (W : Submodule ℂ M) (K : Submodule ℂ (Fin n → ℂ))
    (h0 : Rep 0 0) (hadd : ∀ c c' φ φ', Rep c φ → Rep c' φ' → Rep (c + c') (φ + φ'))
    (hsmul : ∀ (l : ℂ) c φ, Rep c φ → Rep (l • c) (l • φ))
    (h1 : ∀ c ∈ K, ∃! φ, φ ∈ W ∧ Rep c φ) (h2 : ∀ φ ∈ W, ∃! c, c ∈ K ∧ Rep c φ)
    (F : Fin 3 → Fin n → ℂ) (hF : ∀ a, F a ∈ K) (hFspan : K ≤ Submodule.span ℂ (Set.range F))
    (hFind : LinearIndependent ℂ F) :
    ∃ φ : Fin 3 → M, (∀ a, φ a ∈ W ∧ Rep (F a) (φ a)) ∧ LinearIndependent ℂ φ ∧
      Submodule.span ℂ (Set.range φ) = W := by
  choose φ hφ _ using fun a ↦ h1 (F a) (hF a)
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro l hl
    have hr := b65g_rep_finsum Rep h0 hadd hsmul Finset.univ l F φ fun a _ ↦ (hφ a).2
    rw [hl] at hr
    obtain ⟨c0, -, hu⟩ := h2 0 W.zero_mem
    have e1 := hu _ ⟨Submodule.sum_mem _ fun a _ ↦ K.smul_mem _ (hF a), hr⟩
    have e2 := hu _ ⟨K.zero_mem, h0⟩
    exact (Fintype.linearIndependent_iff.mp hFind) l (e1.trans e2.symm)
  · refine le_antisymm (Submodule.span_le.mpr ?_) fun ψ hψ ↦ ?_
    · rintro _ ⟨a, rfl⟩; exact (hφ a).1
    obtain ⟨c, ⟨hcK, hc⟩, -⟩ := h2 ψ hψ
    obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (hFspan hcK)
    have hr := b65g_rep_finsum Rep h0 hadd hsmul Finset.univ l F φ fun a _ ↦ (hφ a).2
    rw [hl] at hr
    obtain ⟨_, -, hu⟩ := h1 c hcK
    have : ψ = ∑ a, l a • φ a :=
      (hu ψ ⟨hψ, hc⟩).trans (hu _ ⟨Submodule.sum_mem _ fun a _ ↦ W.smul_mem _ (hφ a).1, hr⟩).symm
    rw [this]
    exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- A bijective linear relation between a kernel and a space of maps preserves dimension. -/
theorem b65g_finrank_transfer (W : Submodule ℂ M) (K : Submodule ℂ (Fin n → ℂ))
    (hadd : ∀ c c' φ φ', Rep c φ → Rep c' φ' → Rep (c + c') (φ + φ'))
    (hsmul : ∀ (l : ℂ) c φ, Rep c φ → Rep (l • c) (l • φ))
    (h1 : ∀ c ∈ K, ∃! φ, φ ∈ W ∧ Rep c φ) (h2 : ∀ φ ∈ W, ∃! c, c ∈ K ∧ Rep c φ) :
    Module.finrank ℂ K = Module.finrank ℂ W := by
  choose Φ hΦ hΦu using fun c : K ↦ h1 c.1 c.2
  let L : K →ₗ[ℂ] W :=
    { toFun := fun c ↦ ⟨Φ c, (hΦ c).1⟩
      map_add' := fun c c' ↦ Subtype.ext ((hΦu (c + c') _ ⟨W.add_mem (hΦ c).1 (hΦ c').1,
        hadd _ _ _ _ (hΦ c).2 (hΦ c').2⟩)).symm
      map_smul' := fun l c ↦ Subtype.ext ((hΦu (l • c) _ ⟨W.smul_mem l (hΦ c).1,
        hsmul _ _ _ (hΦ c).2⟩)).symm }
  have hbij : Function.Bijective L := by
    constructor
    · intro c c' h
      have h' : Φ c = Φ c' := congrArg Subtype.val h
      obtain ⟨_, -, hu⟩ := h2 (Φ c) (hΦ c).1
      exact Subtype.ext ((hu _ ⟨c.2, (hΦ c).2⟩).trans (hu _ ⟨c'.2, h' ▸ (hΦ c').2⟩).symm)
    · intro ψ
      obtain ⟨c, ⟨hcK, hc⟩, -⟩ := h2 ψ.1 ψ.2
      exact ⟨⟨c, hcK⟩, Subtype.ext (hΦu ⟨c, hcK⟩ _ ⟨ψ.2, hc⟩).symm⟩
  exact (LinearEquiv.ofBijective L hbij).finrank_eq

end Transfer

/-- The value of a principal part away from its pole. -/
theorem b65g_eval_frac {s a : ℂ} (c : ℂ) (k : ℕ) (h : s ≠ a) :
    b65q_eval (RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ k) s = c / (s - a) ^ k := by
  have hZ : (RatFunc.X - RatFunc.C a) ^ k =
      algebraMap ℂ[X] (RatFunc ℂ) ((X - Polynomial.C a) ^ k) := by
    simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have regZ : b65g_reg s ((RatFunc.X - RatFunc.C a) ^ k) := by
    rw [hZ, b65g_reg, RatFunc.denom_algebraMap]; simp
  have evZ : b65q_eval ((RatFunc.X - RatFunc.C a) ^ k) s = (s - a) ^ k := by
    rw [hZ, b65q_eval, RatFunc.eval_algebraMap]; simp [eval₂_id]
  have hne : (RatFunc.X - RatFunc.C a) ^ k ≠ 0 := by
    rw [hZ]; exact RatFunc.algebraMap_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero a))
  have hm := b65g_eval_mul (b65g_reg_frac c k h) regZ
  rw [div_mul_cancel₀ _ hne, evZ] at hm
  rw [eq_div_iff (pow_ne_zero _ (sub_ne_zero.mpr h)), ← hm]
  simp [b65q_eval]

/-- The value of an r-vector away from the poles. -/
theorem b65g_eval_principal (t : Fin 4 ⊕ Fin 12 → ℂ) (c : Fin 36 → ℂ) (j : Fin 4) {s : ℂ}
    (hs : s ∉ Set.range t) : b65q_eval (b65q_principal t c j) s =
      ∑ a : Fin 9, c ⟨4 * a.val + j.val, by omega⟩ /
        (s - t (Sum.inl (b65k_poleIndex a))) ^ b65k_poleOrder a := by
  rw [b65q_principal, b65g_eval_sum _ fun _ _ ↦ b65g_reg_frac _ _ fun h ↦ hs ⟨_, h.symm⟩]
  exact Finset.sum_congr rfl fun a _ ↦ b65g_eval_frac _ _ fun h ↦ hs ⟨_, h.symm⟩

/-- The value of a q-vector away from the poles. -/
theorem b65g_eval_qVector (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (j : Fin 4) {s : ℂ} (hs : s ∉ Set.range t) :
    b65q_eval (b65q_qVector t node w d j) s =
      (∑ a : Fin 9, d ⟨4 * a.val + j.val, by omega⟩ /
        (s - t (Sum.inl (b65k_poleIndex a))) ^ b65k_poleOrder a) +
      ∑ x : Fin 12, (∑ v : Fin 6,
        d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j /
          (s - t (Sum.inr x)) := by
  have hreg : ∀ x : Fin 12, b65g_reg s (RatFunc.C ((∑ v : Fin 6,
      d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j) /
        (RatFunc.X - RatFunc.C (t (Sum.inr x)))) := fun x ↦ by
    have h := b65g_reg_frac (s := s) (k := 1) ((∑ v : Fin 6,
      d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j)
      (fun h ↦ hs ⟨Sum.inr x, h.symm⟩)
    rwa [pow_one] at h
  rw [b65q_qVector, b65g_eval_add (b65g_reg_principal t _ j hs) (b65g_reg_sum _ fun x _ ↦ hreg x),
    b65g_eval_principal t _ j hs, b65g_eval_sum _ fun x _ ↦ hreg x]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have h := b65g_eval_frac (s := s) (k := 1) ((∑ v : Fin 6,
      d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j)
      (fun h ↦ hs ⟨Sum.inr x, h.symm⟩)
  simpa only [pow_one] using h

section Linear
variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
  (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
  (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ)

/-- The zero coefficient vector represents the zero map. -/
theorem b65g_rRep_zero : b65g_rRepresents D t a b poles Y (b65q_principal poles 0) 0 := by
  have h : b65q_principal poles 0 = 0 := by funext j; simp [b65q_principal]
  intro v u _
  simp [h, b65g_rForm, b65q_eval, ← Pi.zero_def]

/-- r-representation is additive. -/
theorem b65g_rRep_add (cv cv' : Fin 36 → ℂ)
    (φ φ' : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
    (h : b65g_rRepresents D t a b poles Y (b65q_principal poles cv) φ)
    (h' : b65g_rRepresents D t a b poles Y (b65q_principal poles cv') φ') :
    b65g_rRepresents D t a b poles Y (b65q_principal poles (cv + cv')) (φ + φ') := by
  intro v u hu
  have hs := b65g_good_sFun hu
  rw [LinearMap.add_apply, Pi.add_apply, h v u hu, h' v u hu]
  have he : (fun j ↦ b65q_eval (b65q_principal poles (cv + cv') j) (b65g_sFun D t a b u.1)) =
      (fun j ↦ b65q_eval (b65q_principal poles cv j) (b65g_sFun D t a b u.1)) +
      (fun j ↦ b65q_eval (b65q_principal poles cv' j) (b65g_sFun D t a b u.1)) := by
    funext j
    simp only [Pi.add_apply, b65g_eval_principal _ _ _ hs, ← Finset.sum_add_distrib, add_div]
  simp only [b65g_rForm]
  rw [he, mulVec_add, dotProduct_add, add_mul]

/-- r-representation is homogeneous. -/
theorem b65g_rRep_smul (l : ℂ) (cv : Fin 36 → ℂ)
    (φ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
    (h : b65g_rRepresents D t a b poles Y (b65q_principal poles cv) φ) :
    b65g_rRepresents D t a b poles Y (b65q_principal poles (l • cv)) (l • φ) := by
  intro v u hu
  have hs := b65g_good_sFun hu
  rw [LinearMap.smul_apply, Pi.smul_apply, h v u hu]
  have he : (fun j ↦ b65q_eval (b65q_principal poles (l • cv) j) (b65g_sFun D t a b u.1)) =
      l • (fun j ↦ b65q_eval (b65q_principal poles cv j) (b65g_sFun D t a b u.1)) := by
    funext j
    simp only [Pi.smul_apply, b65g_eval_principal _ _ _ hs, smul_eq_mul, Finset.mul_sum,
      mul_div_assoc]
  simp only [b65g_rForm]
  rw [he, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- The zero q-coefficient vector represents the zero map. -/
theorem b65g_qRep_zero (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ) :
    b65g_qRepresents D t a b poles Y (b65q_qVector poles node w 0) 0 := by
  have h : b65q_qVector poles node w 0 = 0 := by funext j; simp [b65q_qVector, b65q_principal]
  intro v u _
  simp [h, b65g_qForm, b65q_eval, ← Pi.zero_def]

/-- q-representation is additive. -/
theorem b65g_qRep_add (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ) (dv dv' : Fin 48 → ℂ)
    (ψ ψ' : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
    (h : b65g_qRepresents D t a b poles Y (b65q_qVector poles node w dv) ψ)
    (h' : b65g_qRepresents D t a b poles Y (b65q_qVector poles node w dv') ψ') :
    b65g_qRepresents D t a b poles Y (b65q_qVector poles node w (dv + dv')) (ψ + ψ') := by
  intro v u hu
  have hs := b65g_good_sFun hu
  rw [LinearMap.add_apply, Pi.add_apply, h v u hu, h' v u hu]
  have he : (fun j ↦ b65q_eval (b65q_qVector poles node w (dv + dv') j) (b65g_sFun D t a b u.1)) =
      (fun j ↦ b65q_eval (b65q_qVector poles node w dv j) (b65g_sFun D t a b u.1)) +
      (fun j ↦ b65q_eval (b65q_qVector poles node w dv' j) (b65g_sFun D t a b u.1)) := by
    funext j
    simp only [Pi.add_apply, b65g_eval_qVector _ _ _ _ _ hs]
    rw [add_add_add_comm]
    congr 1
    · rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ add_div _ _ _
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [← add_div, ← add_mul, ← Finset.sum_add_distrib]
      congr 2
      exact Finset.sum_congr rfl fun _ _ ↦ add_mul _ _ _
  simp only [b65g_qForm]
  rw [he, mulVec_add, dotProduct_add, add_mul]

/-- q-representation is homogeneous. -/
theorem b65g_qRep_smul (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ) (l : ℂ) (dv : Fin 48 → ℂ)
    (ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
    (h : b65g_qRepresents D t a b poles Y (b65q_qVector poles node w dv) ψ) :
    b65g_qRepresents D t a b poles Y (b65q_qVector poles node w (l • dv)) (l • ψ) := by
  intro v u hu
  have hs := b65g_good_sFun hu
  rw [LinearMap.smul_apply, Pi.smul_apply, h v u hu]
  have he : (fun j ↦ b65q_eval (b65q_qVector poles node w (l • dv) j) (b65g_sFun D t a b u.1)) =
      l • (fun j ↦ b65q_eval (b65q_qVector poles node w dv j) (b65g_sFun D t a b u.1)) := by
    funext j
    simp only [Pi.smul_apply, b65g_eval_qVector _ _ _ _ _ hs, smul_eq_mul, Finset.mul_sum,
      mul_add, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ ↦ by ring
    · exact Finset.sum_congr rfl fun _ _ ↦ by
        rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp only [b65g_qForm]
  rw [he, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

end Linear

end HodgeLean.Foundations.Program
