import HodgeLean.Foundations.Program.KernelFramesFamilySystems

/-! # B6-5 stage 5d, family part: inverse-block frames of a system

For a system whose selected block is invertible, the inverse-block frame solves the selected
rows, has the identity as free-coordinate block, spans a space containing the full kernel, and
lies in the full kernel exactly when that kernel has dimension three; every independent triple
of kernel vectors is the frame times its own invertible free-coordinate block, uniquely.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

section
variable {m n p : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) (rows : Fin p → Fin m) (piv : Fin p → Fin n)
  (free : Fin 3 → Fin n)

/-- The inverse-block frame of a system with selected rows, pivot and free columns. -/
def b65q_ibFrame : Matrix (Fin n) (Fin 3) ℂ := fun i f ↦
  (∑ a : Fin 3, if i = free a then (if a = f then 1 else 0) else 0) -
    ∑ a : Fin p, if i = piv a then
      ((S.submatrix rows piv)⁻¹ * S.submatrix rows free) a f else 0

variable (hbij : Function.Bijective (Sum.elim piv free))
include hbij

theorem b65q_ibFrame_free (a f : Fin 3) :
    b65q_ibFrame S rows piv free (free a) f = if a = f then 1 else 0 := by
  have hfi : Function.Injective free := fun a b h ↦ by
    have := hbij.1 (a₁ := Sum.inr a) (a₂ := Sum.inr b) h; simpa using this
  have hd : ∀ b, free a ≠ piv b := fun b h ↦ by
    have := hbij.1 (a₁ := Sum.inr a) (a₂ := Sum.inl b) h; simp at this
  simp only [b65q_ibFrame]
  rw [Finset.sum_eq_zero fun b _ ↦ if_neg (hd b), sub_zero,
    Finset.sum_eq_single a (fun b _ hb ↦ if_neg fun h ↦ hb (hfi h).symm) (by simp), if_pos rfl]

theorem b65q_ibFrame_piv (b : Fin p) (f : Fin 3) :
    b65q_ibFrame S rows piv free (piv b) f =
      -((S.submatrix rows piv)⁻¹ * S.submatrix rows free) b f := by
  have hpi : Function.Injective piv := fun a b h ↦ by
    have := hbij.1 (a₁ := Sum.inl a) (a₂ := Sum.inl b) h; simpa using this
  have hd : ∀ a, piv b ≠ free a := fun a h ↦ by
    have := hbij.1 (a₁ := Sum.inl b) (a₂ := Sum.inr a) h; simp at this
  simp only [b65q_ibFrame]
  rw [Finset.sum_eq_zero fun a _ ↦ if_neg (hd a), zero_sub,
    Finset.sum_eq_single b (fun a _ ha ↦ if_neg fun h ↦ ha (hpi h).symm) (by simp), if_pos rfl]

theorem b65q_sum_split (g : Fin n → ℂ) :
    ∑ i, g i = ∑ b : Fin p, g (piv b) + ∑ a : Fin 3, g (free a) := by
  rw [← Equiv.sum_comp (Equiv.ofBijective _ hbij), Fintype.sum_sum_type]
  rfl

variable (hdet : (S.submatrix rows piv).det ≠ 0)
include hdet

theorem b65q_ibFrame_rows : S.submatrix rows id * b65q_ibFrame S rows piv free = 0 := by
  ext r f
  rw [Matrix.mul_apply, b65q_sum_split piv free hbij]
  simp only [submatrix_apply, id, b65q_ibFrame_free S rows piv free hbij,
    b65q_ibFrame_piv S rows piv free hbij, Matrix.zero_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_neg, Finset.sum_neg_distrib]
  have h := congrFun (congrFun (show S.submatrix rows piv * ((S.submatrix rows piv)⁻¹ *
      S.submatrix rows free) = S.submatrix rows free by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul]) r) f
  rw [Matrix.mul_apply] at h
  simp only [submatrix_apply] at h
  rw [h, neg_add_cancel]

theorem b65q_ibFrame_decomp (c : Fin n → ℂ) (hc : S.submatrix rows id *ᵥ c = 0) :
    c = b65q_ibFrame S rows piv free *ᵥ fun a ↦ c (free a) := by
  set F := b65q_ibFrame S rows piv free
  set w : Fin n → ℂ := c - F *ᵥ fun a ↦ c (free a) with hw
  have hFr := b65q_ibFrame_rows S rows piv free hbij hdet
  have hwr : S.submatrix rows id *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_sub, hc, Matrix.mulVec_mulVec, hFr, Matrix.zero_mulVec, sub_zero]
  have hwf : ∀ a, w (free a) = 0 := by
    intro a
    simp only [hw, Pi.sub_apply, Matrix.mulVec, dotProduct, F,
      b65q_ibFrame_free S rows piv free hbij, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  have hwp : (fun b ↦ w (piv b)) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    ext r
    have := congrFun hwr r
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, submatrix_apply, id] at this ⊢
    rw [b65q_sum_split piv free hbij] at this
    simpa [hwf] using this
  have hw0 : w = 0 := by
    ext k
    obtain ⟨x, rfl⟩ := hbij.2 k
    rcases x with b | a
    · exact congrFun hwp b
    · exact hwf a
  rw [hw, sub_eq_zero] at hw0
  exact hw0

theorem b65q_ibFrame_ker_le :
    LinearMap.ker S.mulVecLin ≤
      Submodule.span ℂ (Set.range fun f : Fin 3 ↦ fun i ↦ b65q_ibFrame S rows piv free i f) := by
  intro c hc
  have hc' : S *ᵥ c = 0 := hc
  have hR : S.submatrix rows id *ᵥ c = 0 := by
    ext r; have := congrFun hc' (rows r); simpa [Matrix.mulVec, dotProduct] using this
  rw [b65q_ibFrame_decomp S rows piv free hbij hdet c hR]
  have : (b65q_ibFrame S rows piv free *ᵥ fun a ↦ c (free a)) =
      ∑ f : Fin 3, c (free f) • fun i ↦ b65q_ibFrame S rows piv free i f := by
    ext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun f _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)

end

section
variable {m n p : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) (rows : Fin p → Fin m) (piv : Fin p → Fin n)
  (free : Fin 3 → Fin n) (hbij : Function.Bijective (Sum.elim piv free))
include hbij

theorem b65q_ibFrame_linInd :
    LinearIndependent ℂ (fun f : Fin 3 ↦ fun i ↦ b65q_ibFrame S rows piv free i f) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have := congrFun hg (free a)
  simpa [Finset.sum_apply, b65q_ibFrame_free S rows piv free hbij] using this

theorem b65q_ibFrame_free_block :
    (b65q_ibFrame S rows piv free).submatrix free id = 1 := by
  ext a f; simp [b65q_ibFrame_free S rows piv free hbij, Matrix.one_apply]

variable (hdet : (S.submatrix rows piv).det ≠ 0)
include hdet

theorem b65q_ibFrame_iff :
    S * b65q_ibFrame S rows piv free = 0 ↔ Module.finrank ℂ (LinearMap.ker S.mulVecLin) = 3 := by
  set V := Submodule.span ℂ (Set.range fun f : Fin 3 ↦ fun i ↦ b65q_ibFrame S rows piv free i f)
  have hV : Module.finrank ℂ V = 3 := by
    rw [finrank_span_eq_card (b65q_ibFrame_linInd S rows piv free hbij), Fintype.card_fin]
  have hle := b65q_ibFrame_ker_le S rows piv free hbij hdet
  constructor
  · intro h
    have hge : V ≤ LinearMap.ker S.mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨f, rfl⟩
      show S *ᵥ _ = 0
      ext r; have := congrFun (congrFun h r) f
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    rw [le_antisymm hle hge, hV]
  · intro h
    have heq : LinearMap.ker S.mulVecLin = V :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [h, hV])
    ext r f
    have hf : (fun i ↦ b65q_ibFrame S rows piv free i f) ∈ LinearMap.ker S.mulVecLin := by
      rw [heq]; exact Submodule.subset_span ⟨f, rfl⟩
    have := congrFun (show S *ᵥ _ = 0 from hf) r
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem b65q_ibFrame_change (c : Matrix (Fin n) (Fin 3) ℂ) (hc : S * c = 0)
    (hli : LinearIndependent ℂ (fun f : Fin 3 ↦ fun i ↦ c i f)) :
    IsUnit (c.submatrix free id) ∧ c = b65q_ibFrame S rows piv free * c.submatrix free id ∧
      ∀ M : Matrix (Fin 3) (Fin 3) ℂ, c = b65q_ibFrame S rows piv free * M →
        M = c.submatrix free id := by
  have hcol : ∀ f, c = c → S.submatrix rows id *ᵥ (fun i ↦ c i f) = 0 := fun f _ ↦ by
    ext r; have := congrFun (congrFun hc (rows r)) f
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hdec : c = b65q_ibFrame S rows piv free * c.submatrix free id := by
    ext i f
    have := congrFun (b65q_ibFrame_decomp S rows piv free hbij hdet _ (hcol f rfl)) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  refine ⟨?_, hdec, fun M hM ↦ ?_⟩
  · rw [← Matrix.mulVec_injective_iff_isUnit]
    intro v w hvw
    have h1 : c *ᵥ v = c *ᵥ w := by
      rw [hdec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvw]
    have h2 : ∑ f, (v - w) f • (fun i ↦ c i f) = 0 := by
      ext i; have := congrFun h1 i
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply]
      rw [← sub_eq_zero.mpr this, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun f _ ↦ by ring
    have := Fintype.linearIndependent_iff.mp hli _ h2
    funext f; exact sub_eq_zero.mp (this f)
  · rw [hM, Matrix.submatrix_mul _ _ _ id _ (Function.bijective_id),
      b65q_ibFrame_free_block S rows piv free hbij]
    simp

end

theorem b65q_rFrame_eq (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (θ : ℂ) : b65q_rFrame p R θ =
      b65q_ibFrame (b65q_rFamily p R θ) b65k_rRows b65k_rPivot b65k_rFree := rfl

theorem b65q_qFrame_eq (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (θ : ℂ) : b65q_qFrame p R θ =
      b65q_ibFrame (b65q_qFamily p R θ) b65k_qRows b65k_qPivot b65k_qFree := rfl

end HodgeLean.Foundations.Program
