import HodgeLean.Foundations.Singular.CupOneFaces

/-!
# Steenrod cup-one and its differential identity

Cup-one is constructed in all positive input degrees over every commutative
ring. The full differential identity follows by partitioning the alternating
face sums, cancelling adjacent seams, and identifying the two surviving
endpoints with the Alexander–Whitney cup orders. A separate bidegree `(1,1)`
calculation checks the sign. `GradedComm.lean` descends this identity to cohomology.
HC no distance; AV milestone no distance. S6 retires nothing alone.
-/

noncomputable section
open CategoryTheory Limits AlgebraicTopology.Simplicial
open scoped Simplicial
open Finset
namespace HodgeLean.Foundations.Singular
attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData
variable {R : Type} [CommRing R] (Y : TopCat.{0})

private def ofValues (n : ℕ) (f : (TopCat.toSSet.obj Y) _⦋n⦌ → R) :
    Cochain R (TopCat.toSSet.obj Y) n :=
  ((TopCat.toSSet.obj Y).isColimitChainComplexXCofan (ModuleCat.of R R) n).desc
    (Cofan.mk _ fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton R R (f σ))) |>.hom

private theorem ofValues_apply (n : ℕ) (f : (TopCat.toSSet.obj Y) _⦋n⦌ → R)
    (σ : (TopCat.toSSet.obj Y) _⦋n⦌) : ofValues Y n f (chainOfSimplex R σ) = f σ := by
  have h := (TopCat.toSSet.obj Y).isColimitChainComplexXCofan (ModuleCat.of R R) n |>.fac
    (Cofan.mk _ fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton R R (f τ))) ⟨σ⟩
  have he := ConcreteCategory.congr_hom h (1 : R)
  change ofValues Y n f (chainOfSimplex R σ) = (1 : R) • f σ at he
  simpa only [one_smul] using he

/-- Steenrod cup-one on positive-degree singular cochains. The indices `p`, `q`
are one less than the input degrees; the output degree is `p + q + 1`.
Source: Steenrod, *Products of cocycles and extensions of mappings*, Ann. Math. 48
(1947), 290–320, cup-one construction; explicit convention in Porter–Suciu, equation (4.5).
-/
def cupOneCochain (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
    (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1)) :
    Cochain R (TopCat.toSSet.obj Y) (p + q + 1) :=
  ofValues Y (p + q + 1) fun σ =>
    ∑ j : Fin (p + 1), (-1 : R) ^ ((p + 1 - j.val) * (q + 2)) *
      φ (chainOfSimplex R ((TopCat.toSSet.obj Y).map (cupOneOuterInclusion p q j).op σ)) *
      ψ (chainOfSimplex R ((TopCat.toSSet.obj Y).map (cupOneInnerInclusion p q j).op σ))

/-- Evaluation of cup-one is the signed sum over the overlapping interval faces.
Source: Steenrod (1947), cup-one construction; Porter–Suciu, equation (4.5).
-/
theorem cupOneCochain_apply_simplex (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
    (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1))
    (σ : (TopCat.toSSet.obj Y) _⦋p + q + 1⦌) :
    cupOneCochain Y p q φ ψ (chainOfSimplex R σ) =
      ∑ j : Fin (p + 1), (-1 : R) ^ ((p + 1 - j.val) * (q + 2)) *
        φ (chainOfSimplex R ((TopCat.toSSet.obj Y).map (cupOneOuterInclusion p q j).op σ)) *
        ψ (chainOfSimplex R ((TopCat.toSSet.obj Y).map (cupOneInnerInclusion p q j).op σ)) :=
  ofValues_apply Y _ _ σ

/-- In bidegree `(1,1)`, cup-one multiplies the values on the same edge.
Source: Steenrod, *Products of cocycles and extensions of mappings*, Ann. Math. 48
(1947), 290–320, cup-one construction; explicit convention in Porter–Suciu, equation (4.5).
-/
theorem cupOneCochain_apply_one_one (φ ψ : Cochain R (TopCat.toSSet.obj Y) 1)
    (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    cupOneCochain Y 0 0 φ ψ (chainOfSimplex R σ) =
      φ (chainOfSimplex R σ) * ψ (chainOfSimplex R σ) := by
  have ho : cupOneOuterInclusion 0 0 0 = 𝟙 _ := by ext k; fin_cases k <;> rfl
  have hi : cupOneInnerInclusion 0 0 0 = 𝟙 _ := by ext k; fin_cases k <;> rfl
  simp [cupOneCochain, ofValues_apply, ho, hi]

example (φ ψ : Cochain R (TopCat.toSSet.obj Y) 1)
    (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    cupOneCochain Y 0 0 φ ψ (chainOfSimplex R σ) =
      φ (chainOfSimplex R σ) * ψ (chainOfSimplex R σ) :=
  cupOneCochain_apply_one_one Y φ ψ σ


private theorem extCochain {X : SSet.{0}} {n : ℕ} (φ ψ : Cochain R X n)
    (h : ∀ σ : X _⦋n⦌, φ (chainOfSimplex R σ) = ψ (chainOfSimplex R σ)) : φ = ψ := by
  have hc : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : (X.ιChainComplex (R := ModuleCat.of R R) σ).hom a =
        a • chainOfSimplex R σ := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change φ ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

/-- Cup-one is additive in its first argument.
Source: Steenrod (1947), bilinearity of the cup-one construction.
-/
theorem cupOneCochain_add_left (p q : ℕ)
    (φ χ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
    (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1)) :
    cupOneCochain Y p q (φ + χ) ψ =
      cupOneCochain Y p q φ ψ + cupOneCochain Y p q χ ψ := by
  apply extCochain
  intro σ
  simp only [cupOneCochain_apply_simplex, LinearMap.add_apply,
    mul_add, add_mul, Finset.sum_add_distrib]

/-- Cup-one is additive in its second argument.
Source: Steenrod (1947), bilinearity of the cup-one construction.
-/
theorem cupOneCochain_add_right (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
    (ψ χ : Cochain R (TopCat.toSSet.obj Y) (q + 1)) :
    cupOneCochain Y p q φ (ψ + χ) =
      cupOneCochain Y p q φ ψ + cupOneCochain Y p q φ χ := by
  apply extCochain
  intro σ
  simp only [cupOneCochain_apply_simplex, LinearMap.add_apply,
    mul_add, Finset.sum_add_distrib]

/-- Cup-one is linear in scalars in its first argument.
Source: Steenrod (1947), bilinearity of the cup-one construction.
-/
theorem cupOneCochain_smul_left (p q : ℕ) (r : R)
    (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
    (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1)) :
    cupOneCochain Y p q (r • φ) ψ = r • cupOneCochain Y p q φ ψ := by
  apply extCochain
  intro σ
  simp only [cupOneCochain_apply_simplex, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Cup-one is linear in scalars in its second argument.
Source: Steenrod (1947), bilinearity of the cup-one construction.
-/
theorem cupOneCochain_smul_right (p q : ℕ) (r : R)
    (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
    (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1)) :
    cupOneCochain Y p q φ (r • ψ) = r • cupOneCochain Y p q φ ψ := by
  apply extCochain
  intro σ
  simp only [cupOneCochain_apply_simplex, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pullback along continuous maps preserves cup-one.
Source: Steenrod (1947), Theorem 3.1, naturality of cup-i products.
-/
theorem cupOneCochain_naturality {Z : TopCat.{0}} (f : Z ⟶ Y) (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
    (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1)) :
    cochainMap R (TopCat.toSSet.map f) (p + q + 1) (cupOneCochain Y p q φ ψ) =
      cupOneCochain Z p q (cochainMap R (TopCat.toSSet.map f) (p + 1) φ)
        (cochainMap R (TopCat.toSSet.map f) (q + 1) ψ) := by
  apply extCochain
  intro σ
  simp only [cochainMap_apply, chainOfSimplex_map, cupOneCochain_apply_simplex]
  apply Finset.sum_congr rfl
  intro j _
  rw [(NatTrans.naturality_apply (TopCat.toSSet.map f)
    (cupOneOuterInclusion p q j).op σ),
    (NatTrans.naturality_apply (TopCat.toSSet.map f) (cupOneInnerInclusion p q j).op σ)]

private theorem sum_split_two {A : Type*} [AddCommGroup A] (f : ℕ → A)
    (N j : ℕ) (hj : j + 2 ≤ N) :
    ∑ k ∈ range N, f k =
      (∑ k ∈ range j, f k) + f j + f (j + 1) +
        ∑ k ∈ range (N - (j + 2)), f (j + 2 + k) := by
  have h := sum_range_add f (j + 2) (N - (j + 2))
  rw [Nat.add_sub_of_le hj] at h
  rw [h, sum_range_succ f (j + 1), sum_range_succ f j]

private theorem sum_face_blocks {A : Type*} [AddCommGroup A]
    (p q : ℕ) (F G : ℕ → ℕ → A)
    (hA : ∀ j, j < p + 1 → F (j + 1) (j + 1) + G j 0 = 0)
    (hB : ∀ j, j < p + 1 → F j (j + 1) + G j (q + 2) = 0) :
    (∑ j ∈ range (p + 2), ∑ k ∈ range (p + 3), F j k) +
        (∑ j ∈ range (p + 1), ∑ l ∈ range (q + 3), G j l) =
      (∑ j ∈ range (p + 1),
        ((∑ k ∈ range (j + 1), F (j + 1) k) +
          (∑ l ∈ range (q + 1), G j (l + 1)) +
          ∑ k ∈ range (p + 1 - j), F j (j + 2 + k))) +
        F 0 0 + F (p + 1) (p + 2) := by
  have hF : (∑ j ∈ range (p + 2), ∑ k ∈ range (p + 3), F j k) =
      (∑ j ∈ range (p + 2), ∑ k ∈ range j, F j k) +
      (∑ j ∈ range (p + 2), F j j) +
      (∑ j ∈ range (p + 2), F j (j + 1)) +
      (∑ j ∈ range (p + 2), ∑ k ∈ range (p + 1 - j), F j (j + 2 + k)) := by
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    have hj' : j < p + 2 := mem_range.mp hj
    have he : p + 3 - (j + 2) = p + 1 - j := by omega
    simpa only [he] using sum_split_two (F j) (p + 3) j (by omega)
  have hE : (∑ j ∈ range (p + 2), ∑ k ∈ range j, F j k) =
      ∑ j ∈ range (p + 1), ∑ k ∈ range (j + 1), F (j + 1) k := by
    rw [sum_range_succ' (fun j => ∑ k ∈ range j, F j k) (p + 1)]
    simp
  have hL : (∑ j ∈ range (p + 2), ∑ k ∈ range (p + 1 - j), F j (j + 2 + k)) =
      ∑ j ∈ range (p + 1), ∑ k ∈ range (p + 1 - j), F j (j + 2 + k) := by
    rw [sum_range_succ (fun j => ∑ k ∈ range (p + 1 - j), F j (j + 2 + k)) (p + 1)]
    simp
  have hG : (∑ j ∈ range (p + 1), ∑ l ∈ range (q + 3), G j l) =
      (∑ j ∈ range (p + 1), ∑ l ∈ range (q + 1), G j (l + 1)) +
      (∑ j ∈ range (p + 1), G j 0) + (∑ j ∈ range (p + 1), G j (q + 2)) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rw [sum_range_succ (G j) (q + 2), sum_range_succ' (G j) (q + 1)]
  have hcA : (∑ j ∈ range (p + 1), F (j + 1) (j + 1)) =
      -(∑ j ∈ range (p + 1), G j 0) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← sum_add_distrib]
    exact sum_eq_zero fun j hj => hA j (mem_range.mp hj)
  have hcB : (∑ j ∈ range (p + 1), F j (j + 1)) =
      -(∑ j ∈ range (p + 1), G j (q + 2)) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← sum_add_distrib]
    exact sum_eq_zero fun j hj => hB j (mem_range.mp hj)
  rw [hF, hE, hL, hG, sum_range_succ' (fun j => F j j) (p + 1),
    sum_range_succ (fun j => F j (j + 1)) (p + 1), hcA, hcB]
  simp only [sum_add_distrib]
  abel

private theorem sum_reassemble {A : Type*} [AddCommGroup A]
    (p q : ℕ) (D F G : ℕ → ℕ → A)
    (hE : ∀ j, j < p + 1 → ∀ i, i ≤ j → D j i = F (j + 1) i)
    (hM : ∀ j, j < p + 1 → ∀ i, j < i → i ≤ j + q + 1 → D j i = G j (i - j))
    (hL : ∀ j, j < p + 1 → ∀ i, j + q + 1 < i → i < p + q + 3 →
      D j i = F j (i - q))
    (hA : ∀ j, j < p + 1 → F (j + 1) (j + 1) + G j 0 = 0)
    (hB : ∀ j, j < p + 1 → F j (j + 1) + G j (q + 2) = 0) :
    (∑ j ∈ range (p + 1), ∑ i ∈ range (p + q + 3), D j i) =
      (∑ j ∈ range (p + 2), ∑ k ∈ range (p + 3), F j k) +
        (∑ j ∈ range (p + 1), ∑ l ∈ range (q + 3), G j l) -
        F 0 0 - F (p + 1) (p + 2) := by
  have hrow (j : ℕ) (hj : j < p + 1) :
      (∑ i ∈ range (p + q + 3), D j i) =
        (∑ k ∈ range (j + 1), F (j + 1) k) +
        (∑ l ∈ range (q + 1), G j (l + 1)) +
        ∑ k ∈ range (p + 1 - j), F j (j + 2 + k) := by
    have hn : p + q + 3 = j + 1 + (q + 1 + (p + 1 - j)) := by omega
    have hs := sum_range_add (D j) (j + 1) (q + 1 + (p + 1 - j))
    rw [← hn, sum_range_add (fun k => D j (j + 1 + k)) (q + 1) (p + 1 - j)] at hs
    have he : (∑ k ∈ range (j + 1), D j k) =
        ∑ k ∈ range (j + 1), F (j + 1) k := by
      apply sum_congr rfl
      intro k hk
      exact hE j hj k (by have := mem_range.mp hk; omega)
    have hm : (∑ k ∈ range (q + 1), D j (j + 1 + k)) =
        ∑ k ∈ range (q + 1), G j (k + 1) := by
      apply sum_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      have h := hM j hj (j + 1 + k) (by omega) (by omega)
      simpa only [show j + 1 + k - j = k + 1 by omega] using h
    have hl : (∑ k ∈ range (p + 1 - j), D j (j + 1 + (q + 1 + k))) =
        ∑ k ∈ range (p + 1 - j), F j (j + 2 + k) := by
      apply sum_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      have h := hL j hj (j + 1 + (q + 1 + k)) (by omega) (by omega)
      simpa only [show j + 1 + (q + 1 + k) - q = j + 2 + k by omega] using h
    rw [hs, he, hm, hl]
    abel
  have hs := sum_face_blocks p q F G hA hB
  rw [hs]
  have hr : (∑ j ∈ range (p + 1), ∑ i ∈ range (p + q + 3), D j i) =
      ∑ j ∈ range (p + 1),
        ((∑ k ∈ range (j + 1), F (j + 1) k) +
        (∑ l ∈ range (q + 1), G j (l + 1)) +
        ∑ k ∈ range (p + 1 - j), F j (j + 2 + k)) :=
    sum_congr rfl fun j hj => hrow j (mem_range.mp hj)
  rw [hr]
  abel


private def leftStep (p q : ℕ) :
    SimplexCategory.mk (p + 1 + q + 1) ⟶ SimplexCategory.mk (p + q + 2) :=
  eqToHom (congrArg SimplexCategory.mk (by omega))

private theorem seam_outerA (p q : ℕ) (j : Fin (p + 1)) :
    SimplexCategory.δ j.succ.castSucc ≫ cupOneOuterInclusion (p + 1) q j.succ ≫
      leftStep p q = cupOneOuterInclusion p (q + 1) j := by
  ext k
  simp only [cupOneOuterInclusion, SimplexCategory.δ, leftStep,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  by_cases hk : k.val ≤ j.val
  · rw [Fin.succAbove_of_castSucc_lt]
    · change (if k.val ≤ j.val + 1 then k.val else k.val + q) =
        (if k.val ≤ j.val then k.val else k.val + (q + 1))
      split <;> omega
    · change k.val < j.val + 1
      omega
  · rw [Fin.succAbove_of_le_castSucc]
    · change (if k.val + 1 ≤ j.val + 1 then k.val + 1 else k.val + 1 + q) =
        (if k.val ≤ j.val then k.val else k.val + (q + 1))
      split <;> omega
    · change j.val + 1 ≤ k.val
      omega

private theorem seam_outerB (p q : ℕ) (j : Fin (p + 1)) :
    SimplexCategory.δ j.succ.castSucc ≫ cupOneOuterInclusion (p + 1) q j.castSucc ≫
      leftStep p q = cupOneOuterInclusion p (q + 1) j := by
  ext k
  simp only [cupOneOuterInclusion, SimplexCategory.δ, leftStep,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  by_cases hk : k.val ≤ j.val
  · rw [Fin.succAbove_of_castSucc_lt]
    · change (if k.val ≤ j.val then k.val else k.val + q) =
        (if k.val ≤ j.val then k.val else k.val + (q + 1))
      simp only [ite_eq_left hk]
    · change k.val < j.val + 1
      omega
  · rw [Fin.succAbove_of_le_castSucc]
    · change (if k.val + 1 ≤ j.val then k.val + 1 else k.val + 1 + q) =
        (if k.val ≤ j.val then k.val else k.val + (q + 1))
      split <;> omega
    · change j.val + 1 ≤ k.val
      omega

private theorem seam_innerA (p q : ℕ) (j : Fin (p + 1)) :
    cupOneInnerInclusion (p + 1) q j.succ ≫ leftStep p q =
      SimplexCategory.δ (0 : Fin (q + 3)) ≫ cupOneInnerInclusion p (q + 1) j := by
  ext k
  simp only [cupOneInnerInclusion, SimplexCategory.δ, leftStep,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  rw [Fin.succAbove_of_le_castSucc]
  · change j.val + 1 + k.val = j.val + (k.val + 1)
    omega
  · exact Fin.zero_le _

private theorem seam_innerB (p q : ℕ) (j : Fin (p + 1)) :
    cupOneInnerInclusion (p + 1) q j.castSucc ≫ leftStep p q =
      SimplexCategory.δ (Fin.last (q + 2)) ≫ cupOneInnerInclusion p (q + 1) j := by
  ext k
  simp only [cupOneInnerInclusion, SimplexCategory.δ, leftStep,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · exact Fin.castSucc_lt_last _

private theorem endpoint_outerB (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p + 2)) ≫
      cupOneOuterInclusion (p + 1) q (Fin.last (p + 1)) =
        frontInclusion (p + 1) (q + 1) := by
  ext k
  simp only [cupOneOuterInclusion, frontInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt]
  · change (if k.val ≤ p + 1 then k.val else k.val + q) = k.val
    exact ite_eq_left (by have hk : k.val < p + 2 := k.isLt; omega)
  · exact Fin.castSucc_lt_last _

private theorem endpoint_innerB (p q : ℕ) :
    cupOneInnerInclusion (p + 1) q (Fin.last (p + 1)) =
      backInclusion (p + 1) (q + 1) := by
  ext k
  rfl

private def swapStep (p q : ℕ) :
    SimplexCategory.mk (q + 1 + (p + 1)) ⟶ SimplexCategory.mk (p + q + 2) :=
  eqToHom (congrArg SimplexCategory.mk (by omega))

private theorem endpoint_outerA (p q : ℕ) :
    SimplexCategory.δ (0 : Fin (p + 3)) ≫ cupOneOuterInclusion (p + 1) q 0 ≫
      leftStep p q = backInclusion (q + 1) (p + 1) ≫ swapStep p q := by
  ext k
  simp only [cupOneOuterInclusion, backInclusion, SimplexCategory.δ, leftStep, swapStep,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  rw [Fin.succAbove_of_le_castSucc]
  · change (if k.val + 1 ≤ 0 then k.val + 1 else k.val + 1 + q) = q + 1 + k.val
    split <;> omega
  · exact Fin.zero_le _

private theorem endpoint_innerA (p q : ℕ) :
    cupOneInnerInclusion (p + 1) q 0 ≫ leftStep p q =
      frontInclusion (q + 1) (p + 1) ≫ swapStep p q := by
  ext k
  simp [cupOneInnerInclusion, frontInclusion, leftStep, swapStep,
    SimplexCategory.eqToHom_toOrderHom]
  rfl


private theorem sign_period (a b : ℕ) :
    (-1 : R) ^ (a + 2 * b) = (-1 : R) ^ a := by
  rw [pow_add, pow_mul]
  simp

private theorem sign_opposite (a b d : ℕ) (h : b + 1 = a + 2 * d) :
    (-1 : R) ^ a + (-1 : R) ^ b = 0 := by
  have hp : (-1 : R) ^ a = -(-1 : R) ^ b := by
    calc
      (-1 : R) ^ a = (-1 : R) ^ (a + 2 * d) := (sign_period a d).symm
      _ = (-1 : R) ^ (b + 1) := by rw [h]
      _ = -(-1 : R) ^ b := by rw [pow_succ, mul_neg_one]
  rw [hp]
  simp

private theorem sign_late (p q j i : ℕ) (hj : j < p + 1) (hi : q ≤ i) :
    (-1 : R) ^ ((p + 2 - j) * (q + 2) + (i - q)) =
      (-1 : R) ^ ((p + 1 - j) * (q + 2) + i) := by
  have hd : p + 2 - j = (p + 1 - j) + 1 := by omega
  have he : (p + 2 - j) * (q + 2) + (i - q) =
      ((p + 1 - j) * (q + 2) + i) + 2 * 1 := by
    rw [hd, Nat.add_mul, Nat.one_mul]
    omega
  rw [he, sign_period]

private theorem sign_middle (p q j i : ℕ) (hj : j < p + 1) (hi : j ≤ i) :
    (-1 : R) ^ (p + 1 + (p + 1 - j) * (q + 3) + (i - j)) =
      (-1 : R) ^ ((p + 1 - j) * (q + 2) + i) := by
  have he : p + 1 + (p + 1 - j) * (q + 3) + (i - j) =
      ((p + 1 - j) * (q + 2) + i) + 2 * (p + 1 - j) := by
    rw [show q + 3 = (q + 2) + 1 by omega, Nat.mul_add, Nat.mul_one]
    omega
  rw [he, sign_period]

private theorem sign_seam (p q j t : ℕ) (hj : j < p + 1) :
    (-1 : R) ^ ((p + 1 - j) * (q + 2) + j + 1 + t) +
      (-1 : R) ^ (p + 1 + (p + 1 - j) * (q + 3) + t) = 0 := by
  apply sign_opposite _ _ (p + 1 - j)
  rw [show q + 3 = (q + 2) + 1 by omega, Nat.mul_add, Nat.mul_one]
  omega


section GeneralIdentity
private theorem index_eq {n a : ℕ} [NeZero n] (h : a < n) :
    Fin.ofNat n a = ⟨a, h⟩ := Fin.ext (Nat.mod_eq_of_lt h)

private theorem index_coe {n : ℕ} [NeZero n] (i : Fin n) :
    Fin.ofNat n i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

private def termD (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
    (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1))
    (σ : (TopCat.toSSet.obj Y) _⦋p + q + 2⦌) (j i : ℕ) : R :=
  (-1 : R) ^ ((p + 1 - j) * (q + 2) + i) *
    φ (chainOfSimplex R ((TopCat.toSSet.obj Y).map
      (cupOneOuterInclusion p q (Fin.ofNat (p + 1) j) ≫
        SimplexCategory.δ (Fin.ofNat (p + q + 3) i)).op σ)) *
    ψ (chainOfSimplex R ((TopCat.toSSet.obj Y).map
      (cupOneInnerInclusion p q (Fin.ofNat (p + 1) j) ≫
        SimplexCategory.δ (Fin.ofNat (p + q + 3) i)).op σ))

private def termF (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
    (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1))
    (σ : (TopCat.toSSet.obj Y) _⦋p + q + 2⦌) (j k : ℕ) : R :=
  (-1 : R) ^ ((p + 2 - j) * (q + 2) + k) *
    φ (chainOfSimplex R ((TopCat.toSSet.obj Y).map
      (SimplexCategory.δ (Fin.ofNat (p + 3) k) ≫
        cupOneOuterInclusion (p + 1) q (Fin.ofNat (p + 2) j) ≫ leftStep p q).op σ)) *
    ψ (chainOfSimplex R ((TopCat.toSSet.obj Y).map
      (cupOneInnerInclusion (p + 1) q (Fin.ofNat (p + 2) j) ≫ leftStep p q).op σ))

private def termG (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
    (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1))
    (σ : (TopCat.toSSet.obj Y) _⦋p + q + 2⦌) (j l : ℕ) : R :=
  (-1 : R) ^ (p + 1 + (p + 1 - j) * (q + 3) + l) *
    φ (chainOfSimplex R ((TopCat.toSSet.obj Y).map
      (cupOneOuterInclusion p (q + 1) (Fin.ofNat (p + 1) j)).op σ)) *
    ψ (chainOfSimplex R ((TopCat.toSSet.obj Y).map
      (SimplexCategory.δ (Fin.ofNat (q + 3) l) ≫
        cupOneInnerInclusion p (q + 1) (Fin.ofNat (p + 1) j)).op σ))

variable (p q : ℕ)
  (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1))
  (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1))
  (σ : (TopCat.toSSet.obj Y) _⦋p + q + 2⦌)

private theorem term_early (j i : ℕ) (hj : j < p + 1) (hi : i ≤ j) :
    termD Y p q φ ψ σ j i = termF Y p q φ ψ σ (j + 1) i := by
  have hiN : i < p + q + 3 := by omega
  have hiP : i < p + 3 := by omega
  have hjP : j + 1 < p + 2 := by omega
  have ho := cupOneOuterInclusion_comp_earlyFace p q ⟨j, hj⟩ ⟨i, hiN⟩ hi
  have hn := cupOneInnerInclusion_comp_earlyFace p q ⟨j, hj⟩ ⟨i, hiN⟩ hi
  simp only [termD, termF, index_eq hj, index_eq hiN, index_eq hiP, index_eq hjP,
    show p + 2 - (j + 1) = p + 1 - j by omega]
  rw [ho, hn]
  rfl

private theorem term_late (j i : ℕ) (hj : j < p + 1)
    (hi : j + q + 1 < i) (hiN : i < p + q + 3) :
    termD Y p q φ ψ σ j i = termF Y p q φ ψ σ j (i - q) := by
  have hjP : j < p + 2 := by omega
  have hiP : i - q < p + 3 := by omega
  have ho := cupOneOuterInclusion_comp_lateFace p q ⟨j, hj⟩ ⟨i, hiN⟩ hi
  have hn := cupOneInnerInclusion_comp_lateFace p q ⟨j, hj⟩ ⟨i, hiN⟩ hi
  simp only [termD, termF, index_eq hj, index_eq hiN, index_eq hiP, index_eq hjP]
  rw [ho, hn, sign_late p q j i hj (by omega)]
  rfl

private theorem term_middle (j i : ℕ) (hj : j < p + 1)
    (h₁ : j < i) (h₂ : i ≤ j + q + 1) :
    termD Y p q φ ψ σ j i = termG Y p q φ ψ σ j (i - j) := by
  have hiN : i < p + q + 3 := by omega
  have hiQ : i - j < q + 3 := by omega
  have ho : cupOneOuterInclusion p q ⟨j, hj⟩ ≫ SimplexCategory.δ ⟨i, hiN⟩ =
      cupOneOuterInclusion p (q + 1) ⟨j, hj⟩ := by
    simpa using cupOneOuterInclusion_comp_middleFace p q ⟨j, hj⟩ ⟨i, hiN⟩ h₁ h₂
  have hn : cupOneInnerInclusion p q ⟨j, hj⟩ ≫ SimplexCategory.δ ⟨i, hiN⟩ =
      SimplexCategory.δ ⟨i - j, hiQ⟩ ≫ cupOneInnerInclusion p (q + 1) ⟨j, hj⟩ := by
    simpa using cupOneInnerInclusion_comp_middleFace p q ⟨j, hj⟩ ⟨i, hiN⟩ h₁ h₂
  simp only [termD, termG, index_eq hj, index_eq hiN, index_eq hiQ]
  rw [ho, hn, sign_middle p q j i hj (by omega)]

private theorem term_seamA (j : ℕ) (hj : j < p + 1) :
    termF Y p q φ ψ σ (j + 1) (j + 1) + termG Y p q φ ψ σ j 0 = 0 := by
  have hjP : j + 1 < p + 2 := by omega
  have hkP : j + 1 < p + 3 := by omega
  simp only [termF, termG, index_eq hj, index_eq hjP, index_eq hkP,
    index_eq (show 0 < q + 3 by omega),
    show p + 2 - (j + 1) = p + 1 - j by omega, Nat.add_zero]
  have ho := seam_outerA p q ⟨j, hj⟩
  have hn := seam_innerA p q ⟨j, hj⟩
  simp only [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE] at ho hn
  rw [ho, hn]
  simp only [Fin.zero_eta]
  rw [← add_mul, ← add_mul]
  have hs := sign_seam (R := R) p q j 0 hj
  simp only [Nat.add_zero, Nat.add_assoc] at hs
  simp only [Nat.add_assoc]
  rw [hs, zero_mul, zero_mul]

private theorem term_seamB (j : ℕ) (hj : j < p + 1) :
    termF Y p q φ ψ σ j (j + 1) + termG Y p q φ ψ σ j (q + 2) = 0 := by
  have hjP : j < p + 2 := by omega
  have hkP : j + 1 < p + 3 := by omega
  have hlQ : q + 2 < q + 3 := by omega
  simp only [termF, termG, index_eq hj, index_eq hjP, index_eq hkP, index_eq hlQ]
  have ho := seam_outerB p q ⟨j, hj⟩
  have hn := seam_innerB p q ⟨j, hj⟩
  simp only [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE] at ho hn
  rw [ho, hn]
  simp only [Fin.last]
  have he : (p + 2 - j) * (q + 2) + (j + 1) =
      (p + 1 - j) * (q + 2) + j + 1 + (q + 2) := by
    rw [show p + 2 - j = (p + 1 - j) + 1 by omega, Nat.add_mul, Nat.one_mul]
    omega
  rw [he, ← add_mul, ← add_mul, sign_seam p q j (q + 2) hj, zero_mul, zero_mul]

private theorem eval_D :
    coboundary R (p + q + 1) (cupOneCochain Y p q φ ψ) (chainOfSimplex R σ) =
      ∑ j ∈ Finset.range (p + 1), ∑ i ∈ Finset.range (p + q + 3),
        termD Y p q φ ψ σ j i := by
  simp only [← Fin.sum_univ_eq_sum_range]
  rw [coboundary_chainOfSimplex]
  simp only [cupOneCochain_apply_simplex, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [termD, index_coe, SimplicialObject.δ, ← Functor.map_comp_apply,
    ← op_comp, pow_add]
  ring

private theorem eval_F :
    (cupOneCochain Y (p + 1) q (coboundary R (p + 1) φ) ψ).comp
      (reassocChain R p (q + 1)) (chainOfSimplex R σ) =
      ∑ j ∈ Finset.range (p + 2), ∑ k ∈ Finset.range (p + 3),
        termF Y p q φ ψ σ j k := by
  simp only [← Fin.sum_univ_eq_sum_range, LinearMap.comp_apply, reassocChain,
    XIsoOfEq_chainOfSimplex, cupOneCochain_apply_simplex,
    coboundary_chainOfSimplex, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [termF, index_coe, SimplicialObject.δ, ← Functor.map_comp_apply,
    ← op_comp, pow_add, leftStep]
  ring

private theorem eval_G :
    (-1 : R) ^ (p + 1) *
      cupOneCochain Y p (q + 1) φ (coboundary R (q + 1) ψ) (chainOfSimplex R σ) =
      ∑ j ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 3),
        termG Y p q φ ψ σ j l := by
  simp only [← Fin.sum_univ_eq_sum_range, cupOneCochain_apply_simplex,
    coboundary_chainOfSimplex, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  simp only [termG, index_coe, SimplicialObject.δ, ← Functor.map_comp_apply,
    ← op_comp, pow_add]
  ring


private theorem eval_endpointB :
    termF Y p q φ ψ σ (p + 1) (p + 2) =
      -((-1 : R) ^ (p + q + 1) *
        ((cupCochain Y (p + 1) (q + 1) φ ψ).comp
          (reassocChain R p (q + 1))) (chainOfSimplex R σ)) := by
  simp only [termF, index_eq (show p + 1 < p + 2 by omega),
    index_eq (show p + 2 < p + 3 by omega)]
  have ho := endpoint_outerB p q
  have hn := endpoint_innerB p q
  simp only [Fin.last] at ho hn
  rw [← Category.assoc, ho, hn]
  simp only [LinearMap.comp_apply, reassocChain, XIsoOfEq_chainOfSimplex,
    cupCochain_apply_simplex, frontFace, backFace,
    ← Functor.map_comp_apply, ← op_comp]
  have hs : (-1 : R) ^ ((p + 2 - (p + 1)) * (q + 2) + (p + 2)) =
      -(-1 : R) ^ (p + q + 1) := by
    rw [show (p + 2 - (p + 1)) * (q + 2) + (p + 2) = (p + q + 2) + 2 * 1 by
      simp only [show p + 2 - (p + 1) = 1 by omega, Nat.one_mul]; omega,
      sign_period, show p + q + 2 = (p + q + 1) + 1 by omega, pow_succ, mul_neg_one]
  rw [hs]
  simp only [leftStep, neg_mul, mul_assoc]

private theorem eval_endpointA :
    termF Y p q φ ψ σ 0 0 =
      -((-1 : R) ^ ((p + 1) * (q + 1) + (p + 1) + (q + 1)) *
        ((cupCochain Y (q + 1) (p + 1) ψ φ).comp
          (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq
            (by omega : p + q + 2 = q + 1 + (p + 1))).hom.hom)
          (chainOfSimplex R σ)) := by
  simp only [termF, index_eq (show 0 < p + 2 by omega),
    index_eq (show 0 < p + 3 by omega), Fin.zero_eta]
  rw [endpoint_outerA, endpoint_innerA]
  simp only [LinearMap.comp_apply, XIsoOfEq_chainOfSimplex,
    cupCochain_apply_simplex, frontFace, backFace,
    ← Functor.map_comp_apply, ← op_comp]
  have hs : (-1 : R) ^ ((p + 2 - 0) * (q + 2) + 0) =
      -(-1 : R) ^ ((p + 1) * (q + 1) + (p + 1) + (q + 1)) := by
    rw [show (p + 2 - 0) * (q + 2) + 0 =
      ((p + 1) * (q + 1) + (p + 1) + (q + 1)) + 1 by simp only [Nat.sub_zero]; ring,
      pow_succ, mul_neg_one]
  rw [hs]
  simp only [swapStep]
  ring

/-- Steenrod's cup-one differential identity in all positive input degrees.
Source: Steenrod, *Products of cocycles and extensions of mappings*, Ann. Math. 48
(1947), 290–320; sign convention as in Porter–Suciu, equation (4.5).
-/
theorem coboundary_cupOneCochain :
    coboundary R (p + q + 1) (cupOneCochain Y p q φ ψ) =
      (-1 : R) ^ (p + q + 1) •
        (cupCochain Y (p + 1) (q + 1) φ ψ).comp (reassocChain R p (q + 1)) +
      (-1 : R) ^ ((p + 1) * (q + 1) + (p + 1) + (q + 1)) •
        (cupCochain Y (q + 1) (p + 1) ψ φ).comp
          (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq
            (by omega : p + q + 2 = q + 1 + (p + 1))).hom.hom +
      (cupOneCochain Y (p + 1) q (coboundary R (p + 1) φ) ψ).comp
        (reassocChain R p (q + 1)) +
      (-1 : R) ^ (p + 1) • cupOneCochain Y p (q + 1) φ (coboundary R (q + 1) ψ) := by
  apply extCochain
  intro τ
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [eval_D, eval_F, eval_G]
  rw [sum_reassemble p q (termD Y p q φ ψ τ) (termF Y p q φ ψ τ)
    (termG Y p q φ ψ τ)
    (fun j hj i hi => term_early Y p q φ ψ τ j i hj hi)
    (fun j hj i h₁ h₂ => term_middle Y p q φ ψ τ j i hj h₁ h₂)
    (fun j hj i h₁ h₂ => term_late Y p q φ ψ τ j i hj h₁ h₂) (term_seamA Y p q φ ψ τ) (term_seamB Y p q φ ψ τ)]
  rw [eval_endpointA, eval_endpointB]
  abel

example :
    coboundary R (p + q + 1) (cupOneCochain Y p q φ ψ) =
      (-1 : R) ^ (p + q + 1) •
        (cupCochain Y (p + 1) (q + 1) φ ψ).comp (reassocChain R p (q + 1)) +
      (-1 : R) ^ ((p + 1) * (q + 1) + (p + 1) + (q + 1)) •
        (cupCochain Y (q + 1) (p + 1) ψ φ).comp
          (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq
            (by omega : p + q + 2 = q + 1 + (p + 1))).hom.hom +
      (cupOneCochain Y (p + 1) q (coboundary R (p + 1) φ) ψ).comp
        (reassocChain R p (q + 1)) +
      (-1 : R) ^ (p + 1) • cupOneCochain Y p (q + 1) φ (coboundary R (q + 1) ψ) :=
  coboundary_cupOneCochain Y p q φ ψ

end GeneralIdentity

private theorem front11 : frontInclusion 1 1 = SimplexCategory.δ (2 : Fin 3) := by
  ext i
  fin_cases i <;> rfl

private theorem back11 : backInclusion 1 1 = SimplexCategory.δ (0 : Fin 3) := by
  ext i
  fin_cases i <;> rfl

private theorem cupOne_eval_two_one (φ : Cochain R (TopCat.toSSet.obj Y) 2)
    (ψ : Cochain R (TopCat.toSSet.obj Y) 1) (σ : (TopCat.toSSet.obj Y) _⦋2⦌) :
    cupOneCochain Y 1 0 φ ψ (chainOfSimplex R σ) =
      φ (chainOfSimplex R σ) *
        (ψ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 2 σ)) +
          ψ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 0 σ))) := by
  have ho (j : Fin 2) : cupOneOuterInclusion 1 0 j = 𝟙 _ := by
    ext i
    fin_cases j <;> fin_cases i <;> rfl
  have hi0 : cupOneInnerInclusion 1 0 0 = SimplexCategory.δ (2 : Fin 3) := by
    ext i
    fin_cases i <;> rfl
  have hi1 : cupOneInnerInclusion 1 0 1 = SimplexCategory.δ (0 : Fin 3) := by
    ext i
    fin_cases i <;> rfl
  simp [cupOneCochain, ofValues_apply, Fin.sum_univ_succ, ho, hi0, hi1, mul_add,
    SimplicialObject.δ]

private theorem cupOne_eval_one_two (φ : Cochain R (TopCat.toSSet.obj Y) 1)
    (ψ : Cochain R (TopCat.toSSet.obj Y) 2) (σ : (TopCat.toSSet.obj Y) _⦋2⦌) :
    cupOneCochain Y 0 1 φ ψ (chainOfSimplex R σ) =
      -φ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 1 σ)) * ψ (chainOfSimplex R σ) := by
  have ho : cupOneOuterInclusion 0 1 0 = SimplexCategory.δ (1 : Fin 3) := by
    ext i
    fin_cases i <;> rfl
  have hi : cupOneInnerInclusion 0 1 0 = 𝟙 _ := by
    ext i
    fin_cases i <;> rfl
  simp [cupOneCochain, ofValues_apply, ho, hi, SimplicialObject.δ]
  ring

/-- The full cup-one differential identity in bidegree `(1,1)`, for arbitrary cochains.
Source: Steenrod (1947), cup-one differential identity; Porter–Suciu, equation (3.3).
-/
theorem coboundary_cupOneCochain_one_one (φ ψ : Cochain R (TopCat.toSSet.obj Y) 1) :
    coboundary R 1 (cupOneCochain Y 0 0 φ ψ) =
      -(cupCochain Y 1 1 φ ψ + cupCochain Y 1 1 ψ φ) +
        cupOneCochain Y 1 0 (coboundary R 1 φ) ψ -
        cupOneCochain Y 0 1 φ (coboundary R 1 ψ) := by
  apply extCochain
  intro σ
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.add_apply,
    cupOne_eval_two_one, cupOne_eval_one_two, coboundary_chainOfSimplex,
    cupCochain_apply_simplex, frontFace, backFace, front11, back11,
    Fin.sum_univ_succ, cupOneCochain_apply_one_one]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, pow_succ, one_smul,
    Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one,
    show (1 : Fin 2).succ = (2 : Fin 3) from rfl]
  simp only [SimplicialObject.δ]
  norm_num
  ring

private theorem oneCocycle_edges (φ : Cochain R (TopCat.toSSet.obj Y) 1)
    (hφ : coboundary R 1 φ = 0) (σ : (TopCat.toSSet.obj Y) _⦋2⦌) :
    φ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 1 σ)) =
      φ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 0 σ)) +
      φ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 2 σ)) := by
  have h := LinearMap.congr_fun hφ (chainOfSimplex R σ)
  simp only [coboundary_chainOfSimplex, Fin.sum_univ_succ] at h
  simp at h
  apply eq_of_sub_eq_zero
  calc
    _ = -(φ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 0 σ)) +
      (-φ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 1 σ)) +
        φ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 2 σ)))) := by abel
    _ = 0 := by rw [h, neg_zero]

/-- For degree-one cocycles, cup-one witnesses that the sum of the two cup orders is exact.
Source: Steenrod (1947), cup-one differential identity; Porter–Suciu, equation (3.5).
-/
theorem coboundary_cupOneCochain_one_one_of_closed (φ ψ : Cochain R (TopCat.toSSet.obj Y) 1)
    (hφ : coboundary R 1 φ = 0) (hψ : coboundary R 1 ψ = 0) :
    coboundary R 1 (cupOneCochain Y 0 0 φ ψ) =
      -(cupCochain Y 1 1 φ ψ + cupCochain Y 1 1 ψ φ) := by
  apply extCochain
  intro σ
  simp only [coboundary_chainOfSimplex, Fin.sum_univ_succ, cupOneCochain_apply_one_one,
    LinearMap.neg_apply, LinearMap.add_apply, cupCochain_apply_simplex]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, pow_succ,
    one_smul, Fin.sum_univ_zero, add_zero,
    Fin.succ_zero_eq_one, show (1 : Fin 2).succ = (2 : Fin 3) from rfl]
  rw [oneCocycle_edges Y φ hφ σ, oneCocycle_edges Y ψ hψ σ]
  simp only [frontFace, backFace, front11, back11]
  change _ = -(φ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 2 σ)) *
    ψ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 0 σ)) +
    ψ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 2 σ)) *
    φ (chainOfSimplex R ((TopCat.toSSet.obj Y).δ 0 σ)))
  norm_num
  ring


#print axioms coboundary_cupOneCochain
#print axioms sum_reassemble
#print axioms cupOneCochain
#print axioms cupOneCochain_apply_simplex
#print axioms cupOneCochain_apply_one_one
#print axioms cupOneCochain_add_left
#print axioms cupOneCochain_add_right
#print axioms cupOneCochain_smul_left
#print axioms cupOneCochain_smul_right
#print axioms cupOneCochain_naturality
#print axioms coboundary_cupOneCochain_one_one
#print axioms coboundary_cupOneCochain_one_one_of_closed

end HodgeLean.Foundations.Singular
