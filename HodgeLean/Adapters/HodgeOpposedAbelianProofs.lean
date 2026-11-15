import HodgeLean.Adapters.HodgeHigherDegreeAbelian
import HodgeLean.Adapters.CurveStructureSheafVanishing

/-! # Open obligations of the opposedness stage 1 (`HodgeOpposedAbelian`)

One `_aux` obligation per statement of `HodgeOpposedAbelian.lean`, all open. The statements,
their sources and their falsification checks are in `docs/specs/HodgeOpposedAbelian.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- One direction of the symmetry: `deRhamConj` maps `F^q ⊓ conj F^p` into `F^p ⊓ conj F^q`. -/
theorem hodgePiece_eq_bot_of_swap (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] {p q n : ℤ} (h : hodgePiece X p q n = ⊥) :
    hodgePiece X q p n = ⊥ := by
  refine eq_bot_iff.mpr fun α hα => ?_
  obtain ⟨hαF, hαc⟩ := Submodule.mem_inf.mp hα
  have hmem : deRhamConj X n α ∈ hodgePiece X p q n := by
    refine Submodule.mem_inf.mpr ⟨(mem_conjHodgeFiltrationComplexSubmodule X α).mp hαc, ?_⟩
    rw [mem_conjHodgeFiltrationComplexSubmodule, deRhamConj_deRhamConj]
    exact hαF
  rw [h] at hmem
  rw [Submodule.mem_bot, ← deRhamConj_deRhamConj X n α, (Submodule.mem_bot ℂ).mp hmem, map_zero]

theorem spec_hodgePiece_eq_bot_comm_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p q n : ℤ) :
    hodgePiece X p q n = ⊥ ↔ hodgePiece X q p n = ⊥ :=
  ⟨hodgePiece_eq_bot_of_swap X, hodgePiece_eq_bot_of_swap X⟩

theorem spec_hodgePiece_eq_bot_of_dim_lt_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p q n : ℤ) (h : (dim X.left : ℤ) < p ∨ (dim X.left : ℤ) < q) :
    hodgePiece X p q n = ⊥ := by
  rcases h with hp | hq
  · rw [hodgePiece, spec_hodgeFiltration_eq_bot_of_dim_lt X hp n, bot_inf_eq]
  · rw [hodgePiece, conjHodgeFiltrationComplexSubmodule_eq_bot_of_aux X
      (spec_hodgeFiltration_eq_bot_of_dim_lt X hq n), inf_bot_eq]

theorem spec_opposed_of_two_mul_dim_le_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (n : ℕ) (hn : 2 * dim X.left ≤ n) :
    ∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ := by
  intro p _ _
  refine spec_hodgePiece_eq_bot_of_dim_lt_aux X _ _ _ ?_
  omega

theorem spec_opposed_iff_reduced_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (n : ℕ) :
    (∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) ↔
      (∀ p : ℤ, 1 ≤ p → (n : ℤ) + 1 - dim X.left ≤ p → 2 * p ≤ (n : ℤ) + 1 →
        hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) := by
  refine ⟨fun H p h1 _ h2 => H p h1 (by omega), fun H p h1 hpn => ?_⟩
  by_cases hg : (dim X.left : ℤ) < p ∨ (dim X.left : ℤ) < (n : ℤ) + 1 - p
  · exact spec_hodgePiece_eq_bot_of_dim_lt_aux X _ _ _ hg
  rw [not_or, not_lt, not_lt] at hg
  by_cases h2 : 2 * p ≤ (n : ℤ) + 1
  · exact H p h1 (by omega) h2
  · have hq := H ((n : ℤ) + 1 - p) (by omega) (by omega) (by omega)
    rw [show (n : ℤ) + 1 - ((n : ℤ) + 1 - p) = p by ring] at hq
    exact (spec_hodgePiece_eq_bot_comm_aux X _ _ _).mp hq

/-- The complexified cup product is associative. -/
theorem cupC_assoc {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) {i j l ij jl k : ℕ} (hij : i + j = ij) (hjl : j + l = jl)
    (h₁ : ij + l = k) (h₂ : i + jl = k) (a : ℂ ⊗[ℚ] HQ X i) (b : ℂ ⊗[ℚ] HQ X j)
    (c : ℂ ⊗[ℚ] HQ X l) :
    μ.cupC h₁ (μ.cupC hij a b) c = μ.cupC h₂ a (μ.cupC hjl b c) := by
  induction a using TensorProduct.inductionOn with
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | tmul z a =>
    induction b using TensorProduct.inductionOn with
    | add b b' hb hb' => simp only [map_add, LinearMap.add_apply, hb, hb']
    | tmul w b =>
      induction c using TensorProduct.inductionOn with
      | add c c' hc hc' => simp only [map_add, hc, hc']
      | tmul u c =>
        rw [CupProduct.cupC_tmul, CupProduct.cupC_tmul, CupProduct.cupC_tmul,
          CupProduct.cupC_tmul, μ.assoc hij hjl h₁ h₂, mul_assoc]

/-- Cup product with the complexified unit is the identity. -/
theorem cupC_one_unit {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) {j : ℕ} (h : 0 + j = j)
    (v : Fin 0 → ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X j) :
    μ.cupC h (μ.cupMultiC 0 v) y = y := by
  have h1 := LinearMap.congr_fun (μ.cupC_one_tmul h (unitClass X)) y
  have : μ.cup h (unitClass X) = LinearMap.id := LinearMap.ext (μ.one_cup (j := j))
  rw [this, LinearMap.baseChange_id] at h1
  exact h1

/-- The cup of two iterated cups of degree-one classes is the iterated cup of the concatenated
family. -/
theorem cupC_cupMultiC_cupMultiC {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) :
    ∀ (i j k : ℕ) (h : i + j = k) (v : Fin i → ℂ ⊗[ℚ] HQ X 1) (w : Fin j → ℂ ⊗[ℚ] HQ X 1),
      μ.cupC h (μ.cupMultiC i v) (μ.cupMultiC j w) =
        μ.cupMultiC k (fun t => Fin.append v w (Fin.cast h.symm t))
  | 0, j, k, h, v, w => by
    obtain rfl : k = j := by omega
    rw [cupC_one_unit]
    congr 1
    funext t
    rw [show Fin.cast h.symm t = Fin.natAdd 0 t from Fin.ext (by simp), Fin.append_right]
  | m + 1, j, k, h, v, w => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨m + j, by omega⟩
    obtain rfl : k' = m + j := by omega
    rw [CupProduct.cupMultiC_succ, cupC_assoc μ (Nat.add_comm 1 m) (rfl : m + j = m + j) h
      (Nat.add_comm 1 (m + j)), cupC_cupMultiC_cupMultiC μ m j (m + j) rfl,
      CupProduct.cupMultiC_succ]
    congr 2
    funext t
    simp only [Fin.tail]
    refine Fin.addCases (fun s => ?_) (fun s => ?_) t
    · rw [show Fin.cast h.symm (Fin.castAdd j s).succ = Fin.castAdd j s.succ from
          Fin.ext (by simp), Fin.append_left,
          show Fin.cast (rfl : m + j = m + j).symm (Fin.castAdd j s) = Fin.castAdd j s from rfl,
          Fin.append_left]
      rfl
    · rw [show Fin.cast h.symm (Fin.natAdd m s).succ = Fin.natAdd (m + 1) s from
          Fin.ext (by simp; omega), Fin.append_right,
          show Fin.cast (rfl : m + j = m + j).symm (Fin.natAdd m s) = Fin.natAdd m s from rfl,
          Fin.append_right]

/-- The cup-wedge piece is the image under `bettiDeRhamHQ` of the span of the typed iterated
cups. -/
theorem cupWedgePiece_eq_map_span (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) (n : ℕ) (pq : ℤ × ℤ) :
    cupWedgePiece X μ n pq = (Submodule.span ℂ {z | ∃ (d : Fin n → ℤ × ℤ)
      (v : Fin n → ℂ ⊗[ℚ] HQ X 1), HodgeBlocks.totalBidegree n d = pq ∧
        (∀ i, v i ∈ cohomologyHodgePiece X 1 (d i)) ∧ μ.cupMultiC n v = z}).map
      (bettiDeRhamHQ X n) := by
  rw [Submodule.map_span, cupWedgePiece]
  congr 1
  ext α
  constructor
  · rintro ⟨d, v, hd, hv, rfl⟩
    exact ⟨_, ⟨d, v, hd, hv, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨d, v, hd, hv, rfl⟩, rfl⟩
    exact ⟨d, v, hd, hv, rfl⟩

theorem spec_cupC_mem_cupWedgePiece_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (μ : CupProduct X)
    {i j k : ℕ} (h : i + j = k) {a b c d : ℤ} {x : ℂ ⊗[ℚ] HQ X i} {y : ℂ ⊗[ℚ] HQ X j}
    (hx : bettiDeRhamHQ X i x ∈ cupWedgePiece X μ i (a, b))
    (hy : bettiDeRhamHQ X j y ∈ cupWedgePiece X μ j (c, d)) :
    bettiDeRhamHQ X k (μ.cupC h x y) ∈ cupWedgePiece X μ k (a + c, b + d) := by
  subst h
  have hβ := (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective
  rw [cupWedgePiece_eq_map_span] at hx hy
  obtain ⟨x', hx', hxx'⟩ := hx
  obtain ⟨y', hy', hyy'⟩ := hy
  obtain rfl := (hβ i).1 hxx'
  obtain rfl := (hβ j).1 hyy'
  have hmem := Submodule.apply_mem_map₂ (μ.cupC rfl) hx' hy'
  rw [Submodule.map₂_span_span] at hmem
  suffices hle : Submodule.span ℂ (Set.image2 (fun m n => μ.cupC rfl m n) _ _) ≤
      (cupWedgePiece X μ (i + j) (a + c, b + d)).comap (bettiDeRhamHQ X (i + j)) from hle hmem
  rw [Submodule.span_le]
  rintro _ ⟨_, ⟨dv, v, hdv, hv, rfl⟩, _, ⟨dw, w, hdw, hw, rfl⟩, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  rw [cupC_cupMultiC_cupMultiC]
  refine Submodule.subset_span ⟨Fin.append dv dw, _, ?_, fun t => ?_, rfl⟩
  · simp only [HodgeBlocks.totalBidegree, Prod.ext_iff] at hdv hdw ⊢
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, hdv.1, hdv.2, hdw.1, hdw.2,
      and_self]
  · refine Fin.addCases (fun s => ?_) (fun s => ?_) t
    · simpa only [Fin.cast_eq_self, Fin.append_left] using hv s
    · simpa only [Fin.cast_eq_self, Fin.append_right] using hw s

/-- Rational Poincaré duality under the torus theorem: in complementary degrees `i + j = 2g`, a
class whose cup with every class of degree `j` vanishes is `0`. Through `cupWedgeMap_wedge` the
cup pairing is the wedge pairing, which is perfect (`exteriorPower.instIsPerfPairWedgePairing`). -/
theorem cup_eq_zero_of_forall_cup_eq_zero_torus {X : Over (Spec ↧ℂ)} [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) {i j : ℕ} (h : i + j = 2 * dim X.left) (x : HQ X i)
    (hx : ∀ y : HQ X j, μ.cup h x y = 0) : x = 0 := by
  let := hT.finite
  have hkl : i + j = Module.finrank ℚ (HQ X 1) := by rw [hT.finrank_eq, h]
  obtain ⟨v, rfl⟩ := (hT.bijective i).2 x
  have hwedge : ∀ w : ⋀[ℚ]^j (HQ X 1), exteriorPower.wedge ℚ (HQ X 1) i j v w = 0 := by
    intro w
    apply (hT.bijective (i + j)).1
    rw [map_zero, CupProduct.cupWedgeMap_wedge]
    have := hx (μ.cupWedgeMap j w)
    rw [← CupProduct.castEquiv_cup μ rfl h] at this
    exact (HQ.castEquiv X h).injective (this.trans (map_zero _).symm)
  let vol : ⋀[ℚ]^(Module.finrank ℚ (HQ X 1)) (HQ X 1) ≃ₗ[ℚ] ℚ :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [HodgeBlocks.finrank_topExteriorPower, Module.finrank_self])
  have hinj := (LinearMap.IsPerfPair.bijective_left
    (exteriorPower.wedgePairing vol hkl)).1
  suffices hv : v = 0 by rw [hv, map_zero]
  apply hinj
  refine LinearMap.ext fun w => ?_
  rw [exteriorPower.wedgePairing, LinearMap.compr₂_apply, hwedge w, map_zero,
    map_zero, LinearMap.zero_apply]

/-- Left non-degeneracy of a `ℚ`-bilinear map survives base change to `ℂ`: read coordinates in a
`ℚ`-basis of `ℂ` (`TensorProduct.equivFinsuppOfBasisLeft`). -/
theorem baseChange_eq_zero_of_forall {M N P : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] [AddCommGroup P] [Module ℚ P] (B : M →ₗ[ℚ] N →ₗ[ℚ] P)
    (hB : ∀ m : M, (∀ n : N, B m n = 0) → m = 0) (x : ℂ ⊗[ℚ] M)
    (hx : ∀ n : N, (B.flip n).baseChange ℂ x = 0) : x = 0 := by
  let b := Module.Free.chooseBasis ℚ ℂ
  let e := TensorProduct.equivFinsuppOfBasisLeft (M := ℂ) (N := M) b
  let eP := TensorProduct.equivFinsuppOfBasisLeft (M := ℂ) (N := P) b
  have key : ∀ (n : N) (y : ℂ ⊗[ℚ] M) (s : _),
      eP ((B.flip n).baseChange ℂ y) s = B (e y s) n := by
    intro n y s
    induction y using TensorProduct.inductionOn with
    | tmul z m =>
      simp [e, eP, LinearMap.baseChange_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul]
    | add y y' hy hy' => simp [hy, hy']
  apply e.injective
  ext s
  rw [map_zero, Finsupp.zero_apply]
  refine hB _ fun n => ?_
  rw [← key, hx n, map_zero, Finsupp.zero_apply]

theorem spec_eq_zero_of_forall_cupC_eq_zero_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) {i j : ℕ} (h : i + j = 2 * dim X.left) (x : ℂ ⊗[ℚ] HQ X i)
    (hx : ∀ y : ℂ ⊗[ℚ] HQ X j, μ.cupC h x y = 0) :
    x = 0 := by
  refine baseChange_eq_zero_of_forall (μ.cup h) (cup_eq_zero_of_forall_cup_eq_zero_torus hT h)
    x fun y => ?_
  have key : ∀ x' : ℂ ⊗[ℚ] HQ X i,
      ((μ.cup h).flip y).baseChange ℂ x' = μ.cupC h x' ((1 : ℂ) ⊗ₜ y) := by
    intro x'
    induction x' using TensorProduct.inductionOn with
    | tmul z a => rw [LinearMap.baseChange_tmul, CupProduct.cupC_tmul, mul_one, LinearMap.flip_apply]
    | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb]
  rw [key, hx]

/-- For abelian `X`, `dim H^{1,0} = dim H^{0,1} = g`, unconditionally: stage 4l's degree-one
decomposition in the argument of `spec_finrank_cohomologyHodgePiece_one`. -/
theorem finrank_cohomologyHodgePiece_one_abelian (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Module.finrank ℂ (cohomologyHodgePiece X 1 (1, 0)) = dim X.left ∧
      Module.finrank ℂ (cohomologyHodgePiece X 1 (0, 1)) = dim X.left := by
  have hB := HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X
  obtain ⟨h1, h2⟩ := spec_finrank_hodgeFiltration_one_of_isInternal X
    (spec_deRhamHodgePiece_one_isInternal X)
  rw [cohomologyHodgePiece_eq_map hB 1]
  simp only
  have e10 := spec_deRhamHodgePiece_one X (1, 0)
  have e01 := spec_deRhamHodgePiece_one X (0, 1)
  simp only [Prod.mk.injEq, one_ne_zero, zero_ne_one, and_self, ↓reduceIte] at e10 e01
  rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, e10, e01]
  exact ⟨h1, h2⟩

/-- For abelian `X`, the degree-one pieces other than `(1, 0)` and `(0, 1)` are `⊥`. -/
theorem cohomologyHodgePiece_one_eq_bot (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (d : ℤ × ℤ)
    (h1 : d ≠ (1, 0)) (h2 : d ≠ (0, 1)) : cohomologyHodgePiece X 1 d = ⊥ := by
  rw [cohomologyHodgePiece_eq_map (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X) 1]
  simp only
  rw [spec_deRhamHodgePiece_one X d]
  simp [h1, h2]

/-- Under the torus theorem `cupMultiC` is alternating: it vanishes on a linearly dependent family
(`TorusCohomology.complexificationCongr_symm_ιMulti`). -/
theorem cupMultiC_eq_zero_of_not_linearIndependent {X : Over (Spec ↧ℂ)} [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (m : ℕ) (v : Fin m → ℂ ⊗[ℚ] HQ X 1)
    (h : ¬ LinearIndependent ℂ v) : μ.cupMultiC m v = 0 := by
  rw [← hT.complexificationCongr_symm_ιMulti, AlternatingMap.map_linearDependent _ _ h, map_zero,
    map_zero]

/-- A linearly independent family has at most `finrank P` members in a subspace `P`. -/
theorem card_filter_le_finrank {E ι : Type*} [AddCommGroup E] [Module ℂ E] [Fintype ι]
    [DecidableEq ι] {P : Submodule ℂ E} [FiniteDimensional ℂ P] {v : ι → E}
    (hv : LinearIndependent ℂ v) (S : Finset ι) (hS : ∀ i ∈ S, v i ∈ P) :
    S.card ≤ Module.finrank ℂ P := by
  have h1 : LinearIndependent ℂ (fun i : S => (⟨v i, hS i i.2⟩ : P)) := by
    apply LinearIndependent.of_comp P.subtype
    exact hv.comp Subtype.val Subtype.val_injective
  simpa using h1.fintype_card_le_finrank

theorem spec_cupWedgePiece_top_eq_bot_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (c : ℤ) (hc : c ≠ dim X.left) :
    cupWedgePiece X μ (2 * dim X.left) (c, ((2 * dim X.left : ℕ) : ℤ) - c) = ⊥ := by
  classical
  rw [cupWedgePiece, Submodule.span_eq_bot]
  rintro _ ⟨d, v, hd, hv, rfl⟩
  by_cases hli : LinearIndependent ℂ v
  swap
  · rw [cupMultiC_eq_zero_of_not_linearIndependent hT _ v hli, map_zero]
  by_cases hall : ∀ i, d i = (1, 0) ∨ d i = (0, 1)
  swap
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    rw [not_or] at hi
    have := hv i
    rw [cohomologyHodgePiece_one_eq_bot X (d i) hi.1 hi.2] at this
    rw [(μ.cupMultiC _).map_coord_zero i ((Submodule.mem_bot ℂ).mp this), map_zero]
  exfalso
  let := (finiteBetti_abelian X).finite 1
  obtain ⟨f10, f01⟩ := finrank_cohomologyHodgePiece_one_abelian X
  have hS := card_filter_le_finrank hli (Finset.univ.filter fun i => d i = (1, 0))
    (P := cohomologyHodgePiece X 1 (1, 0)) (fun i hi => by
      have := hv i
      rwa [(Finset.mem_filter.mp hi).2] at this)
  have hT' := card_filter_le_finrank hli (Finset.univ.filter fun i => d i = (0, 1))
    (P := cohomologyHodgePiece X 1 (0, 1)) (fun i hi => by
      have := hv i
      rwa [(Finset.mem_filter.mp hi).2] at this)
  have e1 : (HodgeBlocks.totalBidegree _ d).1 =
      ((Finset.univ.filter fun i => d i = (1, 0)).card : ℤ) := by
    simp only [HodgeBlocks.totalBidegree]
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hall i with h | h <;> simp [h]
  have e2 : (HodgeBlocks.totalBidegree _ d).2 =
      ((Finset.univ.filter fun i => d i = (0, 1)).card : ℤ) := by
    simp only [HodgeBlocks.totalBidegree]
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hall i with h | h <;> simp [h]
  rw [hd] at e1 e2
  simp only at e1 e2
  rw [f10] at hS
  rw [f01] at hT'
  push_cast at e2
  omega

theorem spec_eq_zero_of_cupC_cupWedgePiece_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) {i j : ℕ} (h : i + j = 2 * dim X.left) (a : ℤ)
    (x : ℂ ⊗[ℚ] HQ X i) (hx : bettiDeRhamHQ X i x ∈ cupWedgePiece X μ i (a, (i : ℤ) - a))
    (hxy : ∀ y : ℂ ⊗[ℚ] HQ X j,
      bettiDeRhamHQ X j y ∈
        cupWedgePiece X μ j ((dim X.left : ℤ) - a, (j : ℤ) - ((dim X.left : ℤ) - a)) →
      μ.cupC h x y = 0) :
    x = 0 := by
  have hB := HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X
  let βj := LinearEquiv.ofBijective (bettiDeRhamHQ X j) (hB.bijective j)
  refine spec_eq_zero_of_forall_cupC_eq_zero_aux X hT h x fun y => ?_
  have hy : bettiDeRhamHQ X j y ∈ ⨆ pq, cupWedgePiece X μ j pq := by
    rw [(spec_cupWedgePiece_isInternal X hT j).submodule_iSup_eq_top]
    exact Submodule.mem_top
  have key : μ.cupC h x (βj.symm (bettiDeRhamHQ X j y)) = 0 := by
    refine Submodule.iSup_induction _ (motive := fun z => μ.cupC h x (βj.symm z) = 0) hy
      (fun pq z hz => ?_) (by rw [map_zero, map_zero])
      (fun z z' hz hz' => by rw [map_add, map_add, hz, hz', add_zero])
    have hy' : bettiDeRhamHQ X j (βj.symm z) = z := βj.apply_symm_apply z
    by_cases hline : pq.1 + pq.2 = j
    · by_cases ha : a + pq.1 = dim X.left
      · refine hxy _ ?_
        rw [hy']
        convert hz using 2
        ext <;> simp only <;> omega
      · have hm := spec_cupC_mem_cupWedgePiece_aux X μ h hx (hy'.symm ▸ hz)
        have ht : ((a + pq.1 : ℤ), (i : ℤ) - a + pq.2) =
            (a + pq.1, ((2 * dim X.left : ℕ) : ℤ) - (a + pq.1)) := by
          ext <;> push_cast <;> omega
        rw [ht, spec_cupWedgePiece_top_eq_bot_aux X hT _ ha, Submodule.mem_bot] at hm
        exact (hB.bijective _).1 (hm.trans (map_zero _).symm)
    · rw [spec_cupWedgePiece_eq_bot X μ j pq hline, Submodule.mem_bot] at hz
      rw [hz, map_zero, map_zero]
  rwa [show βj.symm (bettiDeRhamHQ X j y) = y from βj.symm_apply_apply y] at key

/-- Linear algebra behind the upper bound: let `x` lie in `⨆ i, W i`. If, for each `i ∈ S`, every
decomposition `x = z + c` with `z ∈ W i` and `c` in the span of the other pieces has `z = 0`, then
`x` lies in the span of the pieces outside `S`. No independence is needed. -/
theorem mem_iSup_compl_of_forall_eq_zero {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {W : ι → Submodule R M} {S : Set ι} {x : M} (hx : x ∈ ⨆ i, W i)
    (h : ∀ i ∈ S, ∀ z ∈ W i, ∀ c ∈ ⨆ (j) (_ : j ≠ i), W j, x = z + c → z = 0) :
    x ∈ ⨆ (i) (_ : i ∉ S), W i := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
  obtain ⟨f, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum W _).mp hs
  have h0 : ∀ i ∈ s, i ∈ S → (f i : M) = 0 := by
    intro i hi hiS
    refine h i hiS _ (f i).2 (∑ j ∈ s.erase i, (f j : M)) ?_ (Finset.add_sum_erase s _ hi).symm
    exact Submodule.sum_mem _ fun j hj =>
      le_iSup₂_of_le (f := fun j (_ : j ≠ i) => W j) j (Finset.ne_of_mem_erase hj) le_rfl (f j).2
  refine Submodule.sum_mem _ fun i hi => ?_
  by_cases hiS : i ∈ S
  · rw [h0 i hi hiS]; exact zero_mem _
  · exact le_iSup₂_of_le (f := fun i (_ : i ∉ S) => W i) i hiS le_rfl (f i).2

theorem spec_hodgeFiltration_le_iSup_cupWedgePiece_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ) (p : ℤ) :
    F^p H_dR^(n : ℤ)(X) ≤ ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p') := by
  by_cases hn : 2 * dim X.left < n
  · have := spec_subsingleton_deRhamCohomology_of_lt X n hn
    intro α _
    rw [Subsingleton.elim α 0]
    exact zero_mem _
  push Not at hn
  set g := dim X.left with hg
  set m := 2 * g - n with hm
  have hnm : n + m = 2 * g := by omega
  have hmZ : (m : ℤ) = 2 * (g : ℤ) - n := by omega
  have hβ := HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X
  let e := LinearEquiv.ofBijective (bettiDeRhamHQ X n) (hβ.bijective n)
  have he : ∀ w, bettiDeRhamHQ X n (e.symm w) = w := fun w => e.apply_symm_apply w
  intro α hα
  have htop : α ∈ ⨆ i, cupWedgePiece X μ n i := by
    rw [(spec_cupWedgePiece_isInternal X hT n).submodule_iSup_eq_top]
    exact Submodule.mem_top
  have key := mem_iSup_compl_of_forall_eq_zero (S := {i : ℤ × ℤ | i.1 < p}) htop ?_
  · refine (show (⨆ (i : ℤ × ℤ) (_ : i ∉ {i : ℤ × ℤ | i.1 < p}), cupWedgePiece X μ n i) ≤ _ from
      iSup₂_le fun i hi => ?_) key
    by_cases hi' : i.1 + i.2 = n
    · have hi'' : i = (i.1, (n : ℤ) - i.1) := Prod.ext rfl (by simp only; omega)
      rw [hi'']
      exact le_iSup₂_of_le (f := fun (p' : ℤ) (_ : p ≤ p') =>
        cupWedgePiece X μ n (p', (n : ℤ) - p')) i.1 (by simpa using hi) le_rfl
    · rw [spec_cupWedgePiece_eq_bot X μ n i hi']
      exact bot_le
  intro i hi z hz c hc hzc
  by_cases hi' : i.1 + i.2 = n
  swap
  · rw [spec_cupWedgePiece_eq_bot X μ n i hi'] at hz
    exact (Submodule.mem_bot ℂ).mp hz
  obtain ⟨r, s⟩ := i
  simp only at hi'
  obtain rfl : s = n - r := by omega
  simp only [Set.mem_ofPred_eq] at hi
  suffices e.symm z = 0 by rw [← he z, this, map_zero]
  refine spec_eq_zero_of_cupC_cupWedgePiece_aux X hT hnm r (e.symm z) (by rwa [he]) fun y hy => ?_
  let Φ : H_dR^(n : ℤ)(X) →ₗ[ℂ] H_dR^((2 * g : ℕ) : ℤ)(X) :=
    bettiDeRhamHQ X (2 * g) ∘ₗ (μ.cupC hnm).flip y ∘ₗ e.symm.toLinearMap
  have hΦ : ∀ w, Φ w = bettiDeRhamHQ X (2 * g) (μ.cupC hnm (e.symm w) y) := fun w => rfl
  have hΦα : Φ α = 0 := by
    have hyF : bettiDeRhamHQ X m y ∈ F^((g : ℤ) - r) H_dR^(m : ℤ)(X) := by
      have := spec_cupWedgePiece_le_deRhamHodgePiece X hC m _ hy
      rw [deRhamHodgePiece] at this
      split_ifs at this with hl
      · exact this.1
      · exact absurd hl (by omega)
    have := hC.mem hnm p ((g : ℤ) - r) (e.symm α) y (by rwa [he]) hyF
    rw [spec_hodgeFiltration_eq_bot_of_dim_lt X (by omega) _] at this
    rw [hΦ]
    exact (Submodule.mem_bot ℂ).mp this
  have hΦc : Φ c = 0 := by
    have hle : (⨆ (j : ℤ × ℤ) (_ : j ≠ (r, (n : ℤ) - r)), cupWedgePiece X μ n j) ≤
        LinearMap.ker Φ := by
      refine iSup₂_le fun j hj w hw => ?_
      rw [LinearMap.mem_ker, hΦ]
      by_cases hj' : j.1 + j.2 = n
      · have hmem := spec_cupC_mem_cupWedgePiece_aux X μ hnm (x := e.symm w) (y := y)
          (by rw [he]; exact hw) hy
        have hj1 : j.1 ≠ r := fun h => hj (Prod.ext h (by simp only; omega))
        have hpair : (j.1 + ((g : ℤ) - r), j.2 + ((m : ℤ) - ((g : ℤ) - r))) =
            (j.1 + ((g : ℤ) - r), ((2 * g : ℕ) : ℤ) - (j.1 + ((g : ℤ) - r))) :=
          Prod.ext rfl (by simp only; push_cast; omega)
        rw [hpair, spec_cupWedgePiece_top_eq_bot_aux X hT _ (by omega)] at hmem
        exact (Submodule.mem_bot ℂ).mp hmem
      · rw [spec_cupWedgePiece_eq_bot X μ n j hj'] at hw
        simp only [(Submodule.mem_bot ℂ).mp hw, map_zero, LinearMap.zero_apply]
    exact hle hc
  have hΦz : Φ z = 0 := by
    have := congrArg Φ hzc
    rw [map_add, hΦα, hΦc, add_zero] at this
    exact this.symm
  rw [hΦ] at hΦz
  exact (hβ.bijective (2 * g)).1 (hΦz.trans (map_zero _).symm)

theorem spec_hodgeFiltration_eq_iSup_cupWedgePiece_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ) (p : ℤ) :
    F^p H_dR^(n : ℤ)(X) = ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p') := by
  refine le_antisymm (spec_hodgeFiltration_le_iSup_cupWedgePiece_aux X hT hC n p)
    (iSup₂_le fun p' hp' => ?_)
  have := spec_cupWedgePiece_le_deRhamHodgePiece X hC n (p', (n : ℤ) - p')
  simp only [deRhamHodgePiece, show p' + ((n : ℤ) - p') = n by ring, ↓reduceIte] at this
  exact this.trans (inf_le_left.trans (hodgeFiltration_antitone X n hp'))

theorem spec_opposed_of_hodgeFiltration_le_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (n : ℕ)
    (hF : ∀ p : ℤ,
      F^p H_dR^(n : ℤ)(X) ≤ ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p'))
    (p : ℤ) :
    hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ := by
  have hW := spec_cupWedgePiece_isInternal X hT n
  have hA : (⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p')) ≤
      ⨆ i ∈ {i : ℤ × ℤ | p ≤ i.1}, cupWedgePiece X μ n i :=
    iSup₂_le fun p' hp' => le_iSup₂_of_le (f := fun (i : ℤ × ℤ) (_ : i ∈ {i : ℤ × ℤ | p ≤ i.1}) =>
      cupWedgePiece X μ n i) (p', (n : ℤ) - p') hp' le_rfl
  have hB : (⨆ (p'' : ℤ) (_ : (n : ℤ) + 1 - p ≤ p''), cupWedgePiece X μ n (p'', (n : ℤ) - p'')) ≤
      (⨆ i ∈ {i : ℤ × ℤ | i.1 < p}, cupWedgePiece X μ n i).comap (deRhamConjSemilinear X n) := by
    refine iSup₂_le fun p'' hp'' x hx => ?_
    exact le_iSup₂_of_le (f := fun (i : ℤ × ℤ) (_ : i ∈ {i : ℤ × ℤ | i.1 < p}) =>
      cupWedgePiece X μ n i) ((n : ℤ) - p'', p'') (show (n : ℤ) - p'' < p by omega) le_rfl
      (spec_deRhamConj_mem_cupWedgePiece X μ n _ _ hx)
  have hdisj := hW.submodule_iSupIndep.disjoint_biSup_biSup
    (s := {i : ℤ × ℤ | p ≤ i.1}) (t := {i : ℤ × ℤ | i.1 < p})
    (Set.disjoint_left.mpr fun i h1 h2 => by simp only [Set.mem_ofPred_eq] at h1 h2; omega)
  rw [eq_bot_iff]
  intro α hα
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hα
  have hb := hB (hF _ h2)
  rw [Submodule.mem_comap] at hb
  change deRhamConj X n (deRhamConj X n α) ∈ _ at hb
  rw [deRhamConj_deRhamConj] at hb
  exact (Submodule.mem_bot ℂ).mpr ((Submodule.disjoint_def.mp hdisj) α (hA (hF p h1)) hb)

theorem spec_opposed_of_cupFiltered_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ) (p : ℤ) :
    hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ := by
  exact spec_opposed_of_hodgeFiltration_le_aux X hT n
    (fun p => spec_hodgeFiltration_le_iSup_cupWedgePiece_aux X hT hC n p) p

theorem spec_hodgeDecomposition_of_cupFiltered_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) :
    HodgeDecomposition X := by
  exact spec_hodgeDecomposition_of_opposed X hT hC fun n _ _ p _ _ =>
    spec_opposed_of_cupFiltered_aux X hT hC n p

end HodgeLean.Adapters
