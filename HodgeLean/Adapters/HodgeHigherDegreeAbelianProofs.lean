import HodgeLean.Adapters.HodgeHigherDegreeAbelianDefs

/-! # Open obligations of stage 4m (`HodgeHigherDegreeAbelian`)

One `_aux` obligation per statement of `HodgeHigherDegreeAbelian.lean`, all open. The statements,
their sources and their falsification checks are in `docs/specs/HodgeHigherDegreeAbelian.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

theorem spec_hodgeDecomposition_iff_two_le_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    HodgeDecomposition X ↔
      ∀ n : ℕ, 2 ≤ n → DirectSum.IsInternal (deRhamHodgePiece X n) := by
  refine ⟨fun h n _ => h.isInternal n, fun h => ⟨fun n => ?_⟩⟩
  rcases n with _ | _ | n
  · exact deRhamHodgePiece_isInternal_zero X
  · exact spec_deRhamHodgePiece_one_isInternal X
  · exact h _ (by omega)

theorem spec_subsingleton_deRhamCohomology_of_lt_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (hn : 2 * dim X.left < n) :
    Subsingleton H_dR^(n : ℤ)(X) := by
  have := (vanishingAboveTop_abelian X).subsingleton n hn
  have h0 : ∀ x : ℂ ⊗[ℚ] HQ X n, x = 0 := fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul a b => rw [Subsingleton.elim b 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := ((HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective n).2 a
  obtain ⟨y, rfl⟩ := ((HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective n).2 b
  rw [h0 x, h0 y]

theorem spec_deRhamHodgePiece_isInternal_of_lt_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (hn : 2 * dim X.left < n) :
    DirectSum.IsInternal (deRhamHodgePiece X n) := by
  have := spec_subsingleton_deRhamCohomology_of_lt_aux X n hn
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨fun i => by rw [Subsingleton.elim (deRhamHodgePiece X n i) ⊥]; exact disjoint_bot_left,
    Subsingleton.elim _ _⟩

theorem spec_hodgeDecomposition_of_isInternal_le_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (h : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → DirectSum.IsInternal (deRhamHodgePiece X n)) :
    HodgeDecomposition X := by
  refine (spec_hodgeDecomposition_iff_two_le_aux X).2 fun n hn => ?_
  by_cases hle : n ≤ 2 * dim X.left
  · exact h n hn hle
  · exact spec_deRhamHodgePiece_isInternal_of_lt_aux X n (by omega)

theorem spec_inf_eq_of_opposed_aux {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (n : ℤ) {W : ℤ × ℤ → Submodule R M} (hW : DirectSum.IsInternal W)
    (hW0 : ∀ pq : ℤ × ℤ, pq.1 + pq.2 ≠ n → W pq = ⊥) {F G : ℤ → Submodule R M}
    (hF : Antitone F) (hG : Antitone G) (hle : ∀ pq : ℤ × ℤ, W pq ≤ F pq.1 ⊓ G pq.2)
    (hopp : ∀ p : ℤ, F p ⊓ G (n + 1 - p) = ⊥) (p : ℤ) :
    F p ⊓ G (n - p) = W (p, n - p) := by
  refine le_antisymm ?_ (hle (p, n - p))
  set A : Submodule R M := ⨆ (p' : ℤ) (_ : p' < p), W (p', n - p') with hA
  set B : Submodule R M := ⨆ (p' : ℤ) (_ : p < p'), W (p', n - p') with hB
  have hAG : A ≤ G (n + 1 - p) := iSup₂_le fun p' hp' =>
    (hle (p', n - p')).trans (inf_le_right.trans (hG (by omega)))
  have hBF : B ≤ F (p + 1) := iSup₂_le fun p' hp' =>
    (hle (p', n - p')).trans (inf_le_left.trans (hF (by omega)))
  have htop : (⊤ : Submodule R M) ≤ A ⊔ W (p, n - p) ⊔ B := by
    rw [← hW.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    by_cases hi : i.1 + i.2 = n
    · have hi' : i = (i.1, n - i.1) := Prod.ext rfl (by simp only; omega)
      rw [hi']
      rcases lt_trichotomy i.1 p with h | h | h
      · exact le_sup_of_le_left (le_sup_of_le_left (le_iSup₂_of_le i.1 h le_rfl))
      · rw [h]; exact le_sup_of_le_left le_sup_right
      · exact le_sup_of_le_right (le_iSup₂_of_le i.1 h le_rfl)
    · rw [hW0 i hi]; exact bot_le
  intro x hx
  obtain ⟨y, hy, b, hb, rfl⟩ := Submodule.mem_sup.mp (htop (Submodule.mem_top (x := x)))
  obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  have hw' := Submodule.mem_inf.mp (hle (p, n - p) hw)
  have hx' := Submodule.mem_inf.mp hx
  have hbF : b ∈ F p := hF (by omega : p ≤ p + 1) (hBF hb)
  have haF : a ∈ F p := by
    have := sub_mem (sub_mem hx'.1 hw'.1) hbF
    rwa [show a + w + b - w - b = a by abel] at this
  have ha0 : a = 0 := by
    have : a ∈ F p ⊓ G (n + 1 - p) := Submodule.mem_inf.mpr ⟨haF, hAG ha⟩
    rwa [hopp p, Submodule.mem_bot] at this
  subst ha0
  have hbG : b ∈ G (n - p) := by
    have := sub_mem hx'.2 hw'.2
    rwa [show 0 + w + b - w = b by abel] at this
  have hb0 : b = 0 := by
    have : b ∈ F (p + 1) ⊓ G (n + 1 - (p + 1)) :=
      Submodule.mem_inf.mpr ⟨hBF hb, by rwa [show n + 1 - (p + 1) = n - p by ring]⟩
    rwa [hopp (p + 1), Submodule.mem_bot] at this
  subst hb0
  simpa using hw

/-- If every degree-one type `d i` lies on the line `p + q = 1`, the total type of `n` of them lies
on the line `p + q = n`. -/
theorem totalBidegree_add_of_forall (n : ℕ) (d : Fin n → ℤ × ℤ)
    (hall : ∀ i, (d i).1 + (d i).2 = ((1 : ℕ) : ℤ)) :
    (HodgeBlocks.totalBidegree n d).1 + (HodgeBlocks.totalBidegree n d).2 = (n : ℤ) := by
  simp only [HodgeBlocks.totalBidegree]
  rw [← Finset.sum_add_distrib]
  simp [hall]

theorem spec_cupWedgePiece_eq_bot_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) (n : ℕ) (pq : ℤ × ℤ) (h : pq.1 + pq.2 ≠ n) :
    cupWedgePiece X μ n pq = ⊥ := by
  rw [cupWedgePiece, Submodule.span_eq_bot]
  rintro _ ⟨d, v, hd, hv, rfl⟩
  by_cases hall : ∀ i, (d i).1 + (d i).2 = ((1 : ℕ) : ℤ)
  · exact absurd (hd ▸ totalBidegree_add_of_forall n d hall) h
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have := hv i
    simp only [cohomologyHodgePiece, hi, ↓reduceIte] at this
    rw [(μ.cupMultiC n).map_coord_zero i ((Submodule.mem_bot ℂ).mp this), map_zero]

/-- The complexified iterated cup commutes with rational conjugation, factor by factor. -/
theorem sigmaQ_cupMultiC {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) :
    ∀ (m : ℕ) (v : Fin m → ℂ ⊗[ℚ] HQ X 1),
      HodgeBlocks.sigmaQ (HQ X m) (μ.cupMultiC m v) =
        μ.cupMultiC m (fun i => HodgeBlocks.sigmaQ (HQ X 1) (v i))
  | 0, v => by
    exact (HodgeBlocks.sigmaQ_tmul (HQ X 0) 1 (unitClass X)).trans (by simp only [map_one]; rfl)
  | m + 1, v => by
    rw [CupProduct.cupMultiC_succ, CupProduct.cupMultiC_succ, CupProduct.sigmaQ_cupC,
      sigmaQ_cupMultiC μ m]
    rfl

theorem spec_deRhamConj_mem_cupWedgePiece_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (μ : CupProduct X) (n : ℕ) (p q : ℤ)
    {α : H_dR^(n : ℤ)(X)} (hα : α ∈ cupWedgePiece X μ n (p, q)) :
    deRhamConj X n α ∈ cupWedgePiece X μ n (q, p) := by
  induction hα using Submodule.span_induction with
  | mem α hα =>
    obtain ⟨d, v, hd, hv, rfl⟩ := hα
    rw [← bettiDeRhamHQ_sigmaQ, sigmaQ_cupMultiC]
    refine Submodule.subset_span ⟨fun i => (d i).swap, _, ?_, fun i => ?_, rfl⟩
    · simp only [HodgeBlocks.totalBidegree, Prod.fst_swap, Prod.snd_swap] at hd ⊢
      rw [Prod.mk.injEq] at hd ⊢
      exact ⟨hd.2, hd.1⟩
    · rw [← cohomologyHodgePiece_map_sigmaQ]
      exact Submodule.mem_map_of_mem (hv i)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [deRhamConj_smul]; exact Submodule.smul_mem _ _ hx

theorem spec_cupWedgePiece_eq_map_exteriorPowerH_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (n : ℕ) (pq : ℤ × ℤ) :
    letI := (finiteBetti_abelian X).finite 1
    letI := (finiteBetti_abelian X).finite n
    cupWedgePiece X μ n pq =
      ((abelianWeightOneHodgeStructure X).exteriorPowerH (V := HQ X 1) n pq).map
        (bettiDeRhamHQ X n ∘ₗ
          (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^n (HQ X 1))
            (W := HQ X n) (hT.cupWedgeEquiv n)).toLinearMap) := by
  let := (finiteBetti_abelian X).finite 1
  let := (finiteBetti_abelian X).finite n
  rw [exteriorPowerH_eq_wedgePiece, wedgePiece, Submodule.map_span, cupWedgePiece]
  congr 1
  ext α
  constructor
  · rintro ⟨d, v, hd, hv, rfl⟩
    refine ⟨_, ⟨d, v, hd, hv, rfl⟩, ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hT.complexificationCongr_symm_ιMulti]
  · rintro ⟨_, ⟨d, v, hd, hv, rfl⟩, rfl⟩
    refine ⟨d, v, hd, hv, ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hT.complexificationCongr_symm_ιMulti]

theorem spec_cupWedgePiece_isInternal_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (n : ℕ) :
    DirectSum.IsInternal (cupWedgePiece X μ n) := by
  let := (finiteBetti_abelian X).finite 1
  let := (finiteBetti_abelian X).finite n
  classical
  let eβ := LinearEquiv.ofBijective (bettiDeRhamHQ X n)
    ((HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective n)
  let e := (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^n (HQ X 1))
    (W := HQ X n) (hT.cupWedgeEquiv n)).trans eβ
  have h := ((abelianWeightOneHodgeStructure X).exteriorPowerH_isInternal
    (V := HQ X 1) n).mapEquiv e
  convert h using 2 with pq
  exact spec_cupWedgePiece_eq_map_exteriorPowerH_aux X hT n pq

theorem spec_cupWedgePiece_le_deRhamHodgePiece_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X} (hC : CupFiltered X μ) (n : ℕ)
    (pq : ℤ × ℤ) :
    cupWedgePiece X μ n pq ≤ deRhamHodgePiece X n pq := by
  by_cases hpq : pq.1 + pq.2 = n
  · rw [cupWedgePiece, Submodule.span_le]
    rintro _ ⟨d, v, rfl, hv, rfl⟩
    by_cases hall : ∀ i, (d i).1 + (d i).2 = ((1 : ℕ) : ℤ)
    · simp only [SetLike.mem_coe, deRhamHodgePiece, hpq, ↓reduceIte]
      refine hC.bettiDeRhamHQ_cupMultiC_mem n d v fun i => ?_
      have := hv i
      simp only [cohomologyHodgePiece, hall i, ↓reduceIte, Submodule.mem_comap] at this
      exact this
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      have := hv i
      simp only [cohomologyHodgePiece, hi, ↓reduceIte] at this
      rw [SetLike.mem_coe, (μ.cupMultiC n).map_coord_zero i ((Submodule.mem_bot ℂ).mp this),
        map_zero]
      exact Submodule.zero_mem _
  · rw [spec_cupWedgePiece_eq_bot_aux X μ n pq hpq]
    exact bot_le

theorem spec_isInternal_iff_le_cupWedgePiece_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ) :
    DirectSum.IsInternal (deRhamHodgePiece X n) ↔
      ∀ pq : ℤ × ℤ, deRhamHodgePiece X n pq ≤ cupWedgePiece X μ n pq := by
  constructor
  · intro hD pq x hx
    exact mem_of_map_mem_of_iSupIndep_of_map_le
      (spec_cupWedgePiece_isInternal_aux X hT n).submodule_iSup_eq_top
      hD.submodule_iSupIndep (g := id) Function.injective_id (f := LinearMap.id)
      Function.injective_id
      (fun i => by
        rw [Submodule.map_id]
        exact spec_cupWedgePiece_le_deRhamHodgePiece_aux X hC n i) hx
  · intro h
    have heq : deRhamHodgePiece X n = cupWedgePiece X μ n :=
      funext fun pq => le_antisymm (h pq) (spec_cupWedgePiece_le_deRhamHodgePiece_aux X hC n pq)
    rw [heq]
    exact spec_cupWedgePiece_isInternal_aux X hT n

theorem spec_deRhamHodgePiece_eq_cupWedgePiece_of_opposed_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ)
    (hopp : ∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    deRhamHodgePiece X n = cupWedgePiece X μ n := by
  have hG : Antitone fun q : ℤ => conjHodgeFiltrationComplexSubmodule X q n :=
    fun _ _ h => Submodule.comap_mono (hodgeFiltration_antitone X n h)
  have hle : ∀ pq : ℤ × ℤ, cupWedgePiece X μ n pq ≤
      F^pq.1 H_dR^(n : ℤ)(X) ⊓ conjHodgeFiltrationComplexSubmodule X pq.2 n := by
    intro pq
    by_cases hpq : pq.1 + pq.2 = n
    · have := spec_cupWedgePiece_le_deRhamHodgePiece_aux X hC n pq
      simp only [deRhamHodgePiece, hpq, ↓reduceIte] at this
      exact this
    · rw [spec_cupWedgePiece_eq_bot_aux X μ n pq hpq]
      exact bot_le
  have hopp' : ∀ p : ℤ, F^p H_dR^(n : ℤ)(X) ⊓
      conjHodgeFiltrationComplexSubmodule X ((n : ℤ) + 1 - p) n = ⊥ := by
    intro p
    by_cases hp1 : 1 ≤ p
    · by_cases hpn : p ≤ n
      · exact hopp p hp1 hpn
      · exact hodgePiece_eq_bot_of_lt X (Or.inl (by lia))
    · exact hodgePiece_eq_bot_of_lt X (Or.inr (by lia))
  funext pq
  obtain ⟨p, q⟩ := pq
  by_cases hpq : p + q = n
  · obtain rfl : q = (n : ℤ) - p := by lia
    simp only [deRhamHodgePiece, hpq, ↓reduceIte]
    exact spec_inf_eq_of_opposed_aux (n : ℤ) (spec_cupWedgePiece_isInternal_aux X hT n)
      (spec_cupWedgePiece_eq_bot_aux X μ n) (hodgeFiltration_antitone X n) hG hle hopp' p
  · simp only [deRhamHodgePiece, hpq, ↓reduceIte]
    exact (spec_cupWedgePiece_eq_bot_aux X μ n (p, q) hpq).symm

theorem spec_deRhamHodgePiece_isInternal_of_opposed_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ)
    (hopp : ∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    DirectSum.IsInternal (deRhamHodgePiece X n) := by
  rw [spec_deRhamHodgePiece_eq_cupWedgePiece_of_opposed_aux X hT hC n hopp]
  exact spec_cupWedgePiece_isInternal_aux X hT n

theorem spec_hodgeDecomposition_of_opposed_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ)
    (hopp : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    HodgeDecomposition X := by
  exact spec_hodgeDecomposition_of_isInternal_le_aux X fun n h2 hn =>
    spec_deRhamHodgePiece_isInternal_of_opposed_aux X hT hC n (hopp n h2 hn)

end HodgeLean.Adapters
