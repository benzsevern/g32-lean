import HodgeLean.Foundations.Program.PrymParabolicIntersectionWalks

set_option linter.unusedSectionVars false

noncomputable section
namespace HodgeLean.Foundations.Program

open Classical CategoryTheory AlgebraicTopology AlgebraicTopology.Singular

section Reindex

variable {G : Type} [Group G] [Fintype G] (g : Fin 13 → G)

/-- The alternating face combination `α(face₀ τ) s₀ − α(face₁ τ) s₁ + α(face₂ τ) s₂` of a triangle.
Source: Hatcher, *Algebraic Topology*, §2.1, the simplicial boundary. -/
def hga_faceComb {M : Type} [AddCommGroup M] (α : hg2_Edge G 13 → ℤ)
    (s : hg2_Tri G 13 → Fin 3 → M) (τ : hg2_Tri G 13) : M :=
  α (hg2_face0 g τ) • s τ 0 - α (hg2_face1 τ) • s τ 1 + α (hg2_face2 τ) • s τ 2

/-- **Regrouping by edges.** The sum over edges of `α ε` times the difference of the face values in
the incoming and outgoing triangles is the orientation-weighted sum of the alternating face
combinations. -/
theorem hga_edge_sum_reindex {M : Type} [AddCommGroup M] (α : hg2_Edge G 13 → ℤ)
    (s : hg2_Tri G 13 → Fin 3 → M) :
    ∑ ε, α ε • (s (hga_triIn ε) (hga_faceIdx ε) - s (hga_triOut g ε) (hga_faceIdx ε)) =
      ∑ p : Fin 13 × G, (hga_faceComb g α s (Sum.inl p) - hga_faceComb g α s (Sum.inr p)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [hga_triIn, hga_triOut, hga_faceIdx, hga_faceComb, hg2_face0, hg2_face1, hg2_face2]
  -- reindex the arc terms and the `h` terms of the outgoing triangles
  have hf : ∑ p : Fin 13 × G, α (Sum.inr (Sum.inl p)) • s (Sum.inr ((finRotate 13).symm p.1, p.2)) 1 =
      ∑ p : Fin 13 × G, α (Sum.inr (Sum.inl (finRotate 13 p.1, p.2))) • s (Sum.inr p) 1 := by
    apply Fintype.sum_equiv ((finRotate 13).symm.prodCongr (Equiv.refl G))
    rintro ⟨i, x⟩
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
      Equiv.apply_symm_apply]
  have hh : ∑ p : Fin 13 × G, α (Sum.inr (Sum.inr p)) • s (Sum.inr (p.1, p.2 * g p.1)) 0 =
      ∑ p : Fin 13 × G, α (Sum.inr (Sum.inr (p.1, p.2 * (g p.1)⁻¹))) • s (Sum.inr p) 0 := by
    let e : Fin 13 × G ≃ Fin 13 × G :=
      { toFun := fun p ↦ (p.1, p.2 * g p.1)
        invFun := fun p ↦ (p.1, p.2 * (g p.1)⁻¹)
        left_inv := fun p ↦ by simp
        right_inv := fun p ↦ by simp }
    apply Fintype.sum_equiv e
    intro p
    simp [e]
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show ∑ p : Fin 13 × G, α (Sum.inr (Sum.inl (p.1, p.2))) •
      s (Sum.inr ((finRotate 13).symm p.1, p.2)) 1 = _ from hf]
  rw [show ∑ p : Fin 13 × G, α (Sum.inr (Sum.inr (p.1, p.2))) • s (Sum.inr (p.1, p.2 * g p.1)) 0 = _
    from hh]
  abel

/-- **Balance of a cocycle.** For a cellular cocycle `α`, the sums of `α ε F(τ_out ε)` and of
`α ε F(τ_in ε)` agree. -/
theorem hga_cocycle_balance {M : Type} [AddCommGroup M] (α : hg2_Edge G 13 → ℤ)
    (hα : hg2_delta1 ℤ ℤ g α = 0) (F : hg2_Tri G 13 → M) :
    ∑ ε, α ε • F (hga_triIn ε) = ∑ ε, α ε • F (hga_triOut g ε) := by
  have h := hga_edge_sum_reindex g α (fun τ _ ↦ F τ)
  have hτ : ∀ τ, hga_faceComb g α (fun τ _ ↦ F τ) τ = (hg2_delta1 ℤ ℤ g α τ) • F τ := by
    intro τ
    simp only [hga_faceComb, hg2_delta1, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.funLeft_apply, Pi.add_apply, Pi.sub_apply, add_smul, sub_smul]
  simp only [hτ, hα, Pi.zero_apply, zero_smul, sub_zero, Finset.sum_const_zero] at h
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simpa only [smul_sub] using h

end Reindex

section Algebra

/-- The module scalar action of `ℤ` on a singular chain group is the additive-group one. -/
theorem hga_chain_smul_eq (X : SSet.{0}) (k : ℕ) (n : ℤ) (x : Simplicial.ChainGroup ℤ X k) :
    @HSMul.hSMul ℤ _ _ (@instHSMul ℤ _ (inferInstance :
      Module ℤ (Simplicial.ChainGroup ℤ X k)).toDistribMulAction.toDistribSMul.toSMul) n x = n • x :=
  int_smul_eq_zsmul (inferInstance : Module ℤ (Simplicial.ChainGroup ℤ X k)) n x

theorem hga_lc_single (X : SSet.{0}) (k : ℕ) {ι : Type} (f : ι → Simplicial.ChainGroup ℤ X k)
    (τ : ι) : Finsupp.linearCombination ℤ f (Finsupp.single τ 1) = f τ := by
  rw [Finsupp.linearCombination_single]
  exact (hga_chain_smul_eq X k 1 (f τ)).trans (one_zsmul _)

theorem hga_lc_fintype (X : SSet.{0}) (k : ℕ) {ι : Type} [Fintype ι]
    (f : ι → Simplicial.ChainGroup ℤ X k) (c : ι →₀ ℤ) :
    Finsupp.linearCombination ℤ f c = ∑ i, c i • f i := by
  rw [Finsupp.linearCombination_apply]
  refine (Finsupp.sum_fintype c _ ?_).trans (Finset.sum_congr rfl fun i _ ↦ hga_chain_smul_eq X k _ _)
  intro i
  exact (hga_chain_smul_eq X k 0 _).trans (zero_zsmul _)

theorem hga_sum_smul_sum {M : Type} [AddCommGroup M] {ι κ : Type} [Fintype ι] [Fintype κ]
    (a : ι → ℤ) (b : ι → κ → ℤ) (X : κ → M) :
    ∑ i, a i • ∑ j, b i j • X j = ∑ j, (∑ i, a i * b i j) • X j := by
  simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

end Algebra

section Chains

variable {G : Type} [Group G] [Fintype G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]

/-- The singular chain of the dual spoke of face `k` of a realized triangle.
Source: `hga_dualSpoke`. -/
def hga_spokeChain (D : hg8_DeltaMap g T) (τ : hg2_Tri G 13) (k : Fin 3) :
    Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 1 :=
  Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (hga_dualSpoke (D.tri τ) k))

/-- The singular chain of the dual edge of `ε`: spoke into the incoming triangle minus spoke into
the outgoing one. Source: `hga_dualChain`. -/
def hga_dualEdgeChain (D : hg8_DeltaMap g T) (ε : hg2_Edge G 13) :
    Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 1 :=
  hga_spokeChain D (hga_triIn ε) (hga_faceIdx ε) - hga_spokeChain D (hga_triOut g ε) (hga_faceIdx ε)

/-- The singular chain of a dual walk.
Source: `hga_coef`, `hga_dualEdgeChain`. -/
def hga_dWalkChain (D : hg8_DeltaMap g T) (L : List (hg2_Edge G 13 × Bool)) :
    Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 1 :=
  ∑ ε, hga_coef L ε • hga_dualEdgeChain D ε

/-- The singular chain of an edge walk.
Source: `hga_coef`, `hg5_chain1`. -/
def hga_pWalkChain (D : hg8_DeltaMap g T) (L : List (hg2_Edge G 13 × Bool)) :
    Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 1 :=
  ∑ ε, hga_coef L ε • Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (D.edge ε))

theorem hga_dualChain_eq_edges (D : hg8_DeltaMap g T) (α : hg2_Edge G 13 → ℤ) :
    hga_dualChain D α hg2_orient = ∑ ε, α ε • hga_dualEdgeChain D ε := by
  have h := hga_edge_sum_reindex g α (fun τ k ↦ hga_spokeChain D τ k)
  simp only [hga_dualEdgeChain]
  rw [h]
  unfold hga_dualChain hg2_orient
  simp only [map_sum, map_sub, hga_lc_single]
  rw [← Finset.sum_product']
  rw [Finset.univ_product_univ]
  rfl

/-- **Decomposition of the dual chain** into the chains of cyclic dual walks
`W(τ_out ε) · ε · W(τ_in ε)⁻¹`. -/
theorem hga_dualChain_decomp (D : hg8_DeltaMap g T) (α : hg2_Edge G 13 → ℤ)
    (hα : hg2_delta1 ℤ ℤ g α = 0) (W : hg2_Tri G 13 → List (hg2_Edge G 13 × Bool)) :
    hga_dualChain D α hg2_orient =
      ∑ ε₁, α ε₁ • hga_dWalkChain D
        (W (hga_triOut g ε₁) ++ [(ε₁, true)] ++ hga_rev (W (hga_triIn ε₁))) := by
  rw [hga_dualChain_eq_edges]
  simp only [hga_dWalkChain, hga_coef_append, hga_coef_rev, hga_coef_single]
  rw [hga_sum_smul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  congr 1
  have hb := hga_cocycle_balance g α hα (fun τ ↦ hga_coef (W τ) ε)
  simp only [smul_eq_mul] at hb
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, hb]
  have hδ : ∑ x, α x * (if x = ε then 1 else 0) = α ε := by
    simp [mul_ite, Finset.sum_ite_eq']
  rw [hδ]
  ring

end Chains

section Cycles

variable {G : Type} [Group G] [Fintype G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]

/-- **Balance of a cycle.** For a cellular `1`-cycle `z`, the sums of `z ε F(src ε)` and of
`z ε F(tgt ε)` agree. -/
theorem hga_cycle_balance (z : hg2_Edge G 13 →₀ ℤ) (hz : hg2_bd1 ℤ g z = 0)
    (F : hg2_Vert g → ℤ) :
    ∑ ε, z ε * F (hg2_src g ε) = ∑ ε, z ε * F (hg2_tgt g ε) := by
  have h : Finsupp.mapDomain (hg2_tgt g) z = Finsupp.mapDomain (hg2_src g) z := by
    have := hz
    simp only [hg2_bd1, LinearMap.sub_apply, Finsupp.lmapDomain_apply] at this
    exact sub_eq_zero.mp this
  have key : ∀ f : hg2_Edge G 13 → hg2_Vert g,
      (Finsupp.mapDomain f z).sum (fun v n ↦ n * F v) = ∑ ε, z ε * F (f ε) := by
    intro f
    rw [Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)
  rw [← key, ← key, h]

/-- **Decomposition of a cellular cycle** into the chains of cyclic edge walks
`W(src ε) · ε · W(tgt ε)⁻¹`. -/
theorem hga_cycle_decomp (D : hg8_DeltaMap g T) (z : hg2_Edge G 13 →₀ ℤ)
    (hz : hg2_bd1 ℤ g z = 0) (W : hg2_Vert g → List (hg2_Edge G 13 × Bool)) :
    hg5_chain1 D.edge z =
      ∑ ε₁, z ε₁ • hga_pWalkChain D (W (hg2_src g ε₁) ++ [(ε₁, true)] ++ hga_rev (W (hg2_tgt g ε₁))) := by
  rw [hg5_chain1, hga_lc_fintype]
  simp only [hga_pWalkChain, hga_coef_append, hga_coef_rev, hga_coef_single]
  rw [hga_sum_smul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  congr 1
  have hb := hga_cycle_balance z hz (fun v ↦ hga_coef (W v) ε)
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, hb]
  have hδ : ∑ x, z x * (if x = ε then 1 else 0) = z ε := by
    simp [mul_ite, Finset.sum_ite_eq']
  rw [hδ]
  ring

end Cycles

end HodgeLean.Foundations.Program
