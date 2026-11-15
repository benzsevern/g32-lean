import HodgeLean.Foundations.Program.PrymParabolicSkeletaDefs

/-! # Lemmas for stage H3b step C, first part: explicit classes and connecting maps

The class `moduleCatHomologyClass` of an explicit cycle is `homologyπ` of the matching element of
`cycles`, and the connecting map of a short exact sequence of chain complexes sends the class of
`x₃` to the class of `x₁` whenever `x₂` lifts `x₃` and `f x₁ = d x₂` (Mathlib's
`ShortComplex.ShortExact.δ_apply`, restated for explicit classes). Linear maps on singular
chains are determined by their values on simplices, and in a discrete space every singular
`1`-chain has boundary zero. The lifted edges and vertices of step B lie over the base edges and
vertices, paths in the filling over one base path agree where they avoid the marks, and the
lifted cells sit in the skeleta as cells of a `Δ`-complex.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular Convexity

namespace HodgeLean.Foundations.Program

/-- Naturality of the cellular-to-singular map in degree `2`. -/
theorem hg8_chain2_map {ι A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B))
    (σ : ι → C(StdSimplex ℝ (Fin 3), A)) (c : ι →₀ ℤ) :
    hg8_chainMap φ 2 (hg5_chain2 σ c) = hg5_chain2 (fun x ↦ φ.comp (σ x)) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | single x n =>
    simp only [hg5_chain2, Finsupp.linearCombination_single]
    erw [LinearMap.map_smul]
    congr 1
    exact Simplicial.chainOfSimplex_map ℤ (TopCat.toSSet.map (TopCat.ofHom φ)) _

/-- The explicit class of a cycle is `homologyπ` of the matching element of `cycles`. -/
theorem hg8_class_eq_π {R : Type} [CommRing R] (S : ShortComplex (ModuleCat.{0} R))
    (w : LinearMap.ker S.g.hom) :
    S.moduleCatHomologyClass w = S.homologyπ.hom (S.moduleCatCyclesIso.inv.hom w) := by
  have h := congrArg (fun φ ↦ φ.hom w) S.moduleCatCyclesIso_inv_π
  exact h.symm

/-- `cyclesMk` of a complex is the inverse of `moduleCatCyclesIso` on explicit cycles. -/
theorem hg8_cyclesMk_eq {R : Type} [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ) (i j : ℕ)
    (hj : (ComplexShape.down ℕ).next i = j) (w : LinearMap.ker (K.sc i).g.hom)
    (hx : ((forget₂ (ModuleCat R) Ab).map (K.d i j)) w.1 = 0) :
    K.cyclesMk w.1 j hj hx = (K.sc i).moduleCatCyclesIso.inv.hom w := by
  apply (ModuleCat.mono_iff_injective (K.iCycles i)).1 inferInstance
  have h1 := K.i_cyclesMk w.1 j hj hx
  have h2 := congrArg (fun φ ↦ φ.hom w) (K.sc i).moduleCatCyclesIso_inv_iCycles
  exact h1.trans h2.symm

/-- **The connecting map on explicit classes.** For a short exact sequence of chain complexes of
modules, if `x₂` lifts the cycle `w₃` and `f w₁ = d x₂`, then `δ [w₃] = [w₁]`.
Source: Hatcher, *Algebraic Topology*, §2.1 (the boundary map of a short exact sequence of
chain complexes); Mathlib `ShortComplex.ShortExact.δ_apply`. -/
theorem hg8_delta_class {R : Type} [CommRing R]
    (S : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ)) (hS : S.ShortExact) (n : ℕ)
    (w₃ : LinearMap.ker (S.X₃.sc (n + 1)).g.hom) (x₂ : S.X₂.X (n + 1))
    (hx₂ : (S.g.f (n + 1)).hom x₂ = w₃.1)
    (w₁ : LinearMap.ker (S.X₁.sc n).g.hom) (hx₁ : (S.f.f n).hom w₁.1 = (S.X₂.d (n + 1) n).hom x₂) :
    (hS.δ (n + 1) n (by simp)).hom ((S.X₃.sc (n + 1)).moduleCatHomologyClass w₃) =
      (S.X₁.sc n).moduleCatHomologyClass w₁ := by
  have hj : (ComplexShape.down ℕ).next (n + 1) = n := by simp
  have hx₃ : (S.X₃.d (n + 1) n).hom w₃.1 = 0 := by
    have h := w₃.2
    change (S.X₃.d (n + 1) ((ComplexShape.down ℕ).next (n + 1))).hom w₃.1 = 0 at h
    rw [hj] at h
    exact h
  have h := hS.δ_apply (n + 1) n (by simp) w₃.1 hx₃ x₂ hx₂ w₁.1 hx₁ _ rfl
  rw [hg8_class_eq_π, hg8_class_eq_π, ← hg8_cyclesMk_eq _ _ _ hj, ← hg8_cyclesMk_eq _ _ _ rfl]
  exact h

/-! ## Chains on simplices and `H₀` of a discrete space -/

section Chains

open scoped _root_.Simplicial

/-- An explicit class vanishes exactly when the cycle is a boundary. -/
theorem hg8_homologyClass_eq_zero_iff {R : Type} [CommRing R] (S : ShortComplex (ModuleCat.{0} R))
    (w : LinearMap.ker S.g.hom) :
    S.moduleCatHomologyClass w = 0 ↔ w.1 ∈ LinearMap.range S.f.hom := by
  refine ⟨fun h ↦ ?_, hg8_homologyClass_eq_zero S w⟩
  have hq : (LinearMap.range S.moduleCatToCycles).mkQ w = 0 :=
    (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.inv).1 inferInstance
      (h.trans (map_zero _).symm)
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨a, ha⟩ := hq
  exact ⟨a, congrArg Subtype.val ha⟩

/-- Linear maps out of singular chains agreeing on every simplex are equal.
Source: Mathlib `SSet.chainComplex_hom_ext` (chains are free on simplices). -/
theorem hg8_chain_ext {R : Type} [CommRing R] {Y : SSet.{0}} {n : ℕ} {M : Type} [AddCommGroup M]
    [Module R M] (φ ψ : Simplicial.ChainGroup R Y n →ₗ[R] M)
    (h : ∀ σ : Y _⦋n⦌, φ (Simplicial.chainOfSimplex R σ) = ψ (Simplicial.chainOfSimplex R σ)) :
    φ = ψ := by
  have hc : (ModuleCat.ofHom φ : _ ⟶ ModuleCat.of R M) = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : (Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a =
        a • Simplicial.chainOfSimplex R σ := by
      rw [Simplicial.chainOfSimplex, ← map_smul]
      simp
    change φ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

/-- The linear extension to `n`-chains of a function on `n`-simplices.
Source: Hatcher, *Algebraic Topology*, §2.1 (chains are free on simplices); Mathlib
`SSet.isColimitChainComplexXCofan`. -/
def hg8_simplexFun (R : Type) [CommRing R] (Y : SSet.{0}) (n : ℕ) (f : Y _⦋n⦌ → R) :
    Simplicial.ChainGroup R Y n →ₗ[R] R :=
  ((Y.isColimitChainComplexXCofan (ModuleCat.of R R) n).desc
    (Cofan.mk _ fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R R (f σ)))).hom

/-- `hg8_simplexFun` on a single simplex. -/
theorem hg8_simplexFun_chainOfSimplex (R : Type) [CommRing R] (Y : SSet.{0}) (n : ℕ)
    (f : Y _⦋n⦌ → R) (σ : Y _⦋n⦌) :
    hg8_simplexFun R Y n f (Simplicial.chainOfSimplex R σ) = f σ := by
  have h := (Y.isColimitChainComplexXCofan (ModuleCat.of R R) n).fac
    (Limits.Cofan.mk _ fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R R (f σ))) ⟨σ⟩
  have h1 := ConcreteCategory.congr_hom h (1 : R)
  change hg8_simplexFun R Y n f ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) = f σ
  refine h1.trans ?_
  simp

/-- A linear map into singular chains whose range contains every simplex is onto. -/
theorem hg8_range_eq_top {R : Type} [CommRing R] {Y : SSet.{0}} {n : ℕ} {M : Type}
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] Simplicial.ChainGroup R Y n)
    (h : ∀ σ : Y _⦋n⦌, Simplicial.chainOfSimplex R σ ∈ LinearMap.range φ) :
    LinearMap.range φ = ⊤ := by
  have hmk : (LinearMap.range φ).mkQ = 0 := by
    apply hg8_chain_ext
    intro σ
    rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h σ
  rw [eq_top_iff]
  intro x _
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hmk, LinearMap.zero_apply]

/-- In a discrete space the boundary of every singular `1`-chain is zero. -/
theorem hg8_boundary_discrete (X : Type) [TopologicalSpace X] [DiscreteTopology X] :
    Simplicial.boundary ℤ 0 (X := TopCat.toSSet.obj (TopCat.of X)) = 0 := by
  apply hg8_chain_ext
  intro σ
  rw [Simplicial.boundary_chainOfSimplex, Fin.sum_univ_two]
  have hc : HodgeLean.Adapters.simplexPath σ 1 = HodgeLean.Adapters.simplexPath σ 0 := by
    have hp : IsPreconnected (Set.range (HodgeLean.Adapters.simplexPath σ)) :=
      isPreconnected_range (HodgeLean.Adapters.simplexPath σ).continuous
    exact hp.subsingleton ⟨1, rfl⟩ ⟨0, rfl⟩
  have he : (TopCat.toSSet.obj (TopCat.of X)).δ 0 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 1 σ := by
    apply TopCat.toSSetObj₀Equiv.injective
    rw [hg5_obj0_delta_zero, hg5_obj0_delta_one, hc]
  rw [he]
  simp


end Chains

/-! ## The skeletal class of a cellular cycle -/

/-- Singular homology of a discrete space vanishes in positive degrees.
Source: Mathlib `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`. -/
theorem hg8_homology_discrete_eq_zero (X : Type) [TopologicalSpace X] [DiscreteTopology X]
    {n : ℕ} (hn : n ≠ 0) (x : Homology ℤ (TopCat.of X) n) : x = 0 := by
  have h := isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{0} ℤ) n
    (ModuleCat.of ℤ ℤ) (TopCat.of X) hn
  exact (ModuleCat.isZero_iff_subsingleton.1 h).elim x 0

/-- The edge chain of a cellular cycle is a cycle of `T¹`. -/
theorem hg8_d_chain1_skel {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T) (z : hg2_Edge G r →₀ ℤ)
    (hz : z ∈ LinearMap.ker (hg2_bd1 ℤ g)) :
    hg5_chain1 (hg8_edge1 F) z ∈
      LinearMap.ker ((SingularChainComplex ℤ (TopCat.of (hg8_skel1 F))).sc 1).g.hom := by
  have hends : ∀ ε, hg8_edge1 F ε 0 = hg8_vert1 F (hg2_src g ε) ∧
      hg8_edge1 F ε 1 = hg8_vert1 F (hg2_tgt g ε) :=
    fun ε ↦ ⟨Subtype.ext (F.ends ε).1, Subtype.ext (F.ends ε).2⟩
  have key : ∀ j, ((SingularChainComplex ℤ (TopCat.of (hg8_skel1 F))).d 1 j).hom
      (hg5_chain1 (hg8_edge1 F) z) = 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      change Simplicial.boundary ℤ 0 (hg5_chain1 (hg8_edge1 F) z) = 0
      rw [hg5_bd_chain1 (hg8_edge1 F) (hg8_vert1 F) _ _ hends z]
      change hg5_chain0 (hg8_vert1 F) (hg2_bd1 ℤ g z) = 0
      rw [LinearMap.mem_ker.mp hz, map_zero]
    · rw [HomologicalComplex.shape _ _ _ (by simp only [ComplexShape.down_Rel]; omega)]
      rfl
  exact key _


/-- The class in `H₁(T¹)` of the edge chain of a cellular cycle.
Source: Hatcher, *Algebraic Topology*, §2.2 (proof of Theorem 2.35). -/
def hg8_skelClass {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T) (z : LinearMap.ker (hg2_bd1 ℤ g)) :
    Homology ℤ (TopCat.of (hg8_skel1 F)) 1 :=
  ((SingularChainComplex ℤ (TopCat.of (hg8_skel1 F))).sc 1).moduleCatHomologyClass
    ⟨hg5_chain1 (hg8_edge1 F) z.1, hg8_d_chain1_skel F z.1 z.2⟩

/-- Including `T¹` into `T` sends the skeletal class of `z` to `hg8_H1map` of its class. -/
theorem hg8_skelClass_incl {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T) (z : LinearMap.ker (hg2_bd1 ℤ g)) :
    (HomologicalComplex.homologyMap (relativeChainShortComplex ℤ (hg8_pair21 F)).f 1).hom
      (hg8_skelClass F z) = hg8_H1map F (Submodule.Quotient.mk z) := by
  have e1 : hg8_H1map F (Submodule.Quotient.mk z) =
      ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass (hg8_cycle1 F z) := rfl
  rw [e1]
  refine (ShortComplex.moduleCatHomologyClass_naturality _ _).trans
    (congrArg (ShortComplex.moduleCatHomologyClass _) (Subtype.ext ?_))
  change hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 1 (hg5_chain1 (hg8_edge1 F) z.1) =
    hg5_chain1 F.edge z.1
  rw [hg8_chain1_map]
  rfl

/-- Projecting to `H₁(T¹, T⁰)` sends the skeletal class of `z` to its edge class. -/
theorem hg8_skelClass_proj {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T) (z : LinearMap.ker (hg2_bd1 ℤ g)) :
    (HomologicalComplex.homologyMap (relativeChainShortComplex ℤ (hg8_pair10 F)).g 1).hom
      (hg8_skelClass F z) = hg8_edgeRel F z.1 :=
  ShortComplex.moduleCatHomologyClass_naturality _ _


/-! ## Faces, lifted edges and the skeleta of the lifted cells -/

/-- A point of `Δ²` with weight `0` at `k` lies on the face opposite `k`. -/
theorem hg8_face_preimage (a : StdSimplex ℝ (Fin 3)) (k : Fin 3) (hk : a.weights k = 0) :
    ∃ b : StdSimplex ℝ (Fin 2), StdSimplex.map k.succAbove b = a := by
  let w : Fin 2 →₀ ℝ := Finsupp.equivFunOnFinite.symm fun j ↦ a.weights (k.succAbove j)
  have hw : ∀ j, w j = a.weights (k.succAbove j) := fun j ↦ rfl
  refine ⟨⟨w, fun j ↦ by rw [hw]; exact a.weights_nonneg _, ?_⟩, ?_⟩
  · rw [Finsupp.sum_fintype _ _ (by simp)]
    have := a.total_of_fintype
    rw [Fin.sum_univ_succAbove _ k, hk, zero_add] at this
    simpa [hw] using this
  · ext i
    simp only [StdSimplex.weights_map]
    rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
    · rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), hk]
    · rw [Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective w j]
      rfl

/-- A point of a singular triangle with weight `0` at `k` lies on its face `k`. -/
theorem hg8_face_point {X : Type} [TopologicalSpace X] (σ : C(StdSimplex ℝ (Fin 3), X))
    (a : StdSimplex ℝ (Fin 3)) (k : Fin 3) (hk : a.weights k = 0) :
    ∃ t, σ a = hg5_face σ k t := by
  obtain ⟨b, rfl⟩ := hg8_face_preimage a k hk
  refine ⟨StdSimplex.homeomorphI b, ?_⟩
  simp [hg5_face]

/-- The base edge under a lifted edge.
Source: `hg2_Edge`; `hg5_triBase`. -/
def hg8_edgeBase {G : Type*} : hg2_Edge G 13 → hg2_Edge Unit 13
  | Sum.inl (i, _) => Sum.inl (i, ())
  | Sum.inr (Sum.inl (i, _)) => Sum.inr (Sum.inl (i, ()))
  | Sum.inr (Sum.inr (i, _)) => Sum.inr (Sum.inr (i, ()))

/-- The lifted edges lie over the base edges (`hg5_faces`). -/
theorem hg8_f_liftEdge {G C : Type} [TopologicalSpace C] (f : C → OnePoint ℂ)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, ∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) (ε : hg2_Edge G 13) (s : unitInterval) :
    f (hg5_liftEdge L ε s) = hg5_edge (hg8_edgeBase ε) s := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · change f (L _ _) = _
    rw [hL]
    exact congrArg (fun p : C(unitInterval, OnePoint ℂ) ↦ p s) (hg5_faces (Sum.inl (i, ()))).2.2
  · change f (L _ _) = _
    rw [hL]
    exact congrArg (fun p : C(unitInterval, OnePoint ℂ) ↦ p s) (hg5_faces (Sum.inl (i, ()))).2.1
  · change f (L _ _) = _
    rw [hL]
    exact congrArg (fun p : C(unitInterval, OnePoint ℂ) ↦ p s) (hg5_faces (Sum.inl (i, ()))).1

/-- Every vertex of `X̃(g)` is an endpoint of an edge. -/
theorem hg8_vert_end {G : Type} [Group G] (g : Fin 13 → G) (v : hg2_Vert g) :
    ∃ ε, hg2_src g ε = v ∨ hg2_tgt g ε = v := by
  rcases v with x | z | ⟨i, c⟩
  · exact ⟨Sum.inl (0, x), Or.inl rfl⟩
  · refine ⟨Sum.inr (Sum.inl (0, z)), Or.inr ?_⟩
    simp [hg2_tgt, hg2_Q]
  · refine ⟨Sum.inl (i, c.out), Or.inr ?_⟩
    simp [hg2_tgt]

/-- A point of `[0, 1]` outside `(0, 1)` is an endpoint. -/
theorem hg8_unit_endpoint (t : unitInterval) (ht : t ∉ Set.Ioo 0 1) : t = 0 ∨ t = 1 := by
  by_contra h
  push Not at h
  exact ht ⟨lt_of_le_of_ne unitInterval.nonneg' (Ne.symm h.1),
    lt_of_le_of_ne unitInterval.le_one' h.2⟩

/-- A point of `[0, 1]` is an endpoint or interior. -/
theorem hg8_unit_endpoint' (s : unitInterval) : s = 0 ∨ s = 1 ∨ s ∈ Set.Ioo 0 1 := by
  by_cases h : s ∈ Set.Ioo 0 1
  · exact Or.inr (Or.inr h)
  · rcases hg8_unit_endpoint s h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- The endpoints of the base edges are base vertices (`hg5_edge_ends`). -/
theorem hg8_edge_endpoint_vert (ε : hg2_Edge Unit 13) (s : unitInterval) (hs : s ∉ Set.Ioo 0 1) :
    ∃ w, hg5_edge ε s = hg5_vert w := by
  rcases hg8_unit_endpoint s hs with rfl | rfl
  · exact ⟨_, (hg5_edge_ends ε).1⟩
  · exact ⟨_, (hg5_edge_ends ε).2⟩

/-- Each base edge is injective (`hg5_open_cells`, `hg5_edge_ends`). -/
theorem hg8_edge_injective (ε : hg2_Edge Unit 13) : Function.Injective (hg5_edge ε) := by
  obtain ⟨-, -, hc, hd, he⟩ := hg5_open_cells
  intro s s' h
  by_cases hs : s ∈ Set.Ioo 0 1 <;> by_cases hs' : s' ∈ Set.Ioo 0 1
  · exact (hc ε ε s s' hs hs' h).2
  · obtain ⟨w, hw⟩ := hg8_edge_endpoint_vert ε s' hs'
    exact absurd (h.trans hw) (hd ε s hs w)
  · obtain ⟨w, hw⟩ := hg8_edge_endpoint_vert ε s hs
    exact absurd (h.symm.trans hw) (hd ε s' hs' w)
  · have e0 := hg8_unit_endpoint
    have hne : hg2_src hg5_one ε ≠ hg2_tgt hg5_one ε := by
      rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;> simp [hg2_src, hg2_tgt]
    have h01 : hg5_edge ε 0 ≠ hg5_edge ε 1 := by
      rw [(hg5_edge_ends ε).1, (hg5_edge_ends ε).2]
      exact fun e ↦ hne (he e)
    rcases e0 s hs with rfl | rfl <;> rcases e0 s' hs' with rfl | rfl
    · rfl
    · exact absurd h h01
    · exact absurd h.symm h01
    · rfl


/-- **Unique lifting on a preconnected parameter set.** Two paths in the filling over the same
base path, avoiding the marks on a preconnected set `S` and meeting at one point of `S`, agree on
`S`: they are lifts through the covering `π`.
Source: Hatcher, *Algebraic Topology*, Proposition 1.34; Mathlib `IsCoveringMap.eq_of_comp_eq`. -/
theorem hg8_lift_unique_on {G U C : Type} [Group G] [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G) [TopologicalSpace C]
    (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (p q : C(unitInterval, C)) (S : Set unitInterval)
    (hS : _root_.IsPreconnected S) (hpq : ∀ t ∈ S, f (p t) = f (q t))
    (hm : ∀ t ∈ S, f (p t) ∉ Set.range (b6_branch mr_base)) {s t₀ : unitInterval} (hs : s ∈ S)
    (ht : t₀ ∈ S) (h : p s = q s) : p t₀ = q t₀ := by
  have hpW : ∀ t ∈ S, p t ∈ Set.range ι := fun t ht ↦ by rw [hιr]; exact hm t ht
  have hqW : ∀ t ∈ S, q t ∈ Set.range ι := fun t ht ↦ by
    rw [hιr]; change f (q t) ∉ _; rw [← hpq t ht]; exact hm t ht
  let e := hι.isEmbedding.toHomeomorph
  have hιe : ∀ x, ι (e.symm x) = x.1 := fun x ↦ congrArg Subtype.val (e.apply_symm_apply x)
  have : PreconnectedSpace S := Subtype.preconnectedSpace hS
  let g₁ : S → U := fun t ↦ e.symm ⟨p t, hpW t t.2⟩
  let g₂ : S → U := fun t ↦ e.symm ⟨q t, hqW t t.2⟩
  have hc₁ : Continuous g₁ := e.symm.continuous.comp
    (Continuous.subtype_mk (p.continuous.comp continuous_subtype_val) _)
  have hc₂ : Continuous g₂ := e.symm.continuous.comp
    (Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) _)
  have he : π ∘ g₁ = π ∘ g₂ := by
    funext t
    apply Subtype.ext
    change ((π (g₁ t) : OnePoint ℂ)) = π (g₂ t)
    rw [← hfι, ← hfι, hιe, hιe]
    exact hpq t t.2
  have h₀ : g₁ ⟨s, hs⟩ = g₂ ⟨s, hs⟩ := congrArg e.symm (Subtype.ext h)
  have := congrFun ((hπ.isCoveringMap).eq_of_comp_eq hc₁ hc₂ he ⟨s, hs⟩ h₀) ⟨t₀, ht⟩
  have h' := congrArg ι this
  rwa [hιe, hιe] at h'

/-- **Skeletal position of the lifted cells.** A boundary point of a lifted triangle lies in
`C¹`, an interior point does not, and an interior point of a lifted edge is not a lifted vertex.
Source: `hg5_open_cells`, `hg5_lift_faces`, `hg5_lift_vertices`. -/
theorem hg8_lift_skel {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction G C]
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer G c) = orderOf (g j))
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    (∀ τ a, ¬ (∀ k, 0 < a.weights k) → L τ a ∈ hg8_skel1 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) ∧
      (∀ τ a, (∀ k, 0 < a.weights k) → L τ a ∉ hg8_skel1 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) ∧
      (∀ (ε : hg2_Edge G 13) (s : unitInterval), s ∈ Set.Ioo 0 1 →
        ∀ v, hg5_liftEdge L ε s ≠ hg5_liftVert g L v) := by
  obtain ⟨-, hb, -, hd, -⟩ := hg5_open_cells
  have hfe := hg8_f_liftEdge f L (fun τ ↦ (hL τ).1)
  obtain ⟨hends, -⟩ := hg5_lift_vertices U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr
    hstab ι hι hιr hfι hιG L hL
  have hvert : ∀ v, ∃ (ε' : hg2_Edge G 13) (e : unitInterval), e ∉ Set.Ioo 0 1 ∧
      hg5_liftVert g L v = hg5_liftEdge L ε' e := by
    intro v
    obtain ⟨ε', hε'⟩ := hg8_vert_end g v
    rcases hε' with rfl | rfl
    · exact ⟨ε', 0, fun h ↦ lt_irrefl _ h.1, (hends ε').1.symm⟩
    · exact ⟨ε', 1, fun h ↦ lt_irrefl _ h.2, (hends ε').2.symm⟩
  refine ⟨fun τ a ha ↦ ?_, fun τ a ha hmem ↦ ?_, fun ε s hs v h ↦ ?_⟩
  · push Not at ha
    obtain ⟨k, hk⟩ := ha
    obtain ⟨t, ht⟩ := hg8_face_point (L τ) a k (le_antisymm hk (a.weights_nonneg k))
    have hfaces := hg5_lift_faces U π hπ y₀ hy₀ u₀ g γ hγ hroot C f hf ι hι hιr hfι hιG L hL τ
    refine Or.inr (Set.mem_iUnion.2 ?_)
    rw [ht]
    fin_cases k
    · exact ⟨hg2_face0 g τ, t, (congrArg (fun p : C(unitInterval, C) ↦ p t) hfaces.1).symm⟩
    · exact ⟨hg2_face1 τ, t, (congrArg (fun p : C(unitInterval, C) ↦ p t) hfaces.2.1).symm⟩
    · exact ⟨hg2_face2 τ, t, (congrArg (fun p : C(unitInterval, C) ↦ p t) hfaces.2.2).symm⟩
  · have hedge : ∀ ε s, L τ a ≠ hg5_liftEdge L ε s := by
      intro ε s h
      have h' := congrArg f h
      rw [(hL τ).1, hfe] at h'
      exact hb _ a ha _ s h'
    rcases hmem with ⟨v, hv⟩ | hmem
    · obtain ⟨ε', e, -, hve⟩ := hvert v
      exact hedge ε' e (hv.symm.trans hve)
    · obtain ⟨ε, s, hs⟩ := Set.mem_iUnion.1 hmem
      exact hedge ε s hs.symm
  · obtain ⟨ε', e, he, hve⟩ := hvert v
    obtain ⟨w, hw⟩ := hg8_edge_endpoint_vert (hg8_edgeBase ε') e he
    have h' := congrArg f h
    rw [hve, hfe, hfe, hw] at h'
    exact hd _ s hs w h'

example {R : Type} [CommRing R] (S : ShortComplex (ModuleCat.{0} R)) :
    S.moduleCatHomologyClass 0 = 0 := map_zero _

end HodgeLean.Foundations.Program
