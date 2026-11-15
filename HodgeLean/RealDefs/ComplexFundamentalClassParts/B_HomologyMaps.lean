import HodgeLean.RealDefs.ComplexFundamentalClassChainDefs

/-! # Element-level homology lemmas for the relative Mayer–Vietoris sequence

Composition, sums and biproduct components of chain maps on rational homology classes, and the
composition of support restrictions on relative homology.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

lemma homologyMap_hom_comp_apply {K L N : ChainCategory ℚ} (f : K ⟶ L) (g : L ⟶ N) (i : ℕ)
    (x : K.homology i) :
    (HomologicalComplex.homologyMap g i).hom ((HomologicalComplex.homologyMap f i).hom x) =
      (HomologicalComplex.homologyMap (f ≫ g) i).hom x := by
  rw [HomologicalComplex.homologyMap_comp]
  rfl

lemma homologyMap_hom_neg_apply {K L : ChainCategory ℚ} (f : K ⟶ L) (i : ℕ)
    (x : K.homology i) :
    (HomologicalComplex.homologyMap (-f) i).hom x =
      -(HomologicalComplex.homologyMap f i).hom x := by
  rw [HomologicalComplex.homologyMap_neg]
  rfl

lemma homologyMap_hom_add_apply {K L : ChainCategory ℚ} (f g : K ⟶ L) (i : ℕ)
    (x : K.homology i) :
    (HomologicalComplex.homologyMap (f + g) i).hom x =
      (HomologicalComplex.homologyMap f i).hom x + (HomologicalComplex.homologyMap g i).hom x := by
  rw [HomologicalComplex.homologyMap_add]
  rfl

lemma homologyMap_hom_zero_apply {K L : ChainCategory ℚ} (i : ℕ) (x : K.homology i) :
    (HomologicalComplex.homologyMap (0 : K ⟶ L) i).hom x = 0 := by
  rw [HomologicalComplex.homologyMap_zero]
  rfl

lemma homologyMap_hom_id_apply {K : ChainCategory ℚ} (i : ℕ) (x : K.homology i) :
    (HomologicalComplex.homologyMap (𝟙 K) i).hom x = x := by
  rw [HomologicalComplex.homologyMap_id]
  rfl

/-- A homology class of a biproduct of chain complexes is zero when both components are zero. -/
lemma homology_biprod_eq_zero {K L : ChainCategory ℚ} (i : ℕ) (x : (K ⊞ L).homology i)
    (h₁ : (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) i).hom x = 0)
    (h₂ : (HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) i).hom x = 0) :
    x = 0 := by
  have htot : x = (HomologicalComplex.homologyMap (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr
      : K ⊞ L ⟶ K ⊞ L) i).hom x := by
    rw [biprod.total, homologyMap_hom_id_apply]
  rw [htot, homologyMap_hom_add_apply, ← homologyMap_hom_comp_apply, ← homologyMap_hom_comp_apply,
    h₁, h₂, map_zero, map_zero, add_zero]

/-- Exactness at the middle of the homology sequence of a short exact sequence
`K → P ⊞ Q → N` with maps `(u, -v)` and `(p, q)`: classes on `P` and `Q` with the same image in
`N` come from one class on `K`. -/
lemma homology_exact_middle_of_shortExact {K P Q N : ChainCategory ℚ} (u : K ⟶ P) (v : K ⟶ Q)
    (p : P ⟶ N) (q : Q ⟶ N) (w : biprod.lift u (-v) ≫ biprod.desc p q = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) (i : ℕ) (a : P.homology i) (b : Q.homology i)
    (hab : (HomologicalComplex.homologyMap p i).hom a = (HomologicalComplex.homologyMap q i).hom b) :
    ∃ c : K.homology i, (HomologicalComplex.homologyMap u i).hom c = a ∧
      (HomologicalComplex.homologyMap v i).hom c = b := by
  have hex := (ShortComplex.moduleCat_exact_iff _).1 (hS.homology_exact₂ i)
  let x := (HomologicalComplex.homologyMap (biprod.inl : P ⟶ P ⊞ Q) i).hom a -
    (HomologicalComplex.homologyMap (biprod.inr : Q ⟶ P ⊞ Q) i).hom b
  obtain ⟨c, hc⟩ := hex x (by
    change (HomologicalComplex.homologyMap (biprod.desc p q) i).hom x = 0
    simp only [x, map_sub, homologyMap_hom_comp_apply, biprod.inl_desc, biprod.inr_desc, hab,
      sub_self])
  change (HomologicalComplex.homologyMap (biprod.lift u (-v)) i).hom c = x at hc
  refine ⟨c, ?_, ?_⟩
  · have h := congrArg (HomologicalComplex.homologyMap (biprod.fst : P ⊞ Q ⟶ P) i).hom hc
    simpa only [x, map_sub, homologyMap_hom_comp_apply, biprod.lift_fst, biprod.inl_fst,
      biprod.inr_fst, homologyMap_hom_id_apply, homologyMap_hom_zero_apply, sub_zero] using h
  · have h := congrArg (HomologicalComplex.homologyMap (biprod.snd : P ⊞ Q ⟶ Q) i).hom hc
    simpa only [x, map_sub, homologyMap_hom_comp_apply, biprod.lift_snd, biprod.inl_snd,
      biprod.inr_snd, homologyMap_hom_id_apply, homologyMap_hom_zero_apply, zero_sub,
      homologyMap_hom_neg_apply, neg_inj] using h

/-- Exactness at the left of the homology sequence of a short exact sequence
`K → P ⊞ Q → N` with maps `(u, -v)` and `(p, q)`: when `H_{i+1}(N) = 0`, a class on `K` that
vanishes on `P` and on `Q` is zero. -/
lemma homology_exact_left_of_shortExact {K P Q N : ChainCategory ℚ} (u : K ⟶ P) (v : K ⟶ Q)
    (p : P ⟶ N) (q : Q ⟶ N) (w : biprod.lift u (-v) ≫ biprod.desc p q = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) (i : ℕ) (hvan : Subsingleton (N.homology (i + 1)))
    (c : K.homology i) (hu : (HomologicalComplex.homologyMap u i).hom c = 0)
    (hv : (HomologicalComplex.homologyMap v i).hom c = 0) : c = 0 := by
  have hex := (ShortComplex.moduleCat_exact_iff _).1 (hS.homology_exact₁ (i + 1) i rfl)
  obtain ⟨y, hy⟩ := hex c (by
    change (HomologicalComplex.homologyMap (biprod.lift u (-v)) i).hom c = 0
    apply homology_biprod_eq_zero
    · rw [homologyMap_hom_comp_apply, biprod.lift_fst]
      exact hu
    · rw [homologyMap_hom_comp_apply, biprod.lift_snd, homologyMap_hom_neg_apply, hv, neg_zero])
  change (hS.δ (i + 1) i rfl).hom y = c at hy
  rw [← hy, @Subsingleton.elim _ hvan y 0, map_zero]

/-- If `p ≫ φ = r` and `q ≫ φ = s` with `φ` a quasi-isomorphism, classes with the same image
under `r` and `s` have the same image under `p` and `q`. -/
lemma homologyMap_eq_of_comp_quasiIso {P Q N N' : ChainCategory ℚ} (p : P ⟶ N) (q : Q ⟶ N)
    (φ : N ⟶ N') [QuasiIso φ] (r : P ⟶ N') (s : Q ⟶ N') (hr : p ≫ φ = r) (hs : q ≫ φ = s)
    (i : ℕ) (a : P.homology i) (b : Q.homology i)
    (hab : (HomologicalComplex.homologyMap r i).hom a = (HomologicalComplex.homologyMap s i).hom b) :
    (HomologicalComplex.homologyMap p i).hom a = (HomologicalComplex.homologyMap q i).hom b := by
  have hinj : Function.Injective (HomologicalComplex.homologyMap φ i).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [homologyMap_hom_comp_apply, homologyMap_hom_comp_apply, hr, hs]
  exact hab

/-- The homology of the source of a quasi-isomorphism vanishes where that of its target does. -/
lemma homology_subsingleton_of_quasiIso {N N' : ChainCategory ℚ} (φ : N ⟶ N') [QuasiIso φ]
    (i : ℕ) (h : Subsingleton (N'.homology i)) : Subsingleton (N.homology i) :=
  ⟨fun _ _ => ((ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap φ i)).1
    inferInstance (Subsingleton.elim _ _))⟩

variable {M : Type} [TopologicalSpace M]

lemma relativeHomologyMap_eq_homologyMap {X Y : TopPair} (i : ℕ) (f : X ⟶ Y)
    (x : RelativeHomology ℚ X i) :
    relativeHomologyMap ℚ i f x =
      (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map f) i).hom x :=
  rfl

/-- Restricting the support twice is restricting it once. -/
lemma relativeHomologyMap_supportInclusion_trans {Z W U : Set M} (hZW : Z ⊆ W) (hWU : W ⊆ U)
    (i : ℕ) (c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Uᶜ) i) :
    relativeHomologyMap ℚ i (supportInclusionPairMap (TopCat.of M) hZW)
        (relativeHomologyMap ℚ i (supportInclusionPairMap (TopCat.of M) hWU) c) =
      relativeHomologyMap ℚ i (supportInclusionPairMap (TopCat.of M) (hZW.trans hWU)) c := by
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  rfl

end HodgeLean.RealDefs
