import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRelativeMayerVietoris

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
variable (R : Type) [CommRing R]

lemma b6m_homologyMap_hom_comp_apply {K L N : ChainCategory R} (f : K ⟶ L) (g : L ⟶ N) (i : ℕ)
    (x : K.homology i) :
    (HomologicalComplex.homologyMap g i).hom ((HomologicalComplex.homologyMap f i).hom x) =
      (HomologicalComplex.homologyMap (f ≫ g) i).hom x := by
  rw [HomologicalComplex.homologyMap_comp]
  rfl

lemma b6m_homologyMap_hom_neg_apply {K L : ChainCategory R} (f : K ⟶ L) (i : ℕ)
    (x : K.homology i) :
    (HomologicalComplex.homologyMap (-f) i).hom x =
      -(HomologicalComplex.homologyMap f i).hom x := by
  rw [HomologicalComplex.homologyMap_neg]
  rfl

lemma b6m_homologyMap_hom_add_apply {K L : ChainCategory R} (f g : K ⟶ L) (i : ℕ)
    (x : K.homology i) :
    (HomologicalComplex.homologyMap (f + g) i).hom x =
      (HomologicalComplex.homologyMap f i).hom x + (HomologicalComplex.homologyMap g i).hom x := by
  rw [HomologicalComplex.homologyMap_add]
  rfl

lemma b6m_homologyMap_hom_zero_apply {K L : ChainCategory R} (i : ℕ) (x : K.homology i) :
    (HomologicalComplex.homologyMap (0 : K ⟶ L) i).hom x = 0 := by
  rw [HomologicalComplex.homologyMap_zero]
  rfl

lemma b6m_homologyMap_hom_id_apply {K : ChainCategory R} (i : ℕ) (x : K.homology i) :
    (HomologicalComplex.homologyMap (𝟙 K) i).hom x = x := by
  rw [HomologicalComplex.homologyMap_id]
  rfl

lemma b6m_homology_biprod_eq_zero {K L : ChainCategory R} (i : ℕ) (x : (K ⊞ L).homology i)
    (h₁ : (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) i).hom x = 0)
    (h₂ : (HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) i).hom x = 0) :
    x = 0 := by
  have htot : x = (HomologicalComplex.homologyMap (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr
      : K ⊞ L ⟶ K ⊞ L) i).hom x := by
    rw [biprod.total, b6m_homologyMap_hom_id_apply R]
  rw [htot, b6m_homologyMap_hom_add_apply R, ← b6m_homologyMap_hom_comp_apply R, ← b6m_homologyMap_hom_comp_apply R,
    h₁, h₂, map_zero, map_zero, add_zero]

lemma b6m_homology_exact_middle_of_shortExact {K P Q N : ChainCategory R} (u : K ⟶ P) (v : K ⟶ Q)
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
    simp only [x, map_sub, b6m_homologyMap_hom_comp_apply R, biprod.inl_desc, biprod.inr_desc, hab,
      sub_self])
  change (HomologicalComplex.homologyMap (biprod.lift u (-v)) i).hom c = x at hc
  refine ⟨c, ?_, ?_⟩
  · have h := congrArg (HomologicalComplex.homologyMap (biprod.fst : P ⊞ Q ⟶ P) i).hom hc
    simpa only [x, map_sub, b6m_homologyMap_hom_comp_apply R, biprod.lift_fst, biprod.inl_fst,
      biprod.inr_fst, b6m_homologyMap_hom_id_apply R, b6m_homologyMap_hom_zero_apply R, sub_zero] using h
  · have h := congrArg (HomologicalComplex.homologyMap (biprod.snd : P ⊞ Q ⟶ Q) i).hom hc
    simpa only [x, map_sub, b6m_homologyMap_hom_comp_apply R, biprod.lift_snd, biprod.inl_snd,
      biprod.inr_snd, b6m_homologyMap_hom_id_apply R, b6m_homologyMap_hom_zero_apply R, zero_sub,
      b6m_homologyMap_hom_neg_apply R, neg_inj] using h

lemma b6m_homology_exact_left_of_shortExact {K P Q N : ChainCategory R} (u : K ⟶ P) (v : K ⟶ Q)
    (p : P ⟶ N) (q : Q ⟶ N) (w : biprod.lift u (-v) ≫ biprod.desc p q = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) (i : ℕ) (hvan : Subsingleton (N.homology (i + 1)))
    (c : K.homology i) (hu : (HomologicalComplex.homologyMap u i).hom c = 0)
    (hv : (HomologicalComplex.homologyMap v i).hom c = 0) : c = 0 := by
  have hex := (ShortComplex.moduleCat_exact_iff _).1 (hS.homology_exact₁ (i + 1) i rfl)
  obtain ⟨y, hy⟩ := hex c (by
    change (HomologicalComplex.homologyMap (biprod.lift u (-v)) i).hom c = 0
    apply b6m_homology_biprod_eq_zero R
    · rw [b6m_homologyMap_hom_comp_apply R, biprod.lift_fst]
      exact hu
    · rw [b6m_homologyMap_hom_comp_apply R, biprod.lift_snd, b6m_homologyMap_hom_neg_apply R, hv, neg_zero])
  change (hS.δ (i + 1) i rfl).hom y = c at hy
  rw [← hy, @Subsingleton.elim _ hvan y 0, map_zero]

lemma b6m_homologyMap_eq_of_comp_quasiIso {P Q N N' : ChainCategory R} (p : P ⟶ N) (q : Q ⟶ N)
    (φ : N ⟶ N') [QuasiIso φ] (r : P ⟶ N') (s : Q ⟶ N') (hr : p ≫ φ = r) (hs : q ≫ φ = s)
    (i : ℕ) (a : P.homology i) (b : Q.homology i)
    (hab : (HomologicalComplex.homologyMap r i).hom a = (HomologicalComplex.homologyMap s i).hom b) :
    (HomologicalComplex.homologyMap p i).hom a = (HomologicalComplex.homologyMap q i).hom b := by
  have hinj : Function.Injective (HomologicalComplex.homologyMap φ i).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [b6m_homologyMap_hom_comp_apply R, b6m_homologyMap_hom_comp_apply R, hr, hs]
  exact hab

lemma b6m_homology_subsingleton_of_quasiIso {N N' : ChainCategory R} (φ : N ⟶ N') [QuasiIso φ]
    (i : ℕ) (h : Subsingleton (N'.homology i)) : Subsingleton (N.homology i) :=
  ⟨fun _ _ => ((ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap φ i)).1
    inferInstance (Subsingleton.elim _ _))⟩

lemma b6m_relativeHomologyMap_eq_homologyMap {X Y : TopPair} (i : ℕ) (f : X ⟶ Y)
    (x : RelativeHomology R X i) :
    relativeHomologyMap R i f x =
      (HomologicalComplex.homologyMap ((relativeChainFunctor R).map f) i).hom x :=
  rfl

lemma b6m_relativeHomologyMap_supportInclusion_trans {M : Type} [TopologicalSpace M] {Z W U : Set M} (hZW : Z ⊆ W) (hWU : W ⊆ U)
    (i : ℕ) (c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Uᶜ) i) :
    relativeHomologyMap R i (supportInclusionPairMap (TopCat.of M) hZW)
        (relativeHomologyMap R i (supportInclusionPairMap (TopCat.of M) hWU) c) =
      relativeHomologyMap R i (supportInclusionPairMap (TopCat.of M) (hZW.trans hWU)) c := by
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  rfl

end HodgeLean.Foundations.Program
