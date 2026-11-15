module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import HodgeConjecture.Mathlib.Algebra.Homology.LiftToInjective
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenInjectiveResolution

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Maps to a K-injective complex that agree after a quasi-isomorphism are homotopic. -/
theorem homotopy_of_comp_quasiIso_eq
    {C : Type*} [Category* C] [Abelian C]
    {P K I : CochainComplex C ℤ} (a : P ⟶ K) [QuasiIso a]
    [I.IsKInjective] (f g : K ⟶ I) (h : a ≫ f = a ≫ g) :
    Nonempty (Homotopy f g) := by
  letI := HasDerivedCategory.standard C
  refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ I).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app I)).mp
  rw [DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality]
  congr 1
  apply (cancel_epi (DerivedCategory.Q.map a)).mp
  simpa only [← Functor.map_comp] using congrArg DerivedCategory.Q.map h

/-- A nonnegative injective complex detects maps up to homotopy after a quasi-isomorphism. -/
theorem homotopy_of_comp_quasiIso_eq_nat
    {C : Type*} [Category* C] [Abelian C]
    {P K I : CochainComplex C ℕ} (a : P ⟶ K) [QuasiIso a]
    (hI : ∀ n, Injective (I.X n)) (f g : K ⟶ I) (h : a ≫ f = a ≫ g) :
    Nonempty (Homotopy f g) := by
  let e := ComplexShape.embeddingUpNat
  letI : ∀ n, Injective ((I.extend e).X n) := CochainComplex.injective_extend_nat I hI
  letI : CochainComplex.IsKInjective (I.extend e) := CochainComplex.isKInjective_of_injective (I.extend e) 0
  obtain ⟨H⟩ := homotopy_of_comp_quasiIso_eq (HomologicalComplex.extendMap a e)
    (HomologicalComplex.extendMap f e) (HomologicalComplex.extendMap g e) (by
      simpa only [HomologicalComplex.extendMap_comp] using
        congrArg (fun v => HomologicalComplex.extendMap v e) h)
  exact ⟨H.ofExtend⟩

/-- A trace identity on augmentations extends to a homotopy identity on resolutions. -/
theorem resolution_trace_homotopy
    {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
    {P Q K M I : CochainComplex C ℕ}
    (a : P ⟶ K) [QuasiIso a] (b : Q ⟶ M) [Mono b] [QuasiIso b]
    (u : P ⟶ Q) (v : Q ⟶ P) (d : ℕ) (huv : u ≫ v = d • 𝟙 P)
    (f : K ⟶ M) (hf : a ≫ f = u ≫ b)
    (r : P ⟶ I) (c : K ⟶ I) (hc : a ≫ c = r)
    (hI : ∀ n, Injective (I.X n)) :
    ∃ t : M ⟶ I, b ≫ t = v ≫ r ∧ Nonempty (Homotopy (f ≫ t) (d • c)) := by
  let t := CochainComplex.liftToInjectiveNat b (v ≫ r) hI
  have ht : b ≫ t = v ≫ r := CochainComplex.comp_liftToInjectiveNat b (v ≫ r) hI
  refine ⟨t, ht, homotopy_of_comp_quasiIso_eq_nat a hI _ _ ?_⟩
  rw [← Category.assoc, hf, Category.assoc, ht, ← Category.assoc, huv,
    Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul, hc]

/-- A trace extended to injective resolutions also retains its opposite composition.
Source: Weibel, An Introduction to Homological Algebra, §2.3,
comparison of resolutions up to homotopy. -/
theorem resolution_trace_norm_homotopy
    {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
    {P Q M I J : CochainComplex C ℕ}
    (b : Q ⟶ M) [Mono b] [QuasiIso b]
    (u : P ⟶ Q) (v : Q ⟶ P) (N : M ⟶ M)
    (hN : b ≫ N = v ≫ u ≫ b)
    (r : P ⟶ I) (s : Q ⟶ J) (c : M ⟶ J) (hc : b ≫ c = s)
    (hI : ∀ n, Injective (I.X n)) (hJ : ∀ n, Injective (J.X n))
    (l : I ⟶ J) (hl : r ≫ l = u ≫ s) :
    ∃ t : M ⟶ I, b ≫ t = v ≫ r ∧
      Nonempty (Homotopy (t ≫ l) (N ≫ c)) := by
  let t := CochainComplex.liftToInjectiveNat b (v ≫ r) hI
  have ht : b ≫ t = v ≫ r := CochainComplex.comp_liftToInjectiveNat b (v ≫ r) hI
  refine ⟨t, ht, homotopy_of_comp_quasiIso_eq_nat b hJ _ _ ?_⟩
  rw [← Category.assoc, ht, Category.assoc, hl, ← Category.assoc b N c,
    hN, Category.assoc v, Category.assoc u, hc]

/-- Both trace identities and pullback compatibility persist simultaneously in injective models.
Source: Weibel, An Introduction to Homological Algebra, §2.3,
comparison of injective resolutions up to homotopy. -/
theorem resolution_trace_two_sided_homotopy
    {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
    {P Q K M I J : CochainComplex C ℕ}
    (a : P ⟶ K) [QuasiIso a] (b : Q ⟶ M) [Mono b] [QuasiIso b]
    (u : P ⟶ Q) (v : Q ⟶ P) (d : ℕ) (huv : u ≫ v = d • 𝟙 P)
    (f : K ⟶ M) (hf : a ≫ f = u ≫ b)
    (N : M ⟶ M) (hN : b ≫ N = v ≫ u ≫ b)
    (r : P ⟶ I) [Mono r] [QuasiIso r]
    (s : Q ⟶ J) (cK : K ⟶ I) (hcK : a ≫ cK = r)
    (cM : M ⟶ J) (hcM : b ≫ cM = s)
    (hI : ∀ n, Injective (I.X n)) (hJ : ∀ n, Injective (J.X n)) :
    ∃ (t : M ⟶ I) (l : I ⟶ J),
      b ≫ t = v ≫ r ∧ r ≫ l = u ≫ s ∧
      Nonempty (Homotopy (f ≫ t) (d • cK)) ∧
      Nonempty (Homotopy (f ≫ cM) (cK ≫ l)) ∧
      Nonempty (Homotopy (t ≫ l) (N ≫ cM)) := by
  obtain ⟨t, ht, hd⟩ := resolution_trace_homotopy a b u v d huv f hf r cK hcK hI
  let l := CochainComplex.liftToInjectiveNat r (u ≫ s) hJ
  have hl : r ≫ l = u ≫ s := CochainComplex.comp_liftToInjectiveNat r (u ≫ s) hJ
  refine ⟨t, l, ht, hl, hd, ?_, ?_⟩
  · apply homotopy_of_comp_quasiIso_eq_nat a hJ
    rw [← Category.assoc, hf, Category.assoc, hcM,
      ← Category.assoc a cK l, hcK, hl]
  · apply homotopy_of_comp_quasiIso_eq_nat b hJ
    rw [← Category.assoc, ht, Category.assoc, hl,
      ← Category.assoc b N cM, hN, Category.assoc v, Category.assoc u, hcM]

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero-degree homotopy trace detects cohomology classes whenever that
integer acts injectively on the source cohomology. -/
theorem homology_injective_of_trace_homotopy
    {K M I : CochainComplex AddCommGrpCat ℕ}
    (f : K ⟶ M) (t : M ⟶ I) (c : K ⟶ I) [QuasiIso c]
    (d n : ℕ) (hd : Function.Injective (fun x : K.homology n => d • x))
    (h : Homotopy (f ≫ t) (d • c)) :
    Function.Injective (HomologicalComplex.homologyMap f n) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n
  haveI : IsIso (H.map c) := by
    change IsIso (HomologicalComplex.homologyMap c n)
    infer_instance
  have hh := h.homologyMap_eq n
  change H.map (f ≫ t) = H.map (d • c) at hh
  rw [H.map_comp, Functor.map_nsmul] at hh
  intro x y hxy
  apply hd
  apply (ConcreteCategory.bijective_of_isIso (H.map c)).injective
  have ht := congrArg (fun z => H.map t z) hxy
  change H.map f x = H.map f y at hxy
  have he : (H.map f ≫ H.map t) x = (H.map f ≫ H.map t) y := ht
  rw [hh] at he
  change (d • (H.map c).hom) x = (d • (H.map c).hom) y at he
  simpa only [AddMonoidHom.nsmul_apply, map_nsmul] using he

end HodgeLean.Foundations.Program
