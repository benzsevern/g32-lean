import Mathlib.Topology.Homotopy.Lifting

/-! # Pointed sections of covering maps
Implication from covering and simple connectivity inputs to section evaluation.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Evaluation specifies a unique continuous section through a given fibre point.
Source: Mathlib, IsCoveringMap.existsUnique_continuousMap_lifts. -/
theorem s2e_c11_pointed_section
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    (f : E → B) (hf : IsCoveringMap f) (b : B) (e : E) (he : f e = b) :
    ∃! s : C(B, E), s b = e ∧ f ∘ s = id := by
  exact hf.existsUnique_continuousMap_lifts (ContinuousMap.id B) b e he

/-- The values of the pointed sections give a continuous sheet parametrization.
Source: Mathlib, covering lift uniqueness and local section open embeddings. -/
theorem s2e_c11_section_evaluation_homeomorph
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    (f : E → B) (hf : IsCoveringMap f) (b : B) :
    ∃ e : ((f ⁻¹' {b}) × B) ≃ₜ E, ∀ x, f (e x) = x.2 := by
  classical
  have : DiscreteTopology (f ⁻¹' {b}) := (hf b).discreteTopology_fiber
  choose s hs hu using fun a : f ⁻¹' {b} ↦
    s2e_c11_pointed_section f hf b a.1 a.2
  have hsec (a : f ⁻¹' {b}) (x : B) : f (s a x) = x := congrFun (hs a).2 x
  have hopen (a : f ⁻¹' {b}) : Topology.IsOpenEmbedding (s a) := by
    apply hf.isLocalHomeomorph.isOpenEmbedding_of_comp
    · rw [(hs a).2]
      exact Topology.IsOpenEmbedding.id
    · exact (s a).continuous
  let g : (f ⁻¹' {b}) × B → E := fun x ↦ s x.1 x.2
  have hcont : Continuous g := continuous_prod_of_discrete_left.mpr fun a ↦ (s a).continuous
  have hinj : Function.Injective g := by
    intro x y hxy
    have hbase : x.2 = y.2 := (hsec x.1 x.2).symm.trans ((congrArg f hxy).trans (hsec y.1 y.2))
    obtain ⟨t, ht, htuniq⟩ := s2e_c11_pointed_section f hf x.2 (g x) (hsec x.1 x.2)
    have hx : s x.1 = t := htuniq _ ⟨rfl, (hs x.1).2⟩
    have hy : s y.1 = t := htuniq _ ⟨by simpa only [hbase] using hxy.symm, (hs y.1).2⟩
    have hab : x.1 = y.1 := Subtype.ext <| by
      calc
        x.1.1 = s x.1 b := (hs x.1).1.symm
        _ = s y.1 b := congrArg (fun u : C(B, E) ↦ u b) (hx.trans hy.symm)
        _ = y.1.1 := (hs y.1).1
    exact Prod.ext hab hbase
  have hsurj : Function.Surjective g := by
    intro x
    obtain ⟨t, ht, _⟩ := s2e_c11_pointed_section f hf (f x) x rfl
    let a : f ⁻¹' {b} := ⟨t b, congrFun ht.2 b⟩
    have heq : t = s a := hu a t ⟨rfl, ht.2⟩
    exact ⟨(a, f x), (congrArg (fun u : C(B, E) ↦ u (f x)) heq).symm.trans ht.1⟩
  have hopenG : IsOpenMap g := by
    intro U hU
    have heq : g '' U = ⋃ a : f ⁻¹' {b}, s a '' ((fun x : B ↦ (a, x)) ⁻¹' U) := by
      ext x
      constructor
      · rintro ⟨⟨a, y⟩, hy, rfl⟩
        exact Set.mem_iUnion.mpr ⟨a, y, hy, rfl⟩
      · intro hx
        obtain ⟨a, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
        exact ⟨(a, y), hy, rfl⟩
    rw [heq]
    exact isOpen_iUnion fun a ↦ (hopen a).isOpenMap _
      (hU.preimage (continuous_const.prodMk continuous_id))
  refine ⟨(Equiv.ofBijective g ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopenG, ?_⟩
  exact fun x ↦ hsec x.1 x.2

/-- The image of a continuous section of a covering is open and has open complement.
Source: Mathlib, IsSeparatedMap.isClosed_eqLocus and IsLocallyInjective.isOpen_eqLocus. -/
theorem s2e_c11_covering_section_image
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (f : E → B) (hf : IsCoveringMap f) (s : B → E)
    (hc : Continuous s) (hs : ∀ b, f (s b) = b) :
    IsOpen (Set.range s) ∧ IsClosed (Set.range s) := by
  have heq : f ∘ (s ∘ f) = f ∘ id := by ext x; exact hs (f x)
  have hrange : Set.range s = {x | (s ∘ f) x = id x} := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact congrArg s (hs b)
    · intro hx
      exact ⟨f x, hx⟩
  rw [hrange]
  exact ⟨hf.isLocalHomeomorph.isLocallyInjective.isOpen_eqLocus
    (hc.comp hf.continuous) continuous_id heq,
    hf.isSeparatedMap.isClosed_eqLocus (hc.comp hf.continuous) continuous_id heq⟩

/-- A projection preserving sheet parametrization supplies a disjoint family of sections.
Source: Mathlib, Homeomorph inverse identities and product continuity. -/
theorem s2e_c11_trivialization_sections
    {E B I : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace I]
    (f : E → B) (e : E ≃ₜ I × B) (he : ∀ x, (e x).2 = f x) :
    ∃ s : I → C(B, E), (∀ i b, f (s i b) = b) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (s i)) (Set.range (s j))) ∧
      (∀ x : E, ∃ i, x ∈ Set.range (s i)) := by
  let s : I → C(B, E) := fun i ↦
    ⟨fun b ↦ e.symm (i, b), e.symm.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · intro i b
    exact (he _).symm.trans (congrArg Prod.snd (e.apply_symm_apply (i, b)))
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨b, rfl⟩ ⟨c, hc⟩
    apply hij
    exact congrArg Prod.fst (e.symm.injective hc).symm
  · intro x
    exact ⟨(e x).1, (e x).2, e.symm_apply_apply x⟩

end HodgeLean.Foundations.Program
