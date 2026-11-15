import HodgeLean.Foundations.QuotientDuality.DeckDescent

/-! Finite orbit descent on spaces that need not be compact. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma orbitMap_isClosedMap (G : Type) [Group G] [Finite G]
    (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X] :
    IsClosedMap (orbitMap G X) := by
  letI := MulAction.orbitRel G X
  intro S hS
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  change IsClosed ((Quotient.mk' : X → Quotient (MulAction.orbitRel G X)) ⁻¹'
    ((Quotient.mk' : X → Quotient (MulAction.orbitRel G X)) '' S))
  rw [MulAction.quotient_preimage_image_eq_union_mul]
  exact isClosed_iUnion_of_finite fun g => (Homeomorph.smul g).isClosedMap S hS

/-- Finite orbit transfer gives injectivity and lifts fixed singular classes.
Source: Bredon, Sheaf Theory, second edition, Chapter V, finite quotient comparison. -/
theorem orbit_transfer_noncompact
    (G : Type) [Group G] [Fintype G] (A : TopCat.{0}) [MulAction G A]
    [ContinuousConstSMul G A] [T2Space A]
    [∀ U : Opens A, ParacompactSpace U]
    [T2Space (orbitSpace G A)] [∀ U : Opens (orbitSpace G A), ParacompactSpace U]
    (hA : ∀ (x : A) (U : Opens A), x ∈ U →
      ∃ V : Opens A, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hB : ∀ (x : orbitSpace G A) (U : Opens (orbitSpace G A)), x ∈ U →
      ∃ V : Opens (orbitSpace G A), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) :
    Function.Injective (cohomologyMap ℚ n (orbitMap G A)) ∧
      ∀ b : Cohomology ℚ A n, (∀ g : G, cohomologyMap ℚ n (deckMap G A g) b = b) →
        ∃ c, cohomologyMap ℚ n (orbitMap G A) c = b := by
  classical
  let B := orbitSpace G A
  let q' : A ⟶ B := orbitMap G A
  let a' : G → (A ⟶ A) := fun g => TopCat.ofHom ⟨fun x => g • x, continuous_const_smul g⟩
  let ah : G → (A ≃ₜ A) := fun g => Homeomorph.smul g
  have ha' (g h : G) (x : A) : ah (g * h) x = ah g (ah h x) := mul_smul g h x
  have hi (g : G) (x : A) : q' (ah g x) = q' x :=
    MulAction.orbitRel.Quotient.quotient_smul_eq
  have hai (g : G) : a' g ≫ q' = q' := by ext x; exact hi g x
  have ho (x y : A) (hxy : q' x = q' y) : ∃ g, ah g x = y := by
    exact MulAction.mem_orbit_iff.mp (Quotient.exact hxy.symm)
  have hq : Topology.IsQuotientMap q' := isQuotientMap_quotient_mk'
  have hsurj : Function.Surjective q' := Quotient.mk_surjective
  have hfin (y : B) : (q' ⁻¹' {y}).Finite := by
    obtain ⟨x, rfl⟩ := hsurj y
    apply (Set.finite_range (fun g : G => g • x)).subset
    intro z hz
    obtain ⟨g, hg⟩ := ho x z (Set.mem_singleton_iff.mp hz).symm
    exact ⟨g, hg⟩
  letI : ParacompactSpace A := (Homeomorph.Set.univ A).paracompactSpace_iff.mp (inferInstance : ParacompactSpace (⊤ : Opens A))
  letI : ParacompactSpace B := (Homeomorph.Set.univ B).paracompactSpace_iff.mp (inferInstance : ParacompactSpace (⊤ : Opens B))
  letI := s4_finite_closed_pushforward_exact q' (orbitMap_isClosedMap G A) hfin
  letI : QuasiIso (constantsToSingularCochainSheafComplex ℚ A) :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hA
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat q').Additive :=
    { map_add := by intros; rfl }
  haveI : QuasiIso (((TopCat.Sheaf.pushforward AddCommGrpCat q').mapHomologicalComplex
      (.up ℕ)).map (constantsToSingularCochainSheafComplex ℚ A)) := inferInstance
  obtain ⟨L, hL⟩ := constantSheaf_pullback_sections q'
  obtain ⟨T, hT⟩ := finite_quotient_constantSheaf_trace G ah ha' q' hq hi ho
  have hd := finite_quotient_constantSheaf_trace_degree G (fun g => ah g) q' hsurj hi L T hL hT
  constructor
  · exact singular_cohomology_injective_of_sheaf_trace q' hB L T
      (Fintype.card G) Fintype.card_ne_zero hd hL n
  intro b hbInv
  have hb (g : G) : cohomologyMap ℚ n (a' g) b = b := by
    simpa only [deckMap, inv_inv] using hbInv g⁻¹
  let La := fun g => (constantSheaf_pullback_sections (a' g)).choose
  have hLa := fun g => (constantSheaf_pullback_sections (a' g)).choose_spec
  have hn := constantSheafOverPullback_trace_norm G q' a' hai L T hL hT La hLa
  obtain ⟨J, cM, t, l, hcM, _, ⟨hcomp⟩, ⟨hnorm⟩⟩ :=
    singular_resolution_two_sided_trace q' hB G a' hai L T hL La hLa hd hn
  letI := hcM
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let e := ((SingularCochainComplex ℚ A).sc n).mapHomologyIso F
  let z := e.inv b
  have hg (g : G) : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) n z = z :=
    rational_homology_forget_fixed _ _ n b (hb g)
  have hz : HomologicalComplex.homologyMap
      (∑ g : G, ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g)))) n z =
        Fintype.card G • z := by
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n
    change H.map (∑ g : G, (F.mapHomologicalComplex (.up ℕ)).map
      (singularCochainComplexMap ℚ (a' g))) z = _
    rw [H.map_sum]
    have heval : (∑ g : G, H.map
        ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g)))) z =
        ∑ g : G, H.map ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) z := by
      induction Finset.univ (α := G) using Finset.induction_on with
      | empty => rfl
      | @insert g S hS ih =>
        simp only [Finset.sum_insert hS]
        change H.map ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) z + _ = _
        exact congrArg (H.map ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) z + ·) ih
    rw [heval]
    calc
      (∑ g : G, H.map ((F.mapHomologicalComplex (.up ℕ)).map
        (singularCochainComplexMap ℚ (a' g))) z) = ∑ _g : G, z :=
          Finset.sum_congr rfl (fun g _ => hg g)
      _ = Fintype.card G • z := by rw [Finset.sum_const, Finset.card_univ]
  obtain ⟨x, hx⟩ := singular_descent_of_global_trace q' hB G a' hai J cM t l hcomp hnorm
    n Fintype.card_ne_zero z hz
  exact rational_homology_lift_of_forget (singularCochainComplexMap ℚ q') n b x hx


lemma finite_quotient_transfer (G : Type) [Group G] [Fintype G]
    (A B : TopCat.{0}) [MulAction G A] [ContinuousConstSMul G A]
    [T2Space A] [∀ U : Opens A, ParacompactSpace U]
    [T2Space B] [∀ U : Opens B, ParacompactSpace U]
    (q : A ⟶ B) (hq : Topology.IsQuotientMap q) (hclosed : IsClosedMap q)
    (hi : ∀ (g : G) (x : A), q (g • x) = q x)
    (ho : ∀ (x y : A), q x = q y → ∃ g : G, g • x = y)
    (hA : ∀ (x : A) (U : Opens A), x ∈ U →
      ∃ V : Opens A, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hB : ∀ (x : B) (U : Opens B), x ∈ U →
      ∃ V : Opens B, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) :
    Function.Injective (cohomologyMap ℚ n q) ∧
      ∀ b : Cohomology ℚ A n, (∀ g : G, cohomologyMap ℚ n (deckMap G A g) b = b) →
        ∃ c, cohomologyMap ℚ n q c = b := by
  classical
  let q' := q
  let a' : G → (A ⟶ A) := fun g => TopCat.ofHom ⟨fun x => g • x, continuous_const_smul g⟩
  let ah : G → (A ≃ₜ A) := fun g => Homeomorph.smul g
  have ha' (g h : G) (x : A) : ah (g * h) x = ah g (ah h x) := mul_smul g h x
  have hai (g : G) : a' g ≫ q' = q' := by ext x; exact hi g x
  have hsurj : Function.Surjective q' := hq.surjective
  have hfin (y : B) : (q' ⁻¹' {y}).Finite := by
    obtain ⟨x, rfl⟩ := hsurj y
    apply (Set.finite_range (fun g : G => g • x)).subset
    intro z hz
    obtain ⟨g, hg⟩ := ho x z (Set.mem_singleton_iff.mp hz).symm
    exact ⟨g, hg⟩
  letI : ParacompactSpace A := (Homeomorph.Set.univ A).paracompactSpace_iff.mp (inferInstance : ParacompactSpace (⊤ : Opens A))
  letI : ParacompactSpace B := (Homeomorph.Set.univ B).paracompactSpace_iff.mp (inferInstance : ParacompactSpace (⊤ : Opens B))
  letI := s4_finite_closed_pushforward_exact q' hclosed hfin
  letI : QuasiIso (constantsToSingularCochainSheafComplex ℚ A) :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hA
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat q').Additive :=
    { map_add := by intros; rfl }
  haveI : QuasiIso (((TopCat.Sheaf.pushforward AddCommGrpCat q').mapHomologicalComplex
      (.up ℕ)).map (constantsToSingularCochainSheafComplex ℚ A)) := inferInstance
  obtain ⟨L, hL⟩ := constantSheaf_pullback_sections q'
  obtain ⟨T, hT⟩ := finite_quotient_constantSheaf_trace G ah ha' q' hq hi ho
  have hd := finite_quotient_constantSheaf_trace_degree G (fun g => ah g) q' hsurj hi L T hL hT
  constructor
  · exact singular_cohomology_injective_of_sheaf_trace q' hB L T
      (Fintype.card G) Fintype.card_ne_zero hd hL n
  intro b hbInv
  have hb (g : G) : cohomologyMap ℚ n (a' g) b = b := by
    simpa only [deckMap, inv_inv] using hbInv g⁻¹
  let La := fun g => (constantSheaf_pullback_sections (a' g)).choose
  have hLa := fun g => (constantSheaf_pullback_sections (a' g)).choose_spec
  have hn := constantSheafOverPullback_trace_norm G q' a' hai L T hL hT La hLa
  obtain ⟨J, cM, t, l, hcM, _, ⟨hcomp⟩, ⟨hnorm⟩⟩ :=
    singular_resolution_two_sided_trace q' hB G a' hai L T hL La hLa hd hn
  letI := hcM
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let e := ((SingularCochainComplex ℚ A).sc n).mapHomologyIso F
  let z := e.inv b
  have hg (g : G) : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) n z = z :=
    rational_homology_forget_fixed _ _ n b (hb g)
  have hz : HomologicalComplex.homologyMap
      (∑ g : G, ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g)))) n z =
        Fintype.card G • z := by
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n
    change H.map (∑ g : G, (F.mapHomologicalComplex (.up ℕ)).map
      (singularCochainComplexMap ℚ (a' g))) z = _
    rw [H.map_sum]
    have heval : (∑ g : G, H.map
        ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g)))) z =
        ∑ g : G, H.map ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) z := by
      induction Finset.univ (α := G) using Finset.induction_on with
      | empty => rfl
      | @insert g S hS ih =>
        simp only [Finset.sum_insert hS]
        change H.map ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) z + _ = _
        exact congrArg (H.map ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) z + ·) ih
    rw [heval]
    calc
      (∑ g : G, H.map ((F.mapHomologicalComplex (.up ℕ)).map
        (singularCochainComplexMap ℚ (a' g))) z) = ∑ _g : G, z :=
          Finset.sum_congr rfl (fun g _ => hg g)
      _ = Fintype.card G • z := by rw [Finset.sum_const, Finset.card_univ]
  obtain ⟨x, hx⟩ := singular_descent_of_global_trace q' hB G a' hai J cM t l hcomp hnorm
    n Fintype.card_ne_zero z hz
  exact rational_homology_lift_of_forget (singularCochainComplexMap ℚ q') n b x hx

end HodgeLean.Foundations.QuotientDuality
