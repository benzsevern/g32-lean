import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CohomologyZero
import Mathlib.RingTheory.AdjoinRoot
import HodgeLean.RealDefs.DegreeZero
import HodgeLean.Foundations.Program.SchoenTowerL1bActionDeckHomology
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Independent ramified and collected-component tests

Only definitions and existing results are imported. Tests change a sign,
a normalization factor, prime collection, the dimension filter, or a weight.
The affine-line squaring map retains its nonreduced fibre equation.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Convexity CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators Classical Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

private abbrev C1 := Fin 1 → ℂ
private def identityChart : OpenPartialHomeomorph C1 C1 :=
  (Homeomorph.refl C1).toOpenPartialHomeomorph
private def generator := localClassOfChart 1 identityChart (0 : C1) (by trivial)
private theorem generator_ne_zero : generator ≠ 0 :=
  localClassOfChart_ne_zero 1 identityChart 0 (by trivial)
private def localGenerator :=
  neighborhoodOrientation 1 identityChart (0 : C1) (by trivial)
    Set.univ isOpen_univ (by trivial)
private def localIdentity := isolatedPairMap (𝟙 (TopCat.of C1)) Set.univ (0 : C1)
  (fun _ _ h => h)
private theorem identity_degree : relativeHomologyMap ℚ 2 localIdentity localGenerator = generator := by
  change (neighborhoodPointComplementRelativeHomologyIso Set.univ (0 : C1)
    isOpen_univ (by trivial) 2).hom.hom
    ((neighborhoodPointComplementRelativeHomologyIso Set.univ (0 : C1)
      isOpen_univ (by trivial) 2).inv.hom generator) = generator
  exact ConcreteCategory.congr_hom (Iso.inv_hom_id _) generator

/-- A negative sign gives the wrong local degree on the actual identity pair map.
Source: Hatcher, Algebraic Topology, §3.3; complex chart orientation. -/
theorem finite_flat_local_degree_wrong_sign :
    relativeHomologyMap ℚ 2 localIdentity localGenerator ≠ (-1 : ℚ) • generator := by
  rw [identity_degree]
  intro h
  have hh : (2 : ℚ) • generator = 0 := by
    have hn : generator = -generator := by simpa using h
    simpa [two_smul] using (eq_neg_iff_add_eq_zero.mp hn)
  exact generator_ne_zero ((smul_eq_zero.mp hh).resolve_left (by norm_num))

example : relativeHomologyMap ℚ 2 localIdentity localGenerator ≠ (-1 : ℚ) • generator :=
  finite_flat_local_degree_wrong_sign

/-- Rescaling the identity pullback coclass changes its evaluation from one to two.
Source: Hatcher, Algebraic Topology, §3.1, evaluation naturality. -/
theorem finite_flat_local_coclass_wrong_factor :
    relativeCohomologyEquivDualHomology ℚ _ 2
      (relativeCohomologyMap ℚ 2 localIdentity
        (normalizedRelativeCoclass generator generator_ne_zero)) localGenerator ≠ 2 := by
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap, identity_degree,
    normalizedRelativeCoclass_pairing_self]
  norm_num

example : relativeCohomologyEquivDualHomology ℚ _ 2
    (relativeCohomologyMap ℚ 2 localIdentity
      (normalizedRelativeCoclass generator generator_ne_zero)) localGenerator ≠ 2 :=
  finite_flat_local_coclass_wrong_factor

private abbrev P := Spec (CommRingCat.of ℂ)
private abbrev q : P ⟶ Spec (CommRingCat.of ℂ) := 𝟙 P
private abbrev CP := ComplexPoint (Over.mk q)
private def pt : CP := 𝟙 (Over.mk q)
private def p : P := pt.underlying
private instance : Unique CP where
  default := pt
  uniq x := by
    exact Over.mkIdTerminal.hom_ext x pt

private def repeated : P →₀ ℚ := collectPrimes (fun _ : Bool => p)
  (fun i => if i then (2 : ℚ) else 3)
private theorem repeated_eq : repeated = Finsupp.single p 5 := by
  norm_num [repeated, collectPrimes, ← Finsupp.single_add]
private theorem repeated_cycle : collectedCycle repeated =
    Function.locallyFinsuppWithin.single p (5 : ℚ) := by
  rw [repeated_eq]
  simp [collectedCycle]

/-- Retaining only the last occurrence loses part of the collected coefficient.
Source: Fulton, Intersection Theory, second edition, §1.5. -/
theorem collected_coefficients_wrong_last : collectedCycle repeated p ≠ 2 := by
  rw [repeated_cycle]
  norm_num

example : collectedCycle repeated p ≠ 2 := collected_coefficients_wrong_last

/-- Omitting the dimension filter fails even for a nonzero cycle and an identity map.
Source: Stacks Project, Tag 02R4. -/
theorem proper_collected_pushforward_wrong_dimension :
    AlgebraicCycle.map (𝟙 P) (fun _ => (0 : ℕ)) (fun _ => (1 : ℕ))
      (collectedCycle repeated) ≠ collectedCycle repeated := by
  have hz : AlgebraicCycle.map (𝟙 P) (fun _ => (0 : ℕ)) (fun _ => (1 : ℕ))
      (collectedCycle repeated) = 0 := by
    ext z
    simp [AlgebraicCycle.map, AlgebraicCycle.mapCoeff, Function.locallyFinsupp.map]
  rw [hz, repeated_cycle]
  intro h
  have hh := congrArg (fun c : AlgebraicCycle P ℚ => c p) h
  norm_num at hh

example : AlgebraicCycle.map (𝟙 P) (fun _ => (0 : ℕ)) (fun _ => (1 : ℕ))
    (collectedCycle repeated) ≠ collectedCycle repeated :=
  proper_collected_pushforward_wrong_dimension

private theorem primeSupport_full : primeSupport q p = Set.univ := by
  ext x
  simp only [primeSupport, a3b4_cycleSupport]
  have hxp : x.underlying = p := congrArg Point.underlying (Subsingleton.elim x pt)
  simp [hxp, subset_closure (Set.mem_singleton p)]

private def cancelled : P →₀ ℚ := collectPrimes (fun _ : Bool => p)
  (fun i => if i then (2 : ℚ) else -2)
private theorem cancelled_eq : cancelled = 0 := by simp [cancelled, collectPrimes]

/-- Taking support before collection retains a prime that cancellation removes.
Source: Fulton, Intersection Theory, second edition, §§1.5 and 19.1. -/
theorem collected_support_wrong_union :
    a3b4_cycleSupport q (collectedCycle cancelled) ≠ primeSupport q p := by
  rw [cancelled_eq, primeSupport_full]
  simp only [collectedCycle, Finsupp.support_zero, Finset.sum_empty]
  have hz : a3b4_cycleSupport q (0 : AlgebraicCycle P ℚ) = ∅ := by
    ext x
    simp [a3b4_cycleSupport]
  rw [hz]
  exact Set.empty_ne_univ

example : a3b4_cycleSupport q (collectedCycle cancelled) ≠ primeSupport q p :=
  collected_support_wrong_union

-- This test helper realizes whole-support classes directly on the relative complex.
private def wholeEquiv (X : TopCat.{0}) (n : ℕ) :
    CohomologyWithSupport ℚ X Set.univ n ≃ₗ[ℚ] Cohomology ℚ X n := by
  let A := TopPair.ofSubset (X := X) (∅ : Set X)
  have hzero : ((chainPairFunctor ℚ).obj A).hom = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    change (SSet.chainComplexMap (TopCat.toSSet.map A.map) (ModuleCat.of ℚ ℚ)).f i = 0
    apply SSet.chainComplex_hom_ext
    intro σ
    let f := (A.snd.toSSetObjEquiv _) σ
    exact (f StdSimplex.barycenter).2.elim
  have hi : IsIso (relativeChainProjection ℚ A) := cokernel.π_of_zero hzero
  let B := TopPair.ofSubset (X := X) (Set.univ : Set X)ᶜ
  haveI : IsIso (relativeChainProjection ℚ B) := by
    dsimp [B]
    rw [Set.compl_univ]
    exact hi
  let e := HomologicalComplex.homologyMapIso
    (HomologicalComplex.linearDualIso (asIso (relativeChainProjection ℚ B))) n
  exact LinearEquiv.ofBijective (forgetSupport ℚ X Set.univ n)
    ((ConcreteCategory.isIso_iff_bijective e.hom).mp e.isIso_hom)

private def unitSupported : CohomologyWithSupport ℚ (a3b4_an q) (primeSupport q p) 0 :=
  primeSupport_full.symm ▸ (wholeEquiv (a3b4_an q) 0).symm
    (cohomologyUnitZero ℚ (a3b4_an q))

private theorem unit_forget : forgetSupport ℚ (a3b4_an q) (primeSupport q p) 0 unitSupported =
    cohomologyUnitZero ℚ (a3b4_an q) := by
  have h (S : Set (a3b4_an q)) (hS : S = Set.univ) :
      forgetSupport ℚ (a3b4_an q) S 0
        (hS.symm ▸ (wholeEquiv (a3b4_an q) 0).symm
          (cohomologyUnitZero ℚ (a3b4_an q))) =
        cohomologyUnitZero ℚ (a3b4_an q) := by
    subst S
    exact (wholeEquiv (a3b4_an q) 0).apply_symm_apply _
  exact h _ primeSupport_full

private def oneWeight : P →₀ ℚ := Finsupp.single p 2
private theorem support_at (t : oneWeight.support) : primeSupport q t.1 = Set.univ := by
  have ht : t.1 = p := by simpa [oneWeight] using t.2
  rw [ht, primeSupport_full]
private def components (t : oneWeight.support) :
    CohomologyWithSupport ℚ (a3b4_an q) (primeSupport q t.1) 0 :=
  (support_at t).symm ▸ (wholeEquiv (a3b4_an q) 0).symm
    (cohomologyUnitZero ℚ (a3b4_an q))
private theorem components_forget (t : oneWeight.support) :
    forgetSupport ℚ (a3b4_an q) (primeSupport q t.1) 0 (components t) =
      cohomologyUnitZero ℚ (a3b4_an q) := by
  have h (S : Set (a3b4_an q)) (hS : S = Set.univ) :
      forgetSupport ℚ (a3b4_an q) S 0
        (hS.symm ▸ (wholeEquiv (a3b4_an q) 0).symm
          (cohomologyUnitZero ℚ (a3b4_an q))) =
        cohomologyUnitZero ℚ (a3b4_an q) := by
    subst S
    exact (wholeEquiv (a3b4_an q) 0).apply_symm_apply _
  exact h _ (support_at t)

private theorem assembled_absolute :
    forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (collectedCycle oneWeight)) 0
      (assembledClass q oneWeight 0 components) =
      (2 : ℚ) • cohomologyUnitZero ℚ (a3b4_an q) := by
  rw [assembledClass, SupportedClasses.forget_weightedSum_aux]
  let t : oneWeight.support := ⟨p, by simp [oneWeight]⟩
  letI : Unique oneWeight.support := {
    default := t
    uniq := fun s => by
      apply Subtype.ext
      change s.1 = p
      simpa [oneWeight] using s.2 }
  rw [Fintype.sum_unique]
  rw [components_forget]
  congr 1
  have ht : (default : oneWeight.support).1 = p := by
    simpa [oneWeight] using (default : oneWeight.support).2
  rw [ht]
  simp [oneWeight]

/-- Dropping a surviving coefficient changes the absolute image of the actual assembly.
Source: Hatcher, Algebraic Topology, §3.1; `SupportedClasses.forget_weightedSum_aux`. -/
theorem assembled_forget_wrong_weight :
    forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (collectedCycle oneWeight)) 0
      (assembledClass q oneWeight 0 components) ≠ cohomologyUnitZero ℚ (a3b4_an q) := by
  rw [assembled_absolute]
  intro h
  have hh : ((2 : ℚ) - 1) • cohomologyUnitZero ℚ (a3b4_an q) = 0 := by
    rw [sub_smul, one_smul, h, sub_self]
  norm_num at hh
  exact cohomologyUnitZero_ne_zero ℚ (a3b4_an q) hh

example : forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (collectedCycle oneWeight)) 0
    (assembledClass q oneWeight 0 components) ≠ cohomologyUnitZero ℚ (a3b4_an q) :=
  assembled_forget_wrong_weight

private instance : Unique ((Fin 0 → ℂ) × (Fin 0 → ℂ)) where
  default := (0, 0)
  uniq _ := Subsingleton.elim _ _

private def pointNormalChart : OpenPartialHomeomorph CP ((Fin 0 → ℂ) × (Fin 0 → ℂ)) :=
  (Homeomorph.homeomorphOfUnique _ _).toOpenPartialHomeomorph

private theorem one_cycle : collectedCycle oneWeight =
    Function.locallyFinsuppWithin.single p (2 : ℚ) := by
  simp [collectedCycle, oneWeight]
private theorem one_support : a3b4_cycleSupport q (collectedCycle oneWeight) = Set.univ := by
  rw [one_cycle]
  ext x
  have hx : x.underlying = p := congrArg Point.underlying (Subsingleton.elim x pt)
  simp [a3b4_cycleSupport, hx]
private theorem one_multiplicity : a3b4_multiplicity q (collectedCycle oneWeight) pt = 2 := by
  rw [one_cycle]
  have hlocal : ∃ U : Set CP, IsOpen U ∧ pt ∈ U ∧
      U ∩ a3b4_cycleSupport q (Function.locallyFinsuppWithin.single p (2 : ℚ)) ⊆
        Point.underlying ⁻¹' closure ({p} : Set P) := by
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
    intro z hz
    have he : z.underlying = p := congrArg Point.underlying (Subsingleton.elim z pt)
    rw [Set.mem_preimage, he]
    exact subset_closure (Set.mem_singleton p)
  have hs : (a3b2_support_finite
      (Function.locallyFinsuppWithin.single p (2 : ℚ))).toFinset = {p} := by
    ext z
    simp [Subsingleton.elim p (default : P)]
  unfold a3b4_multiplicity
  rw [hs, Finset.sum_singleton, ite_eq_left hlocal]
  simp
private theorem zero_not_normalized :
    ¬ a3b4_IsCycleClass q (collectedCycle oneWeight) 0 0 := by
  intro hc
  have hflat : ∀ z ∈ pointNormalChart.source,
      z ∈ a3b4_cycleSupport q (collectedCycle oneWeight) ↔ (pointNormalChart z).2 = 0 := by
    intro z _
    rw [one_support]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Set.mem_univ _⟩
  have he : a3b4_IsHolChart q pointNormalChart := by
    constructor <;> intro j <;> exact Fin.elim0 j
  obtain ⟨W, hW, hWo, hxW, hnorm⟩ := hc 0 pointNormalChart hflat pt
    (by simp [pointNormalChart]) (by rw [one_support]; trivial) he
  rw [map_zero, one_multiplicity] at hnorm
  have hn := HodgeLean.RealDefs.chartNormalProjectionCoclass_ne_zero
    (Fin 0 → ℂ) 0 pointNormalChart _ hflat hWo hW hxW (Subsingleton.elim _ _)
  exact hn ((smul_eq_zero.mp hnorm.symm).resolve_left (by norm_num))

/-- A regular separated nonzero prime with weight two cannot use the unit-weight assembly.
Source: Fulton, Intersection Theory, second edition, §19.1. -/
theorem assembled_normalized_on_locus_wrong_unit :
    pt ∈ regularSeparatedLocus q oneWeight 0 ∧
    forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (collectedCycle oneWeight)) 0
      (assembledClass q oneWeight 0 components) ≠ cohomologyUnitZero ℚ (a3b4_an q) := by
  refine ⟨?_, assembled_forget_wrong_weight⟩
  let t : oneWeight.support := ⟨p, by simp [oneWeight]⟩
  refine ⟨t, ?_, ?_, 0, pointNormalChart, ?_, ?_, ?_⟩
  · rw [primeSupport_full]
    trivial
  · intro s hst hs
    have hsp : s.1 = p := by simpa [oneWeight] using s.2
    exact hst (Subtype.ext hsp)
  · constructor <;> intro j <;> exact Fin.elim0 j
  · simp [pointNormalChart]
  · intro z hz
    rw [primeSupport_full]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => trivial⟩

example : pt ∈ regularSeparatedLocus q oneWeight 0 ∧
    forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (collectedCycle oneWeight)) 0
      (assembledClass q oneWeight 0 components) ≠ cohomologyUnitZero ℚ (a3b4_an q) :=
  assembled_normalized_on_locus_wrong_unit

example : pt ∈ regularSeparatedLocus q oneWeight 0 ∧
    ¬ a3b4_IsCycleClass q (collectedCycle oneWeight) 0 0 :=
  ⟨assembled_normalized_on_locus_wrong_unit.1, zero_not_normalized⟩

-- An actual affine curve morphism and its nonreduced zero-fibre algebra.
private def squareHom : Polynomial ℂ →+* Polynomial ℂ :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X ^ 2)
private def squareCurve : Spec (CommRingCat.of (Polynomial ℂ)) ⟶
    Spec (CommRingCat.of (Polynomial ℂ)) := Spec.map (CommRingCat.ofHom squareHom)
private abbrev squareFibre := Polynomial ℂ ⧸ Ideal.span {(Polynomial.X : Polynomial ℂ) ^ 2}

example : squareHom Polynomial.X = (Polynomial.X : Polynomial ℂ) ^ 2 := by
  simp [squareHom]

example : (Ideal.span {(Polynomial.X : Polynomial ℂ)}).map squareHom =
    Ideal.span {(Polynomial.X : Polynomial ℂ) ^ 2} := by
  rw [Ideal.map_span, Set.image_singleton]
  simp [squareHom]

example : Module.length ℂ squareFibre = (2 : ℕ∞) := by
  haveI : Module.Finite ℂ squareFibre :=
    (Polynomial.monic_X.pow 2 : (Polynomial.X ^ 2 : Polynomial ℂ).Monic).finite_quotient
  rw [Module.length_eq_finrank, finrank_quotient_span_eq_natDegree]
  simp

example : (TopPair.Hom.fst (isolatedPairMap
    (TopCat.ofHom ⟨fun z : ℂ => z ^ 2, by fun_prop⟩) Set.univ 0
    (by intro z _ hz; simpa using hz))) ⟨(2 : ℂ), by trivial⟩ = (4 : ℂ) := by
  change (2 : ℂ) ^ 2 = 4
  norm_num

private def originIdeal : Ideal (Polynomial ℂ) := RingHom.ker (Polynomial.evalRingHom (0 : ℂ))
private instance : originIdeal.IsPrime := RingHom.ker_isPrime _
private theorem origin_eq : originIdeal = Ideal.span {(Polynomial.X : Polynomial ℂ)} := by
  simpa [originIdeal] using Polynomial.ker_evalRingHom (0 : ℂ)
private theorem origin_ne_bot : originIdeal ≠ ⊥ := by
  rw [origin_eq, ne_eq, Ideal.span_singleton_eq_bot]
  exact Polynomial.X_ne_zero
private abbrev localOrigin := Localization.AtPrime originIdeal
private instance : IsDiscreteValuationRing localOrigin :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ origin_ne_bot _
private def localFibreIdeal : Ideal localOrigin :=
  (originIdeal.map squareHom).map (algebraMap (Polynomial ℂ) localOrigin)
private theorem local_fibre_ideal : localFibreIdeal = IsLocalRing.maximalIdeal localOrigin ^ 2 := by
  have hs : originIdeal.map squareHom = originIdeal ^ 2 := by
    rw [origin_eq, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    simp [squareHom]
  rw [localFibreIdeal, hs, Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]
private abbrev actualLocalFibre := localOrigin ⧸ localFibreIdeal
private instance : Nontrivial actualLocalFibre := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  rw [local_fibre_ideal]
  exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal localOrigin).ne_top
    (Ideal.pow_le_self (by norm_num))
private instance : IsLocalRing actualLocalFibre :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

-- The square map's actual localized fibre, with its nilpotents, has self-length two.
example : Module.length actualLocalFibre actualLocalFibre = (2 : ℕ∞) := by
  rw [← Module.length_eq_of_surjective (R := actualLocalFibre) (S := localOrigin)
    Ideal.Quotient.mk_surjective]
  change Module.length localOrigin (localOrigin ⧸ localFibreIdeal) = 2
  rw [local_fibre_ideal]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal localOrigin 2

example : squareCurve ≠ 𝟙 _ := by
  intro h
  have hh : CommRingCat.ofHom squareHom = 𝟙 (CommRingCat.of (Polynomial ℂ)) :=
    Spec.map_injective (by
      change Spec.map (CommRingCat.ofHom squareHom) = _ at h
      simpa only [← Spec.map_id] using h)
  have hx := congrArg (fun h : CommRingCat.of (Polynomial ℂ) ⟶
      CommRingCat.of (Polynomial ℂ) => h.hom Polynomial.X) hh
  have hd := congrArg Polynomial.natDegree hx
  have hx2 : squareHom Polynomial.X = Polynomial.X ^ 2 := by simp [squareHom]
  simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply,
    Polynomial.natDegree_X] at hd
  rw [hx2] at hd
  norm_num at hd

-- Squaring on the actual point-complement pair, with its punctured map.
private def squarePair : pointComplementPair (0 : ℂ) ⟶ pointComplementPair (0 : ℂ) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun z : ℂ => z ^ (2 : ℕ), by fun_prop⟩)
    (TopCat.ofHom ⟨fun z => ⟨z.1 ^ (2 : ℕ), pow_ne_zero _ z.2⟩, by fun_prop⟩)
    (by ext; rfl)

private theorem square_pair_degree :
    relativeHomologyMap ℤ (2 : ℕ) squarePair
      (HodgeLean.Foundations.Program.b6m_surfaceLocalClass ℤ (0 : ℂ)) =
    (2 : ℤ) • HodgeLean.Foundations.Program.b6m_surfaceLocalClass ℤ (0 : ℂ) := by
  obtain ⟨n, hn⟩ :=
    (HodgeLean.Foundations.Program.b6m_surfaceLocalClass_smul_bijective ℤ (0 : ℂ)).2
      (relativeHomologyMap ℤ (2 : ℕ) squarePair
        (HodgeLean.Foundations.Program.b6m_surfaceLocalClass ℤ (0 : ℂ)))
  have hn' : relativeHomologyMap ℤ (2 : ℕ) squarePair
      (HodgeLean.Foundations.Program.b6m_surfaceLocalClass ℤ (0 : ℂ)) =
      n • HodgeLean.Foundations.Program.b6m_surfaceLocalClass ℤ (0 : ℂ) := by
    rw [← int_smul_eq_zsmul (ModuleCat.isModule _) n]
    exact hn.symm
  have h := HodgeLean.Foundations.Program.s2v_l1b_action_deck_local_sign
    squarePair (fun z : ℂ => (2 : ℂ) * z) (by fun_prop) ?_ (2 : ℤ) ?_ n hn'
  · rw [hn', ← h]
  · intro z
    change Complex.exp ((2 : ℂ) * z) = Complex.exp z ^ (2 : ℕ)
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using Complex.exp_nat_mul z (2 : ℕ)
  · intro z
    push_cast
    ring

/-- Squaring has homological local degree two on the integral source generator.
Source: Hatcher, Algebraic Topology, §2.2; logarithmic lift z ↦ 2z. -/
theorem finite_flat_local_degree_square_homology :
    relativeHomologyMap ℤ (2 : ℕ) squarePair
      (HodgeLean.Foundations.Program.b6m_surfaceLocalClass ℤ (0 : ℂ)) =
    (2 : ℤ) • HodgeLean.Foundations.Program.b6m_surfaceLocalClass ℤ (0 : ℂ) :=
  square_pair_degree

example := finite_flat_local_degree_square_homology

private instance : Nontrivial squareFibre := by
  haveI : Module.Finite ℂ squareFibre :=
    (Polynomial.monic_X.pow (2 : ℕ) : (Polynomial.X ^ (2 : ℕ) : Polynomial ℂ).Monic).finite_quotient
  apply (Module.length_pos_iff (R := ℂ)).mp
  rw [Module.length_eq_finrank, finrank_quotient_span_eq_natDegree]
  norm_num

/-- The doubled origin is not flat over the affine line: X² kills its unit.
Source: Stacks Project, Tag 00HD; flat modules over a domain are torsion free. -/
theorem finite_flat_local_degree_nonflat_exclusion :
    ¬ Module.Flat (Polynomial ℂ) squareFibre := by
  intro hf
  letI := hf
  have hi := Module.Flat.isSMulRegular_of_isRegular
    (M := squareFibre) (isRegular_iff_ne_zero.mpr
      (pow_ne_zero (2 : ℕ) (Polynomial.X_ne_zero (R := ℂ))))
  have hz : ((Polynomial.X : Polynomial ℂ) ^ (2 : ℕ)) • (1 : squareFibre) =
      ((Polynomial.X : Polynomial ℂ) ^ (2 : ℕ)) • (0 : squareFibre) := by
    rw [smul_zero, Algebra.smul_def, mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  exact one_ne_zero (hi hz)

example : ¬ Module.Flat (Polynomial ℂ) squareFibre :=
  finite_flat_local_degree_nonflat_exclusion

#print axioms finite_flat_local_degree_square_homology
#print axioms finite_flat_local_degree_nonflat_exclusion

end AlgebraicGeometry.SingularCycles
