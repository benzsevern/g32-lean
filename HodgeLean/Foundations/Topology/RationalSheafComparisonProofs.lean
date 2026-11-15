import HodgeLean.Foundations.Topology.RationalSheafComparisonComparisonNaturality

/-! Rational singular and constant-sheaf comparison interfaces.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Topology.RationalSheafComparison

private theorem bijective_hom_comp {A B : AddCommGrpCat} {M : Type}
    [AddCommGroup M] (f : A ⟶ B) [IsIso f] (g : M →+ A)
    (hg : Function.Bijective g) : Function.Bijective (f.hom.comp g) :=
  (ConcreteCategory.bijective_of_isIso f).comp hg

variable (X : TopCat.{0})
  (hX : ∀ (x : X) (U : Opens X), x ∈ U →
    ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
  [T2Space X] [∀ U : Opens X, ParacompactSpace U]

/-- Source: Bredon, Sheaf Theory, second edition, II.4 and II.6. -/
theorem comparisonComplex_quasiIso_aux : QuasiIso (comparisonComplex X hX) := by
  letI : ParacompactSpace X :=
    (Homeomorph.Set.univ X).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens X))
  haveI hΓ := TopCat.Sheaf.globalSectionsNat_map_quasiIso
    (singularToConstantInjectiveResolution X hX)
    (fun n => show (singularCochainSheaf ℚ X n).IsFlasque from
      singularCochainSheaf_isFlasque_of_opens_paracompact (R := ℚ) (X := X) n)
    (fun n => @TopCat.Sheaf.injective_isFlasque _ _ ((resolution X).injective n))
  haveI hS := HodgeLean.Foundations.Program.singularGlobalComparison_quasiIso X
  unfold comparisonComplex
  exact quasiIso_comp _ _

/-- Source: Bredon, Sheaf Theory, second edition, II.4, II.6 and III.1. -/
theorem comparison_linearEquiv_aux (n : ℕ) :
    Function.Bijective (comparison X hX n) ∧
      ∃ e : Cohomology ℚ X n ≃ₗ[ℚ] Sheaf.H (constants X) n,
        ∀ v, e v = comparison X hX n v := by
  haveI := comparisonComplex_quasiIso_aux X hX
  have hb : Function.Bijective (comparison X hX n) := by
    dsimp only [comparison]
    apply Function.Bijective.comp (resolutionCohomologyEquiv X n).bijective
    apply bijective_hom_comp
    apply bijective_hom_comp
    apply bijective_hom_comp
    exact ConcreteCategory.bijective_of_isIso _
  exact ⟨hb, LinearEquiv.ofBijective (comparison X hX n).toRatLinearMap hb,
    fun _ => rfl⟩

omit [T2Space X] [∀ U : Opens X, ParacompactSpace U] in
/-- Source: Bredon, Sheaf Theory, second edition, II.4; ComplexSheafSingularParts/Scalar. -/
theorem comparison_scalar_aux (n : ℕ) (a : ℚ) (v : Cohomology ℚ X n) :
    comparison X hX n (a • v) =
      Sheaf.H.map (scalar X a) n (comparison X hX n v) := by
  exact map_rat_smul (comparison X hX n) a v

/-- Source: Bredon, Sheaf Theory, second edition, II.4, II.6 and III.1. -/
theorem comparison_naturality_aux (Y : TopCat.{0})
    (hY : ∀ (y : Y) (U : Opens Y), y ∈ U →
      ∃ V : Opens Y, y ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    [T2Space Y] [∀ U : Opens Y, ParacompactSpace U]
    (f : X ⟶ Y) (n : ℕ) (v : Cohomology ℚ Y n) :
    comparison X hX n (cohomologyMap ℚ n f v) =
      sheafPullback f n (comparison Y hY n v) := by
  exact comparison_naturality_from_resolution f hX hY n v

end HodgeLean.Topology.RationalSheafComparison
