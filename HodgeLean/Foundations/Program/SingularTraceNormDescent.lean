import HodgeLean.Foundations.Program.FiniteQuotientSingularNorm
import HodgeLean.Foundations.Program.HomologyTraceNormDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Resolution trace norms descend ordinary rational singular classes with the specified norm equation.
Source: Bredon, Sheaf Theory, second edition, Chapter V, finite quotient comparison. -/
theorem singular_descent_of_global_trace
    {A B : TopCat.{0}} (q : A ⟶ B) [T2Space A] [T2Space B]
    [ParacompactSpace A] [ParacompactSpace B] [∀ U : Opens B, ParacompactSpace U]
    (hB : ∀ (x : B) (V : Opens B), x ∈ V →
      ∃ (W : Opens B), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)
    (G : Type) [Fintype G] (a : G → (A ⟶ A)) (ha : ∀ g, a g ≫ q = q)
    (J : CochainComplex (TopCat.Sheaf AddCommGrpCat B) ℕ)
    (cM : ((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).obj
      (singularCochainSheafComplex ℚ A) ⟶ J)
    (t : ((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).obj
      (singularCochainSheafComplex ℚ A) ⟶
      (TopCat.Sheaf.ambientConstantInjectiveResolution B (AddCommGrpCat.of ℚ)).cocomplex)
    (l : (TopCat.Sheaf.ambientConstantInjectiveResolution B (AddCommGrpCat.of ℚ)).cocomplex ⟶ J)
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor B).mapHomologicalComplex
      (.up ℕ)).map cM)]
    (hcompat : Homotopy (singularCochainSheafComplexPullback ℚ q ≫ cM)
      (singularToConstantInjectiveResolution B hB ≫ l))
    (hnorm : Homotopy (t ≫ l)
      ((∑ g : G, cochainOverPullback q (a g) (ha g) (singularCochainSheafComplexPullback ℚ (a g))) ≫ cM))
    (n : ℕ) (hd : Fintype.card G ≠ 0)
    (z : (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
      (SingularCochainComplex ℚ A)).homology n)
    (hz : HomologicalComplex.homologyMap
      (∑ g : G, ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
        (singularCochainComplexMap ℚ (a g))) n z = Fintype.card G • z) :
    ∃ x, HomologicalComplex.homologyMap
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
        (singularCochainComplexMap ℚ q)) n x = z := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor B
  let H := Γ.mapHomologicalComplex (.up ℕ)
  let cB := singularToConstantInjectiveResolution B hB
  haveI : QuasiIso (H.map cB) := TopCat.Sheaf.globalSectionsNat_map_quasiIso cB
    (fun m => singularCochainSheaf_isFlasque_of_opens_paracompact (R := ℚ) (X := B) m)
    (fun m => @TopCat.Sheaf.injective_isFlasque _ _
      ((TopCat.Sheaf.ambientConstantInjectiveResolution B (AddCommGrpCat.of ℚ)).injective m))
  haveI : QuasiIso (singularGlobalComparison A) := singularGlobalComparison_quasiIso A
  haveI : QuasiIso (singularGlobalComparison B) := singularGlobalComparison_quasiIso B
  let F := (forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)
  let N := ∑ g : G, F.map (singularCochainComplexMap ℚ (a g))
  have hq : F.map (singularCochainComplexMap ℚ q) ≫ singularGlobalComparison A =
      singularGlobalComparison B ≫ H.map (singularCochainSheafComplexPullback ℚ q) :=
    singularGlobalComparison_naturality q
  have hN : N ≫ singularGlobalComparison A = singularGlobalComparison A ≫
      H.map (∑ g : G, cochainOverPullback q (a g) (ha g) (singularCochainSheafComplexPullback ℚ (a g))) := by
    calc
      N ≫ singularGlobalComparison A =
          ∑ g : G, F.map (singularCochainComplexMap ℚ (a g)) ≫ singularGlobalComparison A :=
        Preadditive.sum_comp _ _ _
      _ = ∑ g : G, singularGlobalComparison A ≫ singularGlobalSheafPullback (a g) :=
        Finset.sum_congr rfl (fun g _ => singularGlobalComparison_naturality (a g))
      _ = singularGlobalComparison A ≫ ∑ g : G, singularGlobalSheafPullback (a g) :=
        (Preadditive.comp_sum _ _ _).symm
      _ = singularGlobalComparison A ≫ H.map
          (∑ g : G, cochainOverPullback q (a g) (ha g) (singularCochainSheafComplexPullback ℚ (a g))) := by
        apply congrArg (singularGlobalComparison A ≫ ·)
        exact (Finset.sum_congr rfl (fun g _ => (singularOverPullback_global q (a g) (ha g)).symm)).trans
          (H.map_sum _ _).symm
  have hc : Homotopy
      (F.map (singularCochainComplexMap ℚ q) ≫ (singularGlobalComparison A ≫ H.map cM))
      ((singularGlobalComparison B ≫ H.map cB) ≫ H.map l) := by
    have h := (Γ.mapHomotopy hcompat).compLeft (singularGlobalComparison B)
    simpa only [Functor.map_comp, ← Category.assoc, hq] using h
  have hn : Homotopy ((singularGlobalComparison A ≫ H.map t) ≫ H.map l)
      (N ≫ (singularGlobalComparison A ≫ H.map cM)) := by
    have h := (Γ.mapHomotopy hnorm).compLeft (singularGlobalComparison A)
    simpa only [Functor.map_comp, ← Category.assoc, hN] using h
  exact homology_descent_of_two_sided_trace
    (F.map (singularCochainComplexMap ℚ q))
    (singularGlobalComparison B ≫ H.map cB) (singularGlobalComparison A ≫ H.map cM)
    (singularGlobalComparison A ≫ H.map t) (H.map l) N hc hn (Fintype.card G) n
    (forgotten_rational_homology_nsmul_bijective _ _ _ hd) z hz

end HodgeLean.Foundations.Program
