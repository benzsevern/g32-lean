import HodgeLean.Foundations.Program.RationalHomologyForget
import HodgeLean.Foundations.Program.ResolutionTraceHomotopy
import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularFlasqueModel
import HodgeLean.Foundations.Program.FiniteQuotientSheafTrace
import HodgeLean.Foundations.Program.SingularCochainSheafPullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- The constructed constant sheaf pullback agrees with actual singular pullback
under the constant zero-cochain augmentation. -/
theorem constantSheaf_pullback_singular_augmentation
    {A B : TopCat.{0}} (q : A ⟶ B)
    (L : 𝓒(B; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ))
    (hL : ∀ (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        (L.hom.app (op U) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U s ⟨q x, x.property⟩) :
    L ≫ (TopCat.Sheaf.pushforward AddCommGrpCat q).map
        (AlgebraicTopology.Singular.constantsToSingularCochainZeroSheaf ℚ A) =
      AlgebraicTopology.Singular.constantsToSingularCochainZeroSheaf ℚ B ≫
        singularCochainSheafPullback ℚ q 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply sheafify_hom_ext (Opens.grothendieckTopology B) _ _
    ((TopCat.Sheaf.pushforward AddCommGrpCat q).obj
      (AlgebraicTopology.Singular.singularCochainSheaf ℚ A 0)).property
  change toSheafify _ _ ≫ (L.hom ≫
    (TopCat.Presheaf.pushforward AddCommGrpCat q).map
      (sheafifyMap (Opens.grothendieckTopology A)
        (AlgebraicTopology.Singular.constantsToSingularCochainZero ℚ A))) =
    toSheafify _ _ ≫ (sheafifyMap (Opens.grothendieckTopology B)
      (AlgebraicTopology.Singular.constantsToSingularCochainZero ℚ B) ≫
        (singularCochainSheafPullback ℚ q 0).hom)
  rw [← Category.assoc, constantSheaf_pullback_sections_unit q L hL,
    ← (TopCat.Presheaf.pushforward AddCommGrpCat q).map_comp,
    ← toSheafify_naturality, (TopCat.Presheaf.pushforward AddCommGrpCat q).map_comp,
    ← singularOpenCochainMap_constants, Category.assoc,
    ← singularCochainSheafPullback_unit, ← Category.assoc,
    toSheafify_naturality, Category.assoc]
  rfl

/-- The pushed singular resolution is augmented by the direct image constant sheaf. -/
def pushedSingularAugmentation {A B : TopCat.{0}} (q : A ⟶ B) :
    (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat B)).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ)) ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicTopology.Singular.singularCochainSheafComplex ℚ A) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (TopCat.Sheaf.pushforward AddCommGrpCat q) (.up ℕ) 0).inv.app 𝓒(A; ℚ) ≫
    ((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).map
      (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ A)

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero component of the pushed augmentation is the actual pushed constant map. -/
theorem pushedSingularAugmentation_zero {A B : TopCat.{0}} (q : A ⟶ B) :
    (pushedSingularAugmentation q).f 0 =
      (TopCat.Sheaf.pushforward AddCommGrpCat q).map
        (AlgebraicTopology.Singular.constantsToSingularCochainZeroSheaf ℚ A) := by
  simp [pushedSingularAugmentation,
    CochainComplex.single₀ObjXSelf,
    AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex]

set_option backward.isDefEq.respectTransparency false in
/-- The actual pullback respects the full constant-to-singular augmentations. -/
theorem constantSheaf_pullback_singular_complex_augmentation
    {A B : TopCat.{0}} (q : A ⟶ B)
    (L : 𝓒(B; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ))
    (hL : ∀ (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        (L.hom.app (op U) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U s ⟨q x, x.property⟩) :
    AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ B ≫
        singularCochainSheafComplexPullback ℚ q =
      (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat B)).map L ≫
        pushedSingularAugmentation q := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  simp only [CochainComplex.fromSingle₀Equiv_apply_coe,
    HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    pushedSingularAugmentation_zero,
    AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  exact (constantSheaf_pullback_singular_augmentation q L hL).symm

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
/-- A constant sheaf trace gives a trace into the target injective resolution,
with the required group order homotopy for actual singular pullback. -/
theorem singular_resolution_trace_homotopy
    {A B : TopCat.{0}} (q : A ⟶ B)
    (hB : ∀ (x : B) (V : Opens B), x ∈ V →
      ∃ (W : Opens B), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)
    [QuasiIso (((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).map
      (constantsToSingularCochainSheafComplex ℚ A))]
    (L : 𝓒(B; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ))
    (T : (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ) ⟶ 𝓒(B; ℚ))
    (d : ℕ) (hd : L ≫ T = d • 𝟙 _)
    (hL : ∀ (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        (L.hom.app (op U) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U s ⟨q x, x.property⟩) :
    ∃ t : ((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).obj
        (singularCochainSheafComplex ℚ A) ⟶
          (TopCat.Sheaf.ambientConstantInjectiveResolution B (AddCommGrpCat.of ℚ)).cocomplex,
      Nonempty (Homotopy (singularCochainSheafComplexPullback ℚ q ≫ t)
        (d • singularToConstantInjectiveResolution B hB)) := by
  let a := constantsToSingularCochainSheafComplex ℚ B
  let b := pushedSingularAugmentation q
  let S := CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat B)
  let I := TopCat.Sheaf.ambientConstantInjectiveResolution B (AddCommGrpCat.of ℚ)
  letI : QuasiIso a := constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hB
  letI : Mono (constantsToSingularCochainSheafComplex ℚ A) :=
    constantsToSingularCochainSheafComplex_mono ℚ A
  letI : Mono b := by dsimp [b, pushedSingularAugmentation]; infer_instance
  letI : QuasiIso b := by dsimp [b, pushedSingularAugmentation]; infer_instance
  have hd' : S.map L ≫ S.map T = d • 𝟙 _ := by
    rw [← S.map_comp, hd, Functor.map_nsmul, S.map_id]
  obtain ⟨t, _, ht⟩ := resolution_trace_homotopy a b (S.map L) (S.map T) d hd'
    (singularCochainSheafComplexPullback ℚ q)
    (constantSheaf_pullback_singular_complex_augmentation q L hL)
    I.ι (singularToConstantInjectiveResolution B hB)
    (constants_comp_singularToConstantInjectiveResolution B hB) I.injective
  exact ⟨t, ht⟩

set_option backward.isDefEq.respectTransparency false in
/-- A finite-degree constant sheaf trace detects actual rational singular cohomology classes. -/
theorem singular_cohomology_injective_of_sheaf_trace
    {A B : TopCat.{0}} (q : A ⟶ B) [T2Space B] [ParacompactSpace B]
    [∀ U : Opens B, ParacompactSpace U]
    (hB : ∀ (x : B) (V : Opens B), x ∈ V →
      ∃ (W : Opens B), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)
    [QuasiIso (((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).map
      (constantsToSingularCochainSheafComplex ℚ A))]
    (L : 𝓒(B; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ))
    (T : (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ) ⟶ 𝓒(B; ℚ))
    (d : ℕ) (hd0 : d ≠ 0) (hd : L ≫ T = d • 𝟙 _)
    (hL : ∀ (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        (L.hom.app (op U) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U s ⟨q x, x.property⟩)
    (n : ℕ) : Function.Injective (cohomologyMap ℚ n q) := by
  obtain ⟨t, ⟨ht⟩⟩ := singular_resolution_trace_homotopy q hB L T d hd hL
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor B
  let G := Γ.mapHomologicalComplex (.up ℕ)
  let c := singularToConstantInjectiveResolution B hB
  haveI : QuasiIso (G.map c) := TopCat.Sheaf.globalSectionsNat_map_quasiIso c
    (fun m => singularCochainSheaf_isFlasque_of_opens_paracompact (R := ℚ) (X := B) m)
    (fun m => @TopCat.Sheaf.injective_isFlasque _ _
      ((TopCat.Sheaf.ambientConstantInjectiveResolution B (AddCommGrpCat.of ℚ)).injective m))
  let β := singularGlobalComparison B
  haveI : QuasiIso β := singularGlobalComparison_quasiIso B
  haveI : QuasiIso (β ≫ G.map c) := inferInstance
  let f := ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
    (singularCochainComplexMap ℚ q)
  have hh : Homotopy (f ≫ (singularGlobalComparison A ≫ G.map t))
      (d • (β ≫ G.map c)) := by
    have h := (Γ.mapHomotopy ht).compLeft β
    have he : f ≫ singularGlobalComparison A =
        β ≫ G.map (singularCochainSheafComplexPullback ℚ q) :=
      singularGlobalComparison_naturality q
    simpa only [Functor.map_comp, Functor.map_nsmul, Preadditive.comp_nsmul,
      ← Category.assoc, he] using h
  apply rational_homology_injective_of_forget (singularCochainComplexMap ℚ q) n
  exact homology_injective_of_trace_homotopy f _ (β ≫ G.map c) d n
    (forgotten_rational_homology_nsmul_injective (SingularCochainComplex ℚ B) d n hd0) hh

end HodgeLean.Foundations.Program
