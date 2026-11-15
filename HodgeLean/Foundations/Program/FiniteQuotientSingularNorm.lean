import HodgeLean.Foundations.Program.SingularOverPullback
import HodgeLean.Foundations.Program.ConstantSheafOverPullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- A finite orbit trace retains its norm identity in global singular resolution models.
Source: Bredon, Sheaf Theory, second edition, II.4 and Chapter V,
finite quotient comparison by rational averaging. -/
theorem singular_resolution_two_sided_trace
    {A B : TopCat.{0}} (q : A ⟶ B) [T2Space A]
    [∀ U : Opens A, ParacompactSpace U]
    (hB : ∀ (x : B) (V : Opens B), x ∈ V →
      ∃ (W : Opens B), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)
    [QuasiIso (((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).map
      (constantsToSingularCochainSheafComplex ℚ A))]
    (G : Type) [Fintype G] (a : G → (A ⟶ A)) (ha : ∀ g, a g ≫ q = q)
    (L : 𝓒(B; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ))
    (T : (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ) ⟶ 𝓒(B; ℚ))
    (hL : ∀ (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        (L.hom.app (op U) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U s ⟨q x, x.property⟩)
    (La : ∀ g, 𝓒(A; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat (a g)).obj 𝓒(A; ℚ))
    (hLa : ∀ g (V : Opens A) (s : 𝓒(A; ℚ).obj.obj (op V)) (x : a g ⁻¹' V),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map (a g)).obj V)
        ((La g).hom.app (op V) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) V s ⟨a g x, x.property⟩)
    (hd : L ≫ T = Fintype.card G • 𝟙 _)
    (hn : T ≫ L = ∑ g : G, sheafOverPullback q (a g) (ha g) (La g)) :
    let K := singularCochainSheafComplex ℚ B
    let M := ((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).obj
      (singularCochainSheafComplex ℚ A)
    let I := (TopCat.Sheaf.ambientConstantInjectiveResolution B (AddCommGrpCat.of ℚ)).cocomplex
    let cK := singularToConstantInjectiveResolution B hB
    let F := singularCochainSheafComplexPullback ℚ q
    let N := ∑ g : G, cochainOverPullback q (a g) (ha g) (singularCochainSheafComplexPullback ℚ (a g))
    ∃ (J : CochainComplex (TopCat.Sheaf AddCommGrpCat B) ℕ)
      (cM : M ⟶ J) (t : M ⟶ I) (l : I ⟶ J),
      QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor B).mapHomologicalComplex
        (.up ℕ)).map cM) ∧
      Nonempty (Homotopy (F ≫ t) (Fintype.card G • cK)) ∧
      Nonempty (Homotopy (F ≫ cM) (cK ≫ l)) ∧
      Nonempty (Homotopy (t ≫ l) (N ≫ cM)) := by
  dsimp only
  let b := pushedSingularAugmentation q
  let S := CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat B)
  let I := TopCat.Sheaf.ambientConstantInjectiveResolution B (AddCommGrpCat.of ℚ)
  let J := InjectiveResolution.of ((TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ))
  let aB := constantsToSingularCochainSheafComplex ℚ B
  letI : QuasiIso aB := constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hB
  letI : Mono (constantsToSingularCochainSheafComplex ℚ A) :=
    constantsToSingularCochainSheafComplex_mono ℚ A
  letI : Mono b := by dsimp [b, pushedSingularAugmentation]; infer_instance
  letI : QuasiIso b := by dsimp [b, pushedSingularAugmentation]; infer_instance
  let cM := CochainComplex.liftToInjectiveNat b J.ι J.injective
  have hcM : b ≫ cM = J.ι := CochainComplex.comp_liftToInjectiveNat b J.ι J.injective
  haveI : QuasiIso cM := by
    haveI : QuasiIso (b ≫ cM) := by rw [hcM]; exact J.quasiIso
    exact quasiIso_of_comp_left b cM
  have hd' : S.map L ≫ S.map T = Fintype.card G • 𝟙 _ := by
    rw [← S.map_comp, hd, Functor.map_nsmul, S.map_id]
  have hn' : b ≫ (∑ g : G, cochainOverPullback q (a g) (ha g)
      (singularCochainSheafComplexPullback ℚ (a g))) = S.map T ≫ S.map L ≫ b := by
    rw [singularOverPullback_sum_augmentation G q a ha La hLa,
      ← Category.assoc, ← S.map_comp, hn]
  letI : Mono I.ι := HomologicalComplex.mono_of_mono_f _ (fun n => inferInstance)
  letI : QuasiIso I.ι := I.quasiIso
  obtain ⟨t, l, _, _, h1, h2, h3⟩ := resolution_trace_two_sided_homotopy aB b
    (S.map L) (S.map T) (Fintype.card G) hd'
    (singularCochainSheafComplexPullback ℚ q)
    (constantSheaf_pullback_singular_complex_augmentation q L hL)
    _ hn' I.ι J.ι (singularToConstantInjectiveResolution B hB)
    (constants_comp_singularToConstantInjectiveResolution B hB) cM hcM I.injective J.injective
  refine ⟨J.cocomplex, cM, t, l, ?_, h1, h2, h3⟩
  apply TopCat.Sheaf.globalSectionsNat_map_quasiIso cM
  · intro m
    change ((TopCat.Sheaf.pushforward AddCommGrpCat q).obj
      (singularCochainSheaf ℚ A m)).IsFlasque
    letI : (singularCochainSheaf ℚ A m).IsFlasque :=
      singularCochainSheaf_isFlasque_of_opens_paracompact (R := ℚ) (X := A) m
    exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque (singularCochainSheaf ℚ A m) q
  · intro m
    exact @TopCat.Sheaf.injective_isFlasque _ _ (J.injective m)

end HodgeLean.Foundations.Program
