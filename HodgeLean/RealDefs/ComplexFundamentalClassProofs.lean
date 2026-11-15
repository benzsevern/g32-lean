import HodgeLean.RealDefs.ComplexFundamentalClassDefs
import HodgeLean.RealDefs.ComplexFundamentalClassParts.A_RelativeMayerVietoris
import HodgeLean.RealDefs.ComplexFundamentalClassParts.A_SmallChains
import HodgeLean.RealDefs.ComplexFundamentalClassChainDefs
import HodgeLean.RealDefs.ComplexFundamentalClassParts.B_HomologyMaps
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.LocalOrientationNeighborhood
import HodgeLean.RealDefs.ComplexFundamentalClassParts.C_ConvexLocal
import HodgeLean.RealDefs.ComplexFundamentalClassParts.C_OpenLift
import HodgeLean.RealDefs.ComplexFundamentalClassParts.C_BallCover
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeLean.RealDefs.ComplexFundamentalClassParts.D_ClosedExcision
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
import HodgeLean.RealDefs.ComplexFundamentalClassParts.E_Chart
import HodgeConjecture.Mathlib.Topology.Category.TopPair
import HodgeLean.RealDefs.ComplexFundamentalClassParts.F_Euclidean

/-! # Proof obligations for the frozen fundamental-class spec (J5c)

All 26 `_aux` theorems below are proved. The frozen statements are in `ComplexFundamentalClass.lean`.
Six parallel provers wrote them, each in dependency order: statements 1-3 (relative Mayer-Vietoris),
4-9 (homology maps and excision), 10-14 (convex local classes), 15-16 (closed excision),
17-22 (chart step, compact manifolds and the fundamental class) and 23-26 (Euclidean classes).
Helpers that need no `_aux` theorem are in `ComplexFundamentalClassParts/`.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

theorem j5c_relativeMayerVietorisShortComplex_shortExact_aux {M : Type} [TopologicalSpace M] (A B : Set M) :
    (relativeMayerVietorisShortComplex M A B).ShortExact :=
  relativeMayerVietorisShortComplex_shortExact M A B

theorem j5c_relativeSumSmallChainComparison_quasiIso_aux {M : Type} [TopologicalSpace M] {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B) :
    QuasiIso (relativeSumSmallChainComparison M A B) :=
  relativeSumSmallChainComparison_quasiIso_of_isClosed A B hA hB

theorem j5c_relativeSumComparison_quasiIso_aux {M : Type} [TopologicalSpace M] {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B) :
    QuasiIso (relativeSumComparison M A B) :=
  relativeSumComparison_quasiIso_of_small M A B
    (j5c_relativeSumSmallChainComparison_quasiIso_aux hA hB)

theorem j5c_relativeMayerVietoris_exact_middle_aux {M : Type} [TopologicalSpace M] (A B : Set M) (i : ℕ)
    (a : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ) i)
    (b : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Bᶜ) i)
    (hab : (HomologicalComplex.homologyMap (relativeSumLeftProjection M A B) i).hom a =
      (HomologicalComplex.homologyMap (relativeSumRightProjection M A B) i).hom b) :
    ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) i,
      relativeHomologyMap ℚ i
          (supportInclusionPairMap (TopCat.of M) (show A ⊆ A ∪ B from Set.subset_union_left)) c =
        a ∧
      relativeHomologyMap ℚ i
          (supportInclusionPairMap (TopCat.of M) (show B ⊆ A ∪ B from Set.subset_union_right)) c =
        b := by
  exact homology_exact_middle_of_shortExact _ _ _ _ _
    (j5c_relativeMayerVietorisShortComplex_shortExact_aux A B) i a b hab

theorem j5c_relativeMayerVietoris_exact_left_aux {M : Type} [TopologicalSpace M] (A B : Set M) (i : ℕ)
    (hvan : Subsingleton ((RelativeSumChainComplex M A B).homology (i + 1)))
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) i)
    (hcA : relativeHomologyMap ℚ i
      (supportInclusionPairMap (TopCat.of M) (show A ⊆ A ∪ B from Set.subset_union_left)) c = 0)
    (hcB : relativeHomologyMap ℚ i
      (supportInclusionPairMap (TopCat.of M) (show B ⊆ A ∪ B from Set.subset_union_right)) c = 0) :
    c = 0 := by
  exact homology_exact_left_of_shortExact _ _ _ _ _
    (j5c_relativeMayerVietorisShortComplex_shortExact_aux A B) i hvan c hcA hcB

theorem j5c_relativeMayerVietoris_glue_aux {M : Type} [TopologicalSpace M] {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B) (i : ℕ)
    (a : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ) i)
    (b : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Bᶜ) i)
    (hab : relativeHomologyMap ℚ i
        (supportInclusionPairMap (TopCat.of M) (show A ∩ B ⊆ A from Set.inter_subset_left)) a =
      relativeHomologyMap ℚ i
        (supportInclusionPairMap (TopCat.of M) (show A ∩ B ⊆ B from Set.inter_subset_right)) b) :
    ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) i,
      relativeHomologyMap ℚ i
          (supportInclusionPairMap (TopCat.of M) (show A ⊆ A ∪ B from Set.subset_union_left)) c =
        a ∧
      relativeHomologyMap ℚ i
          (supportInclusionPairMap (TopCat.of M) (show B ⊆ A ∪ B from Set.subset_union_right)) c =
        b := by
  have := j5c_relativeSumComparison_quasiIso_aux hA hB
  exact j5c_relativeMayerVietoris_exact_middle_aux A B i a b
    (homologyMap_eq_of_comp_quasiIso _ _ (relativeSumComparison M A B) _ _
      (relativeSumLeftProjection_comp_comparison M A B)
      (relativeSumRightProjection_comp_comparison M A B) i a b hab)

theorem j5c_relativeMayerVietoris_injective_aux {M : Type} [TopologicalSpace M] {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B) (i : ℕ)
    (hvan : Subsingleton
      (RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ) (i + 1)))
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) i)
    (hcA : relativeHomologyMap ℚ i
      (supportInclusionPairMap (TopCat.of M) (show A ⊆ A ∪ B from Set.subset_union_left)) c = 0)
    (hcB : relativeHomologyMap ℚ i
      (supportInclusionPairMap (TopCat.of M) (show B ⊆ A ∪ B from Set.subset_union_right)) c = 0) :
    c = 0 := by
  have := j5c_relativeSumComparison_quasiIso_aux hA hB
  exact j5c_relativeMayerVietoris_exact_left_aux A B i
    (homology_subsingleton_of_quasiIso (relativeSumComparison M A B) (i + 1) hvan) c hcA hcB

theorem j5c_union_aux {M : Type} [TopologicalSpace M] (n : ℕ) {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B)
    (hvA : LocalHomologyVanishesAbove M n A) (hvB : LocalHomologyVanishesAbove M n B)
    (hvAB : LocalHomologyVanishesAbove M n (A ∩ B))
    (hdA : LocalHomologyDetectedByPoints M n A) (hdB : LocalHomologyDetectedByPoints M n B) :
    LocalHomologyVanishesAbove M n (A ∪ B) ∧ LocalHomologyDetectedByPoints M n (A ∪ B) := by
  refine ⟨fun i hi => ⟨fun c d => ?_⟩, fun c hc => ?_⟩
  · have hsub : ∀ e : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) i,
        e = 0 := fun e =>
      j5c_relativeMayerVietoris_injective_aux hA hB i (hvAB (i + 1) (by omega)) e
        (@Subsingleton.elim _ (hvA i hi) _ _) (@Subsingleton.elim _ (hvB i hi) _ _)
    rw [hsub c, hsub d]
  · refine j5c_relativeMayerVietoris_injective_aux hA hB n (hvAB (n + 1) (by omega)) c
      (hdA _ fun x hx => ?_) (hdB _ fun x hx => ?_)
    · rw [relativeHomologyMap_supportInclusion_trans]
      exact hc x (Or.inl hx)
    · rw [relativeHomologyMap_supportInclusion_trans]
      exact hc x (Or.inr hx)

theorem j5c_union_hasClassAlong_aux {M : Type} [TopologicalSpace M] (n : ℕ) {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B)
    (μ : ∀ x : M, RelativeHomology ℚ (pointComplementPair x) n)
    (hμA : HasClassAlong M n μ A) (hμB : HasClassAlong M n μ B)
    (hdAB : LocalHomologyDetectedByPoints M n (A ∩ B)) :
    HasClassAlong M n μ (A ∪ B) := by
  obtain ⟨α, hα⟩ := hμA
  obtain ⟨β, hβ⟩ := hμB
  obtain ⟨c, hcA, hcB⟩ := j5c_relativeMayerVietoris_glue_aux hA hB n α β (sub_eq_zero.1 (hdAB _
    fun x hx => by
      rw [map_sub, relativeHomologyMap_supportInclusion_trans,
        relativeHomologyMap_supportInclusion_trans, sub_eq_zero]
      exact (hα x hx.1).trans (hβ x hx.2).symm))
  refine ⟨c, fun x hx => ?_⟩
  rcases hx with hx | hx
  · rw [← hα x hx, ← hcA, relativeHomologyMap_supportInclusion_trans]
  · rw [← hβ x hx, ← hcB, relativeHomologyMap_supportInclusion_trans]

theorem j5c_convex_restrict_bijective_aux {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : Convex ℝ K) (hKc : IsCompact K) {x : E}
    (hx : x ∈ K) (i : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ i
      (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hx))) := by
  exact C_convex_restrict_bijective hK hKc hx i

theorem j5c_convex_aux {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n) {K : Set E}
    (hK : Convex ℝ K) (hKc : IsCompact K) :
    LocalHomologyVanishesAbove E n K ∧ LocalHomologyDetectedByPoints E n K := by
  exact C_convex hn hK hKc

theorem j5c_iUnion_convex_aux {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n) {m : ℕ} (K : Fin m → Set E)
    (hK : ∀ j, Convex ℝ (K j)) (hKc : ∀ j, IsCompact (K j)) :
    LocalHomologyVanishesAbove E n (⋃ j, K j) ∧
      LocalHomologyDetectedByPoints E n (⋃ j, K j) := by
  induction m with
  | zero =>
    rw [Set.iUnion_of_empty]
    exact j5c_convex_aux hn (convex_empty (𝕜 := ℝ)) isCompact_empty
  | succ m ih =>
    have hU : (⋃ j, K j) = (⋃ j : Fin m, K j.castSucc) ∪ K (Fin.last m) := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨j, hj⟩
        induction j using Fin.lastCases with
        | last => exact Or.inr hj
        | cast j => exact Or.inl ⟨j, hj⟩
      · rintro (⟨j, hj⟩ | hj)
        · exact ⟨_, hj⟩
        · exact ⟨_, hj⟩
    rw [hU]
    have h1 := ih (fun j => K j.castSucc) (fun j => hK _) (fun j => hKc _)
    have h2 := j5c_convex_aux hn (hK (Fin.last m)) (hKc _)
    have h3 := ih (fun j => K j.castSucc ∩ K (Fin.last m)) (fun j => (hK _).inter (hK _))
      (fun j => (hKc _).inter_right (hKc _).isClosed)
    rw [← Set.iUnion_inter] at h3
    exact j5c_union_aux n (isCompact_iUnion fun j => hKc _).isClosed (hKc _).isClosed
      h1.1 h2.1 h3.1 h1.2 h2.2

theorem j5c_exists_open_lift_aux {M : Type} [TopologicalSpace M] [T2Space M] (A : Set M)
    (i : ℕ) (α : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ) i) :
    ∃ W : Set M, IsOpen W ∧ A ⊆ W ∧ ∀ (K : Set M) (hAK : A ⊆ K), K ⊆ W →
      ∃ α' : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Kᶜ) i,
        relativeHomologyMap ℚ i (supportInclusionPairMap (TopCat.of M) hAK) α' = α := by
  exact C_exists_open_lift A i α

theorem j5c_compact_euclidean_aux {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n) {A : Set E}
    (hA : IsCompact A) :
    LocalHomologyVanishesAbove E n A ∧ LocalHomologyDetectedByPoints E n A := by
  have hlift : ∀ i (α : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of E) Aᶜ) i),
      ∃ (m : ℕ) (c : Fin m → E) (δ : ℝ), 0 < δ ∧ (∀ j, c j ∈ A) ∧
        ∃ hAK : A ⊆ ⋃ j, Metric.closedBall (c j) δ,
          ∃ α' : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of E)
              (⋃ j, Metric.closedBall (c j) δ)ᶜ) i,
            relativeHomologyMap ℚ i (supportInclusionPairMap (TopCat.of E) hAK) α' = α := by
    intro i α
    obtain ⟨W, hWo, hAW, hW⟩ := j5c_exists_open_lift_aux A i α
    obtain ⟨m, c, δ, hδ, hc, hAK, hKW⟩ := C_exists_closedBall_cover hA hWo hAW
    exact ⟨m, c, δ, hδ, hc, hAK, hW _ hAK hKW⟩
  have hU := fun (m : ℕ) (c : Fin m → E) (δ : ℝ) =>
    j5c_iUnion_convex_aux hn (fun j => Metric.closedBall (c j) δ)
      (fun j => convex_closedBall _ _) (fun j => isCompact_closedBall _ _)
  refine ⟨fun i hi => ?_, fun α hα => ?_⟩
  · suffices h : ∀ α : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of E) Aᶜ) i, α = 0 from
      ⟨fun a b => (h a).trans (h b).symm⟩
    intro α
    obtain ⟨m, c, δ, _, _, hAK, α', rfl⟩ := hlift i α
    have := (hU m c δ).1 i hi
    rw [Subsingleton.elim α' 0, map_zero]
  · obtain ⟨m, c, δ, hδ, hc, hAK, α', rfl⟩ := hlift n α
    suffices h : α' = 0 by rw [h, map_zero]
    refine (hU m c δ).2 α' fun y hy => ?_
    obtain ⟨j, hyB⟩ := Set.mem_iUnion.mp hy
    have hBK : Metric.closedBall (c j) δ ⊆ ⋃ j, Metric.closedBall (c j) δ :=
      Set.subset_iUnion (fun j => Metric.closedBall (c j) δ) j
    have hcB : c j ∈ Metric.closedBall (c j) δ := Metric.mem_closedBall_self hδ.le
    have hinj := (j5c_convex_restrict_bijective_aux (convex_closedBall (c j) δ)
      (isCompact_closedBall (c j) δ) hcB n).1
    have e2 := C_relativeHomologyMap_restrict_trans (Set.singleton_subset_iff.mpr hcB) hBK n α'
    have e3 := C_relativeHomologyMap_restrict_trans (Set.singleton_subset_iff.mpr (hc j)) hAK n α'
    have h0 : relativeHomologyMap ℚ n (supportInclusionPairMap (TopCat.of E) hBK) α' = 0 := by
      apply hinj
      rw [map_zero]
      exact e2.symm.trans (e3.trans (hα (c j) (hc j)))
    have e1 := C_relativeHomologyMap_restrict_trans (Set.singleton_subset_iff.mpr hyB) hBK n α'
    refine e1.trans ?_
    rw [h0, map_zero]

theorem j5c_excision_relativeChainMap_quasiIso_aux {M : Type} [TopologicalSpace M] {U A : Set M} (hU : IsOpen U)
    (hA : IsClosed A) (hAU : A ⊆ U) :
    QuasiIso ((relativeChainFunctor ℚ).map
      (TopPair.ofSubsetHom (A := {u : U | u.1 ∉ A}) (B := Aᶜ)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of M)
        (fun _ ha => ha))) :=
  ClosedExcision.relativeChainMap_quasiIso hU hA hAU

theorem j5c_excision_aux {M : Type} [TopologicalSpace M] {U A : Set M} (hU : IsOpen U)
    (hA : IsClosed A) (hAU : A ⊆ U) (i : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ i
      (TopPair.ofSubsetHom (A := {u : U | u.1 ∉ A}) (B := Aᶜ)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of M)
        (fun _ ha => ha))) := by
  have := j5c_excision_relativeChainMap_quasiIso_aux hU hA hAU
  exact ClosedExcision.relativeHomologyMap_bijective_of_quasiIso _ i

set_option backward.isDefEq.respectTransparency false in
/-- Hatcher, Lemma 3.27, step (5), for any homeomorphism `h : U ≃ₜ V` of an open `U ⊆ M` onto an
open `V ⊆ E`: a closed `A ⊆ U` whose image `A'` under `h` is compact has vanishing local homology
above `n` and point detection in degree `n`. Excision (statement 16) moves `H(M, M \ A)` to
`H(U, U \ A) ≅ H(V, V \ A')`, and from there into `H(E, E \ A')`, where statement 14 applies. -/
theorem j5cE_of_homeomorph {M E : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n)
    {U : Set M} (hU : IsOpen U) {V : Set E} (hV : IsOpen V) (h : U ≃ₜ V)
    {A : Set M} (hA : IsClosed A) (hAU : A ⊆ U) {A' : Set E} (hA'c : IsCompact A')
    (hA'V : A' ⊆ V) (hAA' : ∀ u : U, (h u : E) ∈ A' ↔ (u : M) ∈ A) :
    LocalHomologyVanishesAbove M n A ∧ LocalHomologyDetectedByPoints M n A := by
  have hEuc := j5c_compact_euclidean_aux hn hA'c
  have hexM : ∀ i, Function.Bijective (relativeHomologyMap ℚ i (j5cE_exMap U A)) :=
    fun i => j5c_excision_aux hU hA hAU i
  have hexE : ∀ i, Function.Bijective (relativeHomologyMap ℚ i (j5cE_exMap V A')) :=
    fun i => j5c_excision_aux hV hA'c.isClosed hA'V i
  have hinj : ∀ i, Function.Injective (fun β => relativeHomologyMap ℚ i (j5cE_exMap V A')
      (relativeHomologyMap ℚ i (j5cE_pairIso h A A' hAA').hom β)) :=
    fun i => (hexE i).1.comp (j5cE_iso_injective (j5cE_pairIso h A A' hAA') i)
  refine ⟨?_, ?_⟩
  · intro i hi
    haveI := hEuc.1 i hi
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := (hexM i).2 a
    obtain ⟨b', rfl⟩ := (hexM i).2 b
    have hab : a' = b' := hinj i (Subsingleton.elim _ _)
    rw [hab]
  · intro α hα
    obtain ⟨β, rfl⟩ := (hexM n).2 α
    have hres : ∀ (u : U) (hu : (u : M) ∈ A),
        relativeHomologyMap ℚ n (j5cE_resMap U (Set.singleton_subset_iff.mpr hu)) β = 0 := by
      intro u hu
      have hpt : Function.Injective (relativeHomologyMap ℚ n (j5cE_exMap U {(u : M)})) :=
        (j5c_excision_aux hU isClosed_singleton (Set.singleton_subset_iff.mpr u.2) n).1
      apply hpt
      have hsq := congrArg (fun f => relativeHomologyMap ℚ n f β)
        (j5cE_exMap_comp_supportInclusion U (Set.singleton_subset_iff.mpr hu))
      simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hsq
      rw [← hsq, map_zero]
      exact hα u hu
    have hγ : relativeHomologyMap ℚ n (j5cE_exMap V A')
        (relativeHomologyMap ℚ n (j5cE_pairIso h A A' hAA').hom β) = 0 := by
      apply hEuc.2
      intro y hy
      obtain ⟨u, rfl⟩ : ∃ u : U, (h u : E) = y :=
        ⟨h.symm ⟨y, hA'V hy⟩, congrArg Subtype.val (h.apply_symm_apply _)⟩
      have hu : (u : M) ∈ A := (hAA' u).1 hy
      have hsq := congrArg (fun f => relativeHomologyMap ℚ n f β)
        (j5cE_pairIso_chain h hAA' (j5cE_point_iff h u) (Set.singleton_subset_iff.mpr hu)
          (Set.singleton_subset_iff.mpr hy))
      simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hsq
      rw [hsq, hres u hu, map_zero, map_zero]
    have hIβ : relativeHomologyMap ℚ n (j5cE_pairIso h A A' hAA').hom β = 0 :=
      (hexE n).1 (by rw [hγ, map_zero])
    have hβ0 : β = 0 :=
      j5cE_iso_injective (j5cE_pairIso h A A' hAA') n (by rw [hIβ, map_zero])
    rw [hβ0, map_zero]

/-- Local homology along `∅` vanishes above `n` and is detected by points, in any Hausdorff `M`:
the case `U = V = ∅` of `j5cE_of_homeomorph`. -/
theorem j5cE_empty {M E : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n) :
    LocalHomologyVanishesAbove M n (∅ : Set M) ∧
      LocalHomologyDetectedByPoints M n (∅ : Set M) :=
  j5cE_of_homeomorph hn isOpen_empty isOpen_empty (j5cE_emptyHomeomorph M E) isClosed_empty
    Set.Subset.rfl isCompact_empty Set.Subset.rfl fun u => absurd u.2 (Set.notMem_empty _)

theorem j5c_chart_aux {M E : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n)
    (e : OpenPartialHomeomorph M E) {A : Set M} (hA : IsCompact A) (hAe : A ⊆ e.source) :
    LocalHomologyVanishesAbove M n A ∧ LocalHomologyDetectedByPoints M n A := by
  refine j5cE_of_homeomorph hn e.open_source e.open_target (j5cE_sourceTargetHomeomorph e)
    hA.isClosed hAe (hA.image_of_continuousOn (e.continuousOn.mono hAe)) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hAe hx)
  · intro u
    rw [j5cE_sourceTargetHomeomorph_apply]
    constructor
    · rintro ⟨a, ha, hau⟩
      rw [← e.injOn (hAe ha) u.2 hau]
      exact ha
    · intro hu
      exact Set.mem_image_of_mem e hu

theorem j5c_iUnion_chart_aux {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : Module.finrank ℝ E = n) {m : ℕ} (A : Fin m → Set M)
    (hA : ∀ j, IsCompact (A j)) (hchart : ∀ j, ∃ x : M, A j ⊆ (chartAt E x).source) :
    LocalHomologyVanishesAbove M n (⋃ j, A j) ∧
      LocalHomologyDetectedByPoints M n (⋃ j, A j) := by
  have key : ∀ (m : ℕ) (A : Fin m → Set M), (∀ j, IsCompact (A j)) →
      (∀ j, ∃ x : M, A j ⊆ (chartAt E x).source) →
      LocalHomologyVanishesAbove M n (⋃ j, A j) ∧
        LocalHomologyDetectedByPoints M n (⋃ j, A j) := by
    intro m
    induction m with
    | zero =>
      intro A _ _
      rw [Set.iUnion_eq_empty.2 fun j => Fin.elim0 j]
      exact j5cE_empty hn
    | succ m ih =>
      intro A hA hchart
      have hU : (⋃ j : Fin (m + 1), A j) = A 0 ∪ ⋃ j : Fin m, A j.succ := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union, Fin.exists_fin_succ]
      obtain ⟨x0, hx0⟩ := hchart 0
      have h0 := j5c_chart_aux hn (chartAt E x0) (hA 0) hx0
      have h1 := ih (fun j => A j.succ) (fun j => hA _) (fun j => hchart _)
      have h01 := ih (fun j => A 0 ∩ A j.succ) (fun j => (hA 0).inter_right (hA _).isClosed)
        (fun j => ⟨x0, Set.inter_subset_left.trans hx0⟩)
      rw [← Set.inter_iUnion] at h01
      rw [hU]
      exact j5c_union_aux n (hA 0).isClosed
        (isCompact_iUnion fun (j : Fin m) => hA j.succ).isClosed
        h0.1 h1.1 h01.1 h0.2 h1.2
  exact key m A hA hchart

theorem j5c_compact_manifold_aux {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : Module.finrank ℝ E = n) {A : Set M} (hA : IsCompact A) :
    LocalHomologyVanishesAbove M n A ∧ LocalHomologyDetectedByPoints M n A := by
  classical
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : M => (chartAt E x).source)
    (fun x => (chartAt E x).open_source) (fun x _ => Set.mem_iUnion.2 ⟨x, mem_chart_source E x⟩)
  obtain ⟨K, hKc, hKU, hAK⟩ := hA.finite_compact_cover t (fun x : M => (chartAt E x).source)
    (fun x _ => (chartAt E x).open_source) ht
  have hEq : A = ⋃ j : Fin t.card, K (t.equivFin.symm j : M) := by
    rw [hAK]
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hy⟩
      exact ⟨t.equivFin ⟨i, hi⟩, by simpa using hy⟩
    · rintro ⟨j, hy⟩
      exact ⟨_, (t.equivFin.symm j).2, hy⟩
  rw [hEq]
  exact j5c_iUnion_chart_aux hn _ (fun j => hKc _) (fun j => ⟨_, hKU _⟩)

/-- Along compact sets in a Hausdorff charted space, classes with point values `μ` glue across a
union (statement 9, with detection on the compact intersection from statement 19). -/
theorem j5cE_hasClassAlong_union {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    {μ : ∀ x : M, RelativeHomology ℚ (pointComplementPair x) n} {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B) (hμA : HasClassAlong M n μ A)
    (hμB : HasClassAlong M n μ B) : HasClassAlong M n μ (A ∪ B) :=
  j5c_union_hasClassAlong_aux n hA.isClosed hB.isClosed μ hμA hμB
    (j5c_compact_manifold_aux hn (hA.inter_right hB.isClosed)).2

theorem j5c_hasClassAlong_of_isCompact_aux {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (μ : ∀ x : M, RelativeHomology ℚ (pointComplementPair x) n)
    (hμ : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (U : Set M)ᶜ) n,
        ∀ (y : M) (hy : y ∈ U),
          relativeHomologyMap ℚ n
            (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy)) c = μ y)
    {A : Set M} (hA : IsCompact A) :
    HasClassAlong M n μ A := by
  classical
  choose U hxU c hc using hμ
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : M => (U x : Set M))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  obtain ⟨K, hKc, hKU, hAK⟩ := hA.finite_compact_cover t (fun x : M => (U x : Set M))
    (fun x _ => (U x).isOpen) ht
  have key : ∀ s : Finset M, HasClassAlong M n μ (⋃ i ∈ s, K i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact ⟨0, fun x hx => by simp at hx⟩
    · intro a s _ ih
      rw [Finset.set_biUnion_insert]
      exact j5cE_hasClassAlong_union hn (hKc a) (s.isCompact_biUnion fun i _ => hKc i)
        (j5cE_hasClassAlong_mono (hKU a) ⟨c a, fun y hy => hc a y hy⟩) ih
  rw [hAK]
  exact key t

theorem j5c_exists_fundamentalClass_aux {M E : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {n : ℕ} (hn : Module.finrank ℝ E = n)
    (μ : ∀ x : M, RelativeHomology ℚ (pointComplementPair x) n)
    (hμ : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (U : Set M)ᶜ) n,
        ∀ (y : M) (hy : y ∈ U),
          relativeHomologyMap ℚ n
            (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy)) c = μ y) :
    ∃ w : RelativeHomology ℚ (TopPair.ofSubset
        (((⊤ : Opens M) : Set M)ᶜ : Set (TopCat.of M))) n,
      ∀ y : M,
        relativeHomologyMap ℚ n
            (supportInclusionPairMap (TopCat.of M)
              (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w = μ y := by
  obtain ⟨α, hα⟩ := j5c_hasClassAlong_of_isCompact_aux hn μ hμ
    (A := ((⊤ : Opens M) : Set M)) (by rw [Opens.coe_top]; exact isCompact_univ)
  exact ⟨α, fun y => hα y (Opens.mem_top y)⟩

theorem j5c_exists_complexFundamentalClass_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ∃ w : RelativeHomology ℚ (TopPair.ofSubset
        (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
          Set (TopCat.of (ComplexPoint X)))) (2 * d),
      ∀ y : ComplexPoint X,
        relativeHomologyMap ℚ (2 * d)
            (supportInclusionPairMap (TopCat.of (ComplexPoint X))
              (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w =
          complexLocalOrientation X d y :=
  j5c_exists_fundamentalClass_aux (E := Fin d → ℂ)
    (by rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex, mul_comm])
    (complexLocalOrientation X d) (exists_neighborhood_complexLocalOrientation X d)

theorem j5c_not_exists_fundamentalClass_euclidean_aux {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n)
    (hpos : 0 < n) (μ : ∀ x : E, RelativeHomology ℚ (pointComplementPair x) n)
    (hμ : ∃ x : E, μ x ≠ 0) :
    ¬ ∃ w : RelativeHomology ℚ (TopPair.ofSubset
        (((⊤ : Opens E) : Set E)ᶜ : Set (TopCat.of E))) n,
      ∀ y : E,
        relativeHomologyMap ℚ n
            (supportInclusionPairMap (TopCat.of E)
              (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w = μ y := by
  exact F_not_exists_fundamentalClass_euclidean hpos μ hμ

theorem j5c_translatedStandardComplexLocalClass_ne_zero_aux (d : ℕ) (v : Fin d → ℂ) :
    translatedStandardComplexLocalClass d v ≠ 0 := by
  exact F_translatedStandardComplexLocalClass_ne_zero d v

theorem j5c_translatedStandardComplexLocalClass_locallyCoherent_aux (d : ℕ) :
    ∀ x : Fin d → ℂ, ∃ U : Opens (Fin d → ℂ), x ∈ U ∧
      ∃ c : RelativeHomology ℚ
          (TopPair.ofSubset (X := TopCat.of (Fin d → ℂ)) (U : Set (Fin d → ℂ))ᶜ) (2 * d),
        ∀ (y : Fin d → ℂ) (hy : y ∈ U),
          relativeHomologyMap ℚ (2 * d)
            (supportInclusionPairMap (TopCat.of (Fin d → ℂ)) (Set.singleton_subset_iff.mpr hy)) c =
              translatedStandardComplexLocalClass d y := by
  intro x
  have hR : (0 : ℝ) < ‖x‖ + 1 := by positivity
  have hK : Convex ℝ (Metric.closedBall (0 : Fin d → ℂ) (‖x‖ + 1)) := convex_closedBall _ _
  have hKc : IsCompact (Metric.closedBall (0 : Fin d → ℂ) (‖x‖ + 1)) := isCompact_closedBall _ _
  have h0K : (0 : Fin d → ℂ) ∈ Metric.closedBall (0 : Fin d → ℂ) (‖x‖ + 1) :=
    Metric.mem_closedBall_self hR.le
  obtain ⟨c0, hc0⟩ :=
    (j5c_convex_restrict_bijective_aux hK hKc h0K (2 * d)).2 (standardComplexLocalClass ℚ d)
  have hUK : Metric.ball (0 : Fin d → ℂ) (‖x‖ + 1) ⊆ Metric.closedBall 0 (‖x‖ + 1) :=
    Metric.ball_subset_closedBall
  have h0U : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (‖x‖ + 1) := Metric.mem_ball_self hR
  refine ⟨⟨Metric.ball 0 (‖x‖ + 1), Metric.isOpen_ball⟩, ?_,
    relativeHomologyMap ℚ (2 * d) (supportInclusionPairMap (TopCat.of (Fin d → ℂ)) hUK) c0, ?_⟩
  · change x ∈ Metric.ball 0 (‖x‖ + 1)
    rw [mem_ball_zero_iff]
    linarith
  · intro y hy
    refine F_restrict_eq_translated_of_convex d h0U (convex_ball _ _) _ ?_ y hy
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, ← supportInclusionPairMap_trans]
    exact hc0

theorem j5c_exists_locallyCoherent_not_fundamentalClass_aux (d : ℕ) (hd : 0 < d) :
    ∃ μ : ∀ x : Fin d → ℂ, RelativeHomology ℚ (pointComplementPair x) (2 * d),
      (∀ x : Fin d → ℂ, ∃ U : Opens (Fin d → ℂ), x ∈ U ∧
        ∃ c : RelativeHomology ℚ
            (TopPair.ofSubset (X := TopCat.of (Fin d → ℂ)) (U : Set (Fin d → ℂ))ᶜ) (2 * d),
          ∀ (y : Fin d → ℂ) (hy : y ∈ U),
            relativeHomologyMap ℚ (2 * d)
              (supportInclusionPairMap (TopCat.of (Fin d → ℂ))
                (Set.singleton_subset_iff.mpr hy)) c = μ y) ∧
      (∀ x : Fin d → ℂ, μ x ≠ 0) ∧
      ¬ ∃ w : RelativeHomology ℚ (TopPair.ofSubset
          (((⊤ : Opens (Fin d → ℂ)) : Set (Fin d → ℂ))ᶜ : Set (TopCat.of (Fin d → ℂ)))) (2 * d),
        ∀ y : Fin d → ℂ,
          relativeHomologyMap ℚ (2 * d)
              (supportInclusionPairMap (TopCat.of (Fin d → ℂ))
                (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w = μ y := by
  refine ⟨translatedStandardComplexLocalClass d,
    j5c_translatedStandardComplexLocalClass_locallyCoherent_aux d,
    j5c_translatedStandardComplexLocalClass_ne_zero_aux d, ?_⟩
  exact j5c_not_exists_fundamentalClass_euclidean_aux (E := Fin d → ℂ)
    (by rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex, mul_comm])
    (by omega) _ ⟨0, j5c_translatedStandardComplexLocalClass_ne_zero_aux d 0⟩

end HodgeLean.RealDefs
