import HodgeLean.Foundations.Program.TorusAlgebraizationB54Charts
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization

namespace HodgeLean.Foundations.Program

universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]

def b54_relativeChartMap (f : G →+*ᵍ H) (r : A) :
    (H 0) ⊗[ℤ] Away G r →ₐ[ℤ] Away H (f r) :=
  Algebra.TensorProduct.lift
    (fromZeroRingHom H (Submonoid.powers (f r))).toIntAlgHom
    (Away.map f r).toIntAlgHom (fun _ _ ↦ Commute.all _ _)

theorem b54_relativeChartMap_surjective (f : G →+*ᵍ H)
    {ι : Type*} [Fintype ι] (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (hgen : Algebra.adjoin (H 0) (Set.range (fun i ↦ f (v i))) = ⊤)
    {r : A} (hr : r ∈ G 1) :
    Function.Surjective (b54_relativeChartMap f r) := by
  apply b54_away_surjective_of_ratios H (f.map_mem hr) (fun i ↦ f (v i))
    (fun i ↦ f.map_mem (hv i)) hgen (b54_relativeChartMap f r).toRingHom
  · intro c
    refine ⟨c ⊗ₜ[ℤ] 1, ?_⟩
    simp [b54_relativeChartMap, algebraMap_eq]
  · intro i
    refine ⟨1 ⊗ₜ[ℤ] Away.mk G hr 1 (v i) (by simpa using hv i), ?_⟩
    simp [b54_relativeChartMap, Away.map_mk]

def b54_affineProductIso (C D : Type) [CommRing C] [CommRing D] :
    pullback (terminal.from (Spec (.of C))) (terminal.from (Spec (.of D))) ≅
      Spec (.of (C ⊗[ℤ] D)) :=
  let e := terminalIsTerminal.uniqueUpToIso specZIsTerminal
  (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) e.hom
    (specZIsTerminal.hom_ext _ _) (specZIsTerminal.hom_ext _ _))) ≪≫
    pullbackSpecIso ℤ C D

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem b54_affineProductLift_isClosedImmersion
    {C D E : Type} [CommRing C] [CommRing D] [CommRing E]
    (f : C →+* E) (g : D →+* E)
    (hsurj : Function.Surjective
      (Algebra.TensorProduct.lift f.toIntAlgHom g.toIntAlgHom
        (fun _ _ ↦ Commute.all _ _))) :
    IsClosedImmersion (pullback.lift (f := terminal.from (Spec (.of C)))
      (g := terminal.from (Spec (.of D))) (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom g))
      (terminal.hom_ext _ _)) := by
  let φ := Algebra.TensorProduct.lift f.toIntAlgHom g.toIntAlgHom
    (fun _ _ ↦ Commute.all _ _)
  let e := b54_affineProductIso C D
  have he : pullback.lift (f := terminal.from (Spec (.of C)))
      (g := terminal.from (Spec (.of D))) (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom g))
      (terminal.hom_ext _ _) ≫ e.hom = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    dsimp only [e, b54_affineProductIso, Iso.trans_hom, asIso_hom]
    apply (cancel_mono (pullbackSpecIso ℤ C D).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.comp_id]
      rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      ext c
      simp [φ]
    · simp only [Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
      rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext d
      simp [φ]
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ e.hom, he]
  exact IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hsurj

end HodgeLean.Foundations.Program

namespace HodgeLean.Foundations.Program

variable {A B σ τ : Type} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]

def b54_relativeProj (f : G →+*ᵍ H)
    (hf : HomogeneousIdeal.irrelevant H ≤ (HomogeneousIdeal.irrelevant G).map f) :
    Proj H ⟶ pullback (terminal.from (Spec (.of (H 0)))) (terminal.from (Proj G)) :=
  pullback.lift (Proj.toSpecZero H) (Proj.map f hf) (terminal.hom_ext _ _)

def b54_productChart {Y U : Scheme} (T : Scheme) (i : U ⟶ Y) :
    pullback (terminal.from T) (terminal.from U) ⟶
      pullback (terminal.from T) (terminal.from Y) :=
  pullback.map _ _ _ _ (𝟙 T) i (𝟙 _) (by simp) (by simp)

instance b54_productChart_isOpenImmersion {Y U : Scheme} (T : Scheme)
    (i : U ⟶ Y) [IsOpenImmersion i] : IsOpenImmersion (b54_productChart T i) := by
  unfold b54_productChart
  infer_instance

theorem b54_productChart_range {Y U : Scheme} (T : Scheme) (i : U ⟶ Y) :
    Set.range (b54_productChart T i) =
      pullback.snd (terminal.from T) (terminal.from Y) ⁻¹' Set.range i := by
  rw [b54_productChart, Scheme.Pullback.range_map]
  simp

def b54_relativeProjChart (f : G →+*ᵍ H) (r : A) :
    Spec (.of (Away H (f r))) ⟶
      pullback (terminal.from (Spec (.of (H 0)))) (terminal.from (Spec (.of (Away G r)))) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (fromZeroRingHom H (.powers (f r)))))
    (Spec.map (CommRingCat.ofHom (Away.map f r))) (terminal.hom_ext _ _)

theorem b54_relativeProjChart_isClosedImmersion (f : G →+*ᵍ H)
    {ι : Type*} [Fintype ι] (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (hgen : Algebra.adjoin (H 0) (Set.range (fun i ↦ f (v i))) = ⊤)
    {r : A} (hr : r ∈ G 1) : IsClosedImmersion (b54_relativeProjChart f r) :=
  b54_affineProductLift_isClosedImmersion _ _ (b54_relativeChartMap_surjective f v hv hgen hr)

theorem b54_relativeProj_chart_commutes (f : G →+*ᵍ H)
    (hf : HomogeneousIdeal.irrelevant H ≤ (HomogeneousIdeal.irrelevant G).map f)
    {r : A} {n : ℕ} (hr : r ∈ G n) (hn : 0 < n) :
    Proj.awayι H (f r) (f.map_mem hr) hn ≫ b54_relativeProj f hf =
      b54_relativeProjChart f r ≫
        b54_productChart (Spec (.of (H 0))) (Proj.awayι G r hr hn) := by
  apply pullback.hom_ext
  · simp [b54_relativeProj, b54_relativeProjChart, b54_productChart,
      Category.assoc, Proj.awayι_toSpecZero]
  · simpa [b54_relativeProj, b54_relativeProjChart, b54_productChart,
      Category.assoc] using Proj.awayι_comp_map f hf hn r hr

theorem b54_relativeProj_chart_isPullback (f : G →+*ᵍ H)
    (hf : HomogeneousIdeal.irrelevant H ≤ (HomogeneousIdeal.irrelevant G).map f)
    {r : A} {n : ℕ} (hr : r ∈ G n) (hn : 0 < n) :
    IsPullback (b54_relativeProjChart f r) (Proj.awayι H (f r) (f.map_mem hr) hn)
      (b54_productChart (Spec (.of (H 0))) (Proj.awayι G r hr hn))
      (b54_relativeProj f hf) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (b54_relativeProj_chart_commutes f hf hr hn)
  ext x
  change b54_relativeProj f hf x ∈ Set.range
    (b54_productChart (Spec (.of (H 0))) (Proj.awayι G r hr hn)) ↔ _
  rw [b54_productChart_range, Set.mem_preimage, ← Scheme.Hom.comp_apply]
  simp only [b54_relativeProj, pullback.lift_snd]
  change Proj.map f hf x ∈ (Proj.awayι G r hr hn).opensRange ↔
    x ∈ (Proj.awayι H (f r) (f.map_mem hr) hn).opensRange
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  rfl

def b54_productOpenCover {Y : Scheme} (T : Scheme) (𝒰 : Y.OpenCover) :
    (pullback (terminal.from T) (terminal.from Y)).OpenCover :=
  Scheme.Cover.mkOfCovers 𝒰.I₀
    (fun i ↦ pullback (terminal.from T) (terminal.from (𝒰.X i)))
    (fun i ↦ b54_productChart T (𝒰.f i)) (by
      intro x
      let i := 𝒰.idx (pullback.snd (terminal.from T) (terminal.from Y) x)
      obtain ⟨y, hy⟩ := 𝒰.covers (pullback.snd (terminal.from T) (terminal.from Y) x)
      refine ⟨i, ?_⟩
      change x ∈ Set.range (b54_productChart T (𝒰.f i))
      rw [b54_productChart_range]
      exact ⟨y, hy⟩)

theorem b54_relativeProj_isClosedImmersion (f : G →+*ᵍ H)
    (hf : HomogeneousIdeal.irrelevant H ≤ (HomogeneousIdeal.irrelevant G).map f)
    {ι : Type} [Fintype ι] (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range v))
    (hgen : Algebra.adjoin (H 0) (Set.range (fun i ↦ f (v i))) = ⊤) :
    IsClosedImmersion (b54_relativeProj f hf) := by
  let 𝒰 := Proj.affineOpenCoverOfIrrelevantLESpan G v hv (fun _ ↦ zero_lt_one) hcover
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (b54_productOpenCover (Spec (.of (H 0))) 𝒰.openCover)]
  intro i
  have h := b54_relativeProj_chart_isPullback f hf (hv i) zero_lt_one
  have hi := b54_relativeProjChart_isClosedImmersion f v hv hgen (hv i)
  have he : h.flip.isoPullback.inv ≫ b54_relativeProjChart f (v i) =
      pullback.snd (b54_relativeProj f hf)
        (b54_productChart (Spec (.of (H 0))) (Proj.awayι G (v i) (hv i) zero_lt_one)) := by simp
  change IsClosedImmersion (pullback.snd (b54_relativeProj f hf)
    (b54_productChart (Spec (.of (H 0))) (Proj.awayι G (v i) (hv i) zero_lt_one)))
  rw [← he]
  infer_instance

end HodgeLean.Foundations.Program
