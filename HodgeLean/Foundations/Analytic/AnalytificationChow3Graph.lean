import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-! # Chow's lemma, stage F4g-C2: the graph closure

The core of Chow's lemma (EGA II, Théorème 5.6.1; Hartshorne, *Algebraic Geometry*, Ex. II.4.10),
stated for abstract data. `X ⟶ Y` is a separated morphism; `X` is covered by opens `Uᵢ`, each with
an immersion `φᵢ : Uᵢ ⟶ Pᵢ` into a separated `Y`-scheme; `P` is a `Y`-scheme with maps
`pᵢ : P ⟶ Pᵢ` over `Y`; and `φ : U ⟶ P` on an open `U ⊆ ⋂ Uᵢ` restricts each `φᵢ`. Let
`X' ⊆ X ×_Y P` be the scheme-theoretic image of the graph `U ⟶ X ×_Y P`, with projections
`π : X' ⟶ X` and `h : X' ⟶ P`. Then `h` is an immersion (`AnalytificationChow3_isImmersion_h`),
a closed immersion when `X ⟶ Y` is universally closed, and the range of `π` contains `U`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HodgeLean.Foundations.Analytic

universe u

/-- The scheme-theoretic image map `X ⟶ f.image` has trivial kernel when `f` is quasi-compact.
Source: Stacks Project, Tag 01R8 (the scheme-theoretic image); Mathlib
`Scheme.Hom.toImage_app_injective`. -/
instance AnalytificationChow3_toImage_isSchemeTheoreticallyDominant {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  let V : Y.affineOpens → f.image.affineOpens := fun U ↦
    ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top V ?_ fun U ↦ ?_
  · rw [← Scheme.Hom.preimage_iSup, ← top_le_iff]
    intro x _
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.imageι x)) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  · rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

example {X : Scheme.{u}} : IsSchemeTheoreticallyDominant (Scheme.Hom.toImage (𝟙 X)) :=
  inferInstance

/-- Two morphisms that agree over a separated `s` and agree after a scheme-theoretically dominant
morphism are equal: their equalizer is a closed subscheme through which the dominant morphism
factors, so its kernel is trivial and it is everything.
Source: Stacks Project, Tag 01RH (morphisms agreeing on a scheme-theoretically dense open);
Mathlib `ext_of_isDominant_of_isSeparated` (the reduced case). -/
lemma AnalytificationChow3_ext {W X Y Z : Scheme.{u}} {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have hl : ι' ≫ f' = ι' ≫ g' := by ext1; exact hU
  let l := equalizer.lift ι' hl
  have hle : (equalizer.ι f' g').left.ker = ⊥ := by
    refine le_bot_iff.mp ((Scheme.Hom.le_ker_comp l.left (equalizer.ι f' g').left).trans ?_)
    rw [← Over.comp_left, equalizer.lift_ι]
    exact (IsSchemeTheoreticallyDominant.ker_eq_bot ι).le
  have := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hle
  rw [← cancel_epi (equalizer.ι f' g').left]
  congrm $(equalizer.condition f' g').left

example {X Y : Scheme.{u}} (f : X ⟶ Y) : f = f :=
  AnalytificationChow3_ext (𝟙 Y) rfl (𝟙 X) rfl

/-- Immersions are stable under postcomposition with open immersions. -/
instance AnalytificationChow3_respectsRight :
    MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
  ⟨fun i hi g hg ↦ by
    have : IsOpenImmersion i := hi
    have : IsImmersion g := hg
    exact inferInstanceAs (IsImmersion (g ≫ i))⟩

/-- If `g ≫ i` is an immersion, so is `g` (Mathlib `IsImmersion.of_comp`). -/
instance AnalytificationChow3_hasOfPostcompProperty :
    MorphismProperty.HasOfPostcompProperty @IsImmersion @IsOpenImmersion :=
  ⟨fun g i _ hgi ↦ by
    have : IsImmersion (g ≫ i) := hgi
    exact IsImmersion.of_comp g i⟩

/-- The data of the graph-closure construction of Chow's lemma (EGA II, 5.6.1): the opens `Uᵢ`
covering `X` with immersions `φᵢ : Uᵢ ⟶ Pᵢ` over `Y`, the `Y`-scheme `P` with maps
`pᵢ : P ⟶ Pᵢ` over `Y`, and the morphism `φ : U ⟶ P` on an open `U ⊆ ⋂ Uᵢ` restricting each `φᵢ`.
Source: EGA II, Théorème 5.6.1; Hartshorne, *Algebraic Geometry*, Ex. II.4.10. -/
structure AnalytificationChow3_GraphData {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The ambient `Y`-scheme (a product of the `Pᵢ` in the application). -/
  P : Scheme.{u}
  /-- Its structure morphism. -/
  s : P ⟶ Y
  /-- The index type of the cover. -/
  ι : Type
  /-- The opens covering `X`. -/
  Ui : ι → X.Opens
  /-- The targets of the immersions. -/
  Pi : ι → Scheme.{u}
  /-- Their structure morphisms. -/
  t : ∀ i, Pi i ⟶ Y
  /-- The maps from `P`. -/
  p : ∀ i, P ⟶ Pi i
  /-- The immersions. -/
  φ : ∀ i, (Ui i).toScheme ⟶ Pi i
  /-- The open on which the graph is taken. -/
  U : X.Opens
  le_Ui : ∀ i, U ≤ Ui i
  /-- The morphism to `P` on `U`. -/
  φU : U.toScheme ⟶ P
  isSeparated_t : ∀ i, IsSeparated (t i)
  isImmersion_φ : ∀ i, IsImmersion (φ i)
  p_t : ∀ i, p i ≫ t i = s
  φ_t : ∀ i, φ i ≫ t i = (Ui i).ι ≫ f
  φU_p : ∀ i, φU ≫ p i = X.homOfLE (le_Ui i) ≫ φ i
  φU_s : U.ι ≫ f = φU ≫ s
  mem_Ui : ∀ x : X, ∃ i, x ∈ Ui i
  quasiCompact_graph : QuasiCompact (pullback.lift U.ι φU φU_s)

namespace AnalytificationChow3_GraphData

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (D : AnalytificationChow3_GraphData f)

/-- The graph `U ⟶ X ×_Y P` of `φ`. -/
def graph : D.U.toScheme ⟶ pullback f D.s := pullback.lift D.U.ι D.φU D.φU_s

instance : QuasiCompact D.graph := D.quasiCompact_graph

/-- The closure `X'` of the graph: its scheme-theoretic image in `X ×_Y P`. -/
abbrev X' : Scheme.{u} := D.graph.image

/-- The closed immersion `X' ⟶ X ×_Y P`. -/
abbrev j : D.X' ⟶ pullback f D.s := D.graph.imageι

/-- The first projection `π : X' ⟶ X`. -/
def π : D.X' ⟶ X := D.j ≫ pullback.fst f D.s

/-- The second projection `h : X' ⟶ P`. -/
def h : D.X' ⟶ D.P := D.j ≫ pullback.snd f D.s

lemma π_f : D.π ≫ f = D.h ≫ D.s := by
  simp [π, h, pullback.condition]

@[reassoc]
lemma toImage_π : D.graph.toImage ≫ D.π = D.U.ι := by
  rw [π, j, Scheme.Hom.toImage_imageι_assoc, graph, pullback.lift_fst]

@[reassoc]
lemma toImage_h : D.graph.toImage ≫ D.h = D.φU := by
  rw [h, j, Scheme.Hom.toImage_imageι_assoc, graph, pullback.lift_snd]

/-- The range of `π` contains `U`. -/
lemma le_range_π (x : X) (hx : x ∈ D.U) : x ∈ Set.range D.π := by
  obtain ⟨y, rfl⟩ : x ∈ Set.range D.U.ι := by simpa using hx
  exact ⟨D.graph.toImage y, by rw [← Scheme.Hom.comp_apply, toImage_π]⟩

/-- **Claim A.** On `π⁻¹(Uᵢ)`, `pᵢ ∘ h = φᵢ ∘ π`: both agree on the scheme-theoretically dense
image of `U`, and `Pᵢ` is separated over `Y`. -/
lemma claimA (i : D.ι) :
    (D.π ∣_ D.Ui i) ≫ D.φ i = (D.π ⁻¹ᵁ D.Ui i).ι ≫ D.h ≫ D.p i := by
  have := D.isSeparated_t i
  refine AnalytificationChow3_ext (D.t i) ?_ (pullback.snd D.graph.toImage (D.π ⁻¹ᵁ D.Ui i).ι) ?_
  · rw [Category.assoc, D.φ_t, morphismRestrict_ι_assoc, Category.assoc, Category.assoc,
      D.p_t, D.π_f]
  · have h1 : pullback.snd D.graph.toImage (D.π ⁻¹ᵁ D.Ui i).ι ≫ (D.π ∣_ D.Ui i) =
        pullback.fst _ _ ≫ X.homOfLE (D.le_Ui i) := by
      rw [← cancel_mono (D.Ui i).ι, Category.assoc, morphismRestrict_ι, ← pullback.condition_assoc,
        toImage_π, Category.assoc, Scheme.homOfLE_ι]
    rw [reassoc_of% h1, ← D.φU_p, ← pullback.condition_assoc, toImage_h_assoc]

/-- The open `Vᵢ ⊆ Pᵢ` in which `φᵢ` is a closed immersion. -/
def V (i : D.ι) : (D.Pi i).Opens :=
  have := D.isImmersion_φ i
  (D.φ i).coborderRange

/-- The closed immersion `Uᵢ ⟶ Vᵢ`. -/
def c (i : D.ι) : (D.Ui i).toScheme ⟶ D.V i :=
  have := D.isImmersion_φ i
  (D.φ i).liftCoborder

instance (i : D.ι) : IsClosedImmersion (D.c i) := by
  have := D.isImmersion_φ i
  dsimp [c, V]
  infer_instance

@[reassoc (attr := simp)]
lemma c_ι (i : D.ι) : D.c i ≫ (D.V i).ι = D.φ i := by
  have := D.isImmersion_φ i
  exact (D.φ i).liftCoborder_ι

/-- **Claim B.** `(pᵢ ∘ h)⁻¹(Vᵢ) ⊆ π⁻¹(Uᵢ)`: on `(pᵢ ∘ h)⁻¹(Vᵢ)` the map `pᵢ ∘ h` factors through
the closed `Uᵢ ⊆ Vᵢ`, and the factorization agrees with `π` (`X` separated over `Y`). -/
lemma claimB [IsSeparated f] (i : D.ι) :
    D.h ⁻¹ᵁ (D.p i ⁻¹ᵁ D.V i) ≤ D.π ⁻¹ᵁ D.Ui i := by
  let T : D.X'.Opens := (D.h ≫ D.p i) ⁻¹ᵁ D.V i
  let ψ : T.toScheme ⟶ D.V i := (D.h ≫ D.p i) ∣_ D.V i
  let E := pullback.snd D.graph.toImage T.ι
  have hE : E ≫ ψ = pullback.fst _ _ ≫ X.homOfLE (D.le_Ui i) ≫ D.c i := by
    rw [← cancel_mono (D.V i).ι, Category.assoc, morphismRestrict_ι, ← pullback.condition_assoc,
      toImage_h_assoc, Category.assoc, Category.assoc, c_ι, D.φU_p]
  have hker : (D.c i).ker ≤ ψ.ker := by
    have : ψ.ker = (E ≫ ψ).ker := by
      rw [Scheme.Hom.ker_comp, IsSchemeTheoreticallyDominant.ker_eq_bot E,
        Scheme.IdealSheafData.map_bot]
    rw [this, hE, ← Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _
  let α := IsClosedImmersion.lift (D.c i) ψ hker
  have hα : α ≫ (D.Ui i).ι = T.ι ≫ D.π := by
    refine AnalytificationChow3_ext f ?_ E ?_
    · rw [Category.assoc, ← D.φ_t, ← D.c_ι]
      simp only [Category.assoc, α, IsClosedImmersion.lift_fac_assoc, ψ, morphismRestrict_ι_assoc,
        D.p_t, D.π_f]
      rfl
    · have hEα : E ≫ α = pullback.fst _ _ ≫ X.homOfLE (D.le_Ui i) := by
        rw [← cancel_mono (D.c i), Category.assoc, IsClosedImmersion.lift_fac, hE, Category.assoc]
      rw [reassoc_of% hEα, Scheme.homOfLE_ι, ← pullback.condition_assoc, toImage_π]
  intro x hx
  have hx' : x ∈ T := hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range T.ι := by rw [Scheme.Opens.range_ι]; exact hx'
  change D.π (T.ι y) ∈ D.Ui i
  rw [← Scheme.Hom.comp_apply, ← hα, Scheme.Hom.comp_apply]
  exact (α y).2

/-- **Claim C.** `h` restricted to `π⁻¹(Uᵢ)` is an immersion: it factors through the graph of
`φᵢ` in `Uᵢ ×_{Pᵢ} P`, whose projection to `P` is an immersion (base change of `φᵢ`). -/
lemma claimC (i : D.ι) : IsImmersion ((D.π ⁻¹ᵁ D.Ui i).ι ≫ D.h) := by
  have := D.isImmersion_φ i
  let W := D.π ⁻¹ᵁ D.Ui i
  let k : W.toScheme ⟶ pullback (D.φ i) (D.p i) :=
    pullback.lift (D.π ∣_ D.Ui i) (W.ι ≫ D.h) (by rw [D.claimA i, Category.assoc])
  have hm : pullback.fst (D.φ i) (D.p i) ≫ (D.Ui i).ι ≫ f = pullback.snd (D.φ i) (D.p i) ≫ D.s := by
    rw [← D.φ_t, pullback.condition_assoc, D.p_t]
  let m : pullback (D.φ i) (D.p i) ⟶ pullback f D.s :=
    pullback.lift (pullback.fst _ _ ≫ (D.Ui i).ι) (pullback.snd _ _) (by rw [Category.assoc, hm])
  have hkm : k ≫ m = W.ι ≫ D.j := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, morphismRestrict_ι]
      rfl
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, h, Category.assoc]
  have : IsImmersion (k ≫ m) := by rw [hkm]; infer_instance
  have : IsImmersion k := IsImmersion.of_comp k m
  have hk : W.ι ≫ D.h = k ≫ pullback.snd _ _ := by simp [k]
  rw [hk]
  infer_instance

/-- **The graph closure maps to `P` by an immersion** (EGA II, 5.6.1; Hartshorne Ex. II.4.10):
every point of `X'` lies in some `π⁻¹(Uᵢ)`, which is `h⁻¹(pᵢ⁻¹(Vᵢ))` by claims A and B, and on
which `h` is an immersion by claim C. -/
theorem AnalytificationChow3_isImmersion_h [IsSeparated f] : IsImmersion D.h := by
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage D.h fun x ↦ ?_
  obtain ⟨i, hi⟩ := D.mem_Ui (D.π x)
  refine ⟨D.p i ⁻¹ᵁ D.V i, ?_, ?_⟩
  · obtain ⟨y, rfl⟩ : x ∈ Set.range (D.π ⁻¹ᵁ D.Ui i).ι := by simpa using hi
    have e2 : D.p i (D.h ((D.π ⁻¹ᵁ D.Ui i).ι y)) = D.φ i ((D.π ∣_ D.Ui i) y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, D.claimA i]
    change D.p i (D.h ((D.π ⁻¹ᵁ D.Ui i).ι y)) ∈ D.V i
    rw [e2, ← D.c_ι, Scheme.Hom.comp_apply]
    exact (D.c i _).2
  · have hle := D.claimB i
    have := D.claimC i
    rw [← Scheme.homOfLE_ι D.X' hle, Category.assoc]
    infer_instance

/-- With `X ⟶ Y` universally closed, `h` is a closed immersion: it is the composite of the closed
immersion `X' ⟶ X ×_Y P` with the universally closed projection, so its range is closed. -/
theorem AnalytificationChow3_isClosedImmersion_h [IsSeparated f] [UniversallyClosed f] :
    IsClosedImmersion D.h := by
  have := D.AnalytificationChow3_isImmersion_h
  have : UniversallyClosed D.h := by dsimp [h]; infer_instance
  exact IsClosedImmersion.of_isPreimmersion _ D.h.isClosedMap.isClosed_range

end AnalytificationChow3_GraphData

end HodgeLean.Foundations.Analytic
