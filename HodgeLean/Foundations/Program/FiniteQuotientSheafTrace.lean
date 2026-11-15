import HodgeLean.Foundations.Program.ConstantSheafLocallyConstantSections
import HodgeLean.Foundations.Program.FiniteQuotientSectionTrace
import Mathlib.Topology.Sheaves.Functors

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- The orbit sum defines a morphism from the direct image constant sheaf to
 the constant sheaf on the quotient, with its actual section formula. -/
theorem finite_quotient_constantSheaf_trace
    {A B : TopCat.{0}} (G : Type) [Group G] [Fintype G]
    (a : G → (A ≃ₜ A)) (ha : ∀ g h x, a (g * h) x = a g (a h x))
    (q : A ⟶ B) (hq : Topology.IsQuotientMap q)
    (hinv : ∀ g x, q (a g x) = q x)
    (horbit : ∀ x y, q x = q y → ∃ g, a g x = y) :
    ∃ T : (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ) ⟶ 𝓒(B; ℚ),
      ∀ (U : Opens B) (s : 𝓒(A; ℚ).obj.obj (op ((Opens.map q).obj U)))
        (x : q ⁻¹' U),
        constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U (T.hom.app (op U) s)
          ⟨q x, x.property⟩ =
        ∑ g : G, constantSheafSectionEquiv (AddCommGrpCat.of ℚ)
          ((Opens.map q).obj U) s
          ⟨a g x, by change q (a g x) ∈ U; rw [hinv]; exact x.property⟩ := by
  let tr := fun U : Opens B =>
    (finite_quotient_open_locallyConstant_trace G a ha q hq hinv horbit U).choose
  have htr := fun U : Opens B =>
    (finite_quotient_open_locallyConstant_trace G a ha q hq hinv horbit U).choose_spec
  let eA := fun U : Opens B =>
    constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
  let eB := fun U : Opens B => constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U
  let t := fun U : Opens B => AddCommGrpCat.ofHom
    ((eB U).symm.toAddMonoidHom.comp
      ((tr U).toAddMonoidHom.comp (eA U).toAddMonoidHom))
  have ht (U : Opens B) (s : 𝓒(A; ℚ).obj.obj (op ((Opens.map q).obj U))) :
      eB U (t U s) = tr U (eA U s) := (eB U).apply_symm_apply _
  have hnat : ∀ {U V : (Opens B)ᵒᵖ} (i : U ⟶ V),
      ((TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ)).obj.map i ≫ t V.unop =
        t U.unop ≫ 𝓒(B; ℚ).obj.map i := by
    intro U V i
    ext s
    apply (eB V.unop).injective
    apply LocallyConstant.ext
    intro y
    have hle : V.unop ≤ U.unop := i.unop.le
    change eB V.unop (t V.unop (𝓒(A; ℚ).obj.map ((Opens.map q).map i.unop).op s)) y =
      eB V.unop (𝓒(B; ℚ).obj.map i (t U.unop s)) y
    rw [ht]
    have hh := constantSheafSectionEquiv_restrict (AddCommGrpCat.of ℚ)
      U.unop V.unop hle (t U.unop s) y
    change eB V.unop (𝓒(B; ℚ).obj.map i (t U.unop s)) y =
      eB U.unop (t U.unop s) ⟨y, hle y.property⟩ at hh
    rw [hh, ht U.unop s]
    obtain ⟨x, hx⟩ := hq.surjective (y : B)
    let xV : q ⁻¹' V.unop := ⟨x, by change q x ∈ V.unop; rw [hx]; exact y.property⟩
    have hyV : (⟨q xV, xV.property⟩ : V.unop) = y := Subtype.ext hx
    have hyU : (⟨q xV, hle xV.property⟩ : U.unop) = ⟨y, hle y.property⟩ := Subtype.ext hx
    rw [← hyV, htr V.unop _ xV, htr U.unop _ ⟨x, hle xV.property⟩]
    apply Finset.sum_congr rfl
    intro g _
    exact constantSheafSectionEquiv_restrict (AddCommGrpCat.of ℚ)
      ((Opens.map q).obj U.unop) ((Opens.map q).obj V.unop)
      (fun _ hz => hle hz) s _
  refine ⟨⟨{ app := fun U => t U.unop, naturality := by intro U V i; exact hnat i }⟩, ?_⟩
  intro U s x
  change eB U (t U s) _ = _
  rw [ht]
  exact htr U _ x

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf orbit trace has degree equal to the group order. -/
theorem finite_quotient_constantSheaf_trace_degree
    {A B : TopCat.{0}} (G : Type) [Fintype G] (a : G → A → A)
    (q : A ⟶ B) (hsurj : Function.Surjective q)
    (hinv : ∀ g x, q (a g x) = q x)
    (L : 𝓒(B; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ))
    (T : (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ) ⟶ 𝓒(B; ℚ))
    (hL : ∀ (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        (L.hom.app (op U) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U s ⟨q x, x.property⟩)
    (hT : ∀ (U : Opens B) (s : 𝓒(A; ℚ).obj.obj (op ((Opens.map q).obj U)))
      (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U (T.hom.app (op U) s)
        ⟨q x, x.property⟩ =
      ∑ g : G, constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        s ⟨a g x, by change q (a g x) ∈ U; rw [hinv]; exact x.property⟩) :
    L ≫ T = Fintype.card G • 𝟙 𝓒(B; ℚ) := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  apply (constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U.unop).injective
  apply LocallyConstant.ext
  intro y
  obtain ⟨x, hx⟩ := hsurj (y : B)
  let xU : q ⁻¹' U.unop := ⟨x, by change q x ∈ U.unop; rw [hx]; exact y.property⟩
  have hy : (⟨q xU, xU.property⟩ : U.unop) = y := Subtype.ext hx
  change constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U.unop
    (T.hom.app U (L.hom.app U s)) y = _
  rw [← hy, hT]
  simp only [hL, hinv]
  change (∑ _g : G, constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U.unop s
    ⟨q xU, xU.property⟩) = _
  simp only [Finset.sum_const, Finset.card_univ]
  change Fintype.card G • _ = constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U.unop
    (Fintype.card G • s) _
  rw [map_nsmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The opposite sheaf trace composition retains every stabilizer multiplicity.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter III, section 7, finite orbit transfer. -/
theorem finite_quotient_constantSheaf_trace_norm
    {A B : TopCat.{0}} (G : Type) [Fintype G] (a : G → A → A)
    (q : A ⟶ B) (hinv : ∀ g x, q (a g x) = q x)
    (L : 𝓒(B; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ))
    (T : (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ) ⟶ 𝓒(B; ℚ))
    (hL : ∀ (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        (L.hom.app (op U) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U s ⟨q x, x.property⟩)
    (hT : ∀ (U : Opens B) (s : 𝓒(A; ℚ).obj.obj (op ((Opens.map q).obj U)))
      (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U (T.hom.app (op U) s)
        ⟨q x, x.property⟩ =
      ∑ g : G, constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        s ⟨a g x, by change q (a g x) ∈ U; rw [hinv]; exact x.property⟩)
    (U : Opens B) (s : 𝓒(A; ℚ).obj.obj (op ((Opens.map q).obj U)))
    (x : q ⁻¹' U) :
    constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
      ((T ≫ L).hom.app (op U) s) x =
      ∑ g : G, constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        s ⟨a g x, by change q (a g x) ∈ U; rw [hinv]; exact x.property⟩ := by
  change constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
    (L.hom.app (op U) (T.hom.app (op U) s)) x = _
  rw [hL, hT]

set_option backward.isDefEq.respectTransparency false in
/-- Continuous maps induce the actual composition pullback on constant sheaf sections. -/
theorem constantSheaf_pullback_sections
    {A B : TopCat.{0}} (q : A ⟶ B) :
    ∃ L : 𝓒(B; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ),
      ∀ (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) (x : q ⁻¹' U),
        constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
          (L.hom.app (op U) s) x =
        constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U s ⟨q x, x.property⟩ := by
  let eA := fun U : Opens B =>
    constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
  let eB := fun U : Opens B => constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U
  let qU : ∀ U : Opens B, C(q ⁻¹' U, U) := fun U =>
    ⟨(U : Set B).restrictPreimage q, q.hom.continuous.restrictPreimage⟩
  let t := fun U : Opens B => AddCommGrpCat.ofHom
    ((eA U).symm.toAddMonoidHom.comp
      ((LocallyConstant.comapAddMonoidHom (qU U)).comp (eB U).toAddMonoidHom))
  have ht (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) :
      eA U (t U s) = (eB U s).comap (qU U) := (eA U).apply_symm_apply _
  have hnat : ∀ {U V : (Opens B)ᵒᵖ} (i : U ⟶ V),
      𝓒(B; ℚ).obj.map i ≫ t V.unop = t U.unop ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ)).obj.map i := by
    intro U V i
    ext s
    apply (eA V.unop).injective
    apply LocallyConstant.ext
    intro x
    have hle : V.unop ≤ U.unop := i.unop.le
    change eA V.unop (t V.unop (𝓒(B; ℚ).obj.map i s)) x =
      eA V.unop (𝓒(A; ℚ).obj.map ((Opens.map q).map i.unop).op (t U.unop s)) x
    rw [ht]
    have hh := constantSheafSectionEquiv_restrict (AddCommGrpCat.of ℚ)
      ((Opens.map q).obj U.unop) ((Opens.map q).obj V.unop)
      (fun _ hx => hle hx) (t U.unop s) x
    change eA V.unop
      (𝓒(A; ℚ).obj.map ((Opens.map q).map i.unop).op (t U.unop s)) x =
        eA U.unop (t U.unop s) ⟨x, hle x.property⟩ at hh
    rw [hh, ht]
    exact constantSheafSectionEquiv_restrict (AddCommGrpCat.of ℚ)
      U.unop V.unop hle s ⟨q x, x.property⟩
  refine ⟨⟨{ app := fun U => t U.unop, naturality := by intro U V i; exact hnat i }⟩, ?_⟩
  intro U s x
  change eA U (t U s) x = _
  rw [ht]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A constant sheaf pullback with the composition formula preserves actual constant sections. -/
theorem constantSheaf_pullback_sections_unit
    {A B : TopCat.{0}} (q : A ⟶ B)
    (L : 𝓒(B; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ))
    (hL : ∀ (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        (L.hom.app (op U) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U s ⟨q x, x.property⟩) :
    toSheafify (Opens.grothendieckTopology B) 𝓒ᵖ(B; ℚ) ≫ L.hom =
      (TopCat.Presheaf.pushforward AddCommGrpCat q).map
        (toSheafify (Opens.grothendieckTopology A) 𝓒ᵖ(A; ℚ)) := by
  apply NatTrans.ext
  funext U
  ext a
  apply (constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U.unop)).injective
  apply LocallyConstant.ext
  intro x
  change constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U.unop)
      (L.hom.app U ((toSheafify (Opens.grothendieckTopology B) 𝓒ᵖ(B; ℚ)).app U a)) x =
    constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U.unop)
      ((toSheafify (Opens.grothendieckTopology A) 𝓒ᵖ(A; ℚ)).app
        (op ((Opens.map q).obj U.unop)) a) x
  rw [hL, constantSheafSectionEquiv_constant, constantSheafSectionEquiv_constant]

end HodgeLean.Foundations.Program
