import HodgeLean.Adapters.WedgeThetaComplexProofs

/-! # Wedge with a closed holomorphic `1`-form on the de Rham complex: frozen specification

Stage `WedgeThetaComplex` (`docs/specs/WedgeThetaComplex.md`), stages 2 and 3 of the `hL` track of
`docs/specs/CupFilteredDeRham.md`. `hL` says that cup product with a class in `F^1 H^1` raises the
Hodge filtration by one. On the de Rham side, a class in `F^1 H^1_dR` is the class of a closed
global holomorphic `1`-form `θ` (stages 4c, 4l), and cup product with it should be induced by
`L_θ = θ ∧ − : Ω• ⟶ Ω•[1]`. This stage freezes `L_θ` and its effect on `F^•`.

Claimed:
* for smooth `X` of relative dimension `d`, every global holomorphic `1`-form `θ` and every `n`:
  a morphism of sheaves `Ω^n ⟶ Ω^{n+1}` whose value at each point is `θ(x) ∧ −` exists and is
  unique; for closed `θ`, these morphisms anticommute with `d`: `d(θ ∧ ω) = -θ ∧ dω`;
* for smooth integral `X` and closed `θ`: a morphism of complexes `L_θ : Ω•(X) ⟶ Ω•(X)[1]` (with
  Mathlib's shift, whose differential is `-d`) given by `θ(x) ∧ −` in every degree exists and is
  unique; `L_0 = 0` and `L_{θ+θ'} = L_θ + L_{θ'}`;
* every morphism of complexes `L : Ω•(X) ⟶ Ω•(X)[1]` restricts to `F^q Ω• ⟶ F^{q+1} Ω•[1]`, since
  `F^•` is the stupid filtration;
* the shift map `ℍ^k(K[1]) → ℍ^{k+1}(K)` is bijective and natural, and composed with
  `hypercohomologyMap L` it is composition with `L` as a degree-one shifted morphism;
* for every `L : Ω•(X) ⟶ Ω•(X)[1]`, in particular `L_θ`, the induced map
  `H^k_dR(X) → H^{k+1}_dR(X)` sends `F^q` into `F^{q+1}`.

Not claimed: that the map induced by `L_θ` is the cup product with the class of `θ` (the
comparison with the singular cup, stages 4–6 of the `hL` track), `hL` itself, or anything about
`CupFiltered`, the opposedness or `HodgeDecomposition`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations

namespace HodgeLean.Adapters

/-- **The wedge with a global `1`-form exists on `Ω^n`.** For a global holomorphic `1`-form `θ`
on `X(ℂ)` there is a morphism of sheaves `Ω^n ⟶ Ω^{n+1}` whose value at every point of every open
is `θ(x) ∧ −`. On an open `U`, near each point both `θ` and a section `s` come from Kähler forms
`ι m` and `ω` on one open (`spec_exists_local_representative`); the local products `ι m * ω` have
values `θ(y) ∧ s(y)` (cupf1's `laneB_chartEvaluationHolo_ι_mul`), so they agree on overlaps
(values determine sections, `laneB_section_eq`) and glue; the glued sections are additive and
compatible with restriction for the same reason.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the exterior product of
holomorphic forms); cupf1's statements 6–7 and their local layer. -/
theorem spec_exists_isWedgeBy (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (n : ℕ) :
    ∃ w : holomorphicDeRhamSheaf X d n ⟶ holomorphicDeRhamSheaf X d (n + 1),
      IsWedgeBy X d θ n w :=
  spec_exists_isWedgeBy_aux X d θ n

/-- The wedge on global sections has the pointwise values `θ(x) ∧ ζ(x)`. -/
example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (n : ℕ)
    (ζ : (holomorphicDeRhamSheaf X d n).presheaf.obj (op ⊤)) :
    ∃ ξ : (holomorphicDeRhamSheaf X d (n + 1)).presheaf.obj (op ⊤), ∀ x,
      globalFormValue X d (n + 1) x ξ =
        covectorWedgeForm (globalOneFormCovector X d θ x) (globalFormValue X d n x ζ) := by
  obtain ⟨w, hw⟩ := spec_exists_isWedgeBy X d θ n
  exact ⟨w.hom.app (op ⊤) ζ, fun x => hw ⊤ x trivial ζ⟩

/-- **The wedge is unique.** Two morphisms `Ω^n ⟶ Ω^{n+1}` with the values `θ(x) ∧ −` agree:
sections of `Ω^{n+1}` are determined by their values (cupf1's `laneB_section_eq`).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2; cupf1's
`laneB_section_eq`, the local form of `spec_eq_zero_of_globalFormValue_eq_zero`. -/
theorem spec_isWedgeBy_unique (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (n : ℕ)
    (w w' : holomorphicDeRhamSheaf X d n ⟶ holomorphicDeRhamSheaf X d (n + 1))
    (hw : IsWedgeBy X d θ n w) (hw' : IsWedgeBy X d θ n w') : w = w' :=
  spec_isWedgeBy_unique_aux X d θ n w w' hw hw'

/-- So `IsWedgeBy` pins one morphism: for `θ = 0` it is the zero morphism, once the zero
morphism satisfies it. -/
example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom] (n : ℕ)
    (w : holomorphicDeRhamSheaf X d n ⟶ holomorphicDeRhamSheaf X d (n + 1))
    (hw : IsWedgeBy X d 0 n w) (h0 : IsWedgeBy X d 0 n 0) : w = 0 :=
  spec_isWedgeBy_unique X d 0 n w 0 hw h0

/-- **The wedge with a closed form anticommutes with `d`.** For closed `θ`,
`d(θ ∧ ω) = dθ ∧ ω - θ ∧ dω = -θ ∧ dω`: as morphisms `Ω^n ⟶ Ω^{n+2}`,
`w_n ≫ d_{n+1} = -(d_n ≫ w_{n+1})`. Locally `θ = ι m` and the section is a Kähler form `ω`;
the Leibniz rule (upstream `Algebra.DeRham.extDeriv_mul`) gives
`d(ι m * ω) = d(ι m) * ω - ι m * dω`, and the first term has value zero at every point because
`dθ = 0` (cupf1's `laneB_vanish_ιMulti_mul`, after moving the even factor `d(ι m)` past `ω`);
values determine sections.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the Leibniz rule);
upstream `Algebra.DeRham.extDeriv_mul`; cupf1's `laneB_vanish_extDeriv_ιMulti`. -/
theorem spec_isWedgeBy_comp_differential (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (hθ : (holomorphicDeRhamSheafDifferential X d 1).hom.app (op ⊤) θ = 0) (n : ℕ)
    (w : holomorphicDeRhamSheaf X d n ⟶ holomorphicDeRhamSheaf X d (n + 1))
    (w' : holomorphicDeRhamSheaf X d (n + 1) ⟶ holomorphicDeRhamSheaf X d (n + 1 + 1))
    (hw : IsWedgeBy X d θ n w) (hw' : IsWedgeBy X d θ (n + 1) w') :
    w ≫ holomorphicDeRhamSheafDifferential X d (n + 1) =
      -(holomorphicDeRhamSheafDifferential X d n ≫ w') :=
  spec_isWedgeBy_comp_differential_aux X d θ hθ n w w' hw hw'

/-- With `spec_exists_isWedgeBy`: the two wedges exist and anticommute with `d`. -/
example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (hθ : (holomorphicDeRhamSheafDifferential X d 1).hom.app (op ⊤) θ = 0) (n : ℕ) :
    ∃ (w : holomorphicDeRhamSheaf X d n ⟶ holomorphicDeRhamSheaf X d (n + 1))
      (w' : holomorphicDeRhamSheaf X d (n + 1) ⟶ holomorphicDeRhamSheaf X d (n + 1 + 1)),
      IsWedgeBy X d θ n w ∧ IsWedgeBy X d θ (n + 1) w' ∧
        w ≫ holomorphicDeRhamSheafDifferential X d (n + 1) =
          -(holomorphicDeRhamSheafDifferential X d n ≫ w') := by
  obtain ⟨w, hw⟩ := spec_exists_isWedgeBy X d θ n
  obtain ⟨w', hw'⟩ := spec_exists_isWedgeBy X d θ (n + 1)
  exact ⟨w, w', hw, hw', spec_isWedgeBy_comp_differential X d θ hθ n w w' hw hw'⟩

/-- **`L_θ` as a morphism of complexes.** For smooth integral `X` and a closed global holomorphic
`1`-form `θ`, there is a morphism of complexes `L_θ : Ω•(X) ⟶ Ω•(X)[1]` whose component
`Ω^n ⟶ Ω^{n+1}` is the wedge with `θ` for every `n ≥ 0`. Mathlib's shift has differential
`(K⟦1⟧).d n (n+1) = -K.d (n+1) (n+2)` (`CochainComplex.shiftFunctor_obj_d'`), so the commutation
required of `L_θ` is exactly `spec_isWedgeBy_comp_differential`; in negative degrees `Ω•(X)` is
zero. The components come from `spec_exists_isWedgeBy`, transported along `wedgeThetaXIso` and
`wedgeThetaShiftXIso`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§8.1; `spec_exists_isWedgeBy`, `spec_isWedgeBy_comp_differential`; Mathlib's
`HomologicalComplex.extend`. -/
theorem spec_exists_isWedgeThetaHom (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1) (hθ : θ ∈ closedGlobalHolomorphicForms X 1) :
    ∃ L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧, IsWedgeThetaHom X θ L :=
  spec_exists_isWedgeThetaHom_aux X θ hθ

/-- Its degree-zero component sends a holomorphic function `f` to `f θ`, pointwise. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1) (hθ : θ ∈ closedGlobalHolomorphicForms X 1) :
    ∃ L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧,
      IsWedgeBy X (dim X.left) θ 0 (wedgeThetaComponent X L 0) :=
  (spec_exists_isWedgeThetaHom X θ hθ).imp fun _ h => h 0

/-- **`L_θ` is unique.** Two morphisms of complexes `Ω•(X) ⟶ Ω•(X)[1]` that are the wedge with
`θ` in every degree `n ≥ 0` are equal: their components agree by `spec_isWedgeBy_unique`, and in
negative degrees the source is zero.
Source: `spec_isWedgeBy_unique`; Mathlib's `HomologicalComplex.hom_ext` and
`HomologicalComplex.isZero_extend_X`. -/
theorem spec_isWedgeThetaHom_unique (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1) (L L' : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (hL : IsWedgeThetaHom X θ L) (hL' : IsWedgeThetaHom X θ L') : L = L' :=
  spec_isWedgeThetaHom_unique_aux X θ L L' hL hL'

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1) (hθ : θ ∈ closedGlobalHolomorphicForms X 1) :
    ∃! L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧, IsWedgeThetaHom X θ L := by
  obtain ⟨L, hL⟩ := spec_exists_isWedgeThetaHom X θ hθ
  exact ⟨L, hL, fun L' hL' => spec_isWedgeThetaHom_unique X θ L' L hL' hL⟩

/-- **`L_0 = 0`.** The zero morphism is the wedge with the zero form: `0(x) ∧ − = 0`.
Source: Mathlib's `ContinuousAlternatingMap.alternatizeUncurryFin` (linear in its argument);
`globalOneFormCovector` and `formStalkValue` are additive. -/
theorem spec_isWedgeThetaHom_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    IsWedgeThetaHom X 0 0 :=
  spec_isWedgeThetaHom_zero_aux X

/-- With uniqueness, the wedge with the zero form is the zero morphism. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X 0 L) : L = 0 :=
  spec_isWedgeThetaHom_unique X 0 L 0 hL (spec_isWedgeThetaHom_zero X)

/-- **`L_θ` is additive in `θ`.** `(θ + θ')(x) ∧ − = θ(x) ∧ − + θ'(x) ∧ −`, and values of
sections are additive.
Source: Mathlib's `ContinuousAlternatingMap.alternatizeUncurryFin_add`; additivity of
`globalOneFormCovector` and `formStalkValue`. -/
theorem spec_isWedgeThetaHom_add (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ θ' : GlobalHolomorphicForm X 1) (L L' : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (hL : IsWedgeThetaHom X θ L) (hL' : IsWedgeThetaHom X θ' L') :
    IsWedgeThetaHom X (θ + θ') (L + L') :=
  spec_isWedgeThetaHom_add_aux X θ θ' L L' hL hL'

/-- With uniqueness: `L_{θ + θ'} = L_θ + L_{θ'}`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ θ' : GlobalHolomorphicForm X 1) (L L' M : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (hL : IsWedgeThetaHom X θ L) (hL' : IsWedgeThetaHom X θ' L')
    (hM : IsWedgeThetaHom X (θ + θ') M) : M = L + L' :=
  spec_isWedgeThetaHom_unique X _ M _ hM (spec_isWedgeThetaHom_add X θ θ' L L' hL hL')

/-- **`L` restricts to `F^q Ω• ⟶ F^{q+1} Ω•[1]`.** Every morphism of complexes
`L : Ω•(X) ⟶ Ω•(X)[1]` factors on `F^q Ω•` through `(F^{q+1} Ω•)[1]`: `F^•` is the stupid
filtration (`hodgeFilteredDeRhamComplex` is `stupidTrunc` at `≥ q`), the inclusion
`(F^{q+1} Ω•)[1] ⟶ Ω•[1]` is an isomorphism in degrees `≥ q`, and `F^q Ω•` is zero below `q`.
So the filtration statement needs nothing about `θ`; for `L_θ` it is `θ ∧ F^q ⊆ F^{q+1}`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.4 (the stupid
filtration); Mathlib's `HomologicalComplex.stupidTrunc`, upstream `hodgeFilteredDeRhamInclusion`. -/
theorem spec_exists_hodgeFiltered_comp_inclusion (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (q : ℤ) :
    ∃ L' : F^q Ω•(X) ⟶ (F^(q + 1) Ω•(X))⟦(1 : ℤ)⟧,
      L' ≫ (hodgeFilteredDeRhamInclusion X (q + 1))⟦(1 : ℤ)⟧' =
        hodgeFilteredDeRhamInclusion X q ≫ L :=
  spec_exists_hodgeFiltered_comp_inclusion_aux X L q

/-- For `L_θ`: the wedge with a closed form restricts to the filtered complexes. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1) (hθ : θ ∈ closedGlobalHolomorphicForms X 1) (q : ℤ) :
    ∃ (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (L' : F^q Ω•(X) ⟶ (F^(q + 1) Ω•(X))⟦(1 : ℤ)⟧),
      IsWedgeThetaHom X θ L ∧
        L' ≫ (hodgeFilteredDeRhamInclusion X (q + 1))⟦(1 : ℤ)⟧' =
          hodgeFilteredDeRhamInclusion X q ≫ L := by
  obtain ⟨L, hL⟩ := spec_exists_isWedgeThetaHom X θ hθ
  obtain ⟨L', hL'⟩ := spec_exists_hodgeFiltered_comp_inclusion X L q
  exact ⟨L, L', hL, hL'⟩

/-- **The shift map is bijective.** `hypercohomologyShift X K k` is composition with an
isomorphism of the derived category (the identity of `K[1]` read as a degree-one shifted
morphism), so it is the shift isomorphism `ℍ^k(K[1]) ≅ ℍ^{k+1}(K)`. This rules out a vacuous
shift: the filtration statement below would be trivial for the zero map.
Source: Kashiwara–Schapira, *Sheaves on Manifolds*, Grundlehren 292, §1.3; Mathlib's
`Localization.SmallShiftedHom.equiv` and `shiftFunctorAdd'`. -/
theorem spec_hypercohomologyShift_bijective (X : Over (Spec ↧ℂ))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (k : ℤ) :
    Function.Bijective (hypercohomologyShift X K k) :=
  spec_hypercohomologyShift_bijective_aux X K k

/-- The shift map is injective, so a nonzero class stays nonzero. -/
example (X : Over (Spec ↧ℂ)) (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (k : ℤ)
    (x : ℍ^k(X; K⟦(1 : ℤ)⟧)) (hx : x ≠ 0) : hypercohomologyShift X K k x ≠ 0 := fun h =>
  hx ((spec_hypercohomologyShift_bijective X K k).1 (h.trans (map_zero _).symm))

/-- **The shift map is natural.** For `f : K ⟶ K'`, shifting after `ℍ(f[1])` is `ℍ(f)` after
shifting: both are composition with `f[1]` in the derived category.
Source: Mathlib's `ShiftedHom.comp`, `Functor.commShiftIso` of `DerivedCategory.Q`; upstream
`hypercohomologyAddEquivGlobalSectionsKInjective_shifted_naturality`. -/
theorem spec_hypercohomologyShift_hypercohomologyMap (X : Over (Spec ↧ℂ))
    {K K' : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ K') (k : ℤ)
    (x : ℍ^k(X; K⟦(1 : ℤ)⟧)) :
    hypercohomologyShift X K' k (hypercohomologyMap X (f⟦(1 : ℤ)⟧') k x) =
      hypercohomologyMap X f (k + 1) (hypercohomologyShift X K k x) :=
  spec_hypercohomologyShift_hypercohomologyMap_aux X f k x

example (X : Over (Spec ↧ℂ)) {K K' : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ K')
    (k : ℤ) (x : ℍ^k(X; K⟦(1 : ℤ)⟧))
    (hx : hypercohomologyMap X (f⟦(1 : ℤ)⟧') k x = 0) :
    hypercohomologyMap X f (k + 1) (hypercohomologyShift X K k x) = 0 := by
  rw [← spec_hypercohomologyShift_hypercohomologyMap, hx, map_zero]

/-- **The induced degree-one map is composition with `L`.** For `L : K ⟶ K'[1]`, shifting after
`ℍ(L)` is composition with `L` read as a degree-one shifted morphism `K ⟶ K'`. This is the form
in which the comparison with the singular cup (stages 4–6) will use `L_θ`.
Source: Mathlib's `Localization.SmallShiftedHom.comp_assoc` and `ShiftedHom.mk₀_comp`. -/
theorem spec_hypercohomologyShift_hypercohomologyMap_eq_comp (X : Over (Spec ↧ℂ))
    {K K' : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (L : K ⟶ K'⟦(1 : ℤ)⟧) (k : ℤ)
    (α : ℍ^k(X; K)) :
    hypercohomologyShift X K' k (hypercohomologyMap X L k α) =
      α.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom K K' (1 : ℤ) from L)) (add_comm 1 k) :=
  spec_hypercohomologyShift_hypercohomologyMap_eq_comp_aux X L k α

/-- The induced map is additive in `α`. -/
example (X : Over (Spec ↧ℂ)) {K K' : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (L : K ⟶ K'⟦(1 : ℤ)⟧) (k : ℤ) (α β : ℍ^k(X; K)) :
    (α + β).comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom K K' (1 : ℤ) from L)) (add_comm 1 k) =
      hypercohomologyShift X K' k (hypercohomologyMap X L k α) +
        hypercohomologyShift X K' k (hypercohomologyMap X L k β) := by
  rw [← map_add, ← map_add, spec_hypercohomologyShift_hypercohomologyMap_eq_comp]

/-- **Stage 3: `L` maps `F^q H^k_dR` into `F^{q+1} H^{k+1}_dR`.** For every morphism of complexes
`L : Ω•(X) ⟶ Ω•(X)[1]`, in particular `L_θ`, the map `H^k_dR(X) → H^{k+1}_dR(X)` given by
`hypercohomologyMap L` followed by the shift sends `F^q H^k_dR(X)` into `F^{q+1} H^{k+1}_dR(X)`.
Write `α` as the image of `β ∈ ℍ^k(F^q Ω•)`; `L ∘ ι_q = ι_{q+1}[1] ∘ L'`
(`spec_exists_hodgeFiltered_comp_inclusion`), and the shift commutes with `ℍ(ι_{q+1}[1])`
(`spec_hypercohomologyShift_hypercohomologyMap`), so the image is `ℍ(ι_{q+1})` of
`shift(ℍ(L') β)`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.4; upstream
`hypercohomologyMap_comp_apply`; the two statements named. -/
theorem spec_hypercohomologyShift_mem_hodgeFiltration (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (q k : ℤ) (α : H_dR^k(X))
    (hα : α ∈ F^q H_dR^k(X)) :
    hypercohomologyShift X Ω•(X) k (hypercohomologyMap X L k α) ∈ F^(q + 1) H_dR^(k + 1)(X) :=
  spec_hypercohomologyShift_mem_hodgeFiltration_aux X L q k α hα

/-- For `L_θ` with `θ` closed: the wedge with `θ` raises the Hodge filtration by one. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1) (hθ : θ ∈ closedGlobalHolomorphicForms X 1) :
    ∃ L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧, IsWedgeThetaHom X θ L ∧
      ∀ (q k : ℤ) (α : H_dR^k(X)), α ∈ F^q H_dR^k(X) →
        hypercohomologyShift X Ω•(X) k (hypercohomologyMap X L k α) ∈
          F^(q + 1) H_dR^(k + 1)(X) := by
  obtain ⟨L, hL⟩ := spec_exists_isWedgeThetaHom X θ hθ
  exact ⟨L, hL, fun q k α hα => spec_hypercohomologyShift_mem_hodgeFiltration X L q k α hα⟩

end HodgeLean.Adapters
