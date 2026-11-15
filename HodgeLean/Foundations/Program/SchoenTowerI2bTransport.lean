import HodgeLean.Foundations.Program.SchoenTowerInertiaSuppliers
import HodgeLean.Foundations.Program.SchoenTowerFibreDefs

/-! Retained normalization and exceptional-preimage transport.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every point of the reduced strict transform maps into the original divisor.
Source: Hartshorne, Algebraic Geometry, II.7, definition of strict transform. -/
theorem s2v_strictTransform_support_maps_into {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) {x : X}
    (hx : x ∈ (s2c_strictTransform f D K).support) : f x ∈ D.support := by
  have he : ((s2c_strictTransform f D K).support : Set X) =
      closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))) := by
    simp only [s2c_strictTransform, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  change x ∈ ((s2c_strictTransform f D K).support : Set X) at hx
  rw [he] at hx
  exact (closure_minimal (fun _ h => h.1)
    (D.support.isClosed.preimage f.continuous)) hx

/-- Strict-transform support at any tower stage maps into the original divisor.
Source: Hartshorne, Algebraic Geometry, II.7, successive strict transforms. -/
theorem s2v_tower_strictTransform_support {r : ℕ}
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, (B i).left.IdealSheafData)
    (K : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hD : ∀ i : Fin r, D i.succ = s2c_strictTransform (b i).left (D i.castSucc) (K i))
    (i : Fin (r + 1)) (x : (B i).left) (hx : x ∈ (D i).support) :
    (s2v_towerToInitial B b i).left x ∈ (D 0).support := by
  induction i using Fin.induction with
  | zero => exact hx
  | succ i ih =>
    change (s2v_towerToInitial B b i.castSucc).left ((b i).left x) ∈ (D 0).support
    apply ih
    rw [hD i] at hx
    exact s2v_strictTransform_support_maps_into (b i).left (D i.castSucc) (K i) hx

/-- The retained generic transition equation forces the normalization square over the base.
Source: Stacks Project, tag 035H; uniqueness on a dense source into a separated scheme. -/
theorem s2v_normalization_transition_base {T : Scheme} [IsReduced T]
    {B' B : Over (Spec ↧ℂ)} [IsSeparated B.hom]
    (b : B' ⟶ B) (η' : T ⟶ B'.left) (η : T ⟶ B.left)
    [QuasiCompact η'] [QuasiSeparated η'] [QuasiCompact η] [QuasiSeparated η]
    (hη : η' ≫ b.left = η)
    (w : s2b_normalizationOver B' η' ⟶ s2b_normalizationOver B η)
    (hw : η'.toNormalization ≫ w.left = η.toNormalization) :
    w ≫ s2b_normalizationMap B η = s2b_normalizationMap B' η' ≫ b := by
  apply Over.OverMorphism.ext
  haveI : IsReduced (s2b_normalizationOver B' η').left :=
    inferInstanceAs (IsReduced η'.normalization)
  apply ext_of_isDominant_of_isSeparated B.hom
    (by simp only [← Over.comp_left, Over.w]) η'.toNormalization
  change η'.toNormalization ≫ w.left ≫ η.fromNormalization =
    η'.toNormalization ≫ η'.fromNormalization ≫ b.left
  rw [← Category.assoc, hw, Scheme.Hom.toNormalization_fromNormalization,
    ← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hη]

/-- Every deck iterate retains its exceptional coordinate and acts on its covering coordinate.
Source: Schoen (1988), §2, p. 18, the exceptional-preimage pullback square. -/
theorem s2v_preimageDeck_iterate_projections {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β)
    (n : ℕ) (x : ComplexPoint (s2b_preimage β j)) :
    Point.map (s2b_toCover β j) ((Point.map (s2b_preimageDeck β j d hd))^[n] x) =
      (Point.map d)^[n] (Point.map (s2b_toCover β j) x) ∧
    Point.map (s2b_toExceptional β j) ((Point.map (s2b_preimageDeck β j d hd))^[n] x) =
      Point.map (s2b_toExceptional β j) x := by
  have hc : Function.Semiconj (Point.map (s2b_toCover β j))
      (Point.map (s2b_preimageDeck β j d hd)) (Point.map d) := by
    intro z
    change (z ≫ s2b_preimageDeck β j d hd) ≫ s2b_toCover β j =
      (z ≫ s2b_toCover β j) ≫ d
    simp only [Category.assoc, s2b_preimageDeck, s2b_toCover, pullback.lift_fst]
  have he : Function.Semiconj (Point.map (s2b_toExceptional β j))
      (Point.map (s2b_preimageDeck β j d hd)) id := by
    intro z
    change (z ≫ s2b_preimageDeck β j d hd) ≫ s2b_toExceptional β j =
      z ≫ s2b_toExceptional β j
    simp only [Category.assoc, s2b_preimageDeck, s2b_toExceptional, pullback.lift_snd]
  exact ⟨hc.iterate_right n x, by simpa only [Function.iterate_id, id_eq] using he.iterate_right n x⟩

/-- Fixing an exceptional-preimage point is equivalent to fixing its covering coordinate.
Source: Schoen (1988), §2, p. 18, the exceptional-preimage pullback square. -/
theorem s2v_preimageDeck_iterate_fixed_iff {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β)
    (n : ℕ) (x : ComplexPoint (s2b_preimage β j)) :
    (Point.map (s2b_preimageDeck β j d hd))^[n] x = x ↔
      (Point.map d)^[n] (Point.map (s2b_toCover β j) x) =
        Point.map (s2b_toCover β j) x := by
  obtain ⟨hc, he⟩ := s2v_preimageDeck_iterate_projections β j d hd n x
  constructor
  · intro hx
    rw [hx] at hc
    exact hc.symm
  · intro hx
    apply pullback.hom_ext
    · exact hc.trans hx
    · exact he

/-- A point of the actual covering fibre is fixed exactly when its covering-scheme coordinate is fixed.
Source: Schoen (1988), §2, p. 18, the iterated exceptional-preimage pullback. -/
theorem s2v_coveringFibreDeck_iterate_fixed_iff {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K)
    (d : W ⟶ W) (hd : d ≫ β = β) (k : ComplexPoint K)
    (n : ℕ) (x : ComplexPoint (s2b_coveringFibre β j p k)) :
    (Point.map (s2c_coveringFibreDeck β j p d hd k))^[n] x = x ↔
      (Point.map d)^[n]
        (Point.map (pullback.fst (s2b_toExceptional β j ≫ p) k ≫ s2b_toCover β j) x) =
        Point.map (pullback.fst (s2b_toExceptional β j ≫ p) k ≫ s2b_toCover β j) x := by
  have h₁ := s2v_preimageDeck_iterate_fixed_iff (s2b_toExceptional β j ≫ p) k
    (s2b_preimageDeck β j d hd) (s2b_check_deck_base β j p d hd) n x
  have h₂ := s2v_preimageDeck_iterate_fixed_iff β j d hd n
    (Point.map (pullback.fst (s2b_toExceptional β j ≫ p) k) x)
  have he : s2b_preimageDeck (s2b_toExceptional β j ≫ p) k
      (s2b_preimageDeck β j d hd) (s2b_check_deck_base β j p d hd) =
      s2c_coveringFibreDeck β j p d hd k := by
    apply pullback.hom_ext <;>
      simp only [s2b_preimageDeck, s2c_coveringFibreDeck, s2b_toCover, s2b_toExceptional,
        pullback.lift_fst, pullback.lift_snd]
  rw [he] at h₁
  simpa only [Point.map, Category.assoc] using h₁.trans h₂

/-- The retained normalized tower maps to the original covering square.
Source: Schoen (1988), §2, p. 15, normalization in the original covering function field. -/
theorem s2v_normalization_tower_original_square {T : Scheme} [IsReduced T]
    {r : ℕ} (B : Fin (r + 1) → Over (Spec ↧ℂ)) [∀ i, IsSeparated (B i).hom]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (η : ∀ i, T ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (W₀ B₀ : Over (Spec ↧ℂ)) (β₀ : W₀ ⟶ B₀)
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀) (e₀ : B 0 ≅ B₀)
    (heW : eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom)
    (i : Fin (r + 1)) :
    (s2v_towerToInitial (fun i => s2b_normalizationOver (B i) (η i)) w i ≫ eW.hom) ≫ β₀ =
      s2b_normalizationMap (B i) (η i) ≫ (s2v_towerToInitial B b i ≫ e₀.hom) := by
  have hs := s2v_towerToInitial_naturality
    (fun i => s2b_normalizationOver (B i) (η i)) B w b
    (fun i => s2b_normalizationMap (B i) (η i))
    (fun i => s2v_normalization_transition_base (b i) (η i.succ) (η i.castSucc)
      (hη i) (w i) (hw i)) i
  rw [Category.assoc, heW, ← Category.assoc, hs, Category.assoc]

/-- An exceptional-preimage point over a centre point maps to that point in the preceding base.
Source: Schoen (1988), §2, p. 18, the two retained pullback squares. -/
theorem s2v_exceptionalPreimage_point_base {W' W B' B K : Over (Spec ↧ℂ)}
    (β' : W' ⟶ B') (β : W ⟶ B) (b : B' ⟶ B) (kι : K ⟶ B)
    (w : W' ⟶ W) (hw : w ≫ β = β' ≫ b)
    (k : ComplexPoint K)
    (x : ComplexPoint (s2b_preimage β' (pullback.fst b kι)))
    (hx : Point.map (s2b_toExceptional β' (pullback.fst b kι) ≫ pullback.snd b kι) x = k) :
    Point.map (s2b_toCover β' (pullback.fst b kι) ≫ w ≫ β) x = Point.map kι k := by
  have hs : s2b_toCover β' (pullback.fst b kι) ≫ w ≫ β =
      (s2b_toExceptional β' (pullback.fst b kι) ≫ pullback.snd b kι) ≫ kι := by
    change pullback.fst β' (pullback.fst b kι) ≫ w ≫ β =
      (pullback.snd β' (pullback.fst b kι) ≫ pullback.snd b kι) ≫ kι
    rw [hw, ← Category.assoc, pullback.condition, Category.assoc, pullback.condition,
      ← Category.assoc]
  change x ≫ (s2b_toCover β' (pullback.fst b kι) ≫ w ≫ β) = k ≫ kι
  rw [hs, ← Category.assoc]
  exact congrArg (fun z : ComplexPoint K => z ≫ kι) hx

/-- An actual exceptional-preimage point over strict-transform support maps to the original branch support.
Source: Schoen (1988), §2, pp. 14–18, the retained base and normalization towers. -/
theorem s2v_exceptionalPreimage_original_support {T : Scheme} [IsReduced T]
    {r : ℕ} (B : Fin (r + 1) → Over (Spec ↧ℂ)) [∀ i, IsSeparated (B i).hom]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (η : ∀ i, T ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (W₀ B₀ : Over (Spec ↧ℂ)) (β₀ : W₀ ⟶ B₀)
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀) (e₀ : B 0 ≅ B₀)
    (heW : eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom)
    (D : ∀ i, (B i).left.IdealSheafData)
    (K : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hD : ∀ i : Fin r, D i.succ = s2c_strictTransform (b i).left (D i.castSucc) (K i))
    (D₀ : B₀.left.IdealSheafData) (hD₀ : D 0 = D₀.comap e₀.hom.left)
    (i : Fin r) (k : ComplexPoint (s2c_subscheme (B i.castSucc) (K i)))
    (hk : (Point.map (s2c_subschemeι (B i.castSucc) (K i)) k).left
      (IsLocalRing.closedPoint ℂ) ∈ (D i.castSucc).support)
    (x : ComplexPoint (s2b_preimage (s2b_normalizationMap (B i.succ) (η i.succ))
      (pullback.fst (b i) (s2c_subschemeι (B i.castSucc) (K i)))))
    (hx : Point.map (s2b_toExceptional (s2b_normalizationMap (B i.succ) (η i.succ))
      (pullback.fst (b i) (s2c_subschemeι (B i.castSucc) (K i))) ≫
      pullback.snd (b i) (s2c_subschemeι (B i.castSucc) (K i))) x = k) :
    (Point.map (s2b_toCover (s2b_normalizationMap (B i.succ) (η i.succ))
      (pullback.fst (b i) (s2c_subschemeι (B i.castSucc) (K i))) ≫ w i ≫
      s2v_towerToInitial (fun j => s2b_normalizationOver (B j) (η j)) w i.castSucc ≫
      eW.hom ≫ β₀) x).left (IsLocalRing.closedPoint ℂ) ∈ D₀.support := by
  let β := fun j => s2b_normalizationMap (B j) (η j)
  let kι := s2c_subschemeι (B i.castSucc) (K i)
  let j := pullback.fst (b i) kι
  have hb := s2v_normalization_transition_base (b i) (η i.succ) (η i.castSucc)
    (hη i) (w i) (hw i)
  have hp := s2v_exceptionalPreimage_point_base (β i.succ) (β i.castSucc) (b i) kι
    (w i) hb k x hx
  have hs := s2v_tower_strictTransform_support B b D K hD i.castSucc
    ((Point.map kι k).left (IsLocalRing.closedPoint ℂ)) hk
  rw [hD₀, Scheme.IdealSheafData.support_comap] at hs
  have hn := s2v_normalization_tower_original_square B b η hη w hw W₀ B₀ β₀ eW e₀ heW i.castSucc
  have he : Point.map (s2b_toCover (β i.succ) j ≫ w i ≫
      s2v_towerToInitial (fun j => s2b_normalizationOver (B j) (η j)) w i.castSucc ≫
      eW.hom ≫ β₀) x = Point.map (s2v_towerToInitial B b i.castSucc ≫ e₀.hom)
      (Point.map kι k) := by
    change x ≫ s2b_toCover (β i.succ) j ≫ w i ≫
      s2v_towerToInitial (fun j => s2b_normalizationOver (B j) (η j)) w i.castSucc ≫
      eW.hom ≫ β₀ = _
    rw [← Category.assoc _ eW.hom β₀, hn]
    simpa only [Point.map, Category.assoc] using congrArg
      (fun z : ComplexPoint (B i.castSucc) =>
        Point.map (s2v_towerToInitial B b i.castSucc ≫ e₀.hom) z) hp
  rw [he]
  exact hs

end HodgeLean.Foundations.Program
