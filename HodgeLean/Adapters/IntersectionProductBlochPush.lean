import HodgeLean.Adapters.IntersectionProductBlochHomotopy
import HodgeLean.Foundations.ChowCorrespondencePushforward

/-! # Proper pushforward and the boundary of chains on `X × ℙ¹`

Stage A3.3, the fourth input of Bloch's homotopy, for proper pushforward. Bloch's homotopy pushes a
member `Y ⊆ X × ℙ¹_t` forward along `π × id` before translating; the faces `t = a` of the result
are the push-forwards of the faces of `Y`. This file proves it:
* Fulton's Proposition 1.4 (b) with the norm made explicit (`a3h_pushforward_principal_norm`): for
  a proper dominant `h : W → V` of integral schemes of finite type over `ℂ` of the same dimension,
  `h_*[div φ] = [div N(φ)]`, `N` the norm of `K(W)/K(V)`; the proof is that of
  `a2r_pushforward_principal_of_height_eq`, which states only the existence of such a function;
* the degree at the generic point is `[K(W) : K(V)]` (`a3h_degree_genericPoint`), and
  `[div φ^d] = d [div φ]` (`a3h_principalDivisor_pow`);
* for proper `g : X' → X` and `Y ⊆ X' × ℙ¹` dominating `ℙ¹`,
  `(g × id)_*[div (t|_Y)] = deg · [div (t|_{(g × id)(Y)})]` (`a3h_push_cyc`), since `t|_Y` is pulled
  back from the image (`a3h_pullbackFF_comp`) and so has norm `t^deg`;
* hence `g_* (∂ Z) = ∂ ((g × id)_* Z)` for every chain `Z` on `X' × ℙ¹` (`a3h_push_bd`).

Source: Fulton, *Intersection Theory*, second edition, Proposition 1.4 and §1.6; S. Bloch, *The
moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §2.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open HodgeLean.Foundations.Curves Order AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations
open scoped MonoidalCategory

namespace HodgeLean.Adapters

section fultonNorm

variable {W V : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsIntegral W.left] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsIntegral V.left]
  (h : W ⟶ V) [IsProper h.left] (hdom : h.left (genericPoint W.left) = genericPoint V.left)

include hdom in
/-- **Proper pushforward of a principal cycle, with the norm.** For a proper dominant `h` between
integral schemes of finite type over `ℂ` of the same dimension, `h_*[div φ] = [div N(φ)]`, with
`N` the norm of `K(W) / K(V)`.
Source: Fulton, *Intersection Theory*, second edition, Proposition 1.4 (b). -/
theorem a3h_pushforward_principal_norm
    (hdim : height (genericPoint V.left) = height (genericPoint W.left))
    {φ : W.left.functionField} (hφ : φ ≠ 0) :
    letI := (a2r_ffHom h.left hdom).toAlgebra
    a1p_pushforward h.left (principalDivisor W.left φ : AlgebraicCycle W.left ℤ) =
      (principalDivisor V.left (Algebra.norm V.left.functionField φ) :
        AlgebraicCycle V.left ℤ) := by
  classical
  let := (a2r_ffHom h.left hdom).toAlgebra
  let := (a2r_ffC V).toAlgebra
  let := (a2r_ffC W).toAlgebra
  have : IsScalarTower ℂ V.left.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (a2r_ffHom_ffC h hdom c).symm
  obtain ⟨hessW, nW, hnW, htrW⟩ := a2r_ff_trdeg W
  obtain ⟨-, nV, hnV, htrV⟩ := a2r_ff_trdeg V
  have hnn : nV = nW := by
    rw [hnV, hnW] at hdim
    exact_mod_cast hdim
  have : FiniteDimensional V.left.functionField W.left.functionField :=
    a2r_finiteDimensional_of_trdeg (n := nW) (hnn ▸ htrV) htrW
  have : CharZero V.left.functionField :=
    charZero_of_injective_algebraMap (algebraMap ℂ V.left.functionField).injective
  set ψ := Algebra.norm V.left.functionField φ
  have hψ : ψ ≠ 0 := Algebra.norm_ne_zero_iff.mpr hφ
  ext y
  rw [a2r_principalDivisor_apply V.left ψ y]
  by_cases hy1 : coheight y = 1
  · have hyh : height y + 1 = height (genericPoint W.left) := by
      rw [← hdim, ← hy1]
      exact a2r_height_add_coheight V y
    have hfib := a2r_fibre_coheight h y hyh
    let := (a2r_stalkHom h.left hdom y).toAlgebra
    have : IsScalarTower (V.left.presheaf.stalk y) V.left.functionField
        W.left.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨hfinK, hordK⟩ := a2r_ord_eq_finsum (W := V) hy1 hψ
    have hDVR := a2r_isDVR_of_mem_Dom_stalk (W := V) hy1
    have hfinL : ∀ u ∈ a2r_Dom (V.left.presheaf.stalk y) V.left.functionField,
        (a2r_Dom u W.left.functionField).Finite := fun u hu =>
      have := hDVR u hu
      (a2r_vord_norm_eq_finsum V.left.functionField W.left.functionField u).1
    have hDomV : (a2r_DomV h.left hdom y).Finite := by
      refine (hfinK.biUnion hfinL).subset fun v hv => ?_
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨_, a2r_comap_mem_Dom v hv,
        (a2r_mem_Dom_tower_iff _ (a2r_comap_mem_Dom v hv) v).mpr ⟨hv, rfl⟩⟩
    rw [a2r_pushforward_principal_apply h hdom y hφ hfib (hDomV.subset Set.inter_subset_left)]
    change ∑ᶠ v ∈ a2r_Dom (V.left.presheaf.stalk y) W.left.functionField,
      a2r_vord v φ * (a2r_resDeg (V.left.presheaf.stalk y) v : ℤ) = _
    rw [a2r_finsum_tower _ hfinK hfinL, hordK]
    refine finsum_mem_congr rfl fun u hu => ?_
    have := hDVR u hu
    rw [(a2r_vord_norm_eq_finsum V.left.functionField W.left.functionField u).2 φ hφ, mul_comm,
      mul_finsum_mem' _ _ (hfinL u hu)]
    refine finsum_mem_congr rfl fun v hv => ?_
    rw [a2r_resDeg_tower u hu v hv]
    push_cast
    ring
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hy1]
    by_contra hne
    have hyW := a2r_height_of_pushforward_principal_ne_zero h φ y hne
    obtain ⟨a, b, n, ha, hb, hn, hab⟩ := a2r_height_add_coheight_nat (W := V) y
    rw [ha, ← hdim, hn] at hyW
    have : a + 1 = n := by exact_mod_cast hyW
    apply hy1
    rw [hb]
    have : b = 1 := by omega
    rw [this]
    rfl


end fultonNorm

/-! ## The degree at the generic point and powers of a function -/

section degree

variable {W V : Scheme.{0}} [IsIntegral W] [IsIntegral V] (h : W ⟶ V)
  (hdom : h (genericPoint W) = genericPoint V)

/-- The residue map at the generic point of an integral scheme is an isomorphism. -/
def a3h_residueGen (X : Scheme.{0}) [IsIntegral X] (x : X) (hx : x = genericPoint X) :
    X.presheaf.stalk x ≃+* X.residueField x := by
  refine RingEquiv.ofBijective (X.residue x).hom ⟨?_, X.residue_surjective x⟩
  subst hx
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hm : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (genericPoint X)) :=
    (IsLocalRing.residue_eq_zero_iff a).1 ha
  by_contra h0
  have hu : IsUnit (a : X.functionField) := isUnit_iff_ne_zero.2 h0
  exact (IsLocalRing.mem_maximalIdeal _).1 hm hu

include hdom in
/-- At the generic point the degree of `h` is `[K(W) : K(V)]`.
Source: Fulton, *Intersection Theory*, second edition, §1.4, definition of `deg(W/V)`. -/
theorem a3h_degree_genericPoint :
    letI := (a2r_ffHom h hdom).toAlgebra
    a1p_degree h (genericPoint W) = Module.finrank V.functionField W.functionField := by
  letI := (a2r_ffHom h hdom).toAlgebra
  let e : Inseparable (genericPoint V) (h (genericPoint W)) := by rw [hdom]
  let i : V.functionField ≃+* V.residueField (h (genericPoint W)) :=
    ((V.presheaf.stalkCongr e).commRingCatIsoToRingEquiv).trans
      (a3h_residueGen V (h (genericPoint W)) hdom)
  let j : W.functionField ≃+* W.residueField (genericPoint W) :=
    a3h_residueGen W (genericPoint W) rfl
  letI := (h.residueFieldMap (genericPoint W)).hom.toAlgebra
  refine (Algebra.finrank_eq_of_equiv_equiv i j ?_).symm
  ext a
  change h.residueFieldMap (genericPoint W) (V.residue (h (genericPoint W))
    (V.presheaf.stalkSpecializes e.ge a)) = W.residue (genericPoint W) (a2r_ffHom h hdom a)
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]
  rfl

/-- The order of a power. -/
theorem a3h_ord_pow (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    {φ : X.functionField} (hφ : φ ≠ 0) (z : X) (d : ℕ) :
    X.ord (φ ^ d) z = d * X.ord φ z := by
  induction d with
  | zero =>
    have h := Scheme.ord_mul (x := z) (f := (1 : X.functionField)) (g := 1) one_ne_zero
      one_ne_zero
    rw [mul_one] at h
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    omega
  | succ d ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero d hφ) hφ, ih]
    push_cast
    ring

/-- `[div φ^d] = d [div φ]`. -/
theorem a3h_principalDivisor_pow (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [TopologicalSpace.NoetherianSpace X] {φ : X.functionField} (hφ : φ ≠ 0) (d : ℕ) :
    (principalDivisor X (φ ^ d) : AlgebraicCycle X ℤ) =
      (principalDivisor X φ : AlgebraicCycle X ℤ).mapRange ((d : ℤ) * ·) (mul_zero _) := by
  ext z
  rw [Function.locallyFinsuppWithin.mapRange_apply, a2r_principalDivisor_apply,
    a2r_principalDivisor_apply, a3h_ord_pow X hφ z d]

end degree

/-! ## Pulling back rational functions along a dominant restriction -/

section pullbackFF

variable {Z' Z C : Scheme.{0}} [IsIntegral Z'] [IsIntegral Z] [IsIntegral C]

theorem a3h_pullbackFF_congr {f f' : Z ⟶ C} (hff : f = f') (hf : f (genericPoint Z) = genericPoint C)
    (hf' : f' (genericPoint Z) = genericPoint C) (t : C.functionField) :
    a3m_pullbackFF f hf t = a3m_pullbackFF f' hf' t := by
  subst hff
  rfl

/-- Pulling back along `k ≫ h` is pulling back along `h`, then along `k`. -/
theorem a3h_pullbackFF_comp (k : Z' ⟶ Z) (h : Z ⟶ C) (hk : k (genericPoint Z') = genericPoint Z)
    (hh : h (genericPoint Z) = genericPoint C)
    (hkh : (k ≫ h) (genericPoint Z') = genericPoint C) (t : C.functionField) :
    a3m_pullbackFF (k ≫ h) hkh t = a2r_ffHom k hk (a3m_pullbackFF h hh t) := by
  have s2 : k (genericPoint Z') ⤳ genericPoint Z := by rw [hk]
  unfold a3m_pullbackFF a2r_ffHom
  rw [Scheme.Hom.stalkMap_comp]
  change k.stalkMap _ (h.stalkMap _ _) =
    k.stalkMap _ (Z.presheaf.stalkSpecializes _ (h.stalkMap _ _))
  congr 1
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply h (k (genericPoint Z')) (genericPoint Z) s2,
    TopCat.Presheaf.stalkSpecializes_comp_apply]
  rfl

end pullbackFF

/-! ## The pushforward of `[div t|_Y]` along `g × id` -/

section push

variable {X' X : Over (Spec ↧ℂ)} (g : X' ⟶ X)

/-- `g × id : X' × ℙ¹ → X × ℙ¹`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (fibred products). -/
abbrev a3h_G : a3n_T X' ⟶ a3n_T X := g ▷ a3n_P1

instance a3h_G_proper [IsProper g.left] : IsProper (a3h_G g).left := by
  rw [Over.whiskerRight_left]
  exact MorphismProperty.pullbackMap (P := @IsProper) (inferInstance : IsProper g.left)
    (inferInstance : IsProper (𝟙 a3n_P1.left)) (Over.w g).symm (Category.id_comp _).symm

theorem a3h_G_p : (a3h_G g).left ≫ a3n_p X = a3n_p X' := by
  rw [Over.whiskerRight_left]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem a3h_G_q : (a3h_G g).left ≫ (a3n_q X).left = (a3n_q X').left ≫ g.left := by
  rw [Over.whiskerRight_left]
  exact pullback.lift_fst _ _ _

theorem a3h_G_h : (a3h_G g).left ≫ a3n_h X = a3n_h X' := by
  rw [← Category.assoc, a3h_G_p]

theorem a3h_G_h_apply (τ : (a3n_T X').left) : a3n_h X ((a3h_G g).left τ) = a3n_h X' τ := by
  rw [← Scheme.Hom.comp_apply, a3h_G_h]

variable [IsProper X'.hom] [IsProper X.hom] [IsProper g.left]

/-- **Pushforward of the divisor of `t`.** For `Y = closure {y} ⊆ X' × ℙ¹` dominating `ℙ¹`,
`(g × id)_*[div (t|_Y)] = deg (Y / (g × id)(Y)) [div (t|_{(g × id)(Y)})]`: by Fulton's
Proposition 1.4, the pushforward is the divisor of the norm of `t|_Y`, which is pulled back from
`(g × id)(Y)`, so its norm is the power `deg`; when the dimension drops both sides vanish.
Source: Fulton, *Intersection Theory*, second edition, Proposition 1.4. -/
theorem a3h_push_cyc (y : (a3n_T X').left) (hy : a3n_h X' y = genericPoint (g3c_P 1))
    (hGy : a3n_h X ((a3h_G g).left y) = genericPoint (g3c_P 1)) :
    a1p_pushforward (a3h_G g).left (a3o_cyc X' y hy) =
      a3m_smul (a1p_degree (a3h_G g).left y) (a3o_cyc X ((a3h_G g).left y) hGy) := by
  classical
  set y₀ := (a3h_G g).left y
  obtain ⟨h, hcomm⟩ := a2r_exists_restrict (a3h_G g) y
  have : IsProper (cycleComponentι (a3n_T X').left y ≫ (a3h_G g).left) := inferInstance
  have : IsProper (h.left ≫ cycleComponentι (a3n_T X).left y₀) := hcomm ▸ this
  have : IsProper h.left := IsProper.of_comp h.left (cycleComponentι (a3n_T X).left y₀)
  have hdom : h.left (genericPoint (a2r_component (a3n_T X') y).left) =
      genericPoint (a2r_component (a3n_T X) y₀).left := by
    apply (cycleComponentι (a3n_T X).left y₀).isEmbedding.injective
    change (h.left ≫ cycleComponentι (a3n_T X).left y₀) _ = _
    rw [hcomm, Scheme.Hom.comp_apply]
    change (a3h_G g).left (cycleComponentι (a3n_T X').left y
      (genericPoint (cycleComponent (a3n_T X').left y))) =
      cycleComponentι (a3n_T X).left y₀ (genericPoint (cycleComponent (a3n_T X).left y₀))
    rw [a2r_cycleComponentι_genericPoint, a2r_cycleComponentι_genericPoint]
  -- the function `t|_Y` is pulled back from `(g × id)(Y)`
  have hcomp : h.left ≫ cycleComponentι (a3n_T X).left y₀ ≫ a3n_h X =
      cycleComponentι (a3n_T X').left y ≫ a3n_h X' := by
    rw [← Category.assoc, hcomm, Category.assoc, a3h_G_h]
  have hφ : a3o_φ X' y hy = a2r_ffHom h.left hdom (a3o_φ X y₀ hGy) :=
    (a3h_pullbackFF_congr hcomp.symm _ (by rw [hcomp]; exact a3o_hgen X' y hy) _).trans
      (a3h_pullbackFF_comp h.left (cycleComponentι (a3n_T X).left y₀ ≫ a3n_h X) hdom
        (a3o_hgen X y₀ hGy) _ _)
  -- the degree of `g × id` at `y` is the degree of `h` at the generic point
  have hdeg : a1p_degree (a3h_G g).left y =
      a1p_degree h.left (genericPoint (a2r_component (a3n_T X') y).left) := by
    have h1 := a1p_degree_comp (cycleComponentι (a3n_T X').left y) (a3h_G g).left
      (genericPoint (cycleComponent (a3n_T X').left y))
    have h2 := a1p_degree_comp h.left (cycleComponentι (a3n_T X).left y₀)
      (genericPoint (cycleComponent (a3n_T X').left y))
    rw [← hcomm, h2, a2r_cycleComponentι_genericPoint,
      a3m_degree_closedImmersion (cycleComponentι (a3n_T X).left y₀),
      a3m_degree_closedImmersion (cycleComponentι (a3n_T X').left y), one_mul, mul_one] at h1
    exact h1.symm
  -- push along `ι ≫ (g × id) = h ≫ ι`
  have hpush : a1p_pushforward (a3h_G g).left (a3o_cyc X' y hy) =
      (a1p_pushforward (cycleComponentι (a3n_T X).left y₀)
        (a1p_pushforward h.left (principalDivisor (cycleComponent (a3n_T X').left y)
          (a3o_φ X' y hy) : AlgebraicCycle _ ℤ))).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
    rw [a3o_cyc, a2_principalCycle, a2r_pushforward_mapRange_intCast, ← a1p_pushforward_comp,
      a2r_pushforward_congr hcomm.symm, a1p_pushforward_comp]
  by_cases heq : height (genericPoint (a2r_component (a3n_T X) y₀).left) =
      height (genericPoint (a2r_component (a3n_T X') y).left)
  · letI := (a2r_ffHom h.left hdom).toAlgebra
    have hφ0 : a3o_φ X y₀ hGy ≠ 0 := a3o_φ_ne_zero X y₀ hGy
    have hnorm := a3h_pushforward_principal_norm h hdom heq (a3o_φ_ne_zero X' y hy)
    rw [hφ] at hnorm
    change a1p_pushforward h.left _ = _ at hnorm
    rw [hpush, hφ]
    erw [hnorm]
    have hn : Algebra.norm (a2r_component (a3n_T X) y₀).left.functionField
        (a2r_ffHom h.left hdom (a3o_φ X y₀ hGy)) = a3o_φ X y₀ hGy ^ Module.finrank
          (a2r_component (a3n_T X) y₀).left.functionField
          (a2r_component (a3n_T X') y).left.functionField :=
      Algebra.norm_algebraMap _
    rw [hn, ← a3h_degree_genericPoint h.left hdom, ← hdeg]
    erw [a3h_principalDivisor_pow (a2r_component (a3n_T X) y₀).left hφ0]
    rw [a1p_pushforward_mul]
    ext z
    simp [a3o_cyc, a2_principalCycle, a3m_smul_apply]
    exact Or.inl rfl
  · have h0 := a2r_pushforward_principal_of_height_ne h hdom heq (a3o_φ_ne_zero X' y hy)
    change a1p_pushforward h.left _ = 0 at h0
    have hd0 : a1p_degree (a3h_G g).left y = 0 := by
      rw [hdeg]
      by_contra hne
      exact heq (by
        have := (a1p_degree_pos_iff h _).1 (Nat.pos_of_ne_zero hne)
        rwa [hdom] at this)
    rw [hpush]
    erw [h0]
    rw [hd0]
    have hz : a1p_pushforward (cycleComponentι (a3n_T X).left y₀)
        (0 : AlgebraicCycle (cycleComponent (a3n_T X).left y₀) ℤ) = 0 := by
      have h := a1p_pushforward_add (cycleComponentι (a3n_T X).left y₀)
        (0 : AlgebraicCycle (cycleComponent (a3n_T X).left y₀) ℤ) 0
      rw [add_zero] at h
      exact left_eq_add.mp h
    erw [hz]
    ext z
    simp [a3m_smul_apply]

omit [IsProper g.left] in
theorem a3h_not_dom (y : (a3n_T X').left) (hy : a3n_h X' y ≠ genericPoint (g3c_P 1)) :
    a3n_h X ((a3h_G g).left y) ≠ genericPoint (g3c_P 1) := by
  rwa [a3h_G_h_apply]

/-- `g_*` of the boundary of one member is `deg` times the boundary of its image. -/
theorem a3h_push_piece (y : (a3n_T X').left) :
    a1p_pushforward g.left (a3k_piece X' y) =
      a3m_smul (a1p_degree (a3h_G g).left y) (a3k_piece X ((a3h_G g).left y)) := by
  by_cases hy : a3n_h X' y = genericPoint (g3c_P 1)
  · have hGy : a3n_h X ((a3h_G g).left y) = genericPoint (g3c_P 1) := by
      rw [a3h_G_h_apply]; exact hy
    rw [a3k_piece_of_dom X' y hy, a3k_piece_of_dom X _ hGy, ← a1p_pushforward_comp,
      a2r_pushforward_congr (a3h_G_q g).symm, a1p_pushforward_comp, a3h_push_cyc g y hy hGy,
      a3k_pushforward_smul]
  · have h1 : a3k_piece X' y = 0 := by
      unfold a3k_piece; rw [dif_neg hy]
    have h2 : a3k_piece X ((a3h_G g).left y) = 0 := by
      unfold a3k_piece; rw [dif_neg (a3h_not_dom g y hy)]
    rw [h1, h2, a3k_pushforward_zero]
    ext z
    simp

/-- **Proper pushforward commutes with the boundary.** For a proper `g : X' → X` and a chain `Z`
on `X' × ℙ¹`, `g_* (∂ Z) = ∂ ((g × id)_* Z)`: the faces `t = a` of the pushforward are the
pushforwards of the faces.
Source: Fulton, *Intersection Theory*, second edition, Proposition 1.4 and §1.6; S. Bloch, *The
moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §2. -/
theorem a3h_push_bd (Z : AlgebraicCycle (a3n_T X').left ℚ) :
    a1p_pushforward g.left (a3k_bd X' Z) = a3k_bd X (a1p_pushforward (a3h_G g).left Z) := by
  classical
  set s := (a3m_support_finite Z).toFinset
  have hs : ∀ y ∉ s, Z y = 0 := fun y hy => by simpa [s] using hy
  have hZ := a3m_eq_sum_single Z s hs
  have hpush : a1p_pushforward (a3h_G g).left Z = ∑ y ∈ s, a3m_smul (Z y)
      (a3m_smul (a1p_degree (a3h_G g).left y)
        (Function.locallyFinsuppWithin.single ((a3h_G g).left y) 1)) := by
    conv_lhs => rw [hZ]
    rw [a3k_pushforward_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [a3k_pushforward_smul, a1p_pushforward_single]
    ext z
    simp [Function.locallyFinsuppWithin.single_apply]
  rw [a3k_bd_eq_sum X' Z s hs, a3k_pushforward_sum, hpush, a3k_bd_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [a3k_pushforward_smul, a3h_push_piece, a3k_bd_smul, a3k_bd_smul, a3k_bd_single]

end push

end HodgeLean.Adapters
