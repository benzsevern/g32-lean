import HodgeLean.Foundations.AlgebraicGeometry.Scheme.FixedPointStalkDefs

/-! # Open bodies for fixed-point stalk and jet transport

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.FixedPointStalk

/-- Germ transport and section pullback use the specified point equality.
Source: Hartshorne, Algebraic Geometry, II.1–2 and II.5. -/
theorem germ_transport_aux (X : Scheme) :
    (∀ (U : X.Opens) (x y : X) (hx : x ∈ U) (hy : y ∈ U) (h : x = y),
      X.presheaf.germ U x hx ≫ (X.presheaf.stalkCongr (.of_eq h)).hom =
        X.presheaf.germ U y hy) ∧
    (∀ (f : X ⟶ X) (p : X) (hp : f p = p) (U : X.Opens)
      (hU : U ≤ f ⁻¹ᵁ U) (hmem : p ∈ U),
      X.presheaf.germ U p hmem ≫
          (X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p =
        f.appLE U U hU ≫ X.presheaf.germ U p hmem) := by
  constructor
  · intro U x y hx hy h
    subst y
    simp
  · intro f p hp U hU hmem
    have ht : X.presheaf.germ U p hmem ≫
        (X.presheaf.stalkCongr (.of_eq hp.symm)).hom =
        X.presheaf.germ U (f p) (by rwa [hp]) := by
      exact (show ∀ (x y : X) (hx : x ∈ U) (hy : y ∈ U) (h : x = y),
        X.presheaf.germ U x hx ≫ (X.presheaf.stalkCongr (.of_eq h)).hom =
          X.presheaf.germ U y hy from by
            intro x y hx hy h
            subst y
            simp) p (f p) hmem (by rwa [hp]) hp.symm
    have he : (X.presheaf.stalkCongr (.of_eq hp)).inv =
        (X.presheaf.stalkCongr (.of_eq hp.symm)).hom := by
      simp only [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkCongr_hom]
    rw [he, ← Category.assoc, ht, f.germ_stalkMap]
    dsimp only [Scheme.Hom.appLE]
    rw [Category.assoc, X.presheaf.germ_res]

/-- Identity and literal contravariant composition at a fixed point.
Source: Hartshorne, Algebraic Geometry, II.1–2 and II.5. -/
theorem pullback_laws_aux (X : Scheme) (p : X) :
    pullback X (𝟙 X) p (by simp) = RingHom.id _ ∧
    (∀ (u v : X ⟶ X) (hu : u p = p) (hv : v p = p),
      pullback X (u ≫ v) p (by change v (u p) = p; rw [hu, hv]) =
        (pullback X u p hu).comp (pullback X v p hv)) := by
  constructor
  · simp [pullback, TopCat.Presheaf.stalkCongr]
  · intro u v hu hv
    have h := v.stalkSpecializes_stalkMap (u p) p (specializes_of_eq hu)
    dsimp only [pullback]
    rw [Scheme.Hom.stalkMap_comp]
    have he :
        (X.presheaf.stalkCongr (.of_eq
          (show (u ≫ v) p = p by change v (u p) = p; rw [hu, hv]))).inv ≫
            v.stalkMap (u p) =
        (X.presheaf.stalkCongr (.of_eq hv)).inv ≫ v.stalkMap p ≫
          (X.presheaf.stalkCongr (.of_eq hu)).inv := by
      simp only [TopCat.Presheaf.stalkCongr_inv]
      have hh := congrArg
        (fun k => X.presheaf.stalkSpecializes (specializes_of_eq hv) ≫ k) h
      simpa only [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp,
        TopCat.Presheaf.stalkSpecializes_refl, Category.comp_id] using hh
    change ((X.presheaf.stalkCongr _).inv ≫
      (v.stalkMap (u p) ≫ u.stalkMap p)).hom = _
    rw [← Category.assoc, he]
    rfl

/-- Local stalk pullback preserves every maximal-ideal power.
Source: Hartshorne, Algebraic Geometry, II.1–2 and II.5. -/
theorem pullback_power_aux (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p)
    (n : ℕ) (r : X.presheaf.stalk p)
    (hr : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n) :
    pullback X f p hp r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n := by
  let β := pullback X f p hp
  letI : IsLocalHom (X.presheaf.stalkCongr (.of_eq hp)).inv.hom :=
    isLocalHom_of_iso (X.presheaf.stalkCongr (.of_eq hp)).symm
  letI : IsLocalHom β := inferInstanceAs
    (IsLocalHom ((X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p).hom)
  apply (show (IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n).map β ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n from ?_)
    (Ideal.mem_map_of_mem β hr)
  rw [Ideal.map_pow]
  exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le β) n

/-- The induced finite jet maps agree on representatives and commute with projections.
Source: Hartshorne, Algebraic Geometry, II.1–2 and II.5. -/
theorem jet_pullback_naturality_aux (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p) :
    (∀ (n : ℕ) (r : X.presheaf.stalk p),
      jetPullback X f p hp n (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk _ (pullback X f p hp r)) ∧
    (∀ (m n : ℕ) (h : m ≤ n),
      (projection X p h).comp (jetPullback X f p hp n) =
        (jetPullback X f p hp m).comp (projection X p h)) := by
  constructor
  · intro n r
    rfl
  · intro m n h
    ext a
    rfl

/-- A representative of an invariant stalk jet is invariant under section pullback to the same order.
Source: Hartshorne, Algebraic Geometry, II.1–2 and II.5. -/
theorem section_jet_invariant_aux (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p)
    (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ U) (hmem : p ∈ U) (n : ℕ)
    (r : X.presheaf.stalk p)
    (hr : pullback X f p hp r - r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n)
    (b : Γ(X, U))
    (hb : (X.presheaf.germ U p hmem).hom b - r ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n) :
    (X.presheaf.germ U p hmem).hom ((f.appLE U U hU).hom b - b) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n := by
  let γ := (X.presheaf.germ U p hmem).hom
  let β := pullback X f p hp
  let J := IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n
  have hc : β (γ b) = γ ((f.appLE U U hU).hom b) := by
    exact congrArg (fun k : Γ(X, U) ⟶ X.presheaf.stalk p => k.hom b)
      ((germ_transport_aux X).2 f p hp U hU hmem)
  have hm : β (γ b - r) ∈ J :=
    pullback_power_aux X f p hp n _ hb
  have he : γ ((f.appLE U U hU).hom b - b) =
      β (γ b - r) + (β r - r) - (γ b - r) := by
    rw [map_sub, map_sub, hc]
    ring
  change γ _ ∈ J
  rw [he]
  exact J.sub_mem (J.add_mem hm hr) hb

end AlgebraicGeometry.Scheme.FixedPointStalk
