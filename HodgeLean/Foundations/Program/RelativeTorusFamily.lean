import HodgeLean.Foundations.Program.RelativeTorusKernelDefs

/-!
# Track B2, families of complex tori: helper lemmas for the family statements

Images of flat endomorphisms: the complexified corestriction `ℂ ⊗ Λ_b → ℂ ⊗ e(Λ_b)` commutes
with flat transport, and for a weight-one filtration preserved by `e` it maps `F_b` onto the
preimage filtration, so holomorphic generators of `F` give holomorphic generators of the image
filtration.

The total space: flat transport inside a simply connected set factors through paths, so the
transfer between two flat frames is locally constant on the overlap; with the continuity of the
holomorphic generators of `F` this makes every flat trivialisation an open map onto `π⁻¹(U)`, and
the fibre inclusions embeddings.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

section ImageFamily

variable {B : Type*} [TopologicalSpace B]

namespace b2_LatticeLocalSystem
variable (L : b2_LatticeLocalSystem B) (e : L.functor ⟶ L.functor)

/-- The complexified corestriction `ℂ ⊗ Λ_b → ℂ ⊗ e(Λ_b)`, `c ⊗ x ↦ c ⊗ e x`, of a flat
endomorphism `e`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.2 and §5.3; Mathlib
`LinearMap.baseChange`. -/
def b2f_imageProj (b : B) : L.cFiber b →ₗ[ℂ] (L.image e).cFiber b :=
  ((e.app (FundamentalGroupoid.mk b)).hom.rangeRestrict.toIntLinearMap).baseChange ℂ

example (b : B) : L.b2f_imageProj e b 0 = 0 := map_zero _

theorem b2f_imageProj_tmul (b : B) (c : ℂ) (x : L.fiber b) :
    L.b2f_imageProj e b (c ⊗ₜ x) =
      c ⊗ₜ[ℤ] (show (L.image e).fiber b from (e.app (FundamentalGroupoid.mk b)).hom.rangeRestrict x) :=
  rfl

theorem b2f_cplxMap_comp_imageProj (b : B) :
    (b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom.range.subtype).comp (L.b2f_imageProj e b) =
      b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom := by
  refine LinearMap.ext fun v ↦ ?_
  induction v using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

theorem b2f_cplxMap_imageProj_apply (b : B) (y : L.cFiber b) :
    b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom.range.subtype (L.b2f_imageProj e b y) =
      b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom y :=
  LinearMap.congr_fun (L.b2f_cplxMap_comp_imageProj e b) y

theorem b2f_imageProj_surjective (b : B) : Function.Surjective (L.b2f_imageProj e b) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c y =>
    obtain ⟨_, x, rfl⟩ := y
    exact ⟨c ⊗ₜ x, rfl⟩
  | add y z hy hz =>
    obtain ⟨y', rfl⟩ := hy
    obtain ⟨z', rfl⟩ := hz
    exact ⟨y' + z', map_add _ _ _⟩

theorem b2f_cplxMap_subtype_injective (b : B) :
    Function.Injective (b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom.range.subtype) := by
  have := Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ)
    (e.app (FundamentalGroupoid.mk b)).hom.range.subtype.toIntLinearMap Subtype.val_injective
  convert this using 1
  ext v
  induction v using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end b2_LatticeLocalSystem
end ImageFamily

section Conj
variable {Λ : Type*} [AddCommGroup Λ]

theorem b2f_cplxMap_conj (f : Λ →+ Λ) (v : ℂ ⊗[ℤ] Λ) :
    b2_cplxMap f (b2_conj Λ v) = b2_conj Λ (b2_cplxMap f v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem b2f_conjSubmodule_le_comap (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (f : Λ →+ Λ)
    (hf : F ≤ F.comap (b2_cplxMap f)) :
    b2_conjSubmodule Λ F ≤ (b2_conjSubmodule Λ F).comap (b2_cplxMap f) := by
  rw [b2_conjSubmodule, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  simp only [Submodule.comap_coe, Set.mem_preimage, SetLike.mem_coe]
  rw [b2f_cplxMap_conj]
  exact Submodule.subset_span ⟨_, hf hv, rfl⟩

/-- For a weight-one `F` preserved by `f_ℂ`, an element of `F` in the range of `f_ℂ` is the image
of an element of `F`. -/
theorem b2f_mem_map_of_isWeightOne (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (f : Λ →+ Λ) (hf : F ≤ F.comap (b2_cplxMap f)) (y : ℂ ⊗[ℤ] Λ) (hy : b2_cplxMap f y ∈ F) :
    ∃ y₁ ∈ F, ∃ y₂, b2_cplxMap f y₂ = 0 ∧ y = y₁ + y₂ := by
  have hy' : y ∈ F ⊔ b2_conjSubmodule Λ F := by rw [hF.sup_eq_top]; trivial
  obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := Submodule.mem_sup.1 hy'
  refine ⟨y₁, h₁, y₂, ?_, rfl⟩
  have hc : b2_cplxMap f y₂ ∈ b2_conjSubmodule Λ F := b2f_conjSubmodule_le_comap F f hf h₂
  have hF' : b2_cplxMap f y₂ ∈ F := by
    have := F.sub_mem hy (hf h₁)
    rwa [map_add, add_sub_cancel_left] at this
  have := hF.inf_eq_bot
  exact (Submodule.mem_bot ℂ).1 (this ▸ Submodule.mem_inf.2 ⟨hF', hc⟩)

end Conj

section ImageFamily2
variable {B : Type*} [TopologicalSpace B]
namespace b2_LatticeLocalSystem
variable (L : b2_LatticeLocalSystem B) (e : L.functor ⟶ L.functor)

theorem b2f_imageF_eq_map (F : ∀ b, Submodule ℂ (L.cFiber b))
    (hw : ∀ b, b2_IsWeightOne (L.fiber b) (F b))
    (hf : ∀ b, F b ≤ (F b).comap (b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom)) (b : B) :
    L.imageF F e b = (F b).map (L.b2f_imageProj e b) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, rfl⟩ := L.b2f_imageProj_surjective e b z
    have hy : b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom y ∈ F b :=
      (L.b2f_cplxMap_imageProj_apply e b y) ▸ hz
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := b2f_mem_map_of_isWeightOne (F b) (hw b) _ (hf b) y hy
    have h₂' : L.b2f_imageProj e b y₂ = 0 := by
      apply L.b2f_cplxMap_subtype_injective e b
      exact (L.b2f_cplxMap_imageProj_apply e b y₂).trans (h₂.trans (map_zero _).symm)
    rw [map_add, h₂', add_zero]
    exact ⟨y₁, h₁, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    show b2_cplxMap _ _ ∈ F b
    exact (L.b2f_cplxMap_imageProj_apply e b y) ▸ hf b hy

theorem b2f_imageTransport_comm {b b' : B} (γ : Path.Homotopic.Quotient b b') (v : L.fiber b) :
    (show L.imageObj e (FundamentalGroupoid.mk b') from (L.image e).transport γ
        (show (L.image e).fiber b from (e.app (FundamentalGroupoid.mk b)).hom.rangeRestrict v)).1 =
      (e.app (FundamentalGroupoid.mk b')).hom (L.transport γ v) := by
  have := congrArg (fun φ ↦ φ.hom v) (e.naturality (show FundamentalGroupoid.mk b ⟶
    FundamentalGroupoid.mk b' from γ))
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at this
  exact this.symm

theorem b2f_flatTransport_imageProj (U : Set B) (hU : IsSimplyConnected U) (b b₀ : U)
    (v : L.cFiber b) :
    (L.image e).flatTransport U hU b b₀ (L.b2f_imageProj e b v) =
      L.b2f_imageProj e b₀ (L.flatTransport U hU b b₀ v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c x =>
    show c ⊗ₜ[ℤ] _ = c ⊗ₜ[ℤ] _
    congr 1
    exact Subtype.ext (L.b2f_imageTransport_comm e _ x)
  | add x y hx hy => simp only [map_add, hx, hy]

end b2_LatticeLocalSystem
end ImageFamily2

section ImageHolomorphic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

theorem b2f_image_holomorphic (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b))
    (hT : b2_IsPolarizedTorusFamily E L F Q) (e : L.functor ⟶ L.functor)
    (hf : ∀ b, F b ≤ (F b).comap (b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom)) :
    (L.image e).IsHolomorphicSubbundle E (L.imageF F e) := by
  intro b₁
  obtain ⟨U, hU, h₁, hUo, r, s, hs, hspan⟩ := hT.holomorphic b₁
  refine ⟨U, hU, h₁, hUo, r, fun i b ↦ L.b2f_imageProj e b (s i b), fun i ↦ ?_, fun b hb ↦ ?_⟩
  · have key : (L.image e).flatCoord U hU ⟨b₁, h₁⟩ (fun b ↦ L.b2f_imageProj e b (s i b)) =
        L.b2f_imageProj e b₁ ∘ L.flatCoord U hU ⟨b₁, h₁⟩ (s i) := by
      funext b
      simp only [b2_LatticeLocalSystem.flatCoord, Function.comp_apply]
      split_ifs with hb
      · exact L.b2f_flatTransport_imageProj e U hU ⟨b, hb⟩ ⟨b₁, h₁⟩ (s i b)
      · exact (map_zero _).symm
    let lin : (Fin (Module.finrank ℂ (L.cFiber b₁)) → ℂ) →ₗ[ℂ]
        (Fin (Module.finrank ℂ ((L.image e).cFiber b₁)) → ℂ) :=
      (b2_coord ((L.image e).cFiber b₁)).toLinearMap ∘ₗ L.b2f_imageProj e b₁ ∘ₗ
        (b2_coord (L.cFiber b₁)).symm.toLinearMap
    have hcomp : b2_coord ((L.image e).cFiber b₁) ∘
        (L.image e).flatCoord U hU ⟨b₁, h₁⟩ (fun b ↦ L.b2f_imageProj e b (s i b)) =
        lin ∘ (b2_coord (L.cFiber b₁) ∘ L.flatCoord U hU ⟨b₁, h₁⟩ (s i)) := by
      rw [key]; funext b; simp [lin]
    unfold b2_LatticeLocalSystem.IsHolomorphicSectionOn b2_IsHolomorphicOn
    rw [hcomp]
    exact (LinearMap.toContinuousLinearMap lin).contDiff.contMDiff.comp_contMDiffOn (hs i)
  · rw [L.b2f_imageF_eq_map e F hT.hodge hf b, ← hspan b hb, Submodule.map_span,
      ← Set.range_comp]
    rfl

end ImageHolomorphic

section Transport

variable {B : Type*} [TopologicalSpace B]

namespace b2_LatticeLocalSystem
variable (L : b2_LatticeLocalSystem B)

theorem b2f_transport_apply {b b' : B} (γ : Path.Homotopic.Quotient b b') (x : L.fiber b) :
    L.transport γ x = (L.functor.map (show FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b'
      from γ)).hom x := rfl

theorem b2f_transport_trans {b b' b'' : B} (γ : Path.Homotopic.Quotient b b')
    (δ : Path.Homotopic.Quotient b' b'') (x : L.fiber b) :
    L.transport (γ.trans δ) x = L.transport δ (L.transport γ x) := by
  rw [b2f_transport_apply, b2f_transport_apply, b2f_transport_apply]
  have := L.functor.map_comp (show FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b' from γ)
    (show FundamentalGroupoid.mk b' ⟶ FundamentalGroupoid.mk b'' from δ)
  rw [FundamentalGroupoid.comp_eq] at this
  exact congrArg (fun φ ↦ φ.hom x) this

theorem b2f_classIn_eq (U : Set B) (hU : IsSimplyConnected U) {b b₀ : U} (p : Path b b₀) :
    classIn U hU b b₀ = Path.Homotopic.Quotient.mk (p.map continuous_subtype_val) := by
  have := hU.simplyConnectedSpace
  unfold classIn
  exact Path.Homotopic.Quotient.eq.2 (Path.Homotopic.map (SimplyConnectedSpace.paths_homotopic _ _) ⟨Subtype.val, continuous_subtype_val⟩)

/-- The complexified transport `ℂ ⊗ Λ_b ≃ ℂ ⊗ Λ_{b'}` along a class of paths.
Source: Voisin, *Hodge Theory I*, ch. 9; Mathlib `LinearEquiv.baseChange`. -/
def b2f_cTransport {b b' : B} (γ : Path.Homotopic.Quotient b b') : L.cFiber b ≃ₗ[ℂ] L.cFiber b' :=
  LinearEquiv.baseChange ℤ ℂ _ _ (L.transport γ).toIntLinearEquiv

example (b : B) : L.cFiber b ≃ₗ[ℂ] L.cFiber b := L.b2f_cTransport (Path.Homotopic.Quotient.refl b)

theorem b2f_cTransport_trans {b b' b'' : B} (γ : Path.Homotopic.Quotient b b')
    (δ : Path.Homotopic.Quotient b' b'') (v : L.cFiber b) :
    L.b2f_cTransport (γ.trans δ) v = L.b2f_cTransport δ (L.b2f_cTransport γ v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c x =>
    show c ⊗ₜ[ℤ] L.transport (γ.trans δ) x = c ⊗ₜ[ℤ] L.transport δ (L.transport γ x)
    rw [L.b2f_transport_trans γ δ x]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem b2f_flatTransport_eq (U : Set B) (hU : IsSimplyConnected U) (b b₀ : U) :
    L.flatTransport U hU b b₀ = L.b2f_cTransport (classIn U hU b b₀) := rfl

/-- Flat transport inside `U` from `c` factors through any path in `U` from `c` to `c'`. -/
theorem b2f_flatTransport_path (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) {c c' : B}
    (hc : c ∈ U) (hc' : c' ∈ U) (q : Path c c') (hq : ∀ t, q t ∈ U) (v : L.cFiber c) :
    L.flatTransport U hU ⟨c, hc⟩ b₀ v =
      L.flatTransport U hU ⟨c', hc'⟩ b₀ (L.b2f_cTransport (Path.Homotopic.Quotient.mk q) v) := by
  have := hU.simplyConnectedSpace
  let p : Path (⟨c, hc⟩ : U) ⟨c', hc'⟩ :=
    { toFun := fun t ↦ ⟨q t, hq t⟩
      continuous_toFun := by fun_prop
      source' := by ext; simp
      target' := by ext; simp }
  have hcl : classIn U hU ⟨c, hc⟩ b₀ =
      (Path.Homotopic.Quotient.mk q).trans (classIn U hU ⟨c', hc'⟩ b₀) := by
    rw [b2f_classIn_eq U hU (p.trans (PathConnectedSpace.somePath _ b₀)), Path.map_trans]
    exact (Path.Homotopic.Quotient.mk_trans _ _).trans rfl
  rw [b2f_flatTransport_eq, hcl, b2f_cTransport_trans]
  rfl

/-- The transfer between two flat frames is constant along paths in the overlap. -/
theorem b2f_transfer_path (U₁ U₂ : Set B) (hU₁ : IsSimplyConnected U₁)
    (hU₂ : IsSimplyConnected U₂) (b₁ : U₁) (b₂ : U₂) {c c' : B} (hc₁ : c ∈ U₁) (hc₂ : c ∈ U₂)
    (hc₁' : c' ∈ U₁) (hc₂' : c' ∈ U₂) (q : Path c c') (hq : ∀ t, q t ∈ U₁ ∩ U₂)
    (v : L.cFiber b₁) :
    L.flatTransport U₂ hU₂ ⟨c, hc₂⟩ b₂ ((L.flatTransport U₁ hU₁ ⟨c, hc₁⟩ b₁).symm v) =
      L.flatTransport U₂ hU₂ ⟨c', hc₂'⟩ b₂ ((L.flatTransport U₁ hU₁ ⟨c', hc₁'⟩ b₁).symm v) := by
  have h₁ : (L.flatTransport U₁ hU₁ ⟨c, hc₁⟩ b₁).symm v =
      (L.b2f_cTransport (Path.Homotopic.Quotient.mk q)).symm
        ((L.flatTransport U₁ hU₁ ⟨c', hc₁'⟩ b₁).symm v) := by
    apply (L.flatTransport U₁ hU₁ ⟨c, hc₁⟩ b₁).injective
    rw [LinearEquiv.apply_symm_apply, L.b2f_flatTransport_path U₁ hU₁ b₁ hc₁ hc₁' q
      (fun t ↦ (hq t).1), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [h₁, L.b2f_flatTransport_path U₂ hU₂ b₂ hc₂ hc₂' q (fun t ↦ (hq t).2),
    LinearEquiv.apply_symm_apply]

end b2_LatticeLocalSystem

section TorusFibre
variable {Λ : Type*} [AddCommGroup Λ]

theorem b2f_torus_mk_eq_iff (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (v w : ℂ ⊗[ℤ] Λ) :
    (QuotientAddGroup.mk (Submodule.Quotient.mk v) : b2_torus Λ F) =
        QuotientAddGroup.mk (Submodule.Quotient.mk w) ↔
      ∃ x : Λ, v - w + b2_incl Λ x ∈ F := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, (Submodule.Quotient.mk_eq_zero F).1 ?_⟩
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub]
    change _ + b2_latticeMap Λ F x = 0
    rw [hx]; abel
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have := (Submodule.Quotient.mk_eq_zero F).2 hx
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub] at this
    change _ + b2_latticeMap Λ F x = 0 at this
    rw [← sub_eq_zero, ← this]; abel

end TorusFibre

namespace b2_LatticeLocalSystem
variable (L : b2_LatticeLocalSystem B)

theorem b2f_flatTransport_symm_incl (U : Set B) (hU : IsSimplyConnected U) (b c b₀ : U)
    (x : L.fiber b) :
    ∃ y : L.fiber c, (L.flatTransport U hU c b₀).symm (L.flatTransport U hU b b₀
      (b2_incl _ x)) = b2_incl _ y :=
  ⟨(L.transport (classIn U hU c b₀)).symm (L.transport (classIn U hU b b₀) x), rfl⟩

end b2_LatticeLocalSystem

section Open
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E B]

namespace b2_LatticeLocalSystem
variable (L : b2_LatticeLocalSystem B)

/-- The flat coordinates of a holomorphic section are continuous on its set. -/
theorem b2f_flatCoord_continuousOn (U : Set B) (hU : IsSimplyConnected U) (b₀ : U)
    (s : ∀ b, L.cFiber b) (hs : L.IsHolomorphicSectionOn E U hU b₀ s) :
    ContinuousOn (L.flatCoord U hU b₀ s) U := by
  have h := hs.continuousOn
  have hc : Continuous (b2_coord (L.cFiber b₀)).symm :=
    IsModuleTopology.continuous_of_linearMap (b2_coord (L.cFiber b₀)).symm.toLinearMap
  have := hc.comp_continuousOn h
  convert this using 1
  funext b
  simp

end b2_LatticeLocalSystem

theorem b2f_flatTriv_mk_eq (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))
    (U U' : Set B) (hU : IsSimplyConnected U) (hU' : IsSimplyConnected U') (b₀ : U) (b₀' : U')
    (c : B) (hc : c ∈ U) (hc' : c ∈ U') (v : L.cFiber b₀) (v' : L.cFiber b₀') :
    b2_flatTriv L F U hU b₀ (⟨c, hc⟩, v) = b2_flatTriv L F U' hU' b₀' (⟨c, hc'⟩, v') ↔
      ∃ x : L.fiber c, (L.flatTransport U hU ⟨c, hc⟩ b₀).symm v -
        (L.flatTransport U' hU' ⟨c, hc'⟩ b₀').symm v' + b2_incl _ x ∈ F c := by
  rw [← b2f_torus_mk_eq_iff]
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  · intro h
    exact congrArg (Sigma.mk c) h

theorem b2f_flatTriv_isOpenMap (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (hhol : L.IsHolomorphicSubbundle E F) (U : Set B)
    (hU : IsSimplyConnected U) (hUo : IsOpen U) (b₀ : U) :
    IsOpenMap (b2_flatTriv L F U hU b₀) := by
  have := ChartedSpace.locallyPathConnectedSpace E B
  intro W hW
  refine isOpen_iSup_iff.2 fun U' ↦ isOpen_iSup_iff.2 fun hU' ↦ isOpen_iSup_iff.2 fun hU'o ↦
    isOpen_iSup_iff.2 fun b₀' ↦ ?_
  rw [isOpen_coinduced, isOpen_iff_mem_nhds]
  rintro ⟨⟨b₂, hb'⟩, w'⟩ ⟨⟨⟨b, hb⟩, w⟩, hcw, heq⟩
  obtain rfl : b = b₂ := congrArg Sigma.fst heq
  obtain ⟨x, hx⟩ := (b2f_flatTriv_mk_eq L F U U' hU hU' b₀ b₀' b hb hb' w w').1 heq
  obtain ⟨U'', hU'', hb'', hU''o, r, s, hs, hspan⟩ := hhol b
  rw [← hspan b hb'', Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨a, ha⟩ := hx
  set T := L.flatTransport U hU ⟨b, hb⟩ b₀ with hT
  set T' := L.flatTransport U' hU' ⟨b, hb'⟩ b₀' with hT'
  set T'' := L.flatTransport U'' hU'' ⟨b, hb''⟩ ⟨b, hb''⟩ with hT''
  set N := pathComponentIn (U ∩ U' ∩ U'') b with hN
  have hNo : IsOpen N := (hUo.inter hU'o |>.inter hU''o).pathComponentIn b
  have hbN : b ∈ N := mem_pathComponentIn_self ⟨⟨hb, hb'⟩, hb''⟩
  let g : B → L.cFiber b := fun c ↦ ∑ i, a i • L.flatCoord U'' hU'' ⟨b, hb''⟩ (s i) c
  let G : B × L.cFiber b₀' → L.cFiber b₀ := fun p ↦
    T (T'.symm p.2) - T (b2_incl _ x) + T (T''.symm (g p.1))
  let Ψ : U' × L.cFiber b₀' → B × L.cFiber b₀ := fun p ↦ ((p.1 : B), G ((p.1 : B), p.2))
  have hgb : g b = T'' (∑ i, a i • s i b) := by
    simp only [g, b2_LatticeLocalSystem.flatCoord, dite_eq_left hb'', map_sum, map_smul]
    rfl
  have hΨ : Ψ (⟨b, hb'⟩, w') = (b, w) := by
    simp only [Ψ, G, Prod.mk.injEq, true_and]
    rw [hgb, LinearEquiv.symm_apply_apply, ha, map_add, map_sub, LinearEquiv.apply_symm_apply]
    abel
  have hgc : ContinuousAt g b := by
    refine tendsto_finsetSum _ fun i _ ↦ Filter.Tendsto.const_smul ?_ (a i)
    exact ((L.b2f_flatCoord_continuousOn U'' hU'' _ (s i) (hs i)).continuousAt
      (hU''o.mem_nhds hb''))
  have hΨc : ContinuousAt Ψ (⟨b, hb'⟩, w') := by
    refine (continuous_subtype_val.comp continuous_fst).continuousAt.prodMk ?_
    refine ContinuousAt.add (ContinuousAt.sub ?_ continuousAt_const) ?_
    · exact (IsModuleTopology.continuous_of_linearMap
        (T.toLinearMap ∘ₗ T'.symm.toLinearMap)).continuousAt.comp continuous_snd.continuousAt
    · have hg' : ContinuousAt (fun p : U' × L.cFiber b₀' ↦ g (p.1 : B)) (⟨b, hb'⟩, w') :=
        ContinuousAt.comp (g := g) hgc (continuous_subtype_val.comp continuous_fst).continuousAt
      exact (IsModuleTopology.continuous_of_linearMap
        (T.toLinearMap ∘ₗ T''.symm.toLinearMap)).continuousAt.comp hg'
  have hW' : IsOpen (Prod.map Subtype.val id '' W : Set (B × L.cFiber b₀)) :=
    (hUo.isOpenEmbedding_subtypeVal.prodMap Topology.IsOpenEmbedding.id).isOpenMap W hW
  have h1 : ∀ᶠ p in nhds (⟨b, hb'⟩, w'), Ψ p ∈ Prod.map Subtype.val id '' W :=
    hΨc.preimage_mem_nhds (hW'.mem_nhds (hΨ ▸ ⟨_, hcw, rfl⟩))
  have h2 : ∀ᶠ p in nhds ((⟨b, hb'⟩ : U'), w'), ((p.1 : U') : B) ∈ N :=
    (continuous_subtype_val.comp continuous_fst).continuousAt.preimage_mem_nhds
      (hNo.mem_nhds hbN)
  filter_upwards [h1, h2]
  rintro ⟨⟨c, hc'⟩, u⟩ ⟨⟨⟨c₂, hcU⟩, y⟩, hyW, hyeq⟩ hcN
  simp only [Prod.map, id, Prod.mk.injEq, Ψ] at hyeq
  obtain ⟨rfl, rfl⟩ := hyeq
  refine ⟨_, hyW, ?_⟩
  have hJ := hcN
  obtain ⟨⟨hcU', hc'U⟩, hc''⟩ := hJ.mem.2
  rw [b2f_flatTriv_mk_eq L F U U' hU hU' b₀ b₀' c₂ hcU hc' _ u]
  obtain ⟨y₀, hy₀⟩ := L.b2f_flatTransport_symm_incl U hU ⟨b, hb⟩ ⟨c₂, hcU⟩ b₀ x
  refine ⟨y₀, ?_⟩
  have hJ' : JoinedIn (U ∩ U' ∩ U'') b c₂ := hcN
  have e1 := L.b2f_transfer_path U' U hU' hU b₀' b₀ hb' hb hc'U hcU hJ'.somePath
    (fun t ↦ ⟨(hJ'.somePath_mem t).1.2, (hJ'.somePath_mem t).1.1⟩) u
  have e2 := L.b2f_transfer_path U'' U hU'' hU ⟨b, hb''⟩ b₀ hb'' hb hc'' hcU hJ'.somePath
    (fun t ↦ ⟨(hJ'.somePath_mem t).2, (hJ'.somePath_mem t).1.1⟩)
    (L.flatTransport U'' hU'' ⟨c₂, hc''⟩ ⟨b, hb''⟩ (∑ i, a i • s i c₂))
  have hgc₂ : g c₂ = L.flatTransport U'' hU'' ⟨c₂, hc''⟩ ⟨b, hb''⟩ (∑ i, a i • s i c₂) := by
    simp only [g, b2_LatticeLocalSystem.flatCoord, dite_eq_left hc'', map_sum, map_smul]
  simp only [G]
  rw [e1, map_add, map_sub, LinearEquiv.symm_apply_apply, hy₀, hgc₂, e2, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]
  have hmem : ∑ i, a i • s i c₂ ∈ F c₂ := by
    rw [← hspan c₂ hc'']
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  convert hmem using 1
  abel
end Open

section Embed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E B]

theorem b2f_flatTriv_range (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))
    (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    Set.range (b2_flatTriv L F U hU b₀) = b2_proj L F ⁻¹' U := by
  ext ⟨c, t⟩
  constructor
  · rintro ⟨⟨⟨c', h⟩, v⟩, hv⟩
    obtain rfl : c' = c := congrArg Sigma.fst hv
    exact h
  · intro hc
    obtain ⟨t', rfl⟩ := QuotientAddGroup.mk_surjective t
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t'
    exact ⟨(⟨c, hc⟩, L.flatTransport U hU ⟨c, hc⟩ b₀ v), by
      simp only [b2_flatTriv, LinearEquiv.symm_apply_apply]; rfl⟩

/-- The quotient map `ℂ ⊗ Λ → T` is a quotient map. -/
theorem b2f_torus_mk_isQuotientMap {Λ : Type*} [AddCommGroup Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) :
    Topology.IsQuotientMap (fun v : ℂ ⊗[ℤ] Λ ↦
      (QuotientAddGroup.mk (Submodule.Quotient.mk v) : b2_torus Λ F)) :=
  (QuotientAddGroup.isQuotientMap_mk _).comp (Submodule.isQuotientMap_mkQ F)

theorem b2f_fiberIncl_isEmbedding (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (hhol : L.IsHolomorphicSubbundle E F) (b : B) :
    Topology.IsEmbedding (b2_fiberIncl L F b) := by
  obtain ⟨U, hU, hb, hUo, -⟩ := hhol b
  set b₀ : U := ⟨b, hb⟩
  set T := L.flatTransport U hU b₀ b₀
  have hπ := b2f_torus_mk_isQuotientMap (F b)
  have hφ := b2_flatTriv_continuous L F U hU hUo b₀
  have hT : Continuous T := IsModuleTopology.continuous_of_linearMap T.toLinearMap
  have hTs : Continuous T.symm := IsModuleTopology.continuous_of_linearMap T.symm.toLinearMap
  have hcomp : (b2_fiberIncl L F b ∘ fun v : L.cFiber b ↦
      (QuotientAddGroup.mk (Submodule.Quotient.mk v) : b2_fiberTorus L F b)) =
      fun v ↦ b2_flatTriv L F U hU b₀ (b₀, T v) := by
    funext v
    simp only [b2_fiberIncl, b2_flatTriv, T, LinearEquiv.symm_apply_apply]
    rfl
  have hcont : Continuous (b2_fiberIncl L F b) := by
    rw [hπ.continuous_iff, hcomp]
    exact hφ.comp (continuous_const.prodMk hT)
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.1 hcont) ?_⟩, sigma_mk_injective⟩
  intro O hO
  rw [isOpen_induced_iff]
  refine ⟨b2_flatTriv L F U hU b₀ '' (Set.univ ×ˢ (T.symm ⁻¹' ((fun v : L.cFiber b ↦
      (QuotientAddGroup.mk (Submodule.Quotient.mk v) : b2_fiberTorus L F b)) ⁻¹' O))),
    b2f_flatTriv_isOpenMap L F hhol U hU hUo b₀ _
      (isOpen_univ.prod ((hO.preimage hπ.continuous).preimage hTs)), ?_⟩
  ext t
  constructor
  · rintro ⟨⟨⟨c, hc⟩, v⟩, ⟨-, hv⟩, heq⟩
    obtain rfl : c = b := congrArg Sigma.fst heq
    have := eq_of_heq (Sigma.mk.inj_iff.1 heq).2
    rw [← this]
    exact hv
  · intro ht
    obtain ⟨t', rfl⟩ := QuotientAddGroup.mk_surjective t
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t'
    refine ⟨(b₀, T v), ⟨trivial, ?_⟩, ?_⟩
    · simpa [T] using ht
    · simp only [b2_flatTriv, b2_fiberIncl, T, LinearEquiv.symm_apply_apply]
      rfl

end Embed

end Transport

end HodgeLean.Foundations.Program
