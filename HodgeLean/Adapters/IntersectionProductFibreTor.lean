import HodgeLean.Adapters.IntersectionProductDivisorGlue
import HodgeLean.Adapters.IntersectionProductRegularQuotient

/-! # `Tor` along a flat local map with a retraction

For a flat ring map `f : A → B`, a `B`-module `M` and an `A`-module `N`,
`Tor_n^B(M, B ⊗_A N) ≅ Tor_n^A(M, N)` as `A`-modules (`a3f_tor_restrict`): a projective
resolution `Q` of `N` extends to one of `B ⊗_A N`, and `M ⊗_B (B ⊗_A Q) ≅ M ⊗_A Q`.

If moreover `g : B → A` is a retraction of `f` (`g ∘ f = id`) and `M` is killed by `ker g`, then
`B`-lengths and `A`-lengths agree on such modules (`a3f_length_eq`). This is the comparison of
Serre's multiplicities on `X × ℙ¹` along a fibre `X × {c}` with those on `X`: there `f` is the
stalk map of the projection, flat, and `g` the stalk map of the section `x ↦ (x, c)`.

Source: Weibel, *An Introduction to Homological Algebra*, Proposition 3.2.9 and Corollary 3.2.10
(base change for `Tor`); Serre, *Algèbre locale, multiplicités*, Chapitre V, C.
HC no distance; AV milestone no distance.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HodgeLean.Adapters
universe u

section baseChange
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- `M ⊗_B (B ⊗_A Q) ≅ M ⊗_A Q`, as `A`-modules.
Source: Mathlib, `TensorProduct.AlgebraTensorModule.cancelBaseChange`; Bourbaki, *Algèbre*, II,
§5.1 (base change of tensor products). -/
def a3f_cancelIso (M : ModuleCat.{u} B) (Q : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars.{u} f).obj (M ⊗ (ModuleCat.extendScalars.{u, u, u} f).obj Q) ≅
      (ModuleCat.restrictScalars.{u} f).obj M ⊗ Q := by
  letI := f.toAlgebra
  letI : Module A M := Module.compHom M f
  haveI : IsScalarTower A B M := ⟨fun a b m => mul_smul (f a) b m⟩
  exact ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B B M Q).restrictScalars
    A).toModuleIso

theorem a3f_cancelIso_tmul (M : ModuleCat.{u} B) (Q : ModuleCat.{u} A) (m : M) (b : B) (q : Q) :
    (a3f_cancelIso f M Q).hom (m ⊗ₜ[B] (b ⊗ₜ[A] q : (ModuleCat.extendScalars.{u, u, u} f).obj Q)) =
      (show (ModuleCat.restrictScalars.{u} f).obj M from b • m) ⊗ₜ[A] q := rfl

theorem a3f_cancelIso_natural (M : ModuleCat.{u} B) {Q Q' : ModuleCat.{u} A} (g : Q ⟶ Q') :
    (ModuleCat.restrictScalars.{u} f).map (M ◁ (ModuleCat.extendScalars.{u, u, u} f).map g) ≫
        (a3f_cancelIso f M Q').hom =
      (a3f_cancelIso f M Q).hom ≫ ((ModuleCat.restrictScalars.{u} f).obj M ◁ g) := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul m y =>
    induction y using TensorProduct.inductionOn with
    | tmul b q => rfl
    | add y y' hy hy' =>
      simp only [TensorProduct.tmul_add, map_add] at hy hy' ⊢
      rw [hy, hy']
  | add x x' hx hx' =>
    simp only [map_add] at hx hx' ⊢
    rw [hx, hx']

/-- The complex `M ⊗_B (B ⊗_A C)`, restricted to `A`, is `M ⊗_A C`.
Source: Weibel, *An Introduction to Homological Algebra*, Proposition 3.2.9 (proof). -/
def a3f_complexIso (M : ModuleCat.{u} B) (C : ChainComplex (ModuleCat.{u} A) ℕ) :
    ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex _).obj
        (a3c_tensC M (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex _).obj C)) ≅
      a3c_tensC ((ModuleCat.restrictScalars.{u} f).obj M) C :=
  HomologicalComplex.Hom.isoOfComponents (fun i => a3f_cancelIso f M (C.X i))
    (fun i j _ => (a3f_cancelIso_natural f M (C.d i j)).symm)

example (M : ModuleCat.{u} B) (C : ChainComplex (ModuleCat.{u} A) ℕ) (i : ℕ) :
    (a3f_complexIso f M C).hom.f i = (a3f_cancelIso f M (C.X i)).hom := rfl

instance a3f_restrictScalars_preservesHomology :
    (ModuleCat.restrictScalars.{u} f).PreservesHomology := by
  have : (ModuleCat.restrictScalars.{u} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u, u} f).isLeftAdjoint
  have : (ModuleCat.restrictScalars.{u} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isRightAdjoint
  infer_instance

/-- Base change of `Tor` in one argument: for flat `f : A → B`,
`Tor_n^B(M, B ⊗_A N) ≅ Tor_n^A(M, N)` as `A`-modules.
Source: Weibel, *An Introduction to Homological Algebra*, Proposition 3.2.9 and
Corollary 3.2.10. -/
theorem a3f_tor_restrict (hf : f.Flat) (M : ModuleCat.{u} B) (N : ModuleCat.{u} A) (n : ℕ) :
    Nonempty ((ModuleCat.restrictScalars.{u} f).obj (((Tor (ModuleCat.{u} B) n).obj M).obj
        ((ModuleCat.extendScalars.{u, u, u} f).obj N)) ≅
      ((Tor (ModuleCat.{u} A) n).obj ((ModuleCat.restrictScalars.{u} f).obj M)).obj N) := by
  have := a3q_extendScalars_preservesHomology f hf
  let E := ModuleCat.extendScalars.{u, u, u} f
  let R := ModuleCat.restrictScalars.{u} f
  let Q := ProjectiveResolution.of N
  let Q' := E.mapProjectiveResolution Q
  exact ⟨R.mapIso (a3c_torIso M _ Q' n) ≪≫
    (((a3c_tensC M Q'.complex).sc n).mapHomologyIso R).symm ≪≫
    HomologicalComplex.homologyMapIso (a3f_complexIso f M Q.complex) n ≪≫
    (a3c_torIso _ N Q n).symm⟩

example (M : ModuleCat.{u} B) (Q : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars.{u} f).obj (M ⊗ (ModuleCat.extendScalars.{u, u, u} f).obj Q) ≅
      (ModuleCat.restrictScalars.{u} f).obj M ⊗ Q :=
  a3f_cancelIso f M Q

end baseChange

section retraction
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
  (hg : ∀ a, g (f a) = a)

include hg in
/-- On a `B`-module killed by the kernel of a retraction `g` of `f`, `B`-length and `A`-length
(through `f`) agree. -/
theorem a3f_length_eq (X : ModuleCat.{u} B)
    (hX : ∀ b ∈ RingHom.ker g, ∀ x : X, b • x = 0) :
    Module.length B X = Module.length A ((ModuleCat.restrictScalars.{u} f).obj X) := by
  let : Algebra B A := g.toAlgebra
  let : Module A X := Module.compHom X f
  have : IsScalarTower B A X := ⟨fun b a x => by
    change f (g b * a) • x = b • (f a • x)
    rw [map_mul, mul_smul, ← mul_smul b]
    have h1 : f (g b) - b ∈ RingHom.ker g := by
      rw [RingHom.mem_ker, map_sub, hg, sub_self]
    have h2 := hX _ h1 (f a • x)
    rw [sub_smul, sub_eq_zero] at h2
    rw [h2, mul_smul]⟩
  have hsurj : Function.Surjective (algebraMap B A) := fun a => ⟨f a, hg a⟩
  exact Module.length_eq_of_surjective hsurj

include hg in
theorem a3f_surjective : Function.Surjective g := fun a => ⟨f a, hg a⟩

include hg in
/-- `B ⧸ P ≅ A ⧸ g(P)` as `A`-modules for `P ⊇ ker g`.
Source: Atiyah–Macdonald, *Introduction to Commutative Algebra*, Proposition 1.1 and
Exercise 1.18 (ideals and quotients along a surjection). -/
def a3f_quotEquiv (P : Ideal B) (hP : RingHom.ker g ≤ P) :
    (ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B (B ⧸ P)) ≅
      ModuleCat.of A (A ⧸ P.map g) := by
  have hsurj := a3f_surjective f g hg
  have hle : P ≤ (P.map g).comap g := Ideal.le_comap_map
  let φ : B ⧸ P →+* A ⧸ P.map g := Ideal.quotientMap (P.map g) g hle
  have hbij : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap,
        Ideal.comap_map_of_surjective _ hsurj] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rcases Submodule.mem_sup.1 hx with ⟨p, hp, k, hk, rfl⟩
      refine P.add_mem hp (hP ?_)
      rw [RingHom.mem_ker]
      simpa using hk
    · intro y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk P (f a), by rw [Ideal.quotientMap_mk, hg]⟩
  let e : (ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B (B ⧸ P)) ≃ₗ[A] A ⧸ P.map g :=
    { toFun := φ
      invFun := Function.surjInv hbij.2
      left_inv := Function.leftInverse_surjInv hbij
      right_inv := Function.rightInverse_surjInv hbij.2
      map_add' := map_add φ
      map_smul' := fun a x => by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        change φ (Ideal.Quotient.mk P (f a * b)) = a • φ (Ideal.Quotient.mk P b)
        rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, map_mul, hg, map_mul]
        rfl }
  exact e.toModuleIso

example (P : Ideal B) (hP : RingHom.ker g ≤ P) :
    (ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B (B ⧸ P)) ≅
      ModuleCat.of A (A ⧸ P.map g) :=
  a3f_quotEquiv f g hg P hP

include hg in
/-- Lengths of `Tor` along a flat map with a retraction: for `P ⊇ ker g` and an ideal `I` of
`A`, `ℓ_B Tor_i^B(B ⧸ P, B ⧸ I B) = ℓ_A Tor_i^A(A ⧸ g(P), A ⧸ I)`.
Source: Weibel, *An Introduction to Homological Algebra*, Corollary 3.2.10; Serre, *Algèbre
locale, multiplicités*, Chapitre V, C. -/
theorem a3f_length_tor (hf : f.Flat) (P : Ideal B) (hP : RingHom.ker g ≤ P) (I : Ideal A)
    (i : ℕ) :
    Module.length B (((Tor (ModuleCat.{u} B) i).obj (ModuleCat.of B (B ⧸ P))).obj
        (ModuleCat.of B (B ⧸ I.map f))) =
      Module.length A (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ P.map g))).obj
        (ModuleCat.of A (A ⧸ I))) := by
  let := f.toAlgebra
  -- `B ⧸ I B` is the extension of scalars of `A ⧸ I`
  have eN : ModuleCat.of B (B ⧸ I.map f) ≅
      (ModuleCat.extendScalars.{u, u, u} f).obj (ModuleCat.of A (A ⧸ I)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.toModuleIso
  have hkill : ∀ b ∈ RingHom.ker g, ∀ x : ((Tor (ModuleCat.{u} B) i).obj
      (ModuleCat.of B (B ⧸ P))).obj (ModuleCat.of B (B ⧸ I.map f)), b • x = 0 := by
    intro b hb x
    refine a3c_smul_tor_eq_zero_of_mem_annihilator_left _ _ b ?_ i x
    rw [Module.mem_annihilator]
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk P (b * y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact P.mul_mem_right _ (hP hb)
  rw [a3f_length_eq f g hg _ hkill]
  obtain ⟨e⟩ := a3f_tor_restrict f hf (ModuleCat.of B (B ⧸ P)) (ModuleCat.of A (A ⧸ I)) i
  let e' := (ModuleCat.restrictScalars.{u} f).mapIso
    (((Tor (ModuleCat.{u} B) i).obj (ModuleCat.of B (B ⧸ P))).mapIso eN) ≪≫ e ≪≫
    ((Tor (ModuleCat.{u} A) i).mapIso (a3f_quotEquiv f g hg P hP)).app _
  exact e'.toLinearEquiv.length_eq

end retraction

section domain
open IsLocalRing

/-- A Noetherian local ring with a nonzerodivisor `x ∈ 𝔪` such that `R ⧸ (x)` is a domain is a
domain: a minimal prime `𝔮 ⊆ (x)` satisfies `𝔮 = x 𝔮`, so `𝔮 = 0` by Nakayama's lemma.
Source: Matsumura, *Commutative Ring Theory*, Exercise 9.11; Stacks Project, Tag 00NQ. -/
theorem a3f_isDomain_of_quotient {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular R x)
    (hdom : (Ideal.span {x}).IsPrime) : IsDomain R := by
  -- a minimal prime inside `(x)`
  obtain ⟨𝔮, h𝔮, h𝔮le⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal R) ≤ Ideal.span {x}
    from bot_le)
  have hxnzd : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_right.mpr fun y hy =>
    hreg (show x • y = x • (0 : R) by rw [smul_eq_mul, smul_eq_mul, mul_zero, mul_comm]; exact hy)
  have hx𝔮 : x ∉ 𝔮 := fun h =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h h𝔮 hxnzd
  have hq : 𝔮 ≤ Ideal.span {x} * 𝔮 := by
    intro q hq
    have : q ∈ Ideal.span {x} := h𝔮le hq
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 this
    have hr : r ∈ 𝔮 := (h𝔮.1.1.mem_or_mem hq).resolve_right hx𝔮
    rw [show r * x = x * r from mul_comm r x]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hr
  have h0 : 𝔮 = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) 𝔮
      (IsNoetherian.noetherian 𝔮) (by rwa [smul_eq_mul]) ?_
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).2 hx
  rw [h0] at h𝔮
  have : (⊥ : Ideal R).IsPrime := h𝔮.1.1
  have : IsDomain (R ⧸ (⊥ : Ideal R)) := (Ideal.Quotient.isDomain_iff_prime ⊥).mpr this
  exact (RingEquiv.quotientBot R).symm.toMulEquiv.isDomain _

end domain

section retractionPrime
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
  (hg : ∀ a, g (f a) = a) (x : B) (hreg : IsSMulRegular B x)
  (hker : RingHom.ker g = Ideal.span {x})

include hg hker in
theorem a3f_exists_div (b : B) : ∃ c, b - f (g b) = x * c := by
  have : b - f (g b) ∈ RingHom.ker g := by rw [RingHom.mem_ker, map_sub, hg, sub_self]
  rw [hker, Ideal.mem_span_singleton'] at this
  obtain ⟨c, hc⟩ := this
  exact ⟨c, by rw [← hc, mul_comm]⟩

include hg hker hreg in
/-- For a retraction `g` of `f` whose kernel is generated by a nonzerodivisor `x`, the ideal
`𝔭 B` generated by a prime `𝔭` of `A` satisfies `𝔭 B ∩ x B = x · 𝔭 B`. -/
theorem a3f_mem_of_mul_mem (𝔭 : Ideal A) (b : B) (hb : x * b ∈ 𝔭.map f) : b ∈ 𝔭.map f := by
  classical
  choose δ hδ using a3f_exists_div f g hg x hker
  have hcancel : ∀ c c' : B, x * c = x * c' → c = c' := fun c c' h => hreg h
  have hgJ : ∀ y ∈ 𝔭.map f, g y ∈ 𝔭 := by
    intro y hy
    have hle : 𝔭.map f ≤ 𝔭.comap g := Ideal.map_le_iff_le_comap.2 fun p hp => by
      rw [Ideal.mem_comap, Ideal.mem_comap, hg]
      exact hp
    exact hle hy
  have hδJ : ∀ y ∈ 𝔭.map f, δ y ∈ 𝔭.map f := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      have : δ (f p) = 0 := hcancel _ _ (by rw [← hδ, hg, sub_self, mul_zero])
      rw [this]
      exact Ideal.zero_mem _
    | zero =>
      have : δ 0 = 0 := hcancel _ _ (by rw [← hδ, map_zero, map_zero, sub_self, mul_zero])
      rw [this]
      exact Ideal.zero_mem _
    | add y y' hy hy' ihy ihy' =>
      have : δ (y + y') = δ y + δ y' := hcancel _ _ (by
        rw [← hδ, mul_add, ← hδ, ← hδ, map_add, map_add]
        ring)
      rw [this]
      exact Ideal.add_mem _ ihy ihy'
    | smul c y hy ihy =>
      have hgy : f (g y) ∈ 𝔭.map f := Ideal.mem_map_of_mem f (hgJ y hy)
      have : δ (c • y) = f (g c) * δ y + δ c * f (g y) + x * (δ c * δ y) := by
        refine hcancel _ _ ?_
        rw [← hδ, smul_eq_mul, map_mul, map_mul]
        have h1 := hδ c
        have h2 := hδ y
        linear_combination y * h1 + (f (g c) + x * δ c) * h2
      rw [this]
      exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ ihy)
        (Ideal.mul_mem_left _ _ hgy)) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ihy))
  have hxb : δ (x * b) = b := hcancel _ _ (by
    rw [← hδ, map_mul]
    have : g x = 0 := by
      have : x ∈ RingHom.ker g := by rw [hker]; exact Ideal.mem_span_singleton_self x
      exact this
    rw [this, zero_mul, map_zero, sub_zero])
  rw [← hxb]
  exact hδJ _ hb

include hg hker hreg in
/-- `𝔭 B` is prime for a prime `𝔭` of `A`, when `B` is local Noetherian and `g` is a retraction of
`f` whose kernel is generated by a nonzerodivisor `x`. -/
theorem a3f_isPrime_map [IsLocalRing B] [IsNoetherianRing B] (hx : x ∈ IsLocalRing.maximalIdeal B)
    (𝔭 : Ideal A) [h𝔭 : 𝔭.IsPrime] : (𝔭.map f).IsPrime := by
  classical
  set J := 𝔭.map f
  have hgJ : ∀ y ∈ J, g y ∈ 𝔭 := by
    intro y hy
    have hle : 𝔭.map f ≤ 𝔭.comap g := Ideal.map_le_iff_le_comap.2 fun p hp => by
      rw [Ideal.mem_comap, Ideal.mem_comap, hg]
      exact hp
    exact hle hy
  have hJtop : J ≠ ⊤ := fun h => h𝔭.ne_top (by
    rw [Ideal.eq_top_iff_one]
    have := hgJ 1 (h ▸ Submodule.mem_top)
    rwa [map_one] at this)
  have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (B ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  -- `J + (x) = g⁻¹(𝔭)`
  have hsum : J ⊔ Ideal.span {x} = 𝔭.comap g := by
    refine le_antisymm (sup_le (fun y hy => hgJ y hy) ?_) fun b hb => ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
      have : x ∈ RingHom.ker g := by rw [hker]; exact Ideal.mem_span_singleton_self x
      rw [RingHom.mem_ker.1 this]
      exact 𝔭.zero_mem
    · obtain ⟨c, hc⟩ := a3f_exists_div f g hg x hker b
      have : b = f (g b) + x * c := by rw [← hc]; ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.mem_map_of_mem f hb) (Ideal.mul_mem_right _ _
        (Ideal.mem_span_singleton_self x))
  -- the image of `x` in `B ⧸ J`
  set x' := Ideal.Quotient.mk J x
  have hx' : x' ∈ IsLocalRing.maximalIdeal (B ⧸ J) := by
    have : IsLocalHom (Ideal.Quotient.mk J) := .of_surjective _ Ideal.Quotient.mk_surjective
    rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk J)] at hx
    exact hx
  have hreg' : IsSMulRegular (B ⧸ J) x' := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change Ideal.Quotient.mk J (x * a) = Ideal.Quotient.mk J (x * b) at hab
    rw [Ideal.Quotient.eq, ← mul_sub] at hab
    rw [Ideal.Quotient.eq]
    exact a3f_mem_of_mul_mem f g hg x hreg hker 𝔭 _ hab
  have hprime : (Ideal.span {x'}).IsPrime := by
    have : Ideal.span {x'} = (𝔭.comap g).map (Ideal.Quotient.mk J) := by
      rw [← hsum, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span,
        Set.image_singleton]
    rw [this]
    refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker]
    exact le_sup_left.trans hsum.le
  have hdom := a3f_isDomain_of_quotient x' hx' hreg' hprime
  exact (Ideal.Quotient.isDomain_iff_prime J).mp hdom

end retractionPrime

end HodgeLean.Adapters
