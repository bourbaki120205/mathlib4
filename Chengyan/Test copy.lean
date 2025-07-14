import Mathlib
open Ideal Padic Nat
open scoped algebraMap

theorem pow_eq_ex_eq {L : Type*} [Field L] (ζ : L) (n : ℕ) [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    {a b : ℤ} : ζ ^ a = ζ ^ b ↔ (a:ZMod n) = (b:ZMod n) := by
  constructor
  · rintro h
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
    have h1:ζ^((b-a)) =1 := by
      rw [zpow_sub₀ hζ0,div_eq_one_iff_eq (zpow_ne_zero _ hζ0)]
      simp only[h]
    have h3: (n:Int) ∣ (b - a) := by
      rwa [hζ.zpow_eq_one_iff_dvd] at h1
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub a b n).mpr h3
  · rintro h
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
    rw[←div_eq_one_iff_eq (zpow_ne_zero _ hζ0),←zpow_sub₀ hζ0,hζ.zpow_eq_one_iff_dvd]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub b a n).mp (id (Eq.symm h))

theorem pow_eq_ex_eq' {L : Type*} [Field L] (ζ : L) (n : ℕ) [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    {a b : ℕ} : ζ ^ a = ζ ^ b ↔ (a:ZMod n) = (b:ZMod n) := by
    convert pow_eq_ex_eq ζ n hζ (a := a) (b := b) <;> simp

lemma isDomain_of_faithfulSMul (B L : Type*) [CommRing B] [CommRing L] [IsDomain L]
    [Algebra B L] [FaithfulSMul B L] : IsDomain B :=
  Function.Injective.isDomain (algebraMap B L) <| by
  rwa [← faithfulSMul_iff_algebraMap_injective B L]

lemma faithfulSMul_of_isIntegralClosure (A B L : Type*) [CommRing A] [CommSemiring B] [CommRing L]
    [Algebra A L] [Algebra B L] [IsIntegralClosure B A L] : FaithfulSMul B L where
  eq_of_smul_eq_smul {b₁ b₂} h := by
    apply IsIntegralClosure.algebraMap_injective B A L
    simp [Algebra.algebraMap_eq_smul_one, h 1]

lemma eqv_zero (L B : Type*) (a : ℕ) [CommRing B] [CommRing L] [Algebra B L]
    [FaithfulSMul B L] : NeZero (a : L) ↔ NeZero (a : B) := by
  simp only [neZero_iff, ne_eq, show (a : L) = (algebraMap B L (a : B)) by simp,
    FaithfulSMul.algebraMap_eq_zero_iff B L]

lemma algclosure_HasEnoughRootOfUnity (L K :Type*)(n:ℕ)[Field K]
[Field L][Algebra K L] [IsAlgClosure K L][NeZero (n:L)]:
 HasEnoughRootsOfUnity L n := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  exact IsSepClosed.hasEnoughRootsOfUnity L n

lemma pow_not_in {B : Type*} [CommRing B](I : Ideal B) [hI : I.IsMaximal]
 (l : ℕ) (hlp : ↑l ∉ I): ∀i:ℕ , ↑(l^i) ∉ I := by
  have primeI: I.IsPrime := hI.isPrime
  by_contra hi
  simp[← mem_radical_iff,IsPrime.radical primeI] at hi
  exact hlp hi

lemma neZero_B {B : Type*} [CommRing B]{I : Ideal B}(l : ℕ)(hlp : ↑l ∉ I):NeZero (l:B):=by
  rw[neZero_iff]
  aesop

lemma neZero_pow_B {B : Type*} [CommRing B][IsDomain B]{I : Ideal B}(l : ℕ)(hlp : ↑l ∉ I):
  ∀ (i:ℕ),NeZero (((l^i):ℕ):B) := by
  have:= neZero_B l hlp
  have h0: ∀ (i:ℕ),NeZero ((l^i):B):= by
    exact fun i => NeZero.pow
  intro i
  simp_all only [cast_pow]

variable

    {A K : Type*} [CommRing A] [Field K]
    -- let L be an algebraic closure of K
    {L : Type*} [Field L] [Algebra K L][IsAlgClosure K L]
    [Algebra A L]
    -- and let B be the integral closure of A in L
    {B : Type*} [CommRing B] [Algebra B L]
    [Algebra A B]
    [IsIntegralClosure B A L]
    -- Let G be the Galois group of L/K
    variable {G : Type*} [Group G] [MulSemiringAction G L] [MulSemiringAction G B]
    [SMulCommClass G A B] [IsScalarTower G B L]
    -- Let F be an element of G
    (F : G)
    -- Let I be a maximal ideal of B
    (I : Ideal B) (hI : I.IsMaximal)
    -- assume F is a Frobenius element at I
    (hF : IsArithFrobAt A F I)
    -- Then for a prime ell not in I...
    (l : ℕ) [Fact (Nat.Prime l)](hlp : ↑l ∉ I)

-- the value of the cyclotomic character at Frob_I is #A/PA where P = I ∩ A
include A B L hlp in
omit [Algebra A B] [Fact (Nat.Prime l)] in
lemma neZero_pow_L [IsDomain B] :∀ (i:ℕ),NeZero (((l^i):ℕ):L) := by
  have := faithfulSMul_of_isIntegralClosure A B L
  convert neZero_pow_B l hlp
  exact eqv_zero L B _

lemma foo1 {n : ℕ} (ζ' : B) (ζ : L) [FaithfulSMul B L](hζ'ζ : algebraMap B L ζ' = ζ) (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot ζ' n :=
  IsPrimitiveRoot.of_map_of_injective (by rwa [hζ'ζ])
    (FaithfulSMul.algebraMap_injective B L)

lemma foo2 {n : ℕ} (ζ' : B) (ζ : L) [FaithfulSMul B L](hζ'ζ : algebraMap B L ζ' = ζ) (hζ' : IsPrimitiveRoot ζ' n) :
    IsPrimitiveRoot ζ n := by
  have := IsPrimitiveRoot.map_of_injective hζ'
    (FaithfulSMul.algebraMap_injective B L)
  rwa[hζ'ζ] at this

open Polynomial in
lemma isIntegral_of_roots{n:ℕ} (hpos:0 < n) {ζ:L}(hζ:ζ^n=1): IsIntegral ℤ (ζ:L) := by
  use X ^ n - 1
  constructor
  · exact monic_X_pow_sub_C 1 (Nat.ne_of_lt hpos).symm
  · simpa [sub_eq_zero]

include A in
omit [Algebra A B]  in
lemma ext_algmap {n:ℕ} (hpos: 0 < n) {ζ:L}(hζ:ζ^n=1):
 ∃ζ':B, algebraMap B L ζ'=ζ := by
  have:= isIntegral_of_roots hpos hζ
  have integral_A: IsIntegral A (ζ:L) := IsIntegral.tower_top this
  rw [IsIntegralClosure.isIntegral_iff (A := B)] at integral_A
  exact integral_A

def mapRootsOfUnity {n:ℕ} :rootsOfUnity n B →* rootsOfUnity n L where
  toFun := fun ζ ↦ ⟨Units.map (algebraMap B L) ζ.1 , by
    simpa using congr(Units.map (algebraMap B L).toMonoidHom $(ζ.2))⟩
  map_one' := by simp_all only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one]
  map_mul' := by aesop

def unitsOfPow {R : Type*} [Semiring R] {n : ℕ} (hpos : 0 < n) {x : R}
    (hx : x ^ n = 1) : Rˣ where
  val := x
  inv := x^(n-1)
  val_inv := (by rw [←hx, mul_pow_sub_one (by omega)])
  inv_val := (by rw [←hx, pow_sub_one_mul (by omega)])

variable (A L B) in
noncomputable def rootIso {n:ℕ}(hpos:0<n) :rootsOfUnity n B ≃* rootsOfUnity n L :=
  .ofBijective mapRootsOfUnity <| by
    have inj:= (faithfulSMul_of_isIntegralClosure A B L).algebraMap_injective
    constructor
    · rintro ⟨a, _⟩ ⟨b, _⟩
      simp [mapRootsOfUnity, Units.ext_iff, inj.eq_iff]
    · rintro ⟨ζ,hζ⟩
      simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one] at hζ
      obtain ⟨ζ',hζ'ζ⟩:= ext_algmap (A:=A) (B:=B) hpos hζ
      have hζ':ζ'^n=1 := inj (by simpa [hζ'ζ] using hζ)
      use ⟨unitsOfPow hpos hζ',by simpa [Units.ext_iff] using hζ'⟩
      simpa [mapRootsOfUnity,Units.ext_iff]


lemma intclo_HasEnoughRootOfUnity {A : Type u_1} [CommRing A] {L : Type u_3}
  [Field L] [Algebra A L] [IsAlgClosed L] {B : Type u_4} [CommRing B] [Algebra B L]
  [IsIntegralClosure B A L] (n : ℕ) [NeZero (n:B)] :  HasEnoughRootsOfUnity B n :=by
  have inj:= faithfulSMul_of_isIntegralClosure A B L
  have : NeZero (n:L):= by
    rw[eqv_zero L B n ]
    simp_all only
  have hpos: 0 < n := by exact NeZero.pos_of_neZero_natCast B
  have := IsSepClosed.hasEnoughRootsOfUnity L n
  obtain ⟨⟨ζ,hζ⟩,cyc⟩ := this
  have foo: ∃ζ':B, algebraMap B L ζ'=ζ := ext_algmap (A:=A) hpos hζ.pow_eq_one
  obtain ⟨ζ',hζ'⟩:= foo
  have fooo: IsPrimitiveRoot ζ' n :=foo1 ζ' ζ hζ' hζ
  constructor
  ·use ζ'
  · let f : rootsOfUnity n L ≃* rootsOfUnity n B := (rootIso A L B hpos).symm
    exact isCyclic_of_surjective f f.surjective

include hI hlp A K L
omit [Algebra A B] hI [Fact (Nat.Prime l)] in
variable (A L B K) in
lemma enough_pow_root_L [IsDomain B] : ∀ (i : ℕ), HasEnoughRootsOfUnity L (l ^ i):=by
    intro i
    have := neZero_pow_L I l hlp i (A:=A) (B:=B) (L:=L)
    exact algclosure_HasEnoughRootOfUnity L K (l^i)

omit [Algebra A B] hI [Fact (Nat.Prime l)] in
variable (A L B K) in
lemma enough_pow_root_B [IsDomain B]: ∀ (i : ℕ), ∃ ζ : B,IsPrimitiveRoot ζ (l ^ i):= by
    intro i
    have:= neZero_pow_B l hlp i
    have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
    have foo := intclo_HasEnoughRootOfUnity (l^i) (B := B) (A := A) (L := L)
    exact HasEnoughRootsOfUnity.prim

include hI hF B L
theorem cyclo_thing:
  ((cyclotomicCharacter L l (MulSemiringAction.toRingEquiv G L F)) : ℤ_[l]) =
  Nat.card (A ⧸ I.under A) := by
  set q:= ↑(Nat.card (A ⧸ under A I))
  set g:= (MulSemiringAction.toRingEquiv G L F)
  rw[← PadicInt.ext_of_toZModPow]
  intro i
  have := faithfulSMul_of_isIntegralClosure A B L
  have := isDomain_of_faithfulSMul B L
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have := enough_pow_root_L A K L B I l hlp
  simp
  obtain ⟨ζ,hζ⟩ := enough_pow_root_B A K L B I l hlp i
  have foo: (ζ:L)= algebraMap B L (ζ:B):= rfl
  have hζ': IsPrimitiveRoot (ζ:L) (l ^ i):= foo2 (ζ:B) (ζ:L) foo hζ

  have good_Andrew : g ζ = (ζ ^ q : B) := by
    have tauto: (F • ζ : B) = g ζ := algebraMap.coe_smul G B L F ζ
    rw [←tauto, ←AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF hζ.pow_eq_one (pow_not_in I l hlp i)]
    simp
  have pow_eq: (ζ:L)^q = ζ^( (cyclotomicCharacter L l g).val.toZModPow i).val := by
    rw[← cyclotomicCharacter.spec l g ↑ζ hζ'.pow_eq_one,good_Andrew]
    exact Eq.symm (algebraMap.coe_pow ζ q)
  rw[pow_eq_ex_eq' (ζ:L) (l^i) hζ' (a := q)
    (b := ((cyclotomicCharacter L l g).val.toZModPow i).val)] at pow_eq
  simp at pow_eq
  exact id (Eq.symm pow_eq)
