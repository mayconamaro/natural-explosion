-- This proof was written by Maycon Amaro from Federal University of Ouro Preto in Brazil
-- This was motivated by the studies of PLFA book, in particular chapter 4 - Equality
module NaturalExplosion where

  -- Here I prove that, if 0 is equal 1, then all naturals are the same number

  -- A definition for Naturals
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  -- A definition for equality
  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

  infix 4 _≡_

  -- Equality is transitive
  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  -- Equality is congruent
  cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl

  -- Equality is symmetric
  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  -- Reasoning over equality
  module ≡-Reasoning {A : Set} where
    infix  1 begin_
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_
    infix  3 _∎

    begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
    begin x≡y = x≡y

    _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
    g ≡⟨⟩ x≡y = x≡y

    _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
    g ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

    _∎ : ∀ (x : A) → x ≡ x
    x ∎ = refl

  open ≡-Reasoning

  -- If 0 ≡ 1 then every natural is equal to their successor
  succ-explosion : ∀ (n : ℕ) → zero ≡ suc zero → n ≡ suc n
  succ-explosion zero 0≡1 = 0≡1
  succ-explosion (suc n) 0≡1 =
    begin
      suc n
    ≡⟨ cong suc (succ-explosion n 0≡1) ⟩
      suc (suc n)
    ∎

  -- If 0 ≡ 1 then every natural is zero
  explosion : ∀ (n : ℕ) → zero ≡ suc zero → n ≡ zero
  explosion zero 0≡1 = refl
  explosion (suc n) 0≡1 =
    begin
      suc n
    ≡⟨ sym (succ-explosion n 0≡1) ⟩
      n
    ≡⟨ explosion n 0≡1 ⟩
      zero
    ∎

  -- If 0 ≡ 1 then every natural is equal to every natural
  natural-explosion : ∀ (m n : ℕ) → zero ≡ suc zero → m ≡ n
  natural-explosion m n 0≡1 = trans (explosion m 0≡1) (sym (explosion n 0≡1))
