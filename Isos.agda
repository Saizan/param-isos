{-# OPTIONS --rewriting --type-in-type #-}
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Unit hiding (_≤_)

_+_ : Set → Set → Set
A + B = Σ Bool \ b → if b then A else B

open import lib.Equivalences
open import lib.Funext
open import lib.types.Sigma
open import lib.types.Pi

open import EquivalenceReasoning

-- Shape modality with definitional β rule.
postulate
  isDisc : Set → Set
  ∫ : Set → Set
  inc : ∀ {A : Set} → A → ∫ A
  elim∫ : ∀ {A : Set} {B : ∫ A → Set} {{bd : ∀ ∫a → isDisc (B ∫a)}} (f : ∀ a → B (inc a)) → ∀ ∫a → B ∫a
  elim∫-β : ∀ {A : Set} {B : ∫ A → Set} {{bd : ∀ ∫a → isDisc (B ∫a)}} (f : ∀ a → B (inc a)) → ∀ a → elim∫ {{bd}} f (inc a) ≡ f a

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE elim∫-β #-}

-- Discreteness for quantifiers.
instance
 postulate
  ∫-disc : ∀ {A : Set} → isDisc (∫ A)
  Bool-disc : isDisc Bool
  Pi-disc : ∀ {A : Set} {B : A → Set} (bd : ∀ a → isDisc (B a)) → isDisc ((a : A) -> B a)
  Σ-disc : ∀ {A : Set} {B : A -> Set} → (ad : isDisc A) → (bd : ∀ a → isDisc (B a)) → isDisc (Σ A B)
  ≡-disc : ∀ {A : Set} → isDisc A → ∀ {x y : A} → isDisc (x ≡ y)


-- Time as an abstract ordered type.
postulate
  Time : Set
  `0 : Time
  _≤_ : Time → Time → Set
  su : Time → Time
  su≤ : ∀ i → i ≤ su i
  max : Time → Time → Time
  max-fst : ∀ {i j} → i ≤ max i j
  max-snd : ∀ {i j} → j ≤ max i j
  refl≤ : ∀ i → i ≤ i

_<_ : Time → Time → Set
j < i = su j ≤ i

-- Both Time and _<_ are codiscrete so they are propositional under ∫.
-- Can ∫≤ and ∫≤≤ be derived from a simpler postulate about _<_ ?
postulate
  Time-codisc : ∀ (i j : ∫ Time) → i ≡ j
  ∫≤ : ∀ {j} → (x y : ∫ (Σ Time \ i → j < i)) → x ≡ y
  ∫≤≤ : ∀ {ja jb} → (x y : ∫ (Σ Time \ i → ja < i × jb < i)) → x ≡ y


-- Existential on Time.
∃i : (Time → Set) → Set
∃i A = ∫ (Σ Time A)

pack : ∀ {A : Time → Set} i → A i → ∃i A
pack i a = inc (i , a)

unpack : ∀ {A : Time -> Set} {B : ∃i A → Set} {{bd : ∀ ∫a → isDisc (B ∫a)}} (f : ∀ i a → B (pack i a)) → ∀ ∫a → B ∫a
unpack {{bd}} f = elim∫ {{bd}} (uncurry f)


-- Isomorphisms, scroll down to Summary for the final results.

∫≅ : {A B : Set} → A ≅ B → ∫ A ≅ ∫ B
∫≅ iso = con' (elim∫ (λ a → inc (iso.coe a))) (elim∫ (λ a → inc (iso.inv a)))
              (elim∫ (λ a → cong inc iso.coeinv))
              (elim∫ (λ a → cong inc iso.invcoe))
  where
   module iso = _≅_ iso

module Sigma2 {A : Set} {B C : A → Set} (B≅C : ∀ {a} → B a ≅ C a) where

  Σ≅ : Σ A B ≅ Σ A C
  Σ≅ = con (λ x → (proj₁ x) , B≅C.coe (proj₂ x)) (λ x → (proj₁ x) , (B≅C.inv (proj₂ x))) (cong (_,_ _) B≅C.coeinv) (cong (_,_ _) B≅C.invcoe)
   where
    module B≅C {a} = _≅_ (B≅C {a})

fromEq : {A B : Set} (eq : A ≡ B) → A ≅ B
fromEq refl = con (λ z → z) (λ z → z) (λ {b} → refl) (λ {a} → refl)

module SigmaΠ {X : Set} {A : X → Set} {B : (x : X) → A x -> Set} where

  iso : Σ ((x : X) → A x) (λ f → ∀ i → B i (f i)) ≅ ∀ i → Σ (A i) (B i)
  iso = con (λ x i → proj₁ x i , proj₂ x i) (λ x → (λ x₁ → proj₁ (x x₁)) , (λ i → proj₂ (x i))) refl refl

module Sigma∫ {A : Set} {B : A -> Set} where

  iso : (Ad : isDisc A) → Σ A (λ a → ∫ (B a)) ≅ ∫ (Σ A B)
  iso Ad = con' conv conv- iso2 iso1
    where
      X = Σ A \ a → ∫ (B a)
      Y = ∫ (Σ A B)

      conv : X -> Y
      conv (a , ∫b) = elim∫ (λ b → inc (a , b)) ∫b

      conv- : Y -> X
      conv- = elim∫ (λ a → (proj₁ a) , (inc (proj₂ a)))

      iso1 : ∀ x → conv- (conv x) ≡ x
      iso1 (a , ∫b) = elim∫ {B = \ b → let x = a , b in conv- (conv x) ≡ x} (λ a₁ → refl) ∫b

      iso2 : ∀ x → conv (conv- x) ≡ x
      iso2 = elim∫ (λ _ → refl)


  iso' : ∫ (Σ A λ a → ∫ (B a)) ≅ ∫ (Σ A B)
  iso' = con' conv conv- iso2 iso1
    where
      X = ∫ (Σ A \ a → ∫ (B a))
      Y = ∫ (Σ A B)

      conv : X -> Y
      conv = elim∫ (λ { (a , ∫b) → elim∫ (λ b → inc (a , b)) ∫b })

      conv- : Y -> X
      conv- = elim∫ (λ a → inc (proj₁ a , inc (proj₂ a)))

      iso1 : ∀ x → conv- (conv x) ≡ x
      iso1 = elim∫ (uncurry (λ a → elim∫ (λ b → refl)))

      iso2 : ∀ x → conv (conv- x) ≡ x
      iso2 = elim∫ (λ _ → refl)


module ∀Disc {A : Set} (Ad : isDisc A) {I : Set} (i : I) (codisc : ∀ (x y : ∫ I) → x ≡ y) where

  iso : A ≅ (I → A)
  iso = con (λ z _ → z) (λ x → x i) (\ {f} → λ= (λ x → cong (elim∫ f) (codisc (inc i) (inc x)))) refl

module Top {I : Set} (i : I)(codisc : ∀ (x y : ∫ I) → x ≡ y) where
  iso : ⊤ ≅ ∫ I
  iso = con (λ x → inc i) _ (codisc _ _) refl


module Plus where

  iso∃i : {A B : Time -> Set} → ((∃i \ i → A i) + (∃i \ j → B j)) ≅ ∃i \ i → A i + B i
  iso∃i {A} {B} = begin
   (∃i (λ i → A i) + ∃i (λ j → B j))                      ≈⟨ Sigma2.Σ≅ (\ { {true} → fromEq refl; {false} → fromEq refl}) ⟩
   Σ Bool (λ b → ∫ (Σ Time λ i → if b then A i else B i)) ≈⟨ Sigma∫.iso Bool-disc ⟩
   ∫ (Σ Bool λ b →  Σ Time λ i → if b then A i else B i)  ≈⟨ shuffling ⟩
   (∃i \ i → A i + B i)                                   ∎

   where
     shuffling = ∫≅ (con (λ x → let b , i , y = x in i , b , y)
                         (λ x → let i , b , y = x in b , i , y) refl refl)

  iso∀i : {A B : Time -> Set} → ((∀ i → A i) + (∀ j → B j)) ≅ ∀ i → A i + B i
  iso∀i {A} {B} = begin
             ((∀ i → A i) + (∀ j → B j))                            ≈⟨ Sigma2.Σ≅ (\ { {true} → fromEq refl; {false} → fromEq refl}) ⟩
             Σ Bool (λ b → ∀ i → if b then A i else B i)            ≈⟨ equiv-Σ' (∀Disc.iso Bool-disc `0 Time-codisc) (\ _ → fromEq refl) ⟩
             Σ (Time → Bool) (λ f → ∀ i → if f i then A i else B i) ≈⟨ SigmaΠ.iso ⟩
             (∀ i → A i + B i)                                      ∎



module Force∀ {A : Time → Set} (Ad : ∀ {i} → isDisc (A i)) where

  iso : (∀ j → A j) ≅ (∀ i → ∀ j → su j ≤ i → A j)
  iso = begin (∀ j → A j)                      ≈⟨ equiv-Π-r (λ x → ∀Disc.iso Ad ((su x) , refl≤ _) ∫≤) ⟩
              (∀ j → (∃ \ i → su j ≤ i) → A j) ≈⟨ con (λ z i j z₁ → z j (i , z₁)) (λ x j x₁ → x (proj₁ x₁) j (proj₂ x₁)) refl refl ⟩
              (∀ i → ∀ j → su j ≤ i → A j)     ∎

Time⊤ : ∫ Time ≅ ⊤
Time⊤ = con _ (λ x → inc `0) refl (Time-codisc (inc `0) _)

∫× : {A B : Set} → ∫ (A × B) ≅ (∫ A × ∫ B)
∫× = con' (elim∫ (λ a → (inc (proj₁ a)) , (inc (proj₂ a))))
          (uncurry (elim∫ (λ a → elim∫ (λ a₁ → inc (a , a₁)))))
          staging-unification
          (elim∫ (λ a → refl))
  where staging-unification = (uncurry (elim∫ (λ a → elim∫ (λ b → refl))))


∫Disc : {A : Set} (Ad : isDisc A) → ∫ A ≅ A
∫Disc Ad = con' (elim∫ (λ a → a)) inc (\ _ →  refl) (elim∫ (λ _ → refl))

module ∃Disc {A : Set} (Ad : isDisc A) where

  iso : ∃i (\_ → A) ≅ A
  iso = begin  ∫ (Time × A)   ≈⟨ ∫× ⟩
               (∫ Time × ∫ A) ≈⟨ equiv-Σ' Time⊤ (\ _ → ∫Disc Ad) ⟩
               (⊤ × A)        ≈⟨ con proj₂ (_,_ tt) refl refl ⟩
               A              ∎

module Force∃ {A : Time → Set} (Ad : ∀ {i} → isDisc (A i)) where

  iso : (∃i \ j → A j) ≅ (∃i \ i → ∃i \ j → su j ≤ i × A j)
  iso = begin (∃i \ j → A j)                           ≈⟨ ∫≅ (Sigma2.Σ≅ (con (_,_ tt) proj₂ refl refl)) ⟩
              (∃i \ j → ⊤ × A j)                       ≈⟨ ∫≅ (Sigma2.Σ≅ (equiv-Σ-fst _ (proj₂ (Top.iso (_ , (su≤ _)) ∫≤)))) ⟩
              (∃i \ j → ((∃i \ i → su j ≤ i) × A j))   ≈⟨ shuffling ⟩
              (∃i \ i → ∃i \ j → su j ≤ i × A j)       ∎
   where
    shuffling = con' (unpack (λ x → uncurry (elim∫ (λ p y → let a , b = p in inc (a , (inc (x , (b , y))))))))
                     (unpack (λ x → elim∫ (λ p → let a , b , c = p in inc (a , ((inc (x , b)) , c)))))
                     (unpack (λ x → elim∫ (λ a → refl)))
                     (unpack (λ x → uncurry (elim∫ (λ a y → refl))))

module Prod∃ {A B : Time → Set} where

  iso : ((∃i \ i → A i) × (∃i \ i → B i)) ≅ (∃i \ i → (∃i \ j → j < i × A j) × (∃i \ j → j < i × B j))
  iso = begin ((∃i \ i → A i) × (∃i \ i → B i))                              ≈⟨ shuffling ⟩
              (∃i \ ja → ∃i \ jb → ⊤ × A ja × B jb)                          ≈⟨ ∫≅ (Sigma2.Σ≅ (∫≅ (Sigma2.Σ≅
                                                                                 (equiv-Σ-fst _ (proj₂ Times-codisc))))) ⟩
              (∃i \ ja → ∃i \ jb → (∃i \ i → ja < i × jb < i) × A ja × B jb) ≈⟨ shuffling2 ⟩
              (∃i \ i → (∃i \ j → j < i × A j) × (∃i \ j → j < i × B j))     ∎
   where
     Times-codisc : ∀ {ja jb} → ⊤ ≅ (∃i \ i → ja < i × jb < i)
     Times-codisc = Top.iso ((max _ _) , max-fst , max-snd) ∫≤≤
     shuffling = con' (uncurry (unpack (λ ia a → unpack (λ ib b → inc (ia , (inc (ib , (tt , (a , b)))))))))
                      (unpack (λ ja → unpack (λ jb → λ x → (inc (ja , proj₁ (proj₂ x))) , inc (jb , proj₂ (proj₂ x)))))
                      (unpack (λ ja → unpack (λ jb → λ x → refl)))
                      (uncurry (unpack  (λ ia a → unpack (λ ib b → refl))))
     shuffling2 = con' (unpack (\ ja → unpack (λ jb → uncurry (unpack
                               (λ i a y → pack i ((pack ja (proj₁ a , proj₁ y)) , (pack jb (proj₂ a , proj₂ y))))))))
                       (unpack (λ i → uncurry (unpack
                               (λ ja a → unpack (λ jb b → pack ja (pack jb ((pack i ((proj₁ a) , (proj₁ b))) , ((proj₂ a) , (proj₂ b)))))))))
                       (unpack
                          (λ i → uncurry (unpack (λ ja a → unpack (λ jb b → refl)))))
                       (unpack
                          (λ ja → unpack (λ jb → uncurry (unpack (λ i a y → refl)))))

module Sigma∃ {A : Set} (Ad : isDisc A) {B : Time → A → Set} where
  iso : Σ A (\ a → ∃i \ i → B i a) ≅ ∃i (\ i → Σ A (B i))
  iso = begin (Σ A \ a → ∃i \ i → B i a) ≈⟨ Sigma∫.iso Ad ⟩
              ∫ (Σ A (\ a → Σ Time \ i → B i a)) ≈⟨ ∫≅ shuffling  ⟩
              ∃i (\ i → Σ A (B i)) ∎
    where
     shuffling = con (λ x → _ , (_ , (proj₂ (proj₂ x)))) (λ x → _ , (_ , (proj₂ (proj₂ x)))) refl refl

module ∃Swap {A : Time → Time → Set} where
  iso : (∃i \ i → ∃i \ j → A i j) ≅ (∃i \ j → ∃i \ i → A i j)
  iso = con' (unpack (λ i → unpack (λ j a → pack j (pack i a))))
             (unpack (λ j → unpack (λ i a → pack i (pack j a))))
             (unpack (λ j → unpack (λ i a → refl)))
             (unpack (λ i → unpack (λ j a → refl)))


module Summary where

  Sigma∫ : {A : Set} {B : A -> Set} (Ad : isDisc A) →                                         Σ A (λ a → ∫ (B a)) ≅ ∫ (Σ A B)
  Sigma∫ = Sigma∫.iso

  ∀Disc : {A : Set} (Ad : isDisc A) →                                                                           A ≅ (∀ i → A)
  ∀Disc Ad = ∀Disc.iso Ad `0 Time-codisc

  ∃Disc : {A : Set} (Ad : isDisc A) →                                                                         ∃i (\_ → A) ≅ A
  ∃Disc = ∃Disc.iso

  Plus∃ : {A B : Time -> Set} →                                        ((∃i \ i → A i) + (∃i \ j → B j)) ≅ ∃i \ i → A i + B i
  Plus∃ = Plus.iso∃i

  Plus∀ : {A B : Time -> Set} →                                                 ((∀ i → A i) + (∀ j → B j)) ≅ ∀ i → A i + B i
  Plus∀ = Plus.iso∀i

  Force∀ : {A : Time → Set} (Ad : ∀ {i} → isDisc (A i)) →                          (∀ j → A j) ≅ (∀ i → ∀ j → su j ≤ i → A j)
  Force∀ = Force∀.iso

  Force∃ : {A : Time → Set} (Ad : ∀ {i} → isDisc (A i)) →                 (∃i \ j → A j) ≅ (∃i \ i → ∃i \ j → su j ≤ i × A j)
  Force∃ = Force∃.iso

  Prod∀ : {A B : Time -> Set} →                                                 ((∀ i → A i) × (∀ j → B j)) ≅ ∀ i → A i × B i
  Prod∀ = SigmaΠ.iso

  Prod∃ : {A B : Time → Set} → ((∃i \ i → A i) × (∃i \ i → B i)) ≅ (∃i \ i → (∃i \ j → j < i × A j) × (∃i \ j → j < i × B j))
  Prod∃ = Prod∃.iso

  Sigma∃ : {A : Set} (Ad : isDisc A) {B : Time → A → Set} →                 Σ A (\ a → ∃i \ i → B i a) ≅ ∃i (\ i → Σ A (B i))
  Sigma∃ = Sigma∃.iso

  ∃Swap : {A : Time → Time → Set} →                                     (∃i \ i → ∃i \ j → A i j) ≅ (∃i \ j → ∃i \ i → A i j)
  ∃Swap = ∃Swap.iso
