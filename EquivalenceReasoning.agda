{-# OPTIONS --type-in-type #-}
module EquivalenceReasoning where
open import Data.Product
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality
open import lib.Equivalences


_≅_ : (A B : Set) → Set₁
_≅_ = _≃_

con' : ∀ {A B} → (coe : A → B) → (inv : B → A) → (∀ b → coe (inv b) ≡ b) → (∀ b → inv (coe b) ≡ b) → A ≅ B
con' coe inv eq eq' = coe , is-eq coe inv eq eq'

module _≅_ {A B : Set} (A≅B : A ≅ B) where


  coe : A → B
  coe = –> A≅B
  inv : B → A
  inv = <– A≅B

  coeinv' : ∀ b → coe (inv b) ≡ b
  coeinv' = <–-inv-r A≅B
  invcoe' : ∀ a → inv (coe a) ≡ a
  invcoe' = <–-inv-l A≅B
  coeinv = \ {a} → coeinv' a
  invcoe = \ {a} → invcoe' a

con : ∀ {A B : Set} → (coe : A → B) → (inv : B → A) → (∀ {b} → coe (inv b) ≡ b) → (∀ {b} → inv (coe b) ≡ b) → A ≅ B
con = \ x y z w → con' x y (\ _ → z) (\ _ → w)


isosetoid : Setoid _ _
isosetoid = record { Carrier = Set ; _≈_ = _≅_
                   ; isEquivalence = record { refl = λ {x} → con (λ z → z) (λ z → z) refl refl
                                            ; sym = λ x → let open _≅_ x in con inv coe invcoe coeinv
                                            ; trans = λ x y →
                                                          let module x = _≅_ x
                                                              module y = _≅_ y
                                                          in con (λ z → _≅_.coe y (_≅_.coe x z))
                                                             (λ z → _≅_.inv x (_≅_.inv y z))
                                                             (trans (cong y.coe x.coeinv) y.coeinv)
                                                             (trans (cong x.inv y.invcoe) x.invcoe) } }

open EqR isosetoid public
