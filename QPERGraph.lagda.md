```agda
open import GraphProject

-- _×_ and _⊎_ and ⊤ and ⊥
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit

-- ℕ
open import Data.Nat
import Data.Nat.Properties as Nat

-- List
open import Data.List as List using (List; []; _∷_; _++_; [_]; reverse; _∷ʳ_; lookup; filter)
import Data.List.Properties as List

-- _≡_
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; module ≡-Reasoning)

open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Relation.Nullary.Negation
open import Data.Fin using (Fin)
open import Relation.Nullary.Decidable using (yes; no)
```


We define a QPER that represents a relation between two implementations of a graph.

```agda
record QPERGraph (g : Set) (g' : Set) (G : Graph ℕ g) (G' : Graph ℕ g') : Set₂ where
  field
      R : (M : g) (M' : g') → Set
      zzc : {M N : g} {M' N' : g'} → R M M' → R N N' → R N M' → R M N' 
```
