# Problem Set 4

In this homework, we'll reason about "free theorems" that come with ∀ types, and representation independence that comes with ∃ types.

Here's the key for tasks:
- 🟢 Required for everyone
- 🟡 Required for grad students, bonus for undergrads
- 🔴 Bonus for everyone

We start the module off by importing some types from the standard library and redefining the `QPER` machinery from the previous problem set:
```agda
module GraphProject where

-- ⊤ and _×_
open import Data.Unit
open import Data.Product

-- ⊥ and _+_ and Bool
open import Data.Empty
open import Data.Sum
open import Data.Bool

-- ℕ
open import Data.Nat
import Data.Nat.Properties as Nat

-- List
open import Data.List as List using (List; []; _∷_; _++_; [_]; reverse; _∷ʳ_; lookup; filter)
import Data.List.Properties as List

-- _≡_
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

record QPER (A B : Set) : Set₁ where
  field
    R : (a : A) (b : B) → Set
    zzc : {a a' : A} {b b' : B} → R a b → R a' b' → R a' b → R a b'
open QPER public

variable
  A B A' B' : Set

infixr 2 _Q×_
_Q×_ : (qper₁ : QPER A B) (qper₂ : QPER A' B') → QPER (A × A') (B × B')
R (qper₁ Q× qper₂) (a , a') (b , b') = R qper₁ a b × R qper₂ a' b'
proj₁ (zzc (qper₁ Q× qper₂) h₁ h₂ h₃) = zzc qper₁ (proj₁ h₁) (proj₁ h₂) (proj₁ h₃)
proj₂ (zzc (qper₁ Q× qper₂) h₁ h₂ h₃) = zzc qper₂ (proj₂ h₁) (proj₂ h₂) (proj₂ h₃)

infixr 20 _⇒_
_⇒_ : (qper₁ : QPER A B) (qper₂ : QPER A' B') → QPER (A → A') (B → B')
R (_⇒_ {A} {B} qper₁ qper₂) M g = (a : A) (b : B) → R qper₁ a b → R qper₂ (M a) (g b)
zzc (qper₁ ⇒ qper₂) h₁ h₂ h₃ a b h = zzc qper₂ (h₁ a b h) (h₂ a b h) (h₃ a b h)

Qℕ : QPER ℕ ℕ
R Qℕ m n = m ≡ n
zzc Qℕ Eq.refl Eq.refl Eq.refl = Eq.refl
```

## Problem 3: Existential 

Now let's shift our gears to existential types. Let's start by considering the following type representing the implementation of a sequence of numbers:
```agda
record Seq (A : Set) : Set where
  field
    singleton : ℕ → A
    empty     : A
    append    : A → A → A
    sum       : A → ℕ
```
Here, the type `A` is meant to implement sequences, and the operations are in terms of this type `A`.

```agda
open import Data.Vec using (Vec) renaming (sum to sumv; map to mapv)
import Data.Vec as Vec

record Graph (V : Set) (G : Set) : Set where
  field
    empty : G

    isnode : G → V → Bool
    addnode : (g : G) → (v : V) → (isnode g v ≡ false) → G

    isedge : G → V × V → Bool
    addedge : (g : G) → (uv : V × V) → (isnode g (proj₁ uv) ≡ true) → (isnode g (proj₂ uv) ≡ true) → (isedge g uv ≡ false) → G

    n : G → ℕ
    nodes : (g : G) → Vec V (n g)
    m : G → ℕ
    nnbors : G → V → ℕ
    nbors : (g : G) → (v : V) → Vec V (nnbors g v)
```

```agda
open import Relation.Nullary.Negation

record Graph2 (V : Set) (G : Set) : Set₁ where
  field
    empty : G

    isnode : (g : G) (v : V) → Set
    addnode : (g : G) (v : V) (npv : ¬ isnode g v) → G

    isedge : (g : G) (uv : V × V) → Set
    addedge : (g : G) (uv : V × V) (pu : isnode g (proj₁ uv)) (pv : isnode g (proj₂ uv)) → (npuv : ¬ isedge g uv) → G

    n : G → ℕ
    nodes : (g : G) → Vec V (n g)
    m : G → ℕ
    nnbors : G → V → ℕ
    nbors : (g : G) (v : V) → Vec V (nnbors g v)
    -- nbors : (g : G) (v : V) → List V
```

An implementation (edge and vertex lists)

```agda
open import Data.Fin using (Fin)
-- open import Relation.Unary using (｛_｝)
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Decidable using (yes; no)

contains : ∀ {A : Set} (l : List A) (v : A) → Set
contains l v = Σ[ n ∈ Fin (List.length l) ] lookup l n ≡ v

data First {A B : Set} (P : A → Set) : A × B → Set where
  observe : ∀ {xy : A × B} → P (proj₁ xy) → First P xy

First? : ∀ {A B : Set} {P : A → Set} → Decidable P → Decidable (First {A} {B} P)
First? P? (x , y) with P? x
... | yes Px = yes (observe Px)
... | no ¬Px = no λ{ (observe Px) → ¬Px Px }
-- -- ...                  | yes Px = yes (observe Px)
-- -- ...                  | no ¬Px = no λ{ Px → ¬Px Px}
-- -- All? P? []                                 =  yes []
-- -- All? P? (x ∷ xs) with P? x   | All? P? xs
-- -- ...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
-- -- ...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
-- -- ...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

-- fst-dec : ∀ {A B : Set} → Dec A → Dec (A × B)
-- does  (fst-dec a?) = does a? ∧ does b?
-- proof (fst-dec a?) = proof a? ×-reflects proof b?

edgelist-nat-graph : Graph2 ℕ (List ℕ × List (ℕ × ℕ))
edgelist-nat-graph .Graph2.empty = [] , []
edgelist-nat-graph .Graph2.isnode ( vs , _ ) v = contains vs v
edgelist-nat-graph .Graph2.addnode  ( vs , es ) v _ = v ∷ vs , es
edgelist-nat-graph .Graph2.isedge (_ , es) e = contains es e
edgelist-nat-graph .Graph2.addedge (vs , es) (u , v) _ _ _ = vs , (u , v) ∷ (v , u) ∷ es
edgelist-nat-graph .Graph2.n (vs , _) = List.length vs
edgelist-nat-graph .Graph2.nodes (vs , _) = Vec.fromList vs
edgelist-nat-graph .Graph2.m (_ , es) = List.length es
edgelist-nat-graph .Graph2.nnbors (_ , es) v = List.length (List.map proj₂ (filter (First? (Nat._≟_ v)) es))
edgelist-nat-graph .Graph2.nbors (_ , es) v =  Vec.fromList (List.map proj₂ (filter (First? (Nat._≟_ v)) es))
```

-- Proofs

    undirected : (g : G) → (uv : V × V) → isedge g uv ≡ isedge g (Data.Product.swap uv)

    addnode_incr_node : (g : G) → (v : V) → (p : isnode g v ≡ false) → n (addnode g v p) ≡ 1 + n g
    addnode_const_edge : (g : G) → (v : V) → (p : isnode g v ≡ false) → m (addnode g v p) ≡ m g

    addedge_incr_edge : (g : G) → (uv : V × V) → (p : isedge g uv ≡ false) → m (addedge g uv p) ≡ 1 + m g
    addedge_const_node : (g : G) → (uv : V × V) → (p : isedge g uv ≡ false) → n (addedge g uv p) ≡ n g

-- handshake : ∀ {g : G} sumv (mapv (nnbors g) (nodes g)) ≡ 2 * (m g)
