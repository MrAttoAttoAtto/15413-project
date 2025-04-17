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
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; module ≡-Reasoning)

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
open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Relation.Nullary.Negation

record Graph (V : Set) (G : Set) : Set₁ where
  field
    empty : G

    isnode : (g : G) (v : V) → Set
    addnode : (g : G) (v : V) (npv : ¬ isnode g v) → G

    isedge : (g : G) (uv : V × V) → Set
    addedge : (g : G) (uv : V × V) (nuv : proj₁ uv ≢ proj₂ uv) (pu : isnode g (proj₁ uv)) (pv : isnode g (proj₂ uv)) (npuv : ¬ isedge g uv) → G

    n : G → ℕ
    nodes : (g : G) → Vec V (n g)
    m : G → ℕ
    nnbors : G → V → ℕ
    nbors : (g : G) (v : V) → Vec V (nnbors g v)
```

An implementation (edge and vertex lists)

```agda
-- TODO CITE https://stackoverflow.com/questions/58679462/is-there-an-element-in-list-datatype-defined-in-the-standard-library/58680751#58680751
open import Data.Fin using (Fin)

contains : ∀ {A : Set} (l : List A) (v : A) → Set
contains l v = Σ[ n ∈ Fin (List.length l) ] lookup l n ≡ v

data UniqueWitness {A : Set} : (l : List A) → Set where
  empty : UniqueWitness []
  unique : ∀ {x xs} → ¬ contains xs x → UniqueWitness xs → UniqueWitness (x ∷ xs)

record UniqueList (A : Set) : Set where
  constructor _\\_
  field
    l : List A
    wf : UniqueWitness l
```

```agda
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Decidable using (yes; no)

data First {A B : Set} (P : A → Set) : A × B → Set where
  observe : ∀ {xy : A × B} → P (proj₁ xy) → First P xy

First? : ∀ {A B : Set} {P : A → Set} → Decidable P → Decidable (First {A} {B} P)
First? P? (x , y) with P? x
... | yes Px = yes (observe Px)
... | no ¬Px = no λ{ (observe Px) → ¬Px Px }

Edgelist : Set
Edgelist = UniqueList ℕ × List (ℕ × ℕ)

edgelist-nat-graph : Graph ℕ Edgelist
edgelist-nat-graph .Graph.empty = [] \\ empty , []
edgelist-nat-graph .Graph.isnode ( vs \\ _ , _ ) v = contains vs v
edgelist-nat-graph .Graph.addnode  ( vs \\ wit , es ) v p = (v ∷ vs) \\ (unique p wit) , es
edgelist-nat-graph .Graph.isedge (_ , es) e = contains es e
edgelist-nat-graph .Graph.addedge (vs , es) (u , v) _ _ _ _ = vs , (u , v) ∷ (v , u) ∷ es
edgelist-nat-graph .Graph.n (vs \\ _ , _) = List.length vs
edgelist-nat-graph .Graph.nodes (vs \\ _ , _) = Vec.fromList vs
edgelist-nat-graph .Graph.m (_ , es) = List.length es / 2
edgelist-nat-graph .Graph.nnbors (_ , es) v = List.length (List.map proj₂ (filter (First? (Nat._≟_ v)) es))
edgelist-nat-graph .Graph.nbors (_ , es) v = Vec.fromList (List.map proj₂ (filter (First? (Nat._≟_ v)) es))
```

```agda
data GraphConstruction {V G} (Gr : Graph V G) : G → Set where
  empty-gcons : GraphConstruction Gr (Graph.empty Gr)
  addnode-gcons : ∀ {g} → GraphConstruction Gr g → ∀ {v npv} → GraphConstruction Gr (Graph.addnode Gr g v npv)
  addegde-gcons : ∀ {g} → GraphConstruction Gr g → ∀ {uv nuv pu pv npuv} → GraphConstruction Gr (Graph.addedge Gr g uv nuv pu pv npuv)

graph-induction : ∀ {V G} → (Gr : Graph V G) → (P : Graph V G → G → Set) → Set
graph-induction {G = G} Gr P = {g : G} → GraphConstruction Gr g → P Gr g
```

```agda
undirected : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
undirected {V} Gr g = ((uv : V × V) → Graph.isedge Gr g uv → Graph.isedge Gr g (Data.Product.swap uv))

edgelist-undirected : graph-induction edgelist-nat-graph undirected
edgelist-undirected empty-gcons _ ()
edgelist-undirected (addnode-gcons gc) uv uv-in-g = edgelist-undirected gc uv uv-in-g
edgelist-undirected (addegde-gcons gc) _ (Fin.zero , Eq.refl) = Fin.suc Fin.zero , Eq.refl
edgelist-undirected (addegde-gcons gc) _ (Fin.suc Fin.zero , Eq.refl) = Fin.zero , Eq.refl
edgelist-undirected (addegde-gcons {g} gc) (u , v) (Fin.suc (Fin.suc idx) , Eq.refl) = Fin.suc (Fin.suc (proj₁ ih)) , proj₂ ih
                                      where
                                      ih : Graph.isedge edgelist-nat-graph g (v , u)
                                      ih = edgelist-undirected gc (u , v) (idx , Eq.refl)
```
 