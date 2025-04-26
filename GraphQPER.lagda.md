### PLEASE NOTE: there is another file called QPERGraph.lagda.md which contains **different content**!

This file contains some experiments in proving representation invariance between
the edge list representation and the function-backed adjacency list
representation.

It is modelled on Pset 4.

```agda
open import GraphQPERHelper

-- _×_ and _⊎_ and ⊤ and ⊥
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit

open import Relation.Nullary.Decidable using (does)
open import Data.Bool

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

```agda
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

First we define a QPER on (List ℕ , List ℕ) which simply checks that these are
the same list.

```agda
-- We define a QPER
QList :  QPER (List ℕ) (List ℕ)
R QList a b = a ≡ b
zzc QList Eq.refl Eq.refl Eq.refl = Eq.refl
```

Here, we define two QPERs between these graph representations. Both use the idea
of matching the vertex list and ensuring, for each vertex, the neighbours are
the same. On the edge list side, this is done via the edge list's nbors
implementation. On the function-backed adjlist side, this is done via the
neighbours function.

The only difference between the implementations is where the vertex is taken in:
1. (vertex list same, λ n -> neighbours of n same)
2. λ n → (vertex list same, neighbours of n same)

The benefit of the second option is that it allows easier pattern matching using
the input vertex n and `with` clauses. Obviously, these are interchangeable.

```agda
graph-correspondence : QPER Edgelist (List ℕ × (ℕ → List ℕ))
graph-correspondence .QPER.R (vs , es) (vs' , ns') = (vs ≡ vs') × ((n : ℕ) → List.map proj₂ (filter (First? (Nat._≟_ n)) es) ≡ ns' n)
graph-correspondence .QPER.zzc (Eq.refl , mmpe) (nnpv , nnpe) (Eq.refl , nmpe) = nnpv ,  λ n → Eq.trans (Eq.trans (mmpe n) (Eq.sym (nmpe n))) (nnpe n)

-- This is a good example of helpful pattern matching being possible, in a way
-- it is not possible above.
graph-correspondence2 : QPER Edgelist (List ℕ × (ℕ → List ℕ))
graph-correspondence2 .QPER.R (vs , es) (vs' , ns') = (n : ℕ) → (vs ≡ vs') × List.map proj₂ (filter (First? (Nat._≟_ n)) es) ≡ ns' n
graph-correspondence2 .QPER.zzc mmp nnp nmp n with mmp n | nnp n | nmp n
... | Eq.refl , b | Eq.refl , d | Eq.refl , f = Eq.refl , Eq.trans (Eq.trans b (Eq.sym f)) d
```

Next, we create a representation independence record and prove a few cases.
Unfortunately, not all the cases are complete.

```agda
record Graph≡ (GEdge : Graph ℕ (List ℕ × List (ℕ × ℕ))) (GAdj : Graph ℕ (List ℕ × (ℕ → List ℕ))) : Set where
  field
    empty-ge   : R graph-correspondence2  (Graph.empty GEdge) (Graph.empty GAdj)
    addnode-ge : R (graph-correspondence2 ⇒ (Qℕ ⇒ graph-correspondence2)) (Graph.addnode GEdge) (Graph.addnode GAdj)
    addedge-ge : R (graph-correspondence2 ⇒ ((Qℕ Q× Qℕ) ⇒ graph-correspondence2)) (Graph.addedge GEdge) (Graph.addedge GAdj)
    n-ge : R (graph-correspondence2 ⇒ Qℕ) (Graph.n GEdge) (Graph.n GAdj)
    nodes-ge : R (graph-correspondence2 ⇒ QList) (Graph.nodes GEdge) (Graph.nodes GAdj)
    m-ge : R (graph-correspondence2 ⇒ Qℕ) (Graph.m GEdge) (Graph.m GAdj)
    nnbors-ge : R (graph-correspondence2 ⇒ (Qℕ ⇒ Qℕ)) (Graph.nnbors GEdge) (Graph.nnbors GAdj)
    nbors-ge : R (graph-correspondence2 ⇒ (Qℕ ⇒ QList)) (Graph.nbors GEdge) (Graph.nbors GAdj)

independence : Graph≡ edgelist-nat-graph func-adjlist-nat-graph
independence .Graph≡.empty-ge _ = Eq.refl , Eq.refl
independence .Graph≡.addnode-ge _ _ cl _ _ Eq.refl n with cl n
... | Eq.refl , b = Eq.refl , b
-- This is the hardest case. Unfortunately, there was not enough time to get to
-- it.
independence .Graph≡.addedge-ge = {!   !}
independence .Graph≡.n-ge edgelist adjlist cl with cl 0
... | Eq.refl , _ = Eq.refl
independence .Graph≡.nodes-ge edgelist adjlist cl with cl 0
... | Eq.refl , _ = Eq.refl
-- If in no other way, this may be provable via the handshake lemma.
independence .Graph≡.m-ge = {!   !}
independence .Graph≡.nnbors-ge (_ , es) (_ , ns) cl a _ Eq.refl with cl a
... | Eq.refl , b =  
  let open ≡-Reasoning in
  begin
    List.length (filter (First? (Nat._≟_ a)) es)
  ≡⟨ List.length-map proj₂ (filter (First? (Nat._≟_ a)) es) ⟨
    List.length (List.map proj₂ (filter (First? (Nat._≟_ a)) es))
  ≡⟨ Eq.cong List.length b ⟩
    List.length (ns a)
  ∎
independence .Graph≡.nbors-ge (_ , es) (_ , ns) cl a _ Eq.refl with cl a
... | Eq.refl , b = b
```
