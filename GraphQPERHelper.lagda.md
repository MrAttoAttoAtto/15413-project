# WARNING: This is NOT the same as GraphProject, which is probably what you want
# to read.

This file exists due to an issue with the representation independence structure
not playing nicely with the dependent arguments (e.g. isnode g v) due to a
scoping issue.

In this version, those arguments are removed, as is the uniqueness condition on
the vertex list in the edge list representation.

```agda
module GraphQPERHelper where

-- _×_ and _⊎_ and ⊤ and ⊥
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit

open import Data.Bool
open import Relation.Nullary.Decidable using (does)

-- ℕ
open import Data.Nat
import Data.Nat.Properties as Nat

-- List
open import Data.List as List using (List; []; _∷_; _++_; [_]; reverse; _∷ʳ_; lookup; filter)
import Data.List.Properties as List

-- _≡_
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; module ≡-Reasoning)
```

We define the Graph record, which identifies the operations required for a
graph implementation. Here, `V` represents the type of vertices/nodes (edges are
of type `V × V`), and `G` is the type of the graph instance.

Here, we consider only simple graphs, and we will only consider undirected
implementations.

```agda
open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Relation.Nullary.Negation

record Graph (V : Set) (G : Set) : Set₁ where
  field
    -- The empty graph for the given implementation
    empty : G

    -- Values of isnode g v are proofs that v is a node in g
    isnode : (g : G) (v : V) → Set
    -- Adds a node to the graph, returning the new graph. A proof that the node
    -- does not yet exist is required.
    addnode : (g : G) (v : V) → G

    -- Values of isedge g uv are proofs that uv is an edge in g
    isedge : (g : G) (uv : V × V) → Set
    -- Adds a node to the graph, returning the new graph. A couple proofs are
    -- required:
    --   - The edge must not be a self-loop (u ≢ v)
    --   - Both endpoints must be nodes in the graph
    --   - The edge must not exist yet
    addedge : (g : G) (uv : V × V) → G

    -- The number of nodes in the graph
    n : G → ℕ
    -- A vector of nodes in the graph
    nodes : (g : G) → List V
    -- The number of edges in the graph
    m : G → ℕ
    -- The number of neighbours of a given vertex
    nnbors : G → V → ℕ
    -- The neighbours of a given vertex
    nbors : (g : G) (v : V) → List V
```

The following are definitions of some small tools we will need for a later graph
implementations: a notion of a list containing an element (`contains`) and the
related notion of a list with unique elements (and with a witness to their
uniqueness)

```agda
open import Data.Fin using (Fin)

-- A value of contains l v is a proof that l contains v
-- We take a constructive approach: l contains v iff there is some index n at
-- which `lookup l n` will give us `v`.
contains : ∀ {A : Set} (l : List A) (v : A) → Set
contains l v = Σ[ n ∈ Fin (List.length l) ] lookup l n ≡ v
```

Here, we implement a graph as a list of vertices and edges. The list of vertices
is unique. We specify vertices by (arbitrary) natural numbers.

```agda
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Decidable using (yes; no)


length-conv : {A : Set} {n m : ℕ} → (n ≡ m) → Vec A n → Vec A m
length-conv Eq.refl v = v

-- A predicate on A × B parametrised on a predicate for A. This predicate holds
-- on (u , v) iff the predicate P holds on u.
data First {A B : Set} (P : A → Set) : A × B → Set where
  observe : ∀ {xy : A × B} → P (proj₁ xy) → First P xy

-- A proof/method to convert a decidable predicate for P into a decidable
-- predicate for `First P`.
First? : ∀ {A B : Set} {P : A → Set} → Decidable P → Decidable (First {A} {B} P)
First? P? (x , _) with P? x
... | yes Px = yes (observe Px)
... | no ¬Px = no λ{ (observe Px) → ¬Px Px }

-- Our graph instances - G - is going to be a unique list of vertices and a list
-- of edges.
Edgelist : Set
Edgelist = List ℕ × List (ℕ × ℕ)

-- We implement this graph record below.
edgelist-nat-graph : Graph ℕ Edgelist
edgelist-nat-graph .Graph.empty = [] , []

-- A natural number is a node iff the vertex list contains it
edgelist-nat-graph .Graph.isnode ( vs , _ ) v = contains vs v
edgelist-nat-graph .Graph.addnode  ( vs , es ) v = (v ∷ vs) , es

-- A natural number pair is an edge iff the edge list contains it
edgelist-nat-graph .Graph.isedge (_ , es) e = contains es e
-- This is what makes the graph undirected: when we add (u , v), we also add
-- (v , u)
edgelist-nat-graph .Graph.addedge (vs , es) (u , v) = vs , (u , v) ∷ (v , u) ∷ es

edgelist-nat-graph .Graph.n (vs , _) = List.length vs
edgelist-nat-graph .Graph.nodes (vs , _) = vs

-- Note that, since we added both (u , v) and (v , u) to the edgelist upon
-- adding (u , v), we need to halve our answer for the number of edges.
edgelist-nat-graph .Graph.m (_ , es) = List.length es / 2

-- To find the number of neighbours, we filter the edgelist by looking for
-- edges with 'begin at' u. For every neighbour v, the edge (u , v) will be in
-- the edge list, so we simply count the number of these. To get the neighbours
-- themselves, we omit the counting step (and we project into the second element
-- of the edge, which is the neighbour itself).
edgelist-nat-graph .Graph.nnbors (_ , es) v = List.length (filter (First? (Nat._≟_ v)) es)
edgelist-nat-graph .Graph.nbors (_ , es) v = (List.map proj₂ (filter (First? (Nat._≟_ v)) es))
```

```agda
addedge-helper : ℕ × ℕ → (ℕ → List ℕ) → ℕ → List ℕ
addedge-helper (u , v) ns w with does (Nat._≟_ w u)
... | true = v ∷ (ns u)
... | false = ns w

func-adjlist-nat-graph : Graph ℕ (List ℕ × (ℕ → List ℕ))
func-adjlist-nat-graph .Graph.empty = [] , λ v → []
func-adjlist-nat-graph .Graph.isnode (vs , _) v = contains vs v
func-adjlist-nat-graph .Graph.addnode (vs , ns) v = v ∷ vs , ns
func-adjlist-nat-graph .Graph.isedge (_ , ns) (u , v) = contains (ns u) v
func-adjlist-nat-graph .Graph.addedge (vs , ns) (u , v) = vs , addedge-helper (u , v) (addedge-helper (v , u) ns)
func-adjlist-nat-graph .Graph.n (vs , _) = List.length vs
func-adjlist-nat-graph .Graph.nodes (vs , _) = vs
func-adjlist-nat-graph .Graph.m (vs , ns) = List.sum (List.map (λ v → List.length (ns v)) vs) / 2
func-adjlist-nat-graph .Graph.nnbors (_ , ns) v = List.length (ns v)
func-adjlist-nat-graph .Graph.nbors (_ , ns) v = ns v
```