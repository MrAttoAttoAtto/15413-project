We import our previous graph definitions.

This is a big proof, so we separated it into a new file.

```agda
module HandshakeLemma where

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

```agda
nonnode-no-edges : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
nonnode-no-edges {V} Gr g = (v : V) → (¬ Graph.isnode Gr g v) → Graph.nnbors Gr g v ≡ 0

edgelist-nonnode-no-edges : graph-induction edgelist-nat-graph nonnode-no-edges
edgelist-nonnode-no-edges empty-gcons _ _ = Eq.refl
edgelist-nonnode-no-edges (addnode-gcons {vs \\ _ , _} gc) v vnp = edgelist-nonnode-no-edges gc v vwnp
                            where
                            vwnp : ¬ contains vs v
                            vwnp (idx , Eq.refl) = vnp ((Fin.suc idx) , Eq.refl)
edgelist-nonnode-no-edges (addegde-gcons {vs , es} gc {u , v} {_} {p1} {p2}) w vnp with (First? (Nat._≟_ w) (u , v)) in eq1 | (First? (Nat._≟_ w) (v , u)) in eq2
... | yes (observe Eq.refl) | _ = ⊥-elim (vnp p1)
... | _ | yes (observe Eq.refl) = ⊥-elim (vnp p2)
... | no _ | no _ rewrite eq1 rewrite eq2 = edgelist-nonnode-no-edges gc w vnp
```

```agda
-- addnode-adds-no-nbors : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
-- addnode-adds-no-nbors Gr g = ∀ {v v' p'} → Graph.nnbors Gr g v ≡ Graph.nnbors Gr (Graph.addnode Gr g v' p') v

-- edgelist-addnode-adds-no-nbors : Graph-Induction edgelist-nat-graph addnode-adds-no-nbors
-- edgelist-addnode-adds-no-nbors .Graph-Induction.empty-case = Eq.refl
-- edgelist-addnode-adds-no-nbors .Graph-Induction.addnode-case ih = Eq.refl
-- edgelist-addnode-adds-no-nbors .Graph-Induction.addedge-case ih = Eq.refl

addnode-adds-no-nbors : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addnode-adds-no-nbors Gr g = ∀ {v v' p'} → Graph.nnbors Gr g v ≡ Graph.nnbors Gr (Graph.addnode Gr g v' p') v

edgelist-addnode-adds-no-nbors : (g : Edgelist) → addnode-adds-no-nbors edgelist-nat-graph g
edgelist-addnode-adds-no-nbors g = Eq.refl
```

```agda
addedge-adds-one-nbor : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-one-nbor Gr g = ∀ {u v nuv pu pv npuv} → Graph.nnbors Gr (Graph.addedge Gr g (u , v) nuv pu pv npuv) u ≡ 1 + Graph.nnbors Gr g u

addedge-adds-one-nbor' : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-one-nbor' Gr g = ∀ {u v nuv pu pv npuv} → Graph.nnbors Gr (Graph.addedge Gr g (u , v) nuv pu pv npuv) v ≡ 1 + Graph.nnbors Gr g v

addedge-adds-one-nbor'' : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-one-nbor'' Gr g = ∀ {w u v nuv pu pv npuv} → (w ≡ u ⊎ w ≡ v) → Graph.nnbors Gr (Graph.addedge Gr g (u , v) nuv pu pv npuv) w ≡ 1 + Graph.nnbors Gr g w

-- edgelist-addedge-adds-one-nbor : Graph-Induction edgelist-nat-graph addedge-adds-one-nbor
-- edgelist-addedge-adds-one-nbor .Graph-Induction.empty-case {_} {_} {()}
-- edgelist-addedge-adds-one-nbor .Graph-Induction.addnode-case _ {u} {v} {_} {_} {nuv} {_} with (First? (Nat._≟_ u) (u , v)) in eq1 | (First? (Nat._≟_ u) (v , u)) in eq2
-- ... | no nuu | _ = ⊥-elim (nuu (observe Eq.refl))
-- ... | _ | yes (observe uv) = ⊥-elim (nuv uv)
-- ... | yes _ | no _ rewrite eq1 rewrite eq2 = Eq.refl
-- edgelist-addedge-adds-one-nbor .Graph-Induction.addedge-case = {!   !}

edgelist-addedge-adds-one-nbor : (g : Edgelist) → addedge-adds-one-nbor edgelist-nat-graph g
edgelist-addedge-adds-one-nbor g {u} {v} {nuv} with (First? (Nat._≟_ u) (u , v)) in eq1 | (First? (Nat._≟_ u) (v , u)) in eq2
... | no nuu | _ = ⊥-elim (nuu (observe Eq.refl))
... | _ | yes (observe uv) = ⊥-elim (nuv uv)
... | yes _ | no _ rewrite eq1 rewrite eq2 = Eq.refl

edgelist-addedge-adds-one-nbor' : (g : Edgelist) → addedge-adds-one-nbor' edgelist-nat-graph g
edgelist-addedge-adds-one-nbor' g {u} {v} {nuv} with (First? (Nat._≟_ v) (u , v)) in eq1 | (First? (Nat._≟_ v) (v , u)) in eq2
... | _ | no nuu = ⊥-elim (nuu (observe Eq.refl))
... | yes (observe vu) | _ = ⊥-elim (nuv (Eq.sym vu))
... | no _ | yes _ rewrite eq1 rewrite eq2 = Eq.refl

edgelist-addedge-adds-one-nbor'' : (g : Edgelist) → addedge-adds-one-nbor'' edgelist-nat-graph g
edgelist-addedge-adds-one-nbor'' g {w = u} {u} {v} {nuv} {pu} {pv} {npuv} (inj₁ Eq.refl) = edgelist-addedge-adds-one-nbor g {u} {v} {nuv} {pu} {pv} {npuv}
edgelist-addedge-adds-one-nbor'' g {w = v} {u} {v} {nuv} {pu} {pv} {npuv} (inj₂ Eq.refl) = edgelist-addedge-adds-one-nbor' g {u} {v} {nuv} {pu} {pv} {npuv}
```

```agda
addedge-adds-no-nbors : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-no-nbors Gr g = ∀ {w u v nuv pu pv npuv} (nwu : w ≢ u) (nwv : w ≢ v) → Graph.nnbors Gr (Graph.addedge Gr g (u , v) nuv pu pv npuv) w ≡ Graph.nnbors Gr g w

-- edgelist-addedge-adds-one-nbor : Graph-Induction edgelist-nat-graph addedge-adds-one-nbor
-- edgelist-addedge-adds-one-nbor .Graph-Induction.empty-case {_} {_} {()}
-- edgelist-addedge-adds-one-nbor .Graph-Induction.addnode-case _ {u} {v} {_} {_} {nuv} {_} with (First? (Nat._≟_ u) (u , v)) in eq1 | (First? (Nat._≟_ u) (v , u)) in eq2
-- ... | no nuu | _ = ⊥-elim (nuu (observe Eq.refl))
-- ... | _ | yes (observe uv) = ⊥-elim (nuv uv)
-- ... | yes _ | no _ rewrite eq1 rewrite eq2 = Eq.refl
-- edgelist-addedge-adds-one-nbor .Graph-Induction.addedge-case = {!   !}

edgelist-addedge-adds-no-nbors : (g : Edgelist) → addedge-adds-no-nbors edgelist-nat-graph g
edgelist-addedge-adds-no-nbors g {w} {u} {v} nwu nwv with (First? (Nat._≟_ w) (u , v)) in eq1 | (First? (Nat._≟_ w) (v , u)) in eq2
... | yes (observe wu) | _ = ⊥-elim (nwu wu)
... | _ | yes (observe wv) = ⊥-elim (nwv wv)
... | no _ | no _ rewrite eq1 rewrite eq2 = Eq.refl
```

```agda
tail-contains : {A : Set} {ws : List A} {x : A} {v : A} → contains ws v → contains (x ∷ ws) v
tail-contains (idx , Eq.refl) = (Fin.suc idx) , Eq.refl

tail-ncontains : {A : Set} {ws : List A} {x : A} {v : A} → ¬ contains (x ∷ ws) v → ¬ contains ws v
tail-ncontains = contraposition tail-contains

addedge-adds-no-nbors' : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-no-nbors' Gr g = ∀ {ws u v pu pv nuv npuv} (nwsu : ¬ contains ws u) (nwsv : ¬ contains ws v) → List.map (Graph.nnbors Gr (Graph.addedge Gr g (u , v) pu pv nuv npuv)) ws ≡ List.map (Graph.nnbors Gr g) ws

edgelist-addedge-adds-no-nbors' : (g : Edgelist) → addedge-adds-no-nbors' edgelist-nat-graph g
edgelist-addedge-adds-no-nbors' g {[]} _ _ = Eq.refl
edgelist-addedge-adds-no-nbors' g {x ∷ ws} {u} {v} {nuv} {pu} {pv} {npuv} nlu nlv =
    let gp = Graph.addedge edgelist-nat-graph g (u , v) nuv pu pv npuv in
    let open ≡-Reasoning in
    begin
      List.map (Graph.nnbors edgelist-nat-graph gp) (x ∷ ws)
    ≡⟨⟩
      (Graph.nnbors edgelist-nat-graph gp x) ∷ List.map (Graph.nnbors edgelist-nat-graph gp) ws
    ≡⟨ Eq.cong₂ _∷_ (edgelist-addedge-adds-no-nbors g {x} {u} {v} {nuv} {pu} {pv} {npuv} nxu nxv) (edgelist-addedge-adds-no-nbors' g {ws} {u} {v} {nuv} {pu} {pv} {npuv} (tail-ncontains nlu) (tail-ncontains nlv)) ⟩
      (Graph.nnbors edgelist-nat-graph g x) ∷ List.map (Graph.nnbors edgelist-nat-graph g) ws
    ≡⟨⟩
      List.map (Graph.nnbors edgelist-nat-graph g) (x ∷ ws)
    ∎
    where
    nxu : x ≢ u
    nxu Eq.refl = nlu (Fin.zero , Eq.refl)

    nxv : x ≢ v
    nxv Eq.refl = nlv (Fin.zero , Eq.refl)
```

```agda
open import Data.List.Relation.Unary.Any using (Any)

-- Create isomorphism between "contains" and "Any"
any-to-contains : ∀ {A : Set} {l : List A} {v : A} → Any (_≡_ v) l → contains l v
any-to-contains (Any.here px) = Fin.zero , Eq.sym px
any-to-contains {_} {x ∷ xs} {v} (Any.there a) = Fin.suc (proj₁ p) , proj₂ p
                    where
                    p : contains xs v
                    p = any-to-contains a

contains-to-any : ∀ {A : Set} {l : List A} {v : A} → contains l v → Any (_≡_ v) l
contains-to-any {_} {x ∷ l} (Fin.zero , Eq.refl) = Any.here Eq.refl
contains-to-any {_} {x ∷ l} (Fin.suc idx , Eq.refl) = Any.there (contains-to-any (idx , Eq.refl))

sub-any : {A : Set} {l1 : List A} {l2 : List A} {l3 : List A} {l4 : List A} {v : A} → (l1 ++ l2 ++ l3 ≡ l4) → Any (_≡_ v) l2 → Any (_≡_ v) l4
sub-any {_} {[]} Eq.refl (Any.here Eq.refl) = Any.here Eq.refl
sub-any {A} {[]} {x ∷ xs} {l3} Eq.refl (Any.there c) = Any.there (sub-any {A} {[]} {xs} Eq.refl c)
sub-any {A} {x ∷ l1} {l2} {l3} Eq.refl c = Any.there (sub-any {A} {l1} {l2} Eq.refl c)

sub-contains : {A : Set} {l1 : List A} {l2 : List A} {l3 : List A} {l4 : List A} {v : A} → (l1 ++ l2 ++ l3 ≡ l4) → contains l2 v → contains l4 v
sub-contains {A} {l1} {l2} {l3} {l4} Eq.refl c = any-to-contains (sub-any {A} {l1} {l2} Eq.refl (contains-to-any c))

sub-contains2 : {A : Set} {l1 : List A} {l2 : List A} {l3 : List A} {v : A} → (l1 ++ l2 ≡ l3) → contains l1 v → contains l3 v
sub-contains2 {A} {l1} {l2} = sub-contains {A} {[]} {l1} {l2}
```

```agda
-- contains l v = Σ[ n ∈ Fin (List.length l) ] lookup l n ≡ v
no-contains : {A : Set} {v : A} → ¬ contains [] v
no-contains ()

list-movement : {A : Set} {l1 : List A} {v : A} {l2 : List A} → (l1 ++ v ∷ []) ++ l2 ++ [] ≡ l1 ++ v ∷ l2
list-movement {_} {[]} {v} {[]} = Eq.refl
list-movement {A} {[]} {v} {x ∷ l2} = Eq.cong₂ _∷_ Eq.refl (list-movement {A} {[]} {x} {l2})
list-movement {A} {x ∷ l1} {v} {l2} = Eq.cong₂ _∷_ Eq.refl (list-movement {A} {l1} {v} {l2})

-- sub-any2' : {A : Set} {l1 : List A} {l2 : List A} 

unique-split : ∀ {A : Set} (ul : UniqueList A) (u : A) → (contains (UniqueList.l ul) u) → Σ[ (f , b) ∈ List A × List A ] ((f ++ u ∷ b ≡ UniqueList.l ul) × (¬ contains f u) × (¬ contains b u))
unique-split ((x ∷ l) \\ unique w wf) u (Fin.zero , Eq.refl) = ([] , l) , Eq.refl , no-contains , w
unique-split {A} ((x ∷ l) \\ unique w wf) u (Fin.suc idx , Eq.refl) =
                            let ((f , b) , (eq , fu , bu)) = outp in
                            ( x ∷ f , b) , ( Eq.cong₂ _∷_ Eq.refl eq , fun , bu)
                            where
                            outp : Σ[ (f , b) ∈ List A × List A ] ((f ++ u ∷ b ≡ l) × (¬ contains f u) × (¬ contains b u))
                            outp = unique-split (l \\ wf) u (idx , Eq.refl)

                            -- (outp .proj₁ .proj₁) is f
                            fun : ¬ contains (x ∷ (outp .proj₁ .proj₁)) u
                            fun (Fin.zero , Eq.refl) = w (idx , Eq.refl)
                            fun (Fin.suc idxup , looku) = outp .proj₂ .proj₂ .proj₁ (idxup , looku)

unique-double-split : ∀ {A : Set} (ul : UniqueList A) (u : A) (v : A) → (contains (UniqueList.l ul) u) → (contains (UniqueList.l ul) v) → (u ≢ v) → Σ[ (f , m , b) ∈ List A × List A × List A ] (((f ++ u ∷ m ++ v ∷ b ≡ UniqueList.l ul) ⊎ (f ++ v ∷ m ++ u ∷ b ≡ UniqueList.l ul)) × (¬ contains f u) × (¬ contains f v) × (¬ contains m u) × (¬ contains m v) × (¬ contains b u) × (¬ contains b v))
unique-double-split ([] \\ wf) u v () cv nuv
unique-double-split ((x ∷ l) \\ wf) u v (Fin.zero , Eq.refl) (Fin.zero , Eq.refl) nuv = ⊥-elim (nuv Eq.refl)
unique-double-split {A} ((x ∷ l) \\ unique w wf) u v (Fin.zero , Eq.refl) (Fin.suc idxv , Eq.refl) nuv =
                            let ((m , b) , (eq , mv , bv)) = outp in
                            ([] , m , b) , ( inj₁ (Eq.cong₂ _∷_ Eq.refl eq) , no-contains , no-contains , (λ c → w (sub-contains {A} {[]} {m} lm1 c)) , mv , (λ c → w (sub-contains {A} {m ++ v ∷ []} {b} lm2 c)) , bv )
                            where
                            outp : Σ[ (m , b) ∈ List A × List A ] ((m ++ v ∷ b ≡ l) × (¬ contains m v) × (¬ contains b v))
                            outp = unique-split (l \\ wf) v (idxv , Eq.refl)

                            lm1 : [] ++ (outp .proj₁ .proj₁) ++ v ∷ (outp .proj₁ .proj₂) ≡ l
                            lm1 = outp .proj₂ .proj₁

                            lm2 : ((outp .proj₁ .proj₁) ++ v ∷ []) ++ (outp .proj₁ .proj₂) ++ [] ≡ l
                            lm2 = Eq.trans list-movement (outp .proj₂ .proj₁)
unique-double-split {A} ((x ∷ l) \\ unique w wf) u v (Fin.suc idxu , Eq.refl) (Fin.zero , Eq.refl) nuv =
                            let ((m , b) , (eq , mu , bu)) = outp in
                            ([] , m , b) , ( inj₂ (Eq.cong₂ _∷_ Eq.refl eq) , no-contains , no-contains , mu , (λ c → w (sub-contains {A} {[]} {m} lm1 c)) , bu , (λ c → w (sub-contains {A} {m ++ u ∷ []} {b} lm2 c)) )
                            where
                            outp : Σ[ (m , b) ∈ List A × List A ] ((m ++ u ∷ b ≡ l) × (¬ contains m u) × (¬ contains b u))
                            outp = unique-split (l \\ wf) u (idxu , Eq.refl)

                            lm1 : [] ++ (outp .proj₁ .proj₁) ++ u ∷ (outp .proj₁ .proj₂) ≡ l
                            lm1 = outp .proj₂ .proj₁

                            lm2 : ((outp .proj₁ .proj₁) ++ u ∷ []) ++ (outp .proj₁ .proj₂) ++ [] ≡ l
                            lm2 = Eq.trans list-movement (outp .proj₂ .proj₁)
unique-double-split {A} ((x ∷ l) \\ unique w wf) u v (Fin.suc idxu , Eq.refl) (Fin.suc idxv , Eq.refl) nuv =
                            let ((f , m , b) , (eq , fu , fv , mu , mv , bu , bv)) = outp in
                            ( x ∷ f , m , b) , ( Data.Sum.map (Eq.cong₂ _∷_ Eq.refl) (Eq.cong₂ _∷_ Eq.refl) eq , fun , fvn , mu , mv , bu , bv)
                            where
                            outp : Σ[ (f , m , b) ∈ List A × List A × List A ] (((f ++ u ∷ m ++ v ∷ b ≡ l) ⊎ (f ++ v ∷ m ++ u ∷ b ≡ l)) × (¬ contains f u) × (¬ contains f v) × (¬ contains m u) × (¬ contains m v) × (¬ contains b u) × (¬ contains b v))
                            outp = unique-double-split (l \\ wf) u v (idxu , Eq.refl) (idxv , Eq.refl) nuv

                            -- (outp .proj₁ .proj₁) is f
                            -- (outp .proj₂ .proj₂ .proj₁) is fu
                            fun : ¬ contains (x ∷ (outp .proj₁ .proj₁)) u
                            fun (Fin.zero , Eq.refl) = w (idxu , Eq.refl)
                            fun (Fin.suc idxup , looku) = outp .proj₂ .proj₂ .proj₁ (idxup , looku)

                            fvn : ¬ contains (x ∷ (outp .proj₁ .proj₁)) v
                            fvn (Fin.zero , Eq.refl) = w (idxv , Eq.refl)
                            fvn (Fin.suc idxvp , lookv) = outp .proj₂ .proj₂ .proj₂ .proj₁ (idxvp , lookv)
```

```agda
list-map-split : {A B : Set} {f : List A} {b : List A} {fn : A → B} → List.map fn (f ++ b) ≡ List.map fn f ++ List.map fn b
list-map-split {_} {_} {[]} = Eq.refl
list-map-split {A} {B} {x ∷ f} = Eq.cong₂ _∷_ Eq.refl (list-map-split {A} {B} {f})

list-sum-split : {f : List ℕ} {b : List ℕ} → List.sum (f ++ b) ≡ List.sum f + List.sum b
list-sum-split {[]} = Eq.refl
list-sum-split {x ∷ f} {b} =
    let open ≡-Reasoning in
    begin
      List.sum (x ∷ f ++ b)
    ≡⟨⟩
      x + List.sum (f ++ b)
    ≡⟨ Eq.cong₂ _+_ Eq.refl (list-sum-split {f} {b}) ⟩
      x + (List.sum f + List.sum b)
    ≡⟨ Nat.+-assoc x (List.sum f) (List.sum b) ⟨
      (x + List.sum f) + List.sum b
    ≡⟨⟩
      List.sum (x ∷ f) + List.sum b
    ∎
```

```agda
vec-annoying : {A : Set} {l : List A} {fn : A → ℕ} → Vec.sum (Vec.map fn (Vec.fromList l)) ≡ List.sum (List.map fn l)
vec-annoying {_} {[]} = Eq.refl
vec-annoying {A} {x ∷ l} = Eq.cong₂ _+_ Eq.refl (vec-annoying {A} {l})
```

```agda
-- edgelist-addedge-none-left : ∀ {u v nuv pu pv npuv} (g : Edgelist) (n : ℕ) (n ≤ℕ Graph.n edgelist-nat-graph g) →
--     let Gr = edgelist-nat-graph in
--     let taken = Vec.take n (Graph.nodes Gr g) in
--     let ltaken = Vec.toList taken in
--     let gp = Graph.addedge Gr g (u , v) nuv pu pv npuv in
--     (¬ contains ltaken u) → (¬ contains ltaken v) →
--     Vec.sum (Vec.map (Graph.nnbors Gr gp) taken) ≡ Vec.sum (Vec.map (Graph.nnbors Gr g) taken)
-- edgelist-addedge-none-left {u} {v} {nuv} {pu} {pv} {npuv} g n = ?


addedge-adds-two-nbors : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-two-nbors Gr g = ∀ {u v nuv pu pv npuv} →
    let gp = Graph.addedge Gr g (u , v) nuv pu pv npuv in
    Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr gp)) ≡ 2 + Vec.sum (Vec.map (Graph.nnbors Gr g) (Graph.nodes Gr g))

-- edgelist-addedge-adds-no-nbors : (g : Edgelist) → addedge-adds-no-nbors edgelist-nat-graph g
-- edgelist-addedge-adds-no-nbors g {w} {u} {v} nwu nwv with (First? (Nat._≟_ w) (u , v)) in eq1 | (First? (Nat._≟_ w) (v , u)) in eq2
-- ... | yes (observe wu) | _ = ⊥-elim (nwu wu)
-- ... | _ | yes (observe wv) = ⊥-elim (nwv wv)
-- ... | no _ | no _ rewrite eq1 rewrite eq2 = Eq.refl

-- Dependent elimination?
-- sorter : {A B C D : Set} → A ⊎ B → C → D → (C × D × A) ⊎ (D × C × B)
-- sorter (inj₁ x) ustuff vstuff = inj₁ (ustuff , vstuff , x)
-- sorter (inj₂ y) ustuff vstuff = inj₂ (vstuff , ustuff , y)

sorted : ∀ {u v f m b l} → ((f ++ u ∷ m ++ v ∷ b ≡ l) ⊎ (f ++ v ∷ m ++ u ∷ b ≡ l)) → (¬ contains f u) → (¬ contains f v) → (¬ contains m u) → (¬ contains m v) → (¬ contains b u) → (¬ contains b v) → Σ[ (e1 , e2) ∈ (ℕ × ℕ) ] ((e1 ≡ u ⊎ e1 ≡ v) × (e2 ≡ u ⊎ e2 ≡ v) × (f ++ e1 ∷ m ++ e2 ∷ b ≡ l) × (¬ contains f e1) × (¬ contains f e2) × (¬ contains m e1) × (¬ contains m e2) × (¬ contains b e1) × (¬ contains b e2))
sorted {u} {v} (inj₁ Eq.refl) fu fv mu mv bu bv = (u , v) , (inj₁ Eq.refl , inj₂ Eq.refl , Eq.refl , fu , fv , mu , mv , bu , bv)
sorted {u} {v} (inj₂ Eq.refl) fu fv mu mv bu bv = (v , u) , (inj₂ Eq.refl , inj₁ Eq.refl , Eq.refl , fv , fu , mv , mu , bv , bu)
  
  -- Data.Sum.[ (λ x → (u , v) , (x , fu , fv , mu , mv , bu , bv)) , (λ x → (v , u) , (x , fv , fu , mv , mu , bv , bu)) ] ueq

edgelist-addedge-adds-two-nbors : (g : Edgelist) → addedge-adds-two-nbors edgelist-nat-graph g
edgelist-addedge-adds-two-nbors (vs , es) {u} {v} {nuv} {pu} {pv} {npuv} with unique-double-split vs u v pu pv nuv
... | ((f , m , b) , ( ueq , fu , fv , mu , mv , bu , bv )) with sorted ueq fu fv mu mv bu bv
... | (e1 , e2) , (e1e , e2e , eq , fe1 , fe2 , me1 , me2 , be1 , be2) =
    let g = (vs , es) in
    let Gr = edgelist-nat-graph in
    let gp = Graph.addedge Gr g (u , v) nuv pu pv npuv in
    let open ≡-Reasoning in
    begin
      Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr gp))
    ≡⟨ vec-annoying {ℕ} {UniqueList.l vs} ⟩
      List.sum (List.map (Graph.nnbors Gr gp) (UniqueList.l vs))
    ≡⟨ Eq.cong List.sum (Eq.cong₂ List.map Eq.refl eq) ⟨
      List.sum (List.map (Graph.nnbors Gr gp) (f ++ e1 ∷ m ++ e2 ∷ b))
    ≡⟨⟩
      List.sum (List.map (Graph.nnbors Gr gp) (f ++ (e1 ∷ []) ++ m ++ (e2 ∷ []) ++ b))
    ≡⟨ Eq.cong List.sum (list-map-split {ℕ} {ℕ} {f}) ⟩
      List.sum (List.map (Graph.nnbors Gr gp) f ++ List.map (Graph.nnbors Gr gp) ((e1 ∷ []) ++ m ++ (e2 ∷ []) ++ b))
    ≡⟨ list-sum-split {List.map (Graph.nnbors Gr gp) f} ⟩
      List.sum (List.map (Graph.nnbors Gr gp) f) + List.sum (List.map (Graph.nnbors Gr gp) ((e1 ∷ []) ++ m ++ (e2 ∷ []) ++ b))
    ≡⟨ Eq.cong₂ _+_ (Eq.cong List.sum (edgelist-addedge-adds-no-nbors' g {f} {u} {v} {nuv} {pu} {pv} {npuv} fu fv)) Eq.refl ⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      List.sum (List.map (Graph.nnbors Gr gp) ((e1 ∷ []) ++ m ++ (e2 ∷ []) ++ b))
    ≡⟨ Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {e1 ∷ []} {m ++ (e2 ∷ []) ++ b} {Graph.nnbors Gr gp})) ⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      List.sum (List.map (Graph.nnbors Gr gp) (e1 ∷ []) ++ List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b))
    ≡⟨⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      List.sum ((Graph.nnbors Gr gp e1) ∷ List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b))
    ≡⟨⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr gp e1 +
      List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b)))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (Eq.cong₂ _+_ (edgelist-addedge-adds-one-nbor'' g {nuv = nuv} {pu = pu} {pv = pv} {npuv = npuv} e1e) Eq.refl) ⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      ((1 + Graph.nnbors Gr g e1) +
      List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b)))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (Nat.+-assoc 1 (Graph.nnbors Gr g e1) (List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b)))) ⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (1 + (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b))))
    ≡⟨ Nat.+-assoc (List.sum (List.map (Graph.nnbors Gr g) f)) 1 (Graph.nnbors Gr g e1 + List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b))) ⟨
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      1) + (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b)))
    ≡⟨ Eq.cong₂ _+_ (Nat.+-comm (List.sum (List.map (Graph.nnbors Gr g) f)) 1) Eq.refl ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b)))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {m}))) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr gp) m ++ List.map (Graph.nnbors Gr gp) ((e2 ∷ []) ++ b)))
      -- Plausibly could be more efficient here
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ Eq.refl (list-sum-split {List.map (Graph.nnbors Gr gp) m})) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr gp) m) +
      List.sum (List.map (Graph.nnbors Gr gp) ((e2 ∷ []) ++ b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ (Eq.cong List.sum (edgelist-addedge-adds-no-nbors' g {m} {u} {v} {nuv} {pu} {pv} {npuv} mu mv)) Eq.refl)) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      List.sum (List.map (Graph.nnbors Gr gp) ((e2 ∷ []) ++ b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {e2 ∷ []} {b} {Graph.nnbors Gr gp})))) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      List.sum (List.map (Graph.nnbors Gr gp) (e2 ∷ []) ++ List.map (Graph.nnbors Gr gp) b)))
    ≡⟨⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      List.sum ((Graph.nnbors Gr gp e2) ∷ List.map (Graph.nnbors Gr gp) b)))
    ≡⟨⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr gp e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Eq.cong₂ _+_ (edgelist-addedge-adds-one-nbor'' g {nuv = nuv} {pu = pu} {pv = pv} {npuv = npuv} e2e) Eq.refl))) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      ((1 + Graph.nnbors Gr g e2) +
      List.sum (List.map (Graph.nnbors Gr gp) b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Nat.+-assoc 1 (Graph.nnbors Gr g e2) (List.sum (List.map (Graph.nnbors Gr gp) b))))) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (1 + (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b)))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Nat.+-assoc (List.sum (List.map (Graph.nnbors Gr g) m)) 1 (Graph.nnbors Gr g e2 + List.sum (List.map (Graph.nnbors Gr gp) b)))) ⟨
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      ((List.sum (List.map (Graph.nnbors Gr g) m) +
      1) + (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ (Nat.+-comm (List.sum (List.map (Graph.nnbors Gr g) m)) 1) Eq.refl)) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b)))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Nat.+-assoc (Graph.nnbors Gr g e1) 1 (List.sum (List.map (Graph.nnbors Gr g) m) + (Graph.nnbors Gr g e2 + List.sum (List.map (Graph.nnbors Gr gp) b)))) ⟨
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      ((Graph.nnbors Gr g e1 +
      1) +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ (Nat.+-comm (Graph.nnbors Gr g e1) 1) Eq.refl) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (1 +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b)))))
    ≡⟨ Nat.+-assoc 1 (List.sum (List.map (Graph.nnbors Gr g) f)) (1 + (Graph.nnbors Gr g e1 + (List.sum (List.map (Graph.nnbors Gr g) m) + (Graph.nnbors Gr g e2 + List.sum (List.map (Graph.nnbors Gr gp) b))))) ⟩
      1 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (1 +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b))))))
    ≡⟨ Eq.cong₂ _+_ {1} Eq.refl (Nat.+-assoc (List.sum (List.map (Graph.nnbors Gr g) f)) 1 (Graph.nnbors Gr g e1 + (List.sum (List.map (Graph.nnbors Gr g) m) + (Graph.nnbors Gr g e2 + List.sum (List.map (Graph.nnbors Gr gp) b))))) ⟨
      1 +
      ((List.sum (List.map (Graph.nnbors Gr g) f) +
      1) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b)))))
    ≡⟨ Eq.cong₂ _+_ {1} Eq.refl (Eq.cong₂ _+_ (Nat.+-comm (List.sum (List.map (Graph.nnbors Gr g) f)) 1) Eq.refl) ⟩
      1 +
      (1 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b))))))
    ≡⟨⟩
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b)))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e2} Eq.refl ((Eq.cong List.sum (edgelist-addedge-adds-no-nbors' g {b} {u} {v} {nuv} {pu} {pv} {npuv} bu bv))))))) ⟩
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr g) b)))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e2} (Eq.trans Eq.refl (Nat.+-comm 0 (Graph.nnbors Gr g e2))) Eq.refl)))) ⟩
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (List.sum (List.map (Graph.nnbors Gr g) (e2 ∷ [])) +
      List.sum (List.map (Graph.nnbors Gr g) b)))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (list-sum-split {List.map (Graph.nnbors Gr g) (e2 ∷ [])} {List.map (Graph.nnbors Gr g) b})))) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      List.sum (List.map (Graph.nnbors Gr g) (e2 ∷ []) ++ List.map (Graph.nnbors Gr g) b))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {e2 ∷ []} {b}))))) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      List.sum (List.map (Graph.nnbors Gr g) (e2 ∷ b)))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (list-sum-split {List.map (Graph.nnbors Gr g) m}))) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr g) m ++ List.map (Graph.nnbors Gr g) (e2 ∷ b))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {m} {e2 ∷ b})))) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr g) (m ++ e2 ∷ b))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} (Eq.trans Eq.refl (Nat.+-comm 0 (Graph.nnbors Gr g e1))) Eq.refl)) ⟩
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (List.sum (List.map (Graph.nnbors Gr g) (e1 ∷ [])) +
      List.sum (List.map (Graph.nnbors Gr g) (m ++ e2 ∷ b))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (list-sum-split {List.map (Graph.nnbors Gr g) (e1 ∷ [])} {List.map (Graph.nnbors Gr g) (m ++ e2 ∷ b)})) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (List.sum (List.map (Graph.nnbors Gr g) (e1 ∷ []) ++ List.map (Graph.nnbors Gr g) (m ++ e2 ∷ b))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {e1 ∷ []} {m ++ e2 ∷ b}))) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (List.sum (List.map (Graph.nnbors Gr g) (e1 ∷ m ++ e2 ∷ b))))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (list-sum-split {List.map (Graph.nnbors Gr g) f}) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f ++ List.map (Graph.nnbors Gr g) (e1 ∷ m ++ e2 ∷ b)))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {f})) ⟨
      2 + List.sum (List.map (Graph.nnbors Gr g) (f ++ e1 ∷ m ++ e2 ∷ b))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (Eq.cong List.sum (Eq.cong₂ List.map Eq.refl (Eq.sym eq))) ⟨
      2 + List.sum (List.map (Graph.nnbors Gr g) (UniqueList.l vs))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (vec-annoying {ℕ} {UniqueList.l vs}) ⟨
      2 + Vec.sum (Vec.map (Graph.nnbors Gr g) (Graph.nodes Gr g))
    ∎
    -- where
    -- UNC : Set
    -- UNC = (¬ contains f u) × (¬ contains m u) × (¬ contains b u)

    -- VNC : Set
    -- VNC = (¬ contains f v) × (¬ contains m v) × (¬ contains b v)

    -- sorted : Σ[ (e1 , e2) ∈ (ℕ × ℕ) ] ((f ++ e1 ∷ m ++ e2 ∷ b ≡ UniqueList.l vs) × (¬ contains f e1) × (¬ contains f e2) × (¬ contains m e1) × (¬ contains m e2) × (¬ contains b e1) × (¬ contains b e2))
    -- sorted = Data.Sum.[ (λ x → (u , v) , (x , fu , fv , mu , mv , bu , bv)) , (λ x → (v , u) , (x , fv , fu , mv , mu , bv , bu)) ] ueq
```

```agda
open import Data.Nat.DivMod as DivMod

addedge-adds-an-edge : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-an-edge Gr g = ∀ {u v nuv pu pv npuv} → Graph.m Gr (Graph.addedge Gr g (u , v) nuv pu pv npuv) ≡ 1 + Graph.m Gr g

edgelist-addedge-adds-an-edge : (g : Edgelist) → addedge-adds-an-edge edgelist-nat-graph g
edgelist-addedge-adds-an-edge (vs , es) {u} {v} {nuv} {pu} {pv} {npuv} =
    let g = (vs , es) in
    let Gr = edgelist-nat-graph in
    let (vs' , es') = Graph.addedge Gr g (u , v) nuv pu pv npuv in
    let gp = (vs' , es') in
    let open ≡-Reasoning in
    begin
      List.length es' / 2
    ≡⟨⟩
      (2 + List.length es) / 2
    ≡⟨ +-distrib-/ 2 (List.length es) dlemma ⟩
      1 + List.length es / 2
    ∎
    where
    dlemma : 2 % 2 + (List.length es) % 2 Data.Nat.< 2
    dlemma = m%n<n (List.length es) 2

-- edgelist-addedge-adds-no-nbors' : (g : Edgelist) → addedge-adds-no-nbors' edgelist-nat-graph g
-- edgelist-addedge-adds-no-nbors' g {[]} _ _ = Eq.refl
-- edgelist-addedge-adds-no-nbors' g {x ∷ ws} {u} {v} {nuv} {pu} {pv} {npuv} nlu nlv =
```

```agda
handshake : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
handshake Gr g = Vec.sum (Vec.map (Graph.nnbors Gr g) (Graph.nodes Gr g)) ≡ 2 * Graph.m Gr g

-- addnode-edgelist-const-nnbors : ∀ {g v p vc} → Graph.nnbors edgelist-nat-graph g vc ≡ Graph.nnbors edgelist-nat-graph (Graph.addnode edgelist-nat-graph g v p) vc
-- addnode-edgelist-const-nnbors = {!   !}

-- handshake2 : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
-- handshake2 Gr g = nonnode-no-edges Gr g × handshake Gr g

edgelist-handshake : graph-induction edgelist-nat-graph handshake
edgelist-handshake empty-gcons = Eq.refl
edgelist-handshake {gp} (addnode-gcons {g} gc {v} {p}) =
                        let Gr = edgelist-nat-graph in
                        let open ≡-Reasoning in
                        begin
                        Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr gp))
                        ≡⟨⟩
                        Vec.sum (Vec.map (Graph.nnbors Gr gp) (v Vec.∷ (Graph.nodes Gr g)))
                        ≡⟨⟩
                        Vec.sum ((Graph.nnbors Gr gp v) Vec.∷ Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr g))
                        ≡⟨⟩
                        (Graph.nnbors Gr gp v) + Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr g))
                        ≡⟨⟩
                        (Graph.nnbors Gr gp v) + Vec.sum (Vec.map (Graph.nnbors Gr g) (Graph.nodes Gr g))
                        ≡⟨ Eq.cong₂ _+_ Eq.refl (edgelist-handshake gc) ⟩
                        (Graph.nnbors Gr gp v) + 2 * Graph.m Gr g
                        ≡⟨⟩
                        (Graph.nnbors Gr gp v) + 2 * Graph.m Gr g
                        ≡⟨⟩
                        (Graph.nnbors Gr g v) + 2 * Graph.m Gr g
                        ≡⟨ Eq.cong₂ _+_ (edgelist-nonnode-no-edges gc v p) Eq.refl ⟩
                        0 + 2 * Graph.m Gr g
                        ≡⟨⟩
                        2 * Graph.m Gr gp
                        ∎
edgelist-handshake {gp} (addegde-gcons {g} gc {u , v} {p1} {p2} {p3} {p4}) =
                        let Gr = edgelist-nat-graph in
                        let open ≡-Reasoning in
                        begin
                        Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr gp))
                        ≡⟨⟩
                        Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr g))
                        ≡⟨ edgelist-addedge-adds-two-nbors g {u} {v} {p1} {p2} {p3} {p4} ⟩
                        2 + Vec.sum (Vec.map (Graph.nnbors Gr g) (Graph.nodes Gr g))
                        ≡⟨ Eq.cong₂ _+_ Eq.refl (edgelist-handshake gc) ⟩
                        2 + 2 * Graph.m Gr g
                        ≡⟨⟩
                        2 * 1 + 2 * Graph.m Gr g
                        ≡⟨ Nat.*-distribˡ-+ 2 1 (Graph.m Gr g) ⟨
                        2 * (1 + Graph.m Gr g)
                        ≡⟨ Eq.cong₂ _*_ {2} Eq.refl (edgelist-addedge-adds-an-edge g {u} {v} {p1} {p2} {p3} {p4}) ⟨
                        2 * Graph.m Gr gp
                        ∎
```
 