module Act.SymmetricMonoidalPreorder

import Act.Preorder

%default total
%access public export

|||  Preorder with symmetric monoidal structure (X, <=, ⊗, I) is a preorder (X, <=) equipped with:
|||  - monoidal product: operation ⊗ : X × X -> X
|||  - monoidal unit: element I
|||  such that:
|||  - monotonicity: if a1 <= b1 and a2 <= b2, then a1 ⊗ a2 <= b1 ⊗ b2
|||  - unitality: I ⊗ a = a and a ⊗ I = a
|||  - associativity: (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)
|||  - symmetry: a ⊗ b = b ⊗ a
interface Preorder t => SymmetricMonoidalPreorder t where
  (<=) : t -> t -> Bool
  combine : t -> t -> t
  I : t
  leftUnitality : {a : t} ->
    combine I a = a
  rightUnitality : {a : t} ->
    a = combine a I
  associativity : {a : t} -> {b : t} -> {c : t} ->
    combine (combine a b) c = combine a (combine b c)
  reflexivity : {a : t} ->
    a <= a = true
  transitivity : {a : t} -> {b : t} -> {c : t} ->
    (a <= b) && (b <= c) = (a <= c) -- not sure if this is correct => instead of =
  monotonicity : {a1 : t} -> {a2 : t} -> {b1 : t} -> {b2 : t} ->
    (a1 <= b1) && (a2 <= b2) = (combine a1 b1) <= (combine a2 b2)
  symmetry : {a : t} -> {b : t} ->
    (combine a b) = (combine b a)
