module Act.Preorder

%default total
%access public export

|||  Preorder is a (X, ≤) set X equipped with binary relation ≤
|||  that is reflexive and transitive.
interface Preorder t where
  (<=) : t -> t -> Bool
  reflexivity : {a : t} ->
    a <= a = true
  transitivity : {a : t} -> {b : t} -> {c : t} ->
    (a <= b) && (b <= c) = (a <= c) -- not sure if this is correct => instead of =
