module Act.Equivalence

%default total
%access public export

|||  Equivalence is a binary relation that is reflexive, symmetric and transitive
interface Equivalence t where
  equiv : t -> t -> Bool
  reflexivity : {a : t} ->
    equiv a a = true
  symmetry : {a : t} -> {b : t} ->
    equiv a b = equiv b a
  transitivity : {a : t} -> {b : t} -> {c : t} ->
    (equiv a b) && (equiv b c) = equiv a c -- not sure if this is correct => instead of =
