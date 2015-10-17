signature Stringset =
sig
  eqtype set

  exception NotFound

  val empty        : set
  val singleton    : string -> set
  val fromList     : string list -> set
  val add          : set * string -> set
  val addList      : set * string list -> set
  val retrieve     : set * string -> string
  val peek         : set * string -> string option
  val isEmpty      : set -> bool
  val isSubset     : set * set -> bool
  val member       : set * string -> bool
  val delete       : set * string -> set
  val numItems     : set -> int
  val union        : set * set -> set
  val intersection : set * set -> set
  val big          : (set * set -> set) -> set list -> set
  val difference   : set * set -> set
  val listItems    : set -> string list
  val find         : (string -> bool) -> set -> string option

  val printer : int -> 'a -> set -> PolyML.pretty
end

(*
   [set] is the type of sets of strings.

   [empty] creates a new empty set.

   [singleton i] creates the singleton set containing i.

   [fromList xs] creates the set containing all items from the list xs.

   [add(s, i)] adds item i to set s.

   [addList(s, xs)] adds all items from the list xs to the set s.

   [retrieve(s, i)] returns i if it is in s; raises NotFound otherwise.

   [peek(s, i)] returns SOME i if i is in s; returns NONE otherwise.

   [isEmpty s] returns true if and only if the set is empty.

   [isSubset(s1, s2)] returns true if and only if s1 is a subset of s2.

   [member(s, i)] returns true if and only if i is in s.

   [delete(s, i)] removes item i from s.  Raises NotFound if i is not in s.

   [numItems s] returns the number of items in set s.

   [union(s1, s2)] returns the union of s1 and s2.

   [intersection(s1, s2)] returns the intersection of s1 and s2.

   [difference(s1, s2)] returns the difference between s1 and s2 (that
   is, the set of elements in s1 but not in s2).

   [listItems s] returns a list of the items in set s, in increasing
   order.

   [find p s] returns SOME i, where i is an item in s which satisfies
   p, if one exists; otherwise returns NONE.  Traverses the entries of
   the set in increasing order.
*)

structure Stringset :> Stringset =
struct

fun fst (x, _) = x

type set = unit Stringmap.dict

exception NotFound

val empty = Stringmap.empty: set
val isEmpty = Stringmap.isEmpty: set -> bool
val numItems = Stringmap.numItems: set -> int

fun mku (s: string) = (s, ())
val mkus = List.map mku

fun singleton s = Stringmap.fromList [mku s]: set

val fromList = Stringmap.fromList o mkus: string list -> set

fun add (x: set, s) = Stringmap.insert (x, s, ()): set

fun addList (x: set, ss) = Stringmap.insertList (x, mkus ss): set

fun retrieve (x: set, s) =
   (Stringmap.find (x, s) handle Stringmap.NotFound => raise NotFound; s)

fun peek (x: set, s) = Option.map (fn () => s) (Stringmap.peek (x, s))

fun member (x: set, s) = Stringmap.found (x, s)

fun delete (x: set, s) =
   fst (Stringmap.remove (x, s)): set
   handle Stringmap.NotFound => raise NotFound

val listItems = List.map fst o Stringmap.listItems: set -> string list

fun find P = List.find P o listItems

fun difference (x: set, y) =
   List.foldl (fn (s, z) => delete (z, s)) x (listItems y)

fun isSubset (x: set, y) = List.all (fn s => member (y, s)) (listItems x)

fun order (x: set, y: set) = if numItems x < numItems y then (x, y) else (y, x)

fun union (x, y) =
   let
      val (s1, s2) = order (x, y)
   in
      addList (s2, listItems s1)
   end

fun intersection (x, y) =
   let
      val (s1, s2) = order (x, y)
   in
      fromList (List.filter (fn s => member (s2, s)) (listItems s1))
   end

fun big f [] = empty
  | big f (h::t) = List.foldl f h t

fun printer (_: int) _ (s: set) =
   PolyML.PrettyString ("<set(" ^ Int.toString (numItems s) ^ ")>")

end

val _ = PolyML.addPrettyPrinter Stringset.printer
