(* -------------------------------------------------------------------------
   Helper functions
   ------------------------------------------------------------------------- *)

PolyML.use "Lib.sml";
PolyML.use "Stringmap.sml";
PolyML.use "Stringset.sml";

infixr 6 **
infixr 5 --> --->
infix |-> |=>

(* -------------------------------------------------------------------------
   Positive Integer Sets

   Sets of positive integers, i.e. subsets of {1, 2, ...}
   ------------------------------------------------------------------------- *)

signature PosIntSet =
sig
   eqtype pintset

   val complement: pintset -> pintset
   val diff: pintset -> pintset -> pintset
   val empty: pintset
   val fromList: int list -> pintset
   val fromRangeList: (int * int option) list -> pintset
   val infimum: pintset -> int
   val insert: int -> pintset -> pintset
   val insertList: pintset -> int list -> pintset
   val intersect: pintset -> pintset -> pintset
   val isempty: pintset -> bool
   val issingleton: pintset -> bool
   val isuniv: pintset -> bool
   val member: int -> pintset -> bool
   val remove: int -> pintset -> pintset
   val removeList: pintset -> int list -> pintset
   val singleton: int -> pintset
   val size: pintset -> int
   val subset: pintset -> pintset -> bool
   val supremum: pintset -> int
   val toList: pintset -> int list
   val toRangeList: pintset -> (int * int option) list
   val toString: pintset -> string
   val union: pintset -> pintset -> pintset
   val univ: pintset

   val printer: int -> 'a -> pintset -> PolyML.pretty
end

structure PosIntSet :> PosIntSet =
struct
   type pintset = (int * int) list

   val empty = []: pintset
   val univ = [(1, ~1)]: pintset

   fun infimum l = fst (hd l) handle Empty => raise Fail "PosIntSet: infimum"

   fun supremum l =
     (case List.last l of
         (_, ~1) => ~1
       | (i, d) => i + d)
     handle Empty => raise Fail "PosIntSet: supremum"

   val size =
      let
         fun sz a =
            fn [] => a
             | [(_, ~1)] => ~1
             | (_:int, d)::t => sz (a + 1 + d) t
      in
         sz 0
      end

   val isempty = equal 0 o size
   val isuniv  = equal ~1 o size
   val issingleton = equal 1 o size

   val toList =
      let
         fun tol a =
            fn [] => List.concat (List.rev a)
             | [(_, ~1)] => raise Fail "PosIntSet.toList: infinite"
             | (i, d) :: t => tol (List.tabulate (d + 1, fn j => i + j) :: a) t
      in
         tol []
      end

   fun member i =
      let
         fun mem [] = false
           | mem [(j, ~1)] = j <= i
           | mem ((j, d) :: t) = if i <= j + d then j <= i else mem t
      in
         if i < 1 then K false else mem
      end

   fun insertRange (i, n) =
      let
         fun ins [] = [(i, n)]
           | ins [(j, ~1)] = [(Int.min (i, j), ~1)]
           | ins (l as ((j, d) :: t)) =
               if n = ~1
                  then if j + d < i andalso i <> j + d + 1
                          then (j, d) :: ins t
                       else [(Int.min (i, j), ~1)]
               else if i < j
                       then if i + n < j
                               then if j = i + n + 1
                                       then (i, n + d + 1) :: t
                                    else (i, n) :: l
                            else if i + n <= j + d
                                    then (i, j + d - i) :: t
                                 else ins t
                    else if i <= j + d + 1
                       then if i + n <= j + d andalso i <> j + d + 1
                               then l
                            else insertRange (j, i + n - j) t
                    else (j, d) :: ins t
      in
         if i < 1 orelse n < ~1 then raise Fail "insertRange" else ins
      end

   fun union (s1: pintset) (s2: pintset) =
      case (s1, s2) of
         ([], _) => s2
       | (_, []) => s1
       | (h :: t, _) => union t (insertRange h s2)

   val complement =
      let
         fun cmp (a, j) =
            fn [] => List.rev ((j, ~1)::a)
             | [(1, ~1)] => []
             | [(i, ~1)] => List.rev ((j, i - j - 1) :: a)
             | (1, d)::t => cmp (a, d + 2) t
             | (i, d)::t => cmp ((j, i - j - 1) :: a, i + d + 1) t
      in
         cmp ([], 1)
      end

   fun insert i = insertRange (i, 0)
   fun singleton i = insert i []
   fun intersect a b = complement (union (complement a) (complement b))
   fun diff a b = complement (union (complement a) b)
   fun subset a b = union a b = b
   fun remove i s = diff s (singleton i)

   fun insertList l = List.foldl (uncurry insert) l
   fun removeList l = List.foldl (uncurry remove) l

   val fromList = insertList empty

   val toRangeList =
      List.map (fn (i, d) => if d = ~1 then (i, NONE) else (i, SOME (i + d)))

   local
      val fromRange =
         fn (i, NONE) => if 0 < i then (i, ~1) else raise Fail "Bad range list"
          | (i, SOME j) => if 0 < i andalso i <= j
                              then (i, j - i)
                           else raise Fail "Bad range list"
   in
      val fromRangeList =
         List.foldl (fn (x, s) => insertRange (fromRange x) s) empty
   end

   local
      fun range (i, d) =
         Int.toString i ^
            (case d of
                ~1 => "..."
              | 0 => ""
              | 1 => ", " ^ Int.toString (i + 1)
              | _ => "-" ^ Int.toString (i + d))
   in
      fun toString s = "{" ^ commify range s ^ "}"
   end

   fun printer (_: int) _ (s: pintset) = PolyML.PrettyString (toString s)

end (* structure PosIntSet *)

val _ = PolyML.addPrettyPrinter PosIntSet.printer

(* -------------------------------------------------------------------------
   Constraint Sets

   A partial map from strings to PosIntSet
   ------------------------------------------------------------------------- *)

signature Constrain =
sig
   type constraints

   val add: constraints * string * PosIntSet.pintset -> constraints
   val constraint: constraints * string -> PosIntSet.pintset
   val empty: constraints
   val fromList: (string * PosIntSet.pintset) list -> constraints
   val isEmpty: constraints -> bool
   val lookup: constraints * string -> PosIntSet.pintset option
   val merge: constraints * constraints -> constraints
   val restrict: constraints * Stringset.set -> constraints
   val singleton: string * PosIntSet.pintset -> constraints
   val toList: constraints -> (string * PosIntSet.pintset) list
   val toString: constraints -> string

   val printer: int -> 'a -> constraints -> PolyML.pretty
end

structure Constrain :> Constrain =
struct
   type constraints = PosIntSet.pintset Stringmap.dict

   val empty = Stringmap.empty: constraints

   fun isEmpty (c: constraints) = Stringmap.isEmpty c
   fun lookup (c: constraints, v) = Stringmap.peek (c, v)
   fun constraint (c, v) = Option.getOpt (lookup (c, v), PosIntSet.univ)

   fun primAdd (c, v, s) =
      if PosIntSet.isempty s
         then raise Fail ("Constraint empty: " ^ v)
      else Stringmap.insert (c, v, s)

   fun singleton (v, s) = primAdd (empty, v, s)

   fun add (c, v, s) =
      case lookup (c, v) of
        SOME s2 => raise Fail ("Constraint already exists: " ^ v)
      | NONE => primAdd (c, v, s)

   val fromList = List.foldl (fn ((v, s), c) => add (c, v, s)) empty
   val toList = Stringmap.listItems

   fun merge (c1, c2) =
      if Stringmap.isEmpty c2
         then c1
      else let
              fun mrg (v, s1) =
                  case lookup (c2, v) of
                     SOME s2 => let
                                   val s3 = PosIntSet.intersect s1 s2
                                in
                                   if PosIntSet.isempty s3
                                      then raise Fail "Constraint merge: empty"
                                   else s3
                                end
                   | NONE => s1
              val c3 = Stringmap.map mrg c1
              val l = Stringmap.listItems c2
              val l = List.filter
                         (fn (v, s) => not (Stringmap.found (c3, v)) andalso
                                       not (PosIntSet.isuniv s)) l
           in
              Stringmap.insertList (c3, l)
           end

   fun restrict (c, s) =
      let
         val a = Stringmap.keys c
         val a' = List.filter (fn n => not (Stringset.member (s, n))) a
      in
         Stringmap.removeList (c, a')
      end

   fun toString c =
      case Stringmap.listItems c of
        [] => "-"
      | l => separate " and " (fn (v, s) => v ^ " in " ^ PosIntSet.toString s) l

   fun printer (_: int) _ (c: constraints) = PolyML.PrettyString (toString c)

end (* structure Constrain *)

val _ = PolyML.addPrettyPrinter Constrain.printer

(* -------------------------------------------------------------------------
   Tagging

   Support for tagging operator names with a selection of prefixes
   ------------------------------------------------------------------------- *)

signature Tag =
sig
   val ASTChar: char
   val contains: char -> string -> bool
   val exceptionChar: char
   val isAST: string -> bool
   val isException: string -> bool
   val isRecord: string -> bool
   val mkAST: string -> string
   val mkDefine: string -> string
   val mkException: string -> string
   val mkRecord: string -> string
   val recordChar: char
   val remove: string -> string
end

structure Tag :> Tag =
struct
   fun remove s = String.extract (s, 1, NONE)
   fun contains c s = Substring.isSubstring (String.str c) (Substring.full s)
   fun pc c = (c, fn s => String.str c ^ s, fn s => String.sub (s, 0) = c)

   val (ASTChar, mkAST, isAST) = pc #"@"
   val (recordChar, mkRecord, isRecord) = pc #"!"
   val (exceptionChar, mkException, isException) = pc #"#"

   val string2 = Substring.string ## Substring.string

   fun mkDefine s =
      let
         val ss = Substring.full s
      in
         case string2 (Substring.splitl (not o Lib.equal #"@") ss) of
            ("", _) => raise Fail "mkDefine: is AST"
          | (l, _) => mkAST l
      end
end

(* -------------------------------------------------------------------------
   Type

   Data structure for representing L3 types
   ------------------------------------------------------------------------- *)

signature Type =
sig
   datatype pty = OptionTy | ListTy | SetTy

   datatype bty =
        VarType of string
      | ConstType of string
      | BV of int
      | BVV of string
      | ParamType of pty * bty
      | Prod of bty * bty
      | Arrow of bty * bty

   type ty = bty * Constrain.constraints

   datatype dty =
        FixedBits of int
      | VarBits of string * PosIntSet.pintset
      | Other of string

   datatype typesubst =
        SubstBits of string * dty
      | SubstType of string * ty

   val ** : ty * ty -> ty
   val --> : ty * ty -> ty
   val alphaTy: ty
   val anonTypeToString: ty -> string
   val appType: (ty -> unit) -> ty -> unit
   val betaTy: ty
   val bitsSize: ty -> int option
   val bitsTypeVars: ty -> Stringset.set
   val bitstringTy: ty
   val boolTy: ty
   val charTy: ty
   val checkConstraint: Constrain.constraints -> ty -> unit
   val combineSubst: typesubst list -> typesubst list -> typesubst list
   val compare: ty * ty -> order
   val constrainTy: string -> ty
   val destConstType: ty -> string
   val destType: ty -> dty
   val dom: ty -> ty
   val domrng: ty -> ty * ty
   val eqAlphaTy: ty
   val eqBetaTy: ty
   val filterSubst: int -> typesubst list -> typesubst list
   val fixedTy: int -> ty
   val foldProdList: ty list -> ty
   val freeBitsTypeVars: ty -> Stringset.set
   val freeTypeVars: ty -> Stringset.set
   val freshBitsTypeVars: ty -> Stringset.set
   val freshEqTyVar: unit -> ty
   val freshMarker: unit -> int
   val freshName: unit -> string
   val freshTyVar: unit -> ty
   val freshTypeString: ty -> string
   val freshTypeStrings: ty * ty -> string * string
   val freshTypeVars: ty -> Stringset.set
   val freshWordTy: unit -> ty
   val fstTy: ty -> ty
   val fstsnd: ty -> ty * ty
   val hasFreshTypeVars: ty -> bool
   val hasTypeVars: ty -> bool
   val instructionTy: ty
   val intTy: ty
   val isEqVarType: string -> bool
   val isFixedTy: ty -> bool
   val isFreeVar: string -> bool
   val isFreshVar: string -> bool
   val isListTy: ty -> bool
   val isMapTy: ty -> bool
   val isOptionTy: ty -> bool
   val isProdTy: ty -> bool
   val isSetTy: ty -> bool
   val isWordTy: ty -> bool
   val listProd: ty -> 'a list -> ty
   val listTy: ty -> ty
   val mkConstType: string -> ty
   val mkEmpty: bty -> ty
   val mkFresh: ty -> ty
   val mkVarType: string -> ty
   val natTy: ty
   val normalize: ty -> ty
   val optionTy: ty -> ty
   val resetConstraint: unit -> unit
   val resetName: unit -> unit
   val roundingTy: ty
   val rng: ty -> ty
   val setConstraint: Constrain.constraints -> unit
   val setTy: ty -> ty
   val sndTy: ty -> ty
   val stringTy: ty
   val typeSubst: typesubst list -> ty -> ty
   val typeToString: ty -> string
   val typeVars: ty -> Stringset.set
   val unitTy: ty
   val wordTy: string -> ty
   val |-> : string * ty -> typesubst
   val |=> : string * dty -> typesubst

   val printer: int -> 'a -> bty -> PolyML.pretty
end

structure Type :> Type =
struct
   datatype pty = OptionTy | ListTy | SetTy

   datatype bty =
        VarType of string
      | ConstType of string
      | BV of int
      | BVV of string
      | ParamType of pty * bty
      | Prod of bty * bty
      | Arrow of bty * bty

   type ty = bty * Constrain.constraints

   fun compare_pty (a, b) =
      if a = b
         then General.EQUAL
      else if a = OptionTy
         then General.LESS
      else if a = ListTy
         then if b = OptionTy then General.GREATER else General.LESS
      else General.GREATER

   fun compare_bty (x, y) =
      case (x, y) of
         (VarType a, VarType b) => String.compare (a, b)
       | (VarType _, _) => General.LESS
       | (ConstType _, VarType _) => General.GREATER
       | (ConstType a, ConstType b) => String.compare (a, b)
       | (ConstType _, _) => General.LESS
       | (BV _, VarType _) => General.GREATER
       | (BV _, ConstType _) => General.GREATER
       | (BV a, BV b) => Int.compare (a, b)
       | (BV a, _) => General.LESS
       | (BVV _, VarType _) => General.GREATER
       | (BVV _, ConstType _) => General.GREATER
       | (BVV _, BV _) => General.GREATER
       | (BVV a, BVV b) => String.compare (a, b)
       | (BVV a, _) => General.LESS
       | (ParamType a, ParamType b) =>
            Lib.pairCompare (compare_pty, compare_bty) (a, b)
       | (ParamType _, Prod _) => General.LESS
       | (ParamType _, Arrow _) => General.LESS
       | (ParamType _, _) => General.GREATER
       | (Prod a, Prod b) => Lib.pairCompare (compare_bty, compare_bty) (a, b)
       | (Prod a, Arrow _) => General.LESS
       | (Prod a, _) => General.GREATER
       | (Arrow a, Arrow b) => Lib.pairCompare (compare_bty, compare_bty) (a, b)
       | (Arrow a, _) => General.GREATER

   fun compare (ty1: ty, ty2: ty) = compare_bty (fst ty1, fst ty2)

   fun hasTypeVars P ((bty, _): ty) =
      let
         fun hasvars t =
            case t of
               VarType w => P w
             | BVV w => P w
             | ParamType (_, w) => hasvars w
             | Prod (u, w) => hasvars u orelse hasvars w
             | Arrow (u, w) => hasvars u orelse hasvars w
             | _ => false
      in
         hasvars bty
      end

   fun appType (f: ty -> unit) ((bty, c): ty) =
      let
         fun g t =
           ( f (t, c)
           ; case t of
                ParamType (_, w) => g w
              | Prod (u, w) => (g u; g w)
              | Arrow (u, w) => (g u; g w)
              | _ => ()
           )
      in
         g bty
      end

   fun findTypeVars P Q ty =
      let
         val vs1 = ref Stringset.empty
         val vs2 = ref Stringset.empty
         fun f ((t, _): ty) =
            case t of
               VarType w => if P w then vs1 := Stringset.add (!vs1, w) else ()
             | BVV w => if Q w then vs2 := Stringset.add (!vs2, w) else ()
             | _ => ()
      in
         appType f ty; (!vs1, !vs2)
      end

   val typeVars = fst o findTypeVars (K true) (K false)
   val bitsTypeVars = snd o findTypeVars (K false) (K true)

   fun normalize (t as (bty, c): ty) =
      if Constrain.isEmpty c
         then t
      else let
              val vs = bitsTypeVars t
           in
              (bty, Constrain.restrict (c, vs)): ty
           end

   fun op ** ((bty1, c1), (bty2, c2)) =
      (Prod (bty1, bty2), Constrain.merge (c1, c2))

   fun op --> ((bty1, c1), (bty2, c2)) =
      (Arrow (bty1, bty2), Constrain.merge (c1, c2))

   val rng =
      fn (Arrow (_, ty), c) => normalize (ty, c)
       | _ => raise Fail "rng"

   val dom =
      fn (Arrow (ty, _), c) => normalize (ty, c)
       | _ => raise Fail "dom"

   val domrng =
      fn (Arrow (ty1, ty2), c) => (normalize (ty1, c), normalize (ty2, c))
       | _ => raise Fail "domrng"

   val fstTy =
      fn (Prod (ty, _), c) => normalize (ty, c)
       | _ => raise Fail "fstTy"

   val sndTy =
      fn (Prod (_, ty), c) => normalize (ty, c)
       | _ => raise Fail "sndTy"

   val fstsnd =
      fn (Prod (ty1, ty2), c) => (normalize (ty1, c), normalize (ty2, c))
       | _ => raise Fail "fstsnd"

   fun isProdTy (Prod _, _) = true
     | isProdTy _ = false

   fun isMapTy (Arrow _, _) = true
     | isMapTy _ = false

   fun isListTy (ParamType (ListTy, _), _) = true
     | isListTy _ = false

   fun isOptionTy (ParamType (OptionTy, _), _) = true
     | isOptionTy _ = false

   fun isSetTy (ParamType (SetTy, _), _) = true
     | isSetTy _ = false

   fun isFixedTy (BV _, _) = true
     | isFixedTy _ = false

   fun isWordTy (BV _, _) = true
     | isWordTy (BVV _, _) = true
     | isWordTy _ = false

   val destConstType =
      fn (ConstType s, _) => s
       | _ => raise Fail "destConstType"

   val bitsSize =
      fn (BV i, _) => SOME i
       | (ConstType "bool", _) => SOME 1
       | _ => NONE

   fun isFreshVar v =
      case String.sub (v, 0) of
        #"'" => String.sub (v, 1) = #"_"
      | #"_" => true
      | _ => false

   val isFreeVar = not o isFreshVar
   fun isEqVarType v = String.sub (v, 0) = #"'"

   val hasFreshTypeVars = hasTypeVars isFreshVar
   val hasTypeVars = hasTypeVars (K true)

   val freshTypeVars = fst o findTypeVars isFreshVar (K false)
   val freeTypeVars = fst o findTypeVars isFreeVar (K false)
   val freshBitsTypeVars = snd o findTypeVars (K false) isFreshVar
   val freeBitsTypeVars = snd o findTypeVars (K false) isFreeVar

   fun mkEmpty bty = (bty, Constrain.empty): ty

   val mkVarType = mkEmpty o VarType

   val alphaTy   = mkVarType "a"
   val eqAlphaTy = mkVarType "'a"
   val betaTy    = mkVarType "b"
   val eqBetaTy  = mkVarType "'b"

   val mkConstType = mkEmpty o ConstType

   val boolTy        = mkConstType "bool"
   val charTy        = mkConstType "char"
   val natTy         = mkConstType "nat"
   val intTy         = mkConstType "int"
   val unitTy        = mkConstType "unit"
   val instructionTy = mkConstType "instruction"
   val roundingTy    = mkConstType "rounding"

   val wordTy  = mkEmpty o BVV
   val fixedTy = mkEmpty o BV

   fun listTy (bty, s)   = (ParamType (ListTy, bty), s): ty
   fun optionTy (bty, s) = (ParamType (OptionTy, bty), s): ty
   fun setTy (bty, s)    = (ParamType (SetTy, bty), s): ty

   val stringTy    = mkEmpty (ParamType (ListTy, ConstType "char"))
   val bitstringTy = mkEmpty (ParamType (ListTy, ConstType "bool"))

   local
      val currentConstraint = ref Constrain.empty
   in
      fun setConstraint c = currentConstraint := c
      fun resetConstraint () = currentConstraint := Constrain.empty
      fun constrainTy v = normalize (BVV v, !currentConstraint)
   end

   fun typeVarToString x =
      let
         val e = isEqVarType x
         val s = if e then Tag.remove x else x
         val s = if isFreshVar s then Tag.remove s else s
      in
         (if e then "''" else "'") ^ s
      end

   val paramToString =
      fn ListTy => "list"
       | OptionTy => "option"
       | SetTy => "set"

   local
      val isArrow = fn Arrow _ => true | _ => false

      val isProdOrArrow =
         fn Prod _ => true
          | Arrow _ => true
          | _ => false

      fun brack p s = if p then "(" ^ s ^ ")" else s
   in
      fun typeToString anon ((bty, c): ty) =
         let
            fun var s = if anon andalso isFreshVar s
                           then "'_"
                        else typeVarToString s
            fun bits s = if anon andalso isFreshVar s
                            then "bits('_)"
                         else "bits(" ^ s ^ ")"
            fun tostr t =
               case t of
                  VarType s => var s
                | ConstType s => s
                | BVV s => bits s
                | BV n => "bits(" ^ Int.toString n ^ ")"
                | ParamType (p, e) => brackProdArrow e ^ " " ^ paramToString p
                | Prod (e1, e2) => brackProdArrow e1 ^ " * " ^ brackArrow e2
                | Arrow (e1, e2) => brackArrow e1 ^ " -> " ^ tostr e2
           and brackArrow t = brack (isArrow t) (tostr t)
           and brackProdArrow t = brack (isProdOrArrow t) (tostr t)
           val cons = case Constrain.toString c of
                        "-" => ""
                      | s => " with " ^ s
         in
            tostr bty ^ cons
         end
   end

   val anonTypeToString = typeToString true
   val typeToString = typeToString false

   fun listProd ty = List.foldl (fn (_, ty1) => ty ** ty1) ty

   fun foldProdList [] = raise Fail "foldProdList: empty"
     | foldProdList l =
          let
             val (h, t) = lastButlast l
          in
             List.foldr (fn (ty1, ty) => ty1 ** ty) h t
          end

   datatype dty =
        FixedBits of int
      | VarBits of string * PosIntSet.pintset
      | Other of string

   datatype typesubst =
        SubstBits of string * dty
      | SubstType of string * ty

   val op |-> = SubstType
   val op |=> = SubstBits

   fun destType ((bty, c): ty) =
      case bty of
         ConstType s => Other s
       | BV i => FixedBits i
       | BVV s => VarBits (s, Constrain.constraint (c, s))
       | ParamType (ListTy, ConstType "char") => Other "string"
       | ParamType (ListTy, ConstType "bool") => Other "bitstring"
       | ParamType (p, _) => Other (paramToString p)
       | _ => Other ""

   local
      val newc = ref Constrain.empty
      val oldc = ref Constrain.empty
      fun addc c = newc := Constrain.merge (!newc, c)
      fun constr w = Constrain.constraint (!oldc, w)
      fun fixedOkay (w, i) =
         if PosIntSet.member i (constr w)
            then BV i
         else raise Fail "typeSubst: contraint"
      fun subst x =
         case x of
            ([], bty) => bty
          | (_, bty as BV _) => bty
          | (_, bty as ConstType _) => bty
          | (l, bty as VarType w) =>
              (case List.find (fn SubstType (v, _) => v = w | _ => false) l of
                  SOME (SubstType (_, (ty, c))) => (addc c; ty)
                | _ => bty)
          | (l, bty as BVV w) =>
              (case List.find (fn SubstBits (v, _) => v = w | _ => false) l of
                  SOME (SubstBits (_, FixedBits i)) => fixedOkay (w, i)
                | SOME (SubstBits (_, VarBits (x as (n, s)))) =>
                   (case PosIntSet.size s of
                       0 => raise Fail "typeSubst: empty"
                     | ~1 => if PosIntSet.isuniv (constr w)
                                then BVV n
                             else raise Fail "typeSubst: contraint"
                     | 1 => fixedOkay (w, fst (hd (PosIntSet.toRangeList s)))
                     | _ => if PosIntSet.subset s (constr w)
                               then (addc (Constrain.singleton x); BVV n)
                            else raise Fail "typeSubst: contraint")
                | _ => bty)
          | (l, ParamType (p, w)) => ParamType (p, subst (l, w))
          | (l, Prod (v, w)) => Prod (subst (l, v), subst (l, w))
          | (l, Arrow (v, w)) => Arrow (subst (l, v), subst (l, w))
   in
      fun typeSubst [] ty = ty
        | typeSubst s (ty as (bty, c)) =
         if hasTypeVars ty
            then let
                    val () = (newc := Constrain.empty; oldc := c)
                    val (bty2, c2) = normalize (subst (s, bty), c)
                 in
                    normalize (bty2, Constrain.merge (c2, !newc))
                 end
         else ty
   end

   local
      fun substSubst s1 s2 =
         case (s1, s2) of
            (SubstBits _, SubstType (v, t)) => SOME (v |-> typeSubst [s1] t)
          | (SubstBits (v, t), SubstBits (u, VarBits (w, _))) =>
               if v = u then NONE else SOME (if v = w then u |=> t else s2)
          | (SubstType (v, t1), SubstType (u, t2)) =>
               if v = u then NONE else SOME (u |-> typeSubst [s1] t2)
          | _ => SOME s2
   in
      fun combineSubst [] r = r
        | combineSubst r [] = r
        | combineSubst r1 r2 =
         let
            fun iter ([], l) = l
              | iter (s :: r, l) = iter (r, List.mapPartial (substSubst s) l)
         in
            r1 @ iter (r1, r2)
         end
   end

   local
      val nextVar = ref 0
      val substVar =
         fn SubstType (v, _) => v
          | SubstBits (v, _) => v
      val base = 26
      val base2 = 2 * base
      val toLetterString =
         let
            fun c n = String.str o Char.chr o (fn i => Int.+ (n, i))
            fun d i = c (if i < base then 97 else 39) i
            fun iter a n =
               if n < base2
                  then d n ^ a
               else iter (d (Int.rem (n, base2)) ^ a) (Int.quot (n, base2))
         in
            iter ""
         end
      val fromLetterString =
         let
            fun i c =
               let val j = Char.ord c in j - (if j < 91 then 39 else 97) end
            fun iter a =
               fn [] => a
                | (h::t) => iter (a * base2 + i h) t
         in
            iter 0 o String.explode
         end
   in
      fun freshMarker () = (!nextVar)

      fun resetName () = nextVar := 0

      fun freshName () = "_" ^ toLetterString (!nextVar) before
                         nextVar := !nextVar + 1

      fun freshTyVar () = mkVarType (freshName ())
      fun freshEqTyVar () = mkVarType ("'" ^ freshName ())
      fun freshWordTy () = wordTy (freshName ())

      fun freshList c var s =
         let
            val v = ref 0
            fun w () = toLetterString (!v)
            fun mkEq s = if var andalso isEqVarType s then "'" ^ w() else w()
                         before v := !v + 1
            val l = ref []
            fun mkfresh h =
               let
                  val h' = mkEq h
                  val x = if var then h |-> (VarType h', c)
                          else h |=> VarBits (h', Constrain.constraint (c, h))
               in
                  l := x :: (!l)
               end
            fun fresh [] = ()
              | fresh (h :: t) = (mkfresh h; fresh t)
         in
            fresh (Stringset.listItems s); !l
         end

      fun filterSubst i =
         List.filter
            (fn s =>
                let val v = substVar s in
                   String.sub (v, 0) <> #"_" orelse
                   fromLetterString (Tag.remove v) < i
                end)
   end

   local
      fun mkVarFresh ty =
         List.foldl
            (fn (u, t) =>
               let
                  val v = if isEqVarType u
                             then freshEqTyVar ()
                          else freshTyVar ()
               in
                  typeSubst [u |-> v] t
               end) ty (Stringset.listItems (freeTypeVars ty))

      fun mkBitsFresh (ty as (bty, c)) =
         List.foldl
            (fn (u, t) =>
               let
                  val v = Constrain.constraint (c, u)
               in
                  typeSubst [u |=> VarBits (freshName (), v)] t
               end) ty (Stringset.listItems (freeBitsTypeVars ty))
   in
      val mkFresh = mkVarFresh o mkBitsFresh
   end

   local
      fun renameFresh (ty as (_, c)) =
         let
            val fl = freshList c
            val s1 = fl true (freshTypeVars ty)
            val s2 = fl false (freshBitsTypeVars ty)
         in
            typeSubst (s1 @ s2) ty
         end
   in
      val freshTypeString = typeToString o renameFresh

      fun freshTypeStrings (t1, t2) =
         let
            val ty = renameFresh (t1 ** t2)
         in
            (typeToString (fstTy ty), typeToString (sndTy ty))
         end
   end

   fun checkConstraint c ty =
      let
         val vs = Stringset.fromList (List.map fst (Constrain.toList c))
      in
         ignore (Stringset.isSubset (bitsTypeVars ty, vs) orelse
                 raise Fail ("Bad type/constraint: " ^ typeToString ty ^
                             " with " ^ Constrain.toString c))
      end

   fun printer (_: int) _ (t: bty) =
      PolyML.PrettyString (typeToString (mkEmpty t))

end (* structure Type *)

val _ = PolyML.addPrettyPrinter Type.printer

val op ** = Type.**
val op --> = Type.-->

(* -------------------------------------------------------------------------
   Type constants

   Support for user defined types + type matching and unification
   ------------------------------------------------------------------------- *)

signature Types =
sig
   exception Unify of string
   exception TypeMatch of string

   type cons_dict = Type.ty option Stringmap.dict

   datatype tydef = Constructors of cons
                  | Record of (string * Type.ty) list
                  | Typedef of Type.ty
                  | BaseType
   and cons = Enum of int Stringmap.dict
            | Construct of cons_dict

   type typeconst = {eq: bool, def: tydef, ast: bool, num: int}

   val ---> : Type.ty * Type.ty -> Type.ty
   val addConst: string * {eq: bool, def: tydef, ast: bool} -> unit
   val canMatch: Type.ty -> Type.ty -> bool
   val canUnify: Type.ty -> Type.ty -> bool
   val castTypes: unit -> Type.ty list
   val constructors: Type.ty -> cons_dict
   val dest: Type.ty -> Type.dty
   val destParam: Type.ty -> Type.ty
   val destProd: Type.ty -> Type.ty * Type.ty
   val domain: Type.ty -> Type.ty
   val domainRange: Type.ty -> Type.ty * Type.ty
   val enum: string -> string -> Nat.nat option
   val equalTy: Type.ty -> Type.ty -> bool
   val expand: Type.ty -> Type.ty
   val fstProd: Type.ty -> Type.ty
   val generalize: Type.ty -> Type.ty
   val goodCast: Type.ty -> bool
   val isConst: string -> bool
   val isEnumerated: string -> bool
   val isEqType: Type.ty -> bool
   val isFixedBitsType: Type.ty -> bool
   val isRecord: string -> bool
   val isRecordType: Type.ty -> bool
   val listConsts: unit -> (string * typeconst) list
   val lookupConst: string -> typeconst option
   val match: Type.ty -> Type.ty -> Type.typesubst list
   val range: Type.ty -> Type.ty
   val resetConsts: unit -> unit
   val restoreConsts: unit -> unit
   val revenum: string -> Nat.nat -> string option
   val saveConsts: unit -> unit
   val setType: Type.ty -> Type.ty
   val sizeEnum: string -> Nat.nat option
   val sndProd: Type.ty -> Type.ty
   val splitProd: Type.ty -> Type.ty list
   val unify: Type.ty -> Type.ty -> Type.typesubst list
   val updateCastTypes: unit -> unit
end

structure Types :> Types =
struct
   open Type

   type cons_dict = Type.ty option Stringmap.dict

   datatype tydef = Constructors of cons
                  | Record of (string * Type.ty) list
                  | Typedef of Type.ty
                  | BaseType
   and cons = Enum of int Stringmap.dict
            | Construct of cons_dict

   type typeconst = {eq: bool, def: tydef, ast: bool, num: int}

   val eqTypes =
      ["unit", "bool", "int", "nat", "char", "bits", "list", "option", "set"]

   fun mkEnumType (name: string, l) =
      let
         val e = Stringmap.fromList (Lib.addIndex l)
      in
         (name, {eq = true, def = Constructors (Enum e), ast = false, num = ~1})
      end

   val primTypes =
      Stringmap.fromList
         (mkEnumType ("rounding", ["roundTiesToEven", "roundTowardPositive",
                                   "roundTowardNegative", "roundTowardZero"]) ::
          ("string", {eq = true, def = Typedef Type.stringTy,
                      ast = false, num = ~1}) ::
          Lib.mapl {eq = true, def = BaseType, ast = false, num = ~1} eqTypes)

   val consts = ref primTypes
   val save_consts = ref (!consts)
   val const_num = ref 0
   val save_num = ref (!const_num)

   fun resetConsts () = (consts := primTypes; const_num := 0)
   fun saveConsts () = (save_consts := !consts; save_num := !const_num)
   fun restoreConsts () = (consts := !save_consts; const_num := !save_num)

   local
      val cmp =
         (fn ((_, {num = i, ...}), (_, {num = j, ...})) => Int.compare (i, j))
   in
      fun listConsts () =
         !consts |> Stringmap.listItems
                 |> List.filter (fn (_, {num = i, ...}) => i <> ~1)
                 |> Lib.msort cmp
   end

   fun lookupConst s = Stringmap.peek (!consts, s)

   val isConst = Option.isSome o lookupConst

   fun addConst (s, {eq = e, def = d, ast = a}) =
     ( not (isConst s) orelse raise Fail ("Type already defined: " ^ s)
     ; consts := Stringmap.insert
                    (!consts, s, {eq = e, def = d, ast = a, num = !const_num})
     ; const_num := !const_num + 1
     )

   fun generalize ((bty, _): ty) =
      let
         fun gen t =
            case t of
               Type.VarType _ => t
             | Type.BV _=> Type.BVV (Type.freshName ())
             | Type.BVV _=> Type.BVV (Type.freshName ())
             | Type.ConstType c =>
                  (case lookupConst c of
                      SOME {def = Typedef (d, _), ...} => gen d
                    | _ => t)
             | Type.Prod x => Type.Prod ((gen ## gen) x)
             | Type.Arrow x => Type.Arrow ((gen ## gen) x)
             | Type.ParamType (p, x) => Type.ParamType (p, gen x)
      in
         Type.mkEmpty (gen bty)
      end

   fun expand ((bty, c): ty) =
      let
         fun expd t =
            case t of
               Type.ConstType c =>
                  (case lookupConst c of
                     SOME {def = Typedef (d, _), ...} => expd d
                    | _ => t)
             | Type.Prod x => Type.Prod ((expd ## expd) x)
             | Type.Arrow x => Type.Arrow ((expd ## expd) x)
             | Type.ParamType (p, x) => Type.ParamType (p, expd x)
             | _ => t
      in
         (expd bty, c): ty
      end

   val dest = Type.destType o expand

   fun isEqType (ty as (bty, _): ty) =
      let
         fun isEq t =
            case t of
               VarType v => isEqVarType v
             | ConstType c => #eq (Stringmap.find (!consts, c))
             | BV _ => true
             | BVV _ => true
             | Prod (t1, t2) => isEq t1 andalso isEq t2
             | ParamType (ListTy, t) => isEq t
             | ParamType (OptionTy, t) => isEq t
             | ParamType (setTy, _) => false
             | _ => false
      in
         isEq bty orelse isSetTy ty
      end

   fun op ---> (a, b) =
      if isEqType a
         then a --> b
      else raise Fail "Map domain is not an equality type."

   fun setType a =
      if isEqType a then setTy a else raise Fail ("set: not an equality type")

   fun listConstruct ty =
      Stringmap.fromList

   fun isEnumerated e =
      case lookupConst e of
        SOME {eq = true, def = Constructors (Enum _), ...} => true
      | _ => false

   fun isRecord e =
      case lookupConst e of
        SOME {def = Record _, ...} => true
      | _ => false

   fun isRecordType ty =
      case dest ty of
        Type.Other s => isRecord s
      | _ => false

   val isFixedBitsType = Type.isFixedTy o expand

   local
      fun lift f s (ty as (bty, _): ty) =
         case bty of
            Type.Arrow _ => f ty
          | Type.ConstType c =>
               (case lookupConst c of
                   SOME {def = Typedef d, ...} => lift f s d
                 | _ => raise Fail s)
          | _ => raise Fail s
   in
      val range       = lift Type.rng "range"
      val domain      = lift Type.dom "domain"
      val domainRange = lift Type.domrng "domainRange"
   end

   local
      fun lift f s (ty as (bty, c): ty) =
         case bty of
            Type.Prod (ty1, ty2) => f ((ty1, c), (ty2, c))
          | Type.ConstType c =>
               (case lookupConst c of
                   SOME {def = Typedef d, ...} => lift f s d
                 | _ => raise Fail s)
          | _ => raise Fail s
   in
      val fstProd  = lift (Type.normalize o fst) "fstProd"
      val sndProd  = lift (Type.normalize o snd) "sndProd"
      val destProd = lift (Type.normalize ## Type.normalize) "destProd"
   end

   fun splitProd t =
      let
         val (l, r) = destProd t
      in
         l :: splitProd r
      end
      handle Fail "destProd" => [t]

   val destParam =
      fn (Type.ParamType (_, ty), c): Type.ty => (ty, c): Type.ty
       | _ => raise Fail "destParam"

   local
      fun lookupEnum e =
         case lookupConst e of
           SOME {eq = true, def = Constructors (Enum t), ...} => SOME t
         | _ => NONE
      fun lookup v t = Option.map Nat.fromInt (Stringmap.peek (t, v))
      fun revlookup v t =
         SOME (fst (List.nth (Stringmap.sortItems Int.compare t, Nat.toInt v)))
         handle Subscript => NONE
   in
      fun sizeEnum e =
         case lookupEnum e of
           SOME t => SOME (Nat.fromInt (Stringmap.numItems t))
         | _ => NONE
      fun enum e v = Option.join (Option.map (lookup v) (lookupEnum e))
      fun revenum e v = Option.join (Option.map (revlookup v) (lookupEnum e))
   end

   fun constructors ty =
      let
         val ety = expand ty
      in
         if Type.isOptionTy ety
            then Stringmap.fromList
                    [("None", NONE), ("Some", SOME (destParam ety))]
         else if Type.isListTy ty
            then Stringmap.fromList
                    [("Nil", NONE), ("Cons", SOME (destParam ety ** ety))]
         else case fst ety of
                 Type.ConstType s =>
                   (case lookupConst s of
                       SOME {def = Constructors (Construct d), ...} => d
                     | _ => raise Fail "constructors")
                | _ => raise Fail "constructor"
      end

   local
      fun castable e =
         not (mem e ["unit", "bits", "list", "option", "set"]) andalso
         case lookupConst e of
            SOME {eq = true, def = Constructors (Enum _), ...} => true
          | SOME {eq = true, def = BaseType, ...} => true
          | _ => false

      fun allCastable () = List.filter castable (Stringmap.keys (!consts))

      fun buildCastTypes () =
         [Type.wordTy "a" --> Type.alphaTy,
          Type.bitstringTy --> Type.alphaTy,
          Type.stringTy --> Type.alphaTy] @
         List.map (fn a => Type.mkConstType a --> Type.alphaTy) (allCastable ())

      val castTys = ref (buildCastTypes ())
   in
      fun goodCast ty =
         case fst (expand ty) of
            Type.BV _ => true
          | Type.BVV _ => true
          | Type.ParamType (Type.ListTy, Type.ConstType "char") => true
          | Type.ParamType (Type.ListTy, Type.ConstType "bool") => true
          | Type.ConstType c => castable c
          | _ => false
      fun castTypes () = !castTys
      fun updateCastTypes () = castTys := buildCastTypes ()
   end

   fun typeOccurs v (VarType w) = v = w
     | typeOccurs v (ParamType (_, w)) = typeOccurs v w
     | typeOccurs v (Prod (u, w)) = typeOccurs v u orelse typeOccurs v w
     | typeOccurs v (Arrow (u, w)) = typeOccurs v u orelse typeOccurs v w
     | typeOccurs _ ty = false

   exception Unify of string

   local
      fun unifyErr m t1 t2 =
         let
            val (s1, s2) = Type.freshTypeStrings (t1, t2)
         in
            raise Unify (m ^ ": " ^ s1 ^ ", " ^ s2)
         end

      fun mkEqType ((ParamType (SetTy, _), _): ty) = SOME []
        | mkEqType ((ConstType c, _): ty) =
            if #eq (Stringmap.find (!consts, c)) then SOME [] else NONE
        | mkEqType ((bty, _): ty) =
         let
            val u = ref ([]: typesubst list)
            fun addu v = u := (v |-> freshEqTyVar()) :: !u
            fun iter ty =
               case ty of
                  VarType v => if Type.isEqVarType v then () else addu v
                | ConstType c =>
                    (case lookupConst c of
                       SOME {eq = true, def = def, ...} =>
                          (case def of
                              Typedef (ParamType (SetTy, _), _) =>
                                 raise Fail "mkEqType"
                            | _ => ())
                      | _ => raise Fail "mkEqType")
                | Prod (ty1, ty2) =>
                    (iter ty1; iter (fst (typeSubst (!u) (Type.mkEmpty ty2))))
                | BV _ => ()
                | BVV _ => ()
                | ParamType (SetTy, ty1) => raise Fail "mkEqType"
                | ParamType (_, ty1) => iter ty1
                | _ => raise Fail "mkEqType"
         in
            iter bty; SOME (!u)
         end
         handle Fail "mkEqType" => NONE

      fun trySubstType x t =
         if isEqVarType x
            then (case mkEqType t of
                     SOME u => (x |-> typeSubst u t) :: u
                   | NONE => unifyErr "Cannot unify" (Type.mkVarType x) t)
         else [x |-> t]

      fun ufy (ty1 as (t1, cs1), ty2 as (t2, cs2)) =
        case (t1, t2) of
           (ConstType _, VarType _) => ufy (ty2, ty1)
         | (BV _, VarType _) => ufy (ty2, ty1)
         | (BVV _, VarType _) => ufy (ty2, ty1)
         | (ParamType _, VarType _) => ufy (ty2, ty1)
         | (Prod _, VarType _) => ufy (ty2, ty1)
         | (Arrow _, VarType _) => ufy (ty2, ty1)
         | (BV _, ConstType _) => ufy (ty2, ty1)
         | (BVV _, ConstType _) => ufy (ty2, ty1)
         | (ParamType _, ConstType _) => ufy (ty2, ty1)
         | (Prod _, ConstType _) => ufy (ty2, ty1)
         | (Arrow _, ConstType _) => ufy (ty2, ty1)
         | (BV _, BVV _) => ufy (ty2, ty1)
         | (VarType x, VarType y) =>
              if x = y
                then []
              else if Type.isFreshVar x
                then trySubstType x ty2
              else trySubstType y ty1
         | (VarType x, ConstType _) => trySubstType x ty2
         | (VarType x, BV _) => trySubstType x ty2
         | (VarType x, BVV _) => trySubstType x ty2
         | (VarType x, ParamType _) => if typeOccurs x t2
                                          then unifyErr "Occurs" ty1 ty2
                                       else trySubstType x ty2
         | (VarType x, Prod _) => if typeOccurs x t2
                                     then unifyErr "Occurs" ty1 ty2
                                  else trySubstType x ty2
         | (VarType x, Arrow _) => if typeOccurs x t2
                                      then unifyErr "Occurs" ty1 ty2
                                   else trySubstType x ty2
         | (BVV x, BV i) => [x |=> FixedBits i]
         | (BVV x, BVV y) =>
             let
                val c1 = Constrain.constraint (cs1, x)
                val c2 = Constrain.constraint (cs2, y)
             in
                if x = y andalso c1 = c2
                   then []
                else let
                        val xok = PosIntSet.subset c2 c1
                        val yok = PosIntSet.subset c1 c2
                        val xfresh = Type.isFreshVar x
                        val yfresh = Type.isFreshVar y
                     in
                        if xok andalso (xfresh orelse not (yok andalso yfresh))
                           then [x |=> VarBits (y, c2)]
                        else if yok
                           then [y |=> VarBits (x, c1)]
                        else unifyErr "Constraint" ty1 ty2
                     end
             end
         | (BV i, BV j) =>
             if i = j then []
             else raise Unify ("Word length mismatch: " ^
                               Int.toString i ^ " <> " ^ Int.toString j)
         | (ConstType c1, ConstType c2) =>
             if c1 = c2
                then []
             else
               (case lookupConst c1 of
                  SOME {def = Typedef d, ...} => ufy (d, ty2)
                | _ =>
                    (case lookupConst c2 of
                       SOME {def = Typedef d, ...} => ufy (ty1, d)
                     | _ =>
                       raise Unify ("Const type mismatch: " ^ c1 ^ ", " ^ c2)))
         | (ConstType c, _) =>
            (case lookupConst c of
                SOME {def = Typedef d, ...} => ufy (d, ty2)
              | _ => unifyErr "Type mismatch" ty1 ty2)
         | (ParamType (p1, x), ParamType (p2, y)) =>
             if p1 = p2
                then ufy ((x, cs1), (y, cs2))
             else unifyErr "Type mismatch" ty1 ty2
         | (Prod (x1, y1), Prod (x2, y2)) =>
             let
               val r1 = ufy ((x1, cs1), (x2, cs2))
               val r2 = ufy (typeSubst r1 (y1, cs1), typeSubst r1 (y2, cs2))
             in
               combineSubst r2 r1
             end
         | (Arrow (x1, y1), Arrow (x2, y2)) =>
             let
               val r1 = ufy ((x1, cs1), (x2, cs2))
               val r2 = ufy (typeSubst r1 (y1, cs1), typeSubst r1 (y2, cs2))
             in
               combineSubst r2 r1
             end
         | _ => unifyErr "Type mismatch" ty1 ty2
   in
      fun unify t1 t2 = ufy (t1, t2)
   end

   fun canUnify t1 t2 = (unify t1 t2; true) handle Unify _ => false

   exception TypeMatch of string

   local
      fun matchErr t1 t2 =
         let
            val (s1, s2) = Type.freshTypeStrings (t1, t2)
         in
            raise TypeMatch  (s1 ^ ", " ^ s2)
         end

      fun trySubstType x t =
         if isEqVarType x andalso not (isEqType t)
            then matchErr (Type.mkVarType x) t
         else [x |-> t]
   in
      fun match (ty1 as (t1, cs1)) (ty2 as (t2, cs2)) =
        case (t1, t2) of
           (VarType x, VarType y) => if x = y then [] else trySubstType x ty2
         | (VarType x, ParamType _) => if typeOccurs x t2
                                          then matchErr ty1 ty2
                                       else trySubstType x ty2
         | (VarType x, Prod _) => if typeOccurs x t2
                                     then matchErr ty1 ty2
                                  else trySubstType x ty2
         | (VarType x, Arrow _) => if typeOccurs x t2
                                      then matchErr ty1 ty2
                                   else trySubstType x ty2
         | (VarType x, _) => trySubstType x ty2
         | (BVV x, BV i) => [x |=> Type.FixedBits i]
         | (BVV x, BVV y) =>
             let
                val cx = Constrain.constraint (cs1, x)
                val cy = Constrain.constraint (cs2, y)
             in
                if x = y andalso cx = cy
                   then []
                else if PosIntSet.subset cy cx
                   then [x |=> VarBits (y, cy)]
                else matchErr ty1 ty2
            end
         | (BV i, BV j) => if i = j then [] else matchErr ty1 ty2
         | (ConstType c1, ConstType c2) =>
             if c1 = c2
                then []
             else
               (case lookupConst c1 of
                   SOME {def = Typedef d, ...} => match d ty2
                 | _ =>
                     (case lookupConst c2 of
                         SOME {def = Typedef d, ...} => match ty1 d
                       | _ => matchErr ty1 ty2))
         | (ConstType c, _) =>
            (case lookupConst c of
               SOME {def = Typedef d, ...} => match d ty2
             | _ => matchErr ty1 ty2)
         | (_, ConstType c) =>
            (case lookupConst c of
               SOME {def = Typedef d, ...} => match ty1 d
             | _ => matchErr ty1 ty2)
         | (ParamType (p1, x), ParamType (p2, y)) =>
             if p1 = p2
                then match (x, cs1) (y, cs2)
             else matchErr ty1 ty2
         | (Prod (x1, y1), Prod (x2, y2)) =>
             let
               val r1 = match (x1, cs1) (x2, cs2)
               val r2 = match (typeSubst r1 (y1, cs1)) (typeSubst r1 (y2, cs2))
             in
               combineSubst r2 r1
             end
         | (Arrow (x1, y1), Arrow (x2, y2)) =>
             let
               val r1 = match (x1, cs1) (x2, cs2)
               val r2 = match (typeSubst r1 (y1, cs1)) (typeSubst r1 (y2, cs2))
             in
               combineSubst r2 r1
             end
         | _ => matchErr ty1 ty2
   end

   fun canMatch t1 t2 = (match t1 t2; true) handle TypeMatch _ => false

   fun equalTy t1 t2 = List.null (match t1 t2) handle TypeMatch _ => false

end (* Types *)

val op ---> = Types.--->

(* -------------------------------------------------------------------------
   The environment

   Keep track of mutable and immutable variables
   ------------------------------------------------------------------------- *)

signature Env =
sig
   type var = {typ: Type.ty, mutable: bool}
   type env

   val addImmutableVariable: env * string * Type.ty -> env
   val addImmutableVariableList: env * (string * Type.ty) list -> env
   val addMutableVariable: env * string * Type.ty -> env
   val addMutableVariableList: env * (string * Type.ty) list -> env
   val addVariableList: env * (string * bool * Type.ty) list -> env
   val checkFreeList: env -> (string -> unit) -> string list -> unit
   val empty: env
   val get: unit -> env
   val isImmutableVariable: env * string -> bool
   val isMutableVariable: env * string -> bool
   val isVariable: env * string -> bool
   val listVariables: env -> (string * var) list
   val lookupVariable: env * string -> var option
   val reset: unit -> unit
   val restore: unit -> unit
   val save: unit -> unit
   val update: env -> unit
   val updateEnv: Type.typesubst list -> env -> env
   val variables: env -> string list
end

structure Env :> Env =
struct
   type var = {typ: Type.ty, mutable: bool}
   type env = var Stringmap.dict

   fun mkEnv m ty = {typ = ty, mutable = m}: var
   fun updateEnvType f ({typ, mutable}: var) = mkEnv mutable (f typ)

   val empty = Stringmap.empty: env

   fun updateEnv s (e: env) =
      Stringmap.transform (updateEnvType (Type.typeSubst s)) e: env

   fun lookupVariable (e: env, v) = Stringmap.peek (e, v)

   val isVariable = Option.isSome o lookupVariable

   fun isMutableVariable x =
      case lookupVariable x of
         SOME {mutable = true, ...} => true
       | _ => false

   fun isImmutableVariable x =
      case lookupVariable x of
         SOME {mutable = false, ...} => true
       | _ => false

   fun addVariable m (e: env, v, ty) = Stringmap.insert (e, v, mkEnv m ty): env
   val addMutableVariable = addVariable true
   val addImmutableVariable = addVariable false

   fun addVariableList (e: env, l) =
      Stringmap.insertList
         (e, List.map (fn (v, m, ty) => (v, mkEnv m ty)) l): env

   fun addVList m (e: env, l) =
      Stringmap.insertList (e, List.map (I ## (mkEnv m)) l): env

   val addMutableVariableList = addVList true
   val addImmutableVariableList = addVList false

   fun listVariables (e: env) = Stringmap.listItems e

   fun variables (e: env) = Stringmap.keys e

   fun checkFreeList (env: env) err l =
      let
         fun isUsed v = isVariable (env, v)
      in
         case List.find isUsed l of
            SOME n => err n
          | NONE => ()
      end

   local
      val globals = ref empty
      val saved = ref (!globals)
   in
      fun save () = saved := !globals
      fun restore () = globals := !saved
      fun reset () = (globals := empty; save())
      fun update e = globals := e
      fun get () = !globals
   end

end (* structure Env *)

(* -------------------------------------------------------------------------
   Term

   Support for term construction, destruction and type checking
   ------------------------------------------------------------------------- *)

signature Term =
sig
   exception TermMatch
   exception NoConv

   datatype value =
        Bits of BitsN.nbit
      | Bitstring of Bitstring.bitstring
      | Bool of bool
      | Char of char
      | Enum of Nat.nat * string
      | Int of int
      | Nat of Nat.nat
      | Other of string * Type.ty
      | String of string
      | Unit

   datatype term =
        Lit of value
      | Var of string * Type.ty
      | BVar of int * Type.ty
      | Comb of string * Type.ty * term list
      | Abs of (string * Type.ty) list * Type.ty * term

   exception TypeCheck of {loc: int, operation: string, args: term list,
                           valid_types: Type.ty list, message: string}

   datatype hint = NoTypeHint | TypeHint of Type.ty

   structure TermMap :
     sig
       type 'a map = (term * 'a) list * 'a option
       val updateList: 'a map * (term * 'a) list -> 'a map
       val update: 'a map * term * 'a -> 'a map
       val undefined: 'a map
       val printDiff:
        ('a * 'a -> bool) * (term * term -> order) ->
          string * (string -> string) * (term -> string) *
        ('a -> string) * (term -> string) -> 'a map * 'a map -> bool
       val peek: 'a map * term -> 'a option
       val mk: (term * 'a) list * 'a -> 'a map
       val lookup: 'a map * term -> 'a
       val fromList: (term * 'a) list -> 'a map
       val find: (term * 'a) list * term -> (term * 'a) option
       val diff:
        ('a * 'a -> bool) ->
          'a map * 'a map ->
          (term * 'a option) list * (term list * 'a option) option
       val all: 'a -> 'a map
       exception Undefined
     end

   val compare: term * term -> order

   val unitHint: hint
   val natHint: hint
   val boolHint: hint

   val isLit: term -> bool
   val isVar: term -> bool
   val isBVar: term -> bool
   val isComb: term -> bool
   val isAbs: term -> bool

   val destAbs: term -> term * term
   val destAbsPair: term -> term * term
   val destApp: term -> string * term
   val destBinOp: string -> term -> term * term
   val destBitsLit: term -> BitsN.nbit
   val destBitstringLit: term -> Bitstring.bitstring
   val destBoolLit: term -> bool
   val destCase: term -> term * term
   val destCharLit: term -> char
   val destConcats: term -> term list
   val destEnumLit: term -> Nat.nat * string
   val destIfThens: term -> (term * term) list * term
   val destIntLit: term -> int
   val destLet: term -> term * term * term
   val destLets: term -> (term * term) list * term
   val destList: term -> term list
   val destMap: term -> term TermMap.map
   val destMatch: term -> term * (term * term) list
   val destNatLit: term -> int
   val destNumLit: term -> Nat.nat
   val destPair: term -> term * term
   val destRounding: term -> IEEEReal.rounding_mode
   val destStringLit: term -> string
   val destTermSet: term -> term list
   val destTriple: term -> term * (term * term)
   val destTuple: term -> term list
   val destVar: term -> string * Type.ty

   val anon: Type.ty -> term
   val unknown: Type.ty -> term
   val unitTm: term

   val mkAbs: term * term -> term
   val mkApply: term * term -> term
   val mkBitsLit: BitsN.nbit -> term
   val mkBitstringLit: Bitstring.bitstring -> term
   val mkBoolLit: bool -> term
   val mkBoolOp: string -> term * term -> term
   val mkCase: term * term -> term
   val mkCharLit: char -> term
   val mkCompose: term * term -> term
   val mkExtract: term * int * int -> term
   val mkFold: (term * term -> term) -> term list -> term
   val mkFst: term -> term
   val mkIfThen: term * term * term -> term
   val mkIfThens: (term * term) list * term -> term
   val mkIntLit: int -> term
   val mkLet: term * term * term -> term
   val mkList: ('a -> term) * Type.ty -> 'a list -> term
   val mkMap: Type.ty * Type.ty -> term TermMap.map -> term
   val mkMatch: term * (term * term) list -> term
   val mkMatchApply: Type.ty -> term * term -> term
   val mkNatLit: int -> term
   val mkNot: term -> term
   val mkNumLit: Nat.nat -> term
   val mkPair: term * term -> term
   val mkSize: string -> term
   val mkSnd: term -> term
   val mkStringLit: string -> term
   val mkTermSet: term list -> term
   val mkTuple: term list -> term

   val absList: (string * Type.ty) list -> term -> term
   val appTerm: (term -> unit) -> term -> unit
   val apply: term -> term -> term
   val bitsToHexString: term -> string
   val bitsToPaddedHexString: term -> string
   val bitsToString: term -> string
   val bvar: term -> term
   val canMatch: term -> term -> bool
   val checkMatch: term -> int list * bool
   val dTypeOf: term -> Type.dty
   val depthconv: (term -> term) -> term -> term
   val equalTm: term -> term -> bool
   val expandBitstringLit: term -> term
   val expandStringLit: term -> term
   val findMapTerm: (term -> 'a option) -> term -> 'a option
   val findTerm: (term -> bool) -> term -> term option
   val freeVars: term -> (string * Type.ty) list
   val genUnknown: Type.ty -> term
   val hasFreshTypeVars: term -> bool
   val inst1: string * term -> term -> term
   val inst: term Stringmap.dict -> term -> term
   val match: term -> term -> term Stringmap.dict * Type.typesubst list
   val matchType: Type.ty -> term -> term
   val multipleOccs: string * Type.ty -> term -> bool
   val newVars: term list -> (string * Type.ty) list -> term list
   val normalizeCons: term -> term
   val primTypeOf: term -> Type.ty
   val printMapDiff:
      string * (string -> string) * (term -> string) *
      (term -> string) * (term -> string) -> term * term -> bool
   val rawTermToString: term -> string
   val subst: int -> term -> term -> term
   val termTypeSubst: Type.typesubst list -> term -> term
   val topconv: (term -> term) -> term -> term
   val tryMatch:
      term -> term -> (term Stringmap.dict * Type.typesubst list) option
   val tupleVars: term -> (string * Type.ty) list
   val typeOf: term -> Type.ty
   val valueEqual: value * value -> bool

   val typeCheck:
     int * string -> Env.env ->
      (term -> Type.ty) ->
      (term list -> Type.ty) ->
      Type.ty list ->
      ((Env.env -> 'a -> Type.typesubst list * term) * 'a) list ->
      Type.typesubst list * Type.ty * term list

   val printer: int -> 'a -> term -> PolyML.pretty

end

structure Term :> Term =
struct
   open Type Types

   datatype value =
        Bits of BitsN.nbit
      | Bitstring of Bitstring.bitstring
      | Bool of bool
      | Char of char
      | Enum of Nat.nat * string
      | Int of int
      | Nat of Nat.nat
      | Other of string * Type.ty
      | String of string
      | Unit

   datatype term =
        Lit of value
      | Var of string * Type.ty
      | BVar of int * Type.ty
      | Comb of string * Type.ty * term list
      | Abs of (string * Type.ty) list * Type.ty * term

   val compare_value =
      fn (Unit, Unit) => General.EQUAL
       | (Unit, _) => General.LESS
       | (Bool _, Unit) => General.GREATER
       | (Bool a, Bool b) => if a = b
                                then General.EQUAL
                             else if a then
                                General.GREATER
                             else General.LESS
       | (Bool _, _) => General.LESS
       | (Enum _, Unit) => General.GREATER
       | (Enum _, Bool _) => General.GREATER
       | (Enum (a, b), Enum (c, d)) =>
             Lib.pairCompare (String.compare, Nat.compare) ((b, a), (d, c))
       | (Enum _, _) => General.LESS
       | (Char _, Unit) => General.GREATER
       | (Char _, Bool _) => General.GREATER
       | (Char _, Enum _) => General.GREATER
       | (Char a, Char b) => Char.compare (a, b)
       | (Char _, _) => General.LESS
       | (Bits _, Unit) => General.GREATER
       | (Bits _, Bool _) => General.GREATER
       | (Bits _, Enum _) => General.GREATER
       | (Bits _, Char _) => General.GREATER
       | (Bits a, Bits b) => BitsN.compare (a, b)
       | (Bits _, _) => General.LESS
       | (Other _, Bitstring _) => General.LESS
       | (Other _, String _) => General.LESS
       | (Other _, Nat _) => General.LESS
       | (Other _, Int _) => General.LESS
       | (Other (a, b), Other (c, d)) =>
             Lib.pairCompare (Type.compare, String.compare) ((b, a), (d, c))
       | (Other _, _) => General.GREATER
       | (Bitstring _, String _) => General.LESS
       | (Bitstring _, Nat _) => General.LESS
       | (Bitstring _, Int _) => General.LESS
       | (Bitstring a, Bitstring b) => Bitstring.compare (a, b)
       | (Bitstring _, _) => General.GREATER
       | (String _, Nat _) => General.LESS
       | (String _, Int _) => General.LESS
       | (String a, String b) => String.compare (a, b)
       | (String _, _) => General.GREATER
       | (Nat _, Int _) => General.LESS
       | (Nat a, Nat b) => Nat.compare (a, b)
       | (Nat _, _) => General.GREATER
       | (Int a, Int b) => Int.compare (a, b)
       | (Int _, _) => General.GREATER

   fun compare (tm1, tm2) =
      case (tm1, tm2) of
         (Lit a, Lit b) => compare_value (a, b)
       | (Lit _, _) => General.LESS
       | (Var _, Lit _) => General.GREATER
       | (Var (a, b), Var (c, d)) =>
             Lib.pairCompare (Type.compare, String.compare) ((b, a), (d, c))
       | (Var _, _) => General.LESS
       | (BVar _, Lit _) => General.GREATER
       | (BVar _, Var _) => General.GREATER
       | (BVar (a, b), BVar (c, d)) =>
             Lib.pairCompare (Type.compare, Int.compare) ((b, a), (d, c))
       | (BVar _, _) => General.LESS
       | (Comb _, Abs _) => General.LESS
       | (Comb (f1, ty1, l1), Comb (f2, ty2, l2)) =>
             Lib.pairCompare
                (String.compare,
                 Lib.pairCompare (Type.compare, Lib.listCompare compare))
                ((f1, (ty1, l1)), (f2, (ty2, l2)))
       | (Comb _, _) => General.GREATER
       | (Abs (l1, ty1, t1), Abs (l2, ty2, t2)) =>
             Lib.pairCompare
                (Type.compare,
                 Lib.pairCompare
                    (compare,
                     Lib.listCompare
                        (Lib.pairCompare (String.compare, Type.compare))))
                ((ty1, (t1, l1)), (ty2, (t2, l2)))
       | (Abs _, _) => General.GREATER

   fun ppQ p =
      PolyML.PrettyBlock
         (0, false, [], [PolyML.PrettyString "`", p, PolyML.PrettyString "`"])

   fun ppC (s, p) =
      PolyML.PrettyBlock
         (1, false, [], [PolyML.PrettyString s, PolyML.PrettyBreak (1, 0), p])

   fun printer d ply =
      fn Lit (Bits w) => ppQ (PolyML.prettyRepresentation (w, d))
       | Lit (Bitstring s) =>
            PolyML.PrettyString ("`0s" ^ Bitstring.toBinString s ^ "`")
       | Lit (Bool b) => ppQ (PolyML.prettyRepresentation (b, d))
       | Lit (Char c) => ppQ (PolyML.prettyRepresentation (c, d))
       | Lit (e as Enum (n, s)) =>
           (case Types.revenum s n of
               SOME v => PolyML.PrettyString ("`" ^ v ^ "::" ^ s ^ "`")
             | NONE => ppQ (PolyML.prettyRepresentation (e, d)))
       | Lit (Int i) =>
            PolyML.PrettyString ("`" ^ (if i < 0 then "~" else "") ^ "0i" ^
                                 Int.toString (Int.abs i) ^ "`")
       | Lit (Nat n) => PolyML.PrettyString ("`0n" ^ Nat.toString n ^ "`")
       | Lit (Other (v, ty as (bty, cty))) =>
            ppQ (PolyML.PrettyBlock
                   (1, false, [],
                    [PolyML.PrettyString v,
                     PolyML.PrettyString "::",
                     if Constrain.isEmpty cty
                        then PolyML.prettyRepresentation (bty, d - 1)
                     else PolyML.prettyRepresentation (ty, d - 1)]))
       | Lit (String s) => ppQ (PolyML.PrettyString ("\"" ^ s ^ "\""))
       | Lit Unit => ppQ (PolyML.prettyRepresentation ((), d))
       | Var (v, ty as (bty, cty)) =>
            ppC ("Var", if Constrain.isEmpty cty
                           then PolyML.prettyRepresentation ((v, bty), d - 1)
                        else PolyML.prettyRepresentation ((v, ty), d - 1))
       | BVar (v, ty as (bty, cty)) =>
            ppC ("BVar", if Constrain.isEmpty cty
                           then PolyML.prettyRepresentation ((v, bty), d - 1)
                        else PolyML.prettyRepresentation ((v, ty), d - 1))
       | Comb (f, ty as (bty, cty), l) =>
            let
               val pl =
                  Lib.mapSeparate
                     (printer (d - 1) ply)
                     [PolyML.PrettyString ",", PolyML.PrettyBreak (1, 0)] l
               val pl =
                 [PolyML.PrettyString "["] @ pl @ [PolyML.PrettyString "]"]
            in
               ppC ("\"" ^ f ^ "\"",
                    PolyML.PrettyBlock
                       (1, false, [],
                        [PolyML.PrettyString "(",
                         if Constrain.isEmpty cty
                            then PolyML.prettyRepresentation (bty, d - 1)
                         else PolyML.prettyRepresentation (ty, d - 1),
                         PolyML.PrettyString ",",
                         PolyML.PrettyBreak (1, 0),
                         PolyML.PrettyBlock (1, false, [], pl),
                         PolyML.PrettyString ")"]))
            end
       | Abs (l, ty as (bty, cty), tm) =>
            ppC ("Abs",
                 PolyML.PrettyBlock
                    (1, false, [],
                     [PolyML.PrettyString "(",
                      PolyML.prettyRepresentation (l, d - 1),
                      PolyML.PrettyString ",",
                      PolyML.PrettyBreak (1, 0),
                      if Constrain.isEmpty cty
                         then PolyML.prettyRepresentation (bty, d - 1)
                      else PolyML.prettyRepresentation (ty, d - 1),
                      PolyML.PrettyString ",",
                      PolyML.PrettyBreak (1, 0),
                      printer (d - 1) ply tm,
                      PolyML.PrettyString ")"]))

   val () = PolyML.addPrettyPrinter printer

   datatype hint = TypeHint of Type.ty | NoTypeHint

   local
      fun constHint c = TypeHint (Type.mkConstType c)
   in
      val natHint  = constHint "nat"
      val boolHint = constHint "bool"
      val unitHint = constHint "unit"
   end

   val isLit = fn Lit _ => true | _ => false
   val isVar = fn Var _ => true | _ => false
   val isBVar = fn BVar _ => true | _ => false
   val isComb = fn Comb _ => true | _ => false
   val isAbs = fn Abs _ => true | _ => false

   fun primTypeOf tm =
      case tm of
         Lit (Bits v) => Type.fixedTy (Nat.toInt (BitsN.size v))
       | Lit (Bitstring v) => Type.bitstringTy
       | Lit (Bool _) => Type.boolTy
       | Lit (Char _) => Type.charTy
       | Lit (Enum (_, s)) => Type.mkConstType s
       | Lit (Int _) => Type.intTy
       | Lit (Nat _) => Type.natTy
       | Lit (Other (_, ty)) => ty
       | Lit (String _) => Type.stringTy
       | Lit Unit => Type.unitTy
       | Var (_, ty) => ty
       | Comb (_, ty, _) => ty
       | Abs (_, ty, _) => ty
       | BVar (_, ty) => ty

   val typeOf = Types.expand o primTypeOf
   val dTypeOf = Types.dest o typeOf

   val unitTm = Lit Unit
   val mkCharLit = Lit o Char
   val mkBoolLit = Lit o Bool
   val mkNumLit = Lit o Nat
   val mkNatLit = mkNumLit o Nat.fromInt
   val mkIntLit = Lit o Int
   val mkBitsLit = Lit o Bits
   val mkStringLit = Lit o String
   val mkBitstringLit = Lit o Bitstring

   fun anon ty = Var ("_", ty)
   fun unknown ty = if Types.equalTy Type.unitTy ty
                       then unitTm
                    else Lit (Other ("UNKNOWN", ty))

   fun mkPair (tm1, tm2) =
      Comb (",", primTypeOf tm1 ** primTypeOf tm2, [tm1, tm2])

   fun mkList (mk, ty) =
      fn l =>
         let
            val _ = case l of
                       h :: _ =>
                          let
                             val hty = Type.listTy (primTypeOf (mk h))
                          in
                             Types.equalTy ty hty
                             orelse raise Fail
                                      ("mkList: inconsistent types: " ^
                                       PolyML.makestring ty ^ " and " ^
                                       PolyML.makestring hty)
                          end
                     | _ => true
            val x = Lit (Other ("Nil", ty))
         in
            List.foldr (fn y => Comb ("Cons", ty, [mkPair y])) x (List.map mk l)
         end

   val expandStringLit =
      fn Lit (String s) => mkList (mkCharLit, Type.stringTy) (String.explode s)
       | _ => raise Fail "expandStringLit"

   val expandBitstringLit =
      fn Lit (Bitstring s) =>
           mkList (mkBoolLit, Type.bitstringTy) (Bitstring.toList s)
       | _ => raise Fail "expandBitstringLit"

   local
      fun contractStringLit tm =
         case tm of
            Comb ("Cons", _,
                  [Comb (",", _, [Lit (Char c), Lit (Other ("Nil", _))])]) =>
               mkStringLit (Char.toString c)
          | Comb ("Cons", ty1, [Comb (",", ty2, [h, t])]) =>
             (case (h, contractStringLit t) of
                 (Lit (Char c), Lit (String s)) =>
                    mkStringLit (Char.toString c ^ s)
               | (_, r) => Comb ("Cons", ty1, [Comb (",", ty2, [h, r])]))
          | _ => tm
      fun contractBitstringLit tm =
         case tm of
            Comb ("Cons", _,
                  [Comb (",", _, [Lit (Bool c), Lit (Other ("Nil", _))])]) =>
               mkBitstringLit (Bitstring.fromList [c])
          | Comb ("Cons", ty1, [Comb (",", ty2, [h, t])]) =>
             (case (h, contractBitstringLit t) of
                 (Lit (Bool c), Lit (Bitstring s)) =>
                    mkBitstringLit (Bitstring.@@ (Bitstring.fromList [c], s))
               | (_, r) => Comb ("Cons", ty1, [Comb (",", ty2, [h, r])]))
          | _ => tm
   in
      val normalizeCons =
         fn t as Comb ("Cons", ty, [_]) =>
              if Types.equalTy Type.bitstringTy ty
                 then contractBitstringLit t
              else if Types.equalTy Type.stringTy ty
                 then contractStringLit t
              else t
          | tm => tm
   end

   fun mkFold _[] = raise Fail "mkFoldr"
     | mkFold (f: term * term -> term) l =
         let
            val (h, t) = lastButlast l
         in
            List.foldr f h t
         end

   val mkTuple = mkFold mkPair

   fun mkNot b = Comb ("not", Type.boolTy, [b])
   fun mkBoolOp f (x, y) = Comb (f, Type.boolTy, [x, y])
   fun mkFst tm = Comb ("Fst", Types.fstProd (primTypeOf tm), [tm])
   fun mkSnd tm = Comb ("Snd", Types.sndProd (primTypeOf tm), [tm])

   fun mkSize v =
      Comb ("Size", Type.natTy, [Lit (Other ("?d0", Type.constrainTy v))])

   val intFromNatLit = Option.compose (Nat.toInt,  Nat.fromLit)

   fun primMkExtract (w, tm, h, l) =
      Comb ("<..>", Type.fixedTy w, [mkNatLit h, mkNatLit l, tm])

   fun mkExtract (tm, h, l) =
      let
         val w = h + 1 - l
         val () = ignore (0 < w orelse raise Fail "mkExtract")
         fun default () = primMkExtract (w, tm, h, l)
      in
         case (tm, dTypeOf tm) of
            (Lit (Bits r), FixedBits n) =>
               mkBitsLit (BitsN.bits (Nat.fromInt h, Nat.fromInt l) r)
          | (Comb ("<..>", _, [Lit (Nat m), Lit (Nat n), tm2]), FixedBits b) =>
               (case dTypeOf tm2 of
                   FixedBits c =>
                      let
                         val m = Nat.toInt m
                         val n = Nat.toInt n
                         val mn = Lib.curry Int.min
                         fun pred n = if n <= 0 then 0 else n - 1
                         val t = mn m (mn (h + n) (mn (pred c) (pred (b + n))))
                      in
                         primMkExtract (w, tm2, t, l + n)
                      end
                 | _ => default ())
          | (_, Type.Other _) => raise Fail "mkExtract"
          | _ => default ()
      end

   fun abstract i (x as (b, bty)) t =
      case t of
         Lit _ => t
       | BVar _ => t
       | Var ("_", _) => t
       | Var (a, aty) =>
           if a = b andalso Types.equalTy aty bty then BVar (i, bty) else t
       | Abs (l, ty, u) => Abs (l, ty, abstract (i + List.length l) x u)
       | Comb ("var =", ty, [Var (a, aty), tm1, tm2]) =>
           Comb ("var =", ty,
                 [Var (a, aty), abstract i x tm1,
                  if a = b andalso Types.equalTy aty bty
                     then tm2
                  else abstract i x tm2])
       | Comb (s, ty, l) => Comb (s, ty, List.map (abstract i x) l)

   fun absList xs t =
      if List.null xs
         then t
      else Abs (xs, Type.foldProdList (List.map snd xs) --> primTypeOf t,
              snd (List.foldl
                     (fn (x, (i, u)) => (i + 1, abstract i x u)) (0, t) xs))

   fun inst env tm =
      let
         fun iter t =
            case t of
              Lit _ => t
            | BVar _ => t
            | Var (a, aty) =>
               (case Stringmap.peek (env, a) of
                  SOME tm => if Types.equalTy aty (primTypeOf tm) then tm else t
                | NONE => t)
            | Abs (l, ty, u) => Abs (l, ty, iter u)
            | Comb (s, ty, l) => Comb (s, ty, List.map iter l)
       in
          if Stringmap.numItems env = 0 then tm else iter tm
       end

   fun inst1 x = inst (Stringmap.fromList [x])

   fun shift i d t =
      if i = 0
         then t
      else case t of
              Lit _ => t
            | Var _ => t
            | BVar (j, ty) => if j >= d then BVar (j + i, ty) else t
            | Abs (l, ty, q) => Abs (l, ty, shift i (d + List.length l) q)
            | Comb (s, ty, l) => Comb (s, ty, List.map (shift i d) l)

   fun subst i u t =
      case t of
         Lit _ => t
       | Var _ => t
       | BVar (j, ty) =>
           if j < i
              then t
           else if j = i
              then shift i 0 u
           else BVar (j - 1, ty)
       | Abs (l, ty, q) => Abs (l, ty, subst (i + List.length l) u q)
       | Comb (s, ty, l) => Comb (s, ty, List.map (subst i u) l)

   fun rep_error s i =
      raise Fail ("Literal 0" ^ s ^ " cannot be represented with\
                  \ <= " ^ Int.toString i ^ " bits")

   fun termTypeSubst [] = Lib.I
     | termTypeSubst subst =
      fn Lit (Other (s, ty)) =>
         let
            val ty2 = typeSubst subst ty
         in
            if String.sub(s, 0) = #"?"
               then let
                       val s2 = Tag.remove s
                       fun mkLit f c =
                          case f s2 of
                             SOME v => Lit (c v)
                           | NONE => raise Fail ("Bad literal: " ^ s2)
                       val ty3 = Types.expand ty2
                    in
                       case fst ty3 of
                          VarType _ => Lit (Other (s, ty2))
                        | ConstType "nat" => mkLit Nat.fromLit Nat
                        | ConstType "int" => mkLit Int.fromLit Int
                        | BV n => mkLit (fn s => BitsN.fromLit (s, n)) Bits
                        | BVV _ =>
                            let
                               val tm = Lit (Other (s, ty2))
                            in
                               case (Option.map safeLog2 (Int.fromLit s2),
                                     Type.destType ty3) of
                                  (SOME b, Type.VarBits (_, s)) =>
                                     let
                                        val i = PosIntSet.supremum s
                                     in
                                        if i = ~1 orelse b < i
                                           then tm
                                        else rep_error s2 i
                                     end
                                | _ => tm
                            end
                        | ParamType (ListType, ConstType "bool") =>
                             mkLit Bitstring.fromLit Bitstring
                        | _ => raise Fail "termTypeSubst"
                    end
            else if s = "UNKNOWN"
               then unknown ty2
            else Lit (Other (s, ty2))
         end
       | t as Lit _ => t
       | Var (s, ty) => Var (s, typeSubst subst ty)
       | BVar (s, ty) => BVar (s, typeSubst subst ty)
       | Comb (s, ty, l) =>
           Comb (s, typeSubst subst ty, List.map (termTypeSubst subst) l)
       | Abs (l, ty, t) =>
           Abs (List.map (I ## typeSubst subst) l, typeSubst subst ty,
                termTypeSubst subst t)

   val valueEqual =
      fn (Bits x, Bits y) => (x = y)
       | (Bitstring x, Bitstring y) => (x = y)
       | (Bitstring x, Other ("Nil", ty)) =>
           Bitstring.size x = Nat.zero andalso Types.equalTy Type.bitstringTy ty
       | (Bool x, Bool y) => (x = y)
       | (Char x, Char y) => (x = y)
       | (Enum (x, s1), Enum (y, s2)) =>
           (x = y) andalso
           Types.equalTy (Type.mkConstType s1) (Type.mkConstType s2)
       | (Int x, Int y) => (x = y)
       | (Nat x, Nat y) => (x = y)
       | (Other (s1, ty1), Other (s2, ty2)) =>
           s1 = s2 andalso Types.equalTy ty1 ty2
       | (String x, String y) => (x = y)
       | (String "", Other ("Nil", ty)) => Types.equalTy Type.stringTy ty
       | (Other ("Nil", ty), String "") => Types.equalTy Type.stringTy ty
       | (Unit, Unit) => true
       | _ => false

   fun equalTm (t1, t2) =
      case (t1, t2) of
        (Lit v1, Lit v2) => valueEqual (v1, v2)
      | (Var (v1, ty1), Var (v2, ty2)) => v1 = v2 andalso Types.equalTy ty1 ty2
      | (BVar (i1, ty1), BVar (i2, ty2)) =>
           i1 = i2 andalso Types.equalTy ty1 ty2
      | (Comb ("{..}", ty1, l1), Comb ("{..}", ty2, l2)) =>
           Types.equalTy ty1 ty2 andalso Lib.setEqualEq equalTm l1 l2
      | (Comb (f1, ty1, l1), Comb (f2, ty2, l2)) =>
           f1 = f2 andalso Types.equalTy ty1 ty2 andalso
           List.all equalTm (ListPair.zip (l1, l2))
      | (Abs (l1, ty1, b1), Abs (l2, ty2, b2)) =>
           List.length l1 = List.length l2 andalso Types.equalTy ty1 ty2 andalso
           equalTm (b1, b2)
      | _ => false

   fun mkTermSet l =
      let
         val ty = if List.null l
                     then raise Fail "mkFiniteSet"
                  else Type.setTy (primTypeOf (hd l))
         val s = Lib.mkSetEq equalTm l
      in
         if List.null s
            then Lit (Other ("{}", ty))
         else Comb ("{..}", ty, s)
      end

   val equalTm = curry equalTm

   fun matchType ty tm = termTypeSubst (Types.match (primTypeOf tm) ty) tm

   exception TermMatch

   fun match t1 t2 =
      let
         val m = ref (Stringmap.empty: term Stringmap.dict)
         fun assign (v, t) = m := Stringmap.extend (!m, v, normalizeCons t)
                             handle Stringmap.Extend =>
                               ignore (equalTm t (Stringmap.find (!m, v))
                                       orelse raise TermMatch)
         fun mtch (x as (t1, t2)) =
            case x of
               (Lit (String _), _) => mtch (expandStringLit t1, t2)
             | (_, Lit (String _)) => mtch (t1, expandStringLit t2)
             | (Lit (Bitstring _), _) => mtch (expandBitstringLit t1, t2)
             | (_, Lit (Bitstring _)) => mtch (t1, expandBitstringLit t2)
             | (Lit v1, Lit v2) =>
                  if valueEqual (v1, v2) then [] else raise TermMatch
             | (Var ("_", ty), _) =>
                 (Types.match ty (primTypeOf t2)
                  handle Types.TypeMatch _ => raise TermMatch)
             | (Var (v, ty), _) =>
                  if equalTm t1 t2
                     then []
                  else ( assign (v, t2)
                       ; Types.match ty (primTypeOf t2)
                         handle Types.TypeMatch _ => raise TermMatch
                       )
             | (Comb (":", ty, [tm1, tm2]), _) =>
                 (case (dTypeOf tm1, dTypeOf tm2, Types.dest ty) of
                     (FixedBits s1, FixedBits s2, FixedBits s3) =>
                          (let
                              val _ = s1 + s2 = s3 andalso
                                      Types.equalTy ty (primTypeOf t2) orelse
                                      raise TermMatch
                              val h = s3 - 1
                              val m = h - s1
                              val tm3 = mkExtract (t2, h, m + 1)
                              val tm4 = mkExtract (t2, m, 0)
                              val u1 = mtch (tm1, tm3)
                              val u2 = mtch (termTypeSubst u1 tm2, tm4)
                           in
                              Type.combineSubst u2 u1
                           end
                           handle Fail _ => raise TermMatch)
                   | _ => raise TermMatch)
             | (Comb (",", _, [tm1, tm2]), _) =>
                 (case t2 of
                     Comb (",", _, [tm3, tm4]) =>
                       let
                          val u1 = mtch (tm1, tm3)
                          val u2 = mtch (termTypeSubst u1 tm2, tm4)
                       in
                          Type.combineSubst u2 u1
                       end
                   | _ =>
                     let
                        val ty2 = typeOf t2
                        val (lty, rty) = Types.destProd ty2
                                         handle Fail _ => raise TermMatch
                     in
                        mtch (t1, Comb (",", ty2, [Comb ("Fst", lty, [t2]),
                                                   Comb ("Snd", rty, [t2])]))
                     end)
             | (Comb (f, ty1, l1), Comb (g, ty2, l2)) =>
                  if f = g andalso List.length l1 = List.length l2
                     then let
                             val u1 =
                                List.foldl
                                   (fn ((x, y), u) =>
                                      let
                                         val u1 = mtch (termTypeSubst u x, y)
                                      in
                                         Type.combineSubst u1 u
                                      end) [] (ListPair.zip (l1, l2))
                             val u2 = Types.match (Type.typeSubst u1 ty1) ty2
                          in
                             Type.combineSubst u2 u1
                          end
                          handle Types.TypeMatch _ => raise TermMatch
                  else raise TermMatch
             | (Abs (l1, ty1, b1), Abs (l2, ty2, b2)) =>
                  if List.length l1 = List.length l2
                     then let
                             val u1 = mtch (b1, b2)
                             val u2 = Types.match (Type.typeSubst u1 ty1) ty2
                          in
                             Type.combineSubst u2 u1
                          end
                          handle Types.TypeMatch _ => raise TermMatch
                  else raise TermMatch
             | _ => raise TermMatch
         val u = mtch (t1, t2)
      in
         (!m, u)
      end

   fun tryMatch a b = SOME (match a b) handle TermMatch => NONE
   fun canMatch a b = Option.isSome (tryMatch a b)

   fun bvar (Abs (l, _, _)) = mkTuple (List.map Var l)
     | bvar _ = raise Fail "bvar"

   fun apply t v =
      case t of
         Abs (l, ty, b) =>
            let
               val (m, u) = match (bvar t) v
                            handle TermMatch => raise Fail "apply"
               fun f (v, ty) = Stringmap.find (m, v)
                               handle Stringmap.NotFound => Var (v, ty)
            in
               List.foldl (fn (x, tm) => subst 0 (f x) tm) (termTypeSubst u b) l
            end
       | _ => raise Fail "apply"

   fun appTerm f t =
      ( f t
      ; case t of
           Comb (_, _, l) => List.app (appTerm f) l
         | Abs (_, _, b) => appTerm f b
         | _ => ()
      )

   fun findMapTerm f =
      let
         fun findF (t as Lit _) = f t
           | findF (t as Var _) = f t
           | findF (t as BVar _) = f t
           | findF (t as Comb (_, _, l)) =
               (case f t of
                  SOME r => SOME r
                | NONE => findSome findF l)
           | findF (t as Abs (_, _, u)) =
               (case f t of
                  SOME r => SOME r
                | NONE => findF u)
      in
         findF
      end

   fun findTerm P =
      let
         fun findP (t as Lit _) = if P t then SOME t else NONE
           | findP (t as Var _) = if P t then SOME t else NONE
           | findP (t as BVar _) = if P t then SOME t else NONE
           | findP (t as Comb (_, _, l)) =
               if P t then SOME t else findSome findP l
           | findP (t as Abs (_, _, u)) = if P t then SOME t else findP u
      in
         findP
      end

   fun multipleOccs (s, ty) =
      let
         val occs = ref 0
         val eqty = Types.equalTy ty
      in
         Option.isSome o
         findTerm (fn Var (v, ty2) =>
                         v = s andalso eqty ty2 andalso
                         (0 < !occs orelse (Lib.inc occs; false))
                    | _ => false)
      end

   fun hasFreshTypeVars t =
      Option.isSome (findTerm (Type.hasFreshTypeVars o primTypeOf) t)

   fun freeVars t =
      let
         val vars = ref []
         fun eq ((v1, ty1), (v2, ty2)) = v1 = v2 andalso Types.equalTy ty1 ty2
         val ins = insertEq eq
      in
         appTerm (fn Var v => vars := ins v (!vars) | _ => ()) t
         ; !vars
      end

   val listFreeVars = Lib.mkSet o List.map fst o List.concat o List.map freeVars

   fun newVars l1 l2 =
      let
         val (vs, tys) = ListPair.unzip l2
         val l = List.foldr (fn (v, vs) => Lib.indexVariant vs v :: vs)
                    (listFreeVars l1) vs
         val l = List.take (l, List.length l2)
      in
         ListPair.map Var (l, tys)
      end

   val destEnumLit =
      fn Lit (Enum b) => b
       | _ => raise Fail "destEnumLit"

   val destCharLit =
      fn Lit (Char b) => b
       | _ => raise Fail "destCharLit"

   val destBoolLit =
      fn Lit (Bool b) => b
       | _ => raise Fail "destBoolLit"

   val destNumLit =
      fn Lit (Nat b) => b
       | _ => raise Fail "destNumLit"

   val destNatLit = Nat.toInt o destNumLit

   val destIntLit =
      fn Lit (Int b) => b
       | _ => raise Fail "destIntLit"

   val destBitsLit =
      fn Lit (Bits b) => b
       | _ => raise Fail "destBitsLit"

   val destRounding =
      fn Lit (Enum (0, "rounding")) => IEEEReal.TO_NEAREST
       | Lit (Enum (1, "rounding")) => IEEEReal.TO_POSINF
       | Lit (Enum (2, "rounding")) => IEEEReal.TO_NEGINF
       | Lit (Enum (3, "rounding")) => IEEEReal.TO_ZERO
       | _ => raise Fail "destRounding"

   val destStringLit =
      fn Lit (String b) => b
       | Lit (Other ("Nil", ty)) =>
           if Types.equalTy Type.stringTy ty then
              ""
           else raise Fail "destStringLit"
       | _ => raise Fail "destStringLit"

   val destBitstringLit =
      fn Lit (Bitstring b) => b
       | Lit (Other ("Nil", ty)) =>
           if Types.equalTy Type.bitstringTy ty then
              Bitstring.fromList []
           else raise Fail "destBitstringLit"
       | _ => raise Fail "destBitstringLit"

   val destVar =
      fn Var x => x
       | _ => raise Fail "destVar"

   val destTuple =
      let
         fun iter a =
            fn Comb (",", _, [l, r]) => iter (iter a l) r
             | tm => tm :: a
      in
         List.rev o iter []
      end

   val tupleVars = List.map destVar o destTuple

   local
      val dest =
         let
            fun iter a =
               fn Comb (",", _, [l, r]) => iter (iter a l) r
                | Comb (":", _, [l, r]) => iter (iter a l) r
                | tm => tm :: a
         in
            List.rev o iter []
         end
   in
      val lhsVars = List.map destVar o dest
   end

   fun destApp tm =
      case tm of
        Comb (f, _, [a]) => (f, a)
      | _ => raise Fail "destApp"

   fun destPair tm =
      case tm of
        Comb (",", _, [l, r]) => (l, r)
      | _ => raise Fail "destPair"

   fun destTriple tm =
      case destTuple tm of
         [a, b, c] => (a, (b, c))
       | _ => raise Fail "destTriple"

   val destTermSet =
      fn Lit (Other ("{}", _)) => []
       | Comb ("{..}", _, l) => l
       | _ => raise Fail "destTermSet"

   fun mkAbs (v, b) = absList (tupleVars v) b

   fun mkCase (p, b) =
      let
         val ty = primTypeOf b
         val bvars = freeVars p
      in
         Comb ("case", ty, [absList bvars (mkPair (p, b))])
      end

   fun mkMatch (v, []) = raise Fail "mkMatch: no cases"
     | mkMatch (v, cs) =
         Comb ("match", primTypeOf (snd (hd cs)), v :: List.map mkCase cs)

   fun mkApply (f, x) =
      let
         val (ty1, ty2) = Type.domrng (primTypeOf f)
         val s = Types.match ty1 (primTypeOf x)
      in
         Comb ("abs-apply", Type.typeSubst s ty2, [termTypeSubst s f, x])
      end
      handle Types.TypeMatch _ => raise Fail "mkApply"

   fun mkMatchApply ty = matchType ty o mkApply

   fun mkCompose (f, g) =
      let
         val (fty1, fty2) = Types.domainRange (primTypeOf f)
         val (gty1, gty2) = Types.domainRange (primTypeOf g)
         val () = ignore (Types.equalTy gty2 fty1 orelse
                          raise Fail "mkCompose: bad types")
         val v = hd (newVars [f, g] [("v", gty1)])
      in
         mkAbs (v, mkApply (f, mkApply (g, v)))
      end

   fun mkIfThen (b, t, e) =
      let
         val ty = primTypeOf t
         val () = ignore (Types.equalTy ty (primTypeOf e) andalso
                          Types.equalTy Type.boolTy (primTypeOf b) orelse
                          raise Fail "mkIfThen")
      in
         Comb ("i-t-e", ty, [b, t, e])
      end

   fun mkIfThens (l, e) = List.foldr (fn ((b, t), e) => mkIfThen (b, t, e)) e l

   fun mkLet (t, expr, body) =
      let
         val ty = primTypeOf expr
         val () = ignore (Types.equalTy (primTypeOf t) ty orelse
                          raise Fail "type mismatch")
         val vs = lhsVars t
         val abs =
            case vs of
               [] => raise Fail "mkLet"
             | [_] => absList vs body
             | _ => let
                       val fvs = List.map fst (freeVars body)
                       val x = Lib.indexVariant fvs "x"
                       val a = (x, ty)
                    in
                       absList [a] (mkMatch (Var a, [(t, body)]))
                    end
      in
         mkApply (abs, expr)
      end
      handle Fail m => raise Fail ("mkLet: " ^ m)

   fun destAbs tm =
      case tm of
         Abs (l, _, b) =>
           let
              val v = mkTuple (newVars [b] l)
           in
              (v, apply tm v)
           end
       | _ => raise Fail "destAbs"

   val destAbsPair = destPair o snd o destAbs

   local
      val f = Fail "destMatch"
   in
      fun destCase tm =
         case tm of
           Comb ("case", _, [x]) =>
            ((case x of
                Abs _ => destAbsPair x
              | _ => destPair x)
             handle Fail _ => raise f)
         | _ => raise f
      fun destMatch tm =
         case tm of
           Comb ("match", _, h :: l) => (h, List.map destCase l)
         | _ => raise f
   end

   val destLet =
      fn Comb ("abs-apply", ty, [a as Abs (l, _, b), e]) =>
         (case (l, b) of
            ([_], Comb ("match", _, [BVar (0, _), c])) =>
              (case c of
                 Comb ("case", _, [a2 as Abs (_, _, Comb (",", _, [_, _]))]) =>
                    (case snd (destAbs a2) of
                       Comb (",", _, [t, bd]) => (t, e, bd)
                     | _ => raise Fail "destLet")
               | Comb ("case", _, [Comb (",", _, [t, bd])]) => (t, e, bd)
               | _ => raise Fail "destLet")
          | _ => let
                    val (t, bd) = destAbs a
                 in
                    (t, e, bd)
                 end)
       | _ => raise Fail "destLet"

   val destList =
      let
         fun iter a t =
            case t of
               Lit (Other ("Nil", _)) => List.rev a
             | Lit (String s) =>
                  List.rev a @ List.map mkCharLit (String.explode s)
             | Lit (Bitstring s) =>
                  List.rev a @ List.map mkBoolLit (Bitstring.toList s)
             | Comb ("Cons", _, [Comb (",", _, [x, y])]) =>
                 iter (x :: a) y
             | _ => raise Fail "destList"
      in
         iter []
      end

   val destLets =
      let
         fun iter a t =
            case Lib.total destLet t of
               SOME (v, e, b) => iter ((v, e) :: a) b
             | NONE => (List.rev a, t)
      in
         iter []
      end

   val destIfThens =
      let
         fun iter a =
            fn Comb ("i-t-e", _, [b, t, e]) => iter ((b, t) :: a) e
             | e => (List.rev a, e)
      in
         iter []
      end

   val destConcats =
      let
         fun iter a =
            fn Comb (":", _, [b, c]) => iter (b :: a) c
             | t => List.rev (t :: a)
      in
         iter []
      end

   fun destBinOp s =
      fn Comb (f, _, [a, b]) =>
           if f = s then (a, b) else raise Fail ("destBinop " ^ s ^ " : " ^ f)
       | _ => raise Fail ("destBinOp " ^ s)

   structure TermMap = Map (type index = term val eq = Lib.uncurry equalTm)

   fun destMap tm =
      let
         val (cs, d) = destIfThens (snd (destAbs tm))
      in
         TermMap.mk (List.map ((snd o destBinOp "==") ## Lib.I) cs, d)
      end

   fun printMapDiff x =
      TermMap.printDiff (Lib.uncurry equalTm, compare) x o (destMap ## destMap)

   fun mkMap (dty, rty) ((l, b): term TermMap.map) =
         let
            val v = Var ("a", dty)
            val d = case b of SOME v => v | NONE => unknown rty
            fun mkeq t = Comb ("==", Type.boolTy, [v, t])
         in
            mkAbs (v, mkIfThens (List.map (mkeq ## I) l, d))
         end

   exception NoConv

   fun depthconv c =
      let
         fun cv tm =
            case tm of
              Abs _ =>
                let
                   val (v, b) = destAbs tm
                   val d = mkAbs (v, cv b)
                in
                   c d handle NoConv => d
                end
            | Comb (f, ty, l) =>
               let
                  val d = Comb (f, ty, List.map cv l)
               in
                   c d handle NoConv => d
               end
            | _ => c tm handle NoConv => tm
      in
         cv
      end

   fun topconv c =
      let
         fun cv tm =
            case tm of
              Abs _ =>
                 (c tm handle NoConv =>
                    let
                       val (v, b) = destAbs tm
                    in
                       mkAbs (v, cv b)
                    end)
            | Comb (f, ty, l) =>
               (c tm handle NoConv => Comb (f, ty, List.map cv l))
            | _ => c tm handle NoConv => tm
      in
         cv
      end

   local
      fun annotate s ty = s ^ "::" ^ anonTypeToString ty
   in
      fun rawTermToString tm =
         case tm of
            Lit (Bits w) => PolyML.makestring w
          | Lit (Bitstring w) => "0s" ^ Bitstring.toBinString w
          | Lit (Bool true) => "true"
          | Lit (Bool false) => "false"
          | Lit (Char c) => "#\"" ^ String.str c ^ "\""
          | Lit (Enum (n, s)) => annotate (Nat.toString n) (Type.mkConstType s)
          | Lit (Int i) => "0i" ^ Int.toString i
          | Lit (Nat i) => "0n" ^ Nat.toString i
          | Lit (Other (s, ty)) => annotate s ty
          | Lit (String s) => "\"" ^ s ^ "\""
          | Lit Unit => "()"
          | Var (s, ty) => annotate ("(var " ^ s ^ ")") ty
          | BVar (n, ty) => annotate ("(bvar " ^ Int.toString n ^ ")") ty
          | Comb (",", ty, l) => commify rawTermToString l
          | Comb (f, ty, l) =>
             annotate (f ^ "(" ^ commify rawTermToString l ^ ")") ty
          | Abs (_, ty, _) =>
             let
                val (v, b) = destAbs tm
             in
                annotate ("(\\(" ^ rawTermToString v ^ ")." ^
                          rawTermToString b ^ ")") ty
             end
   end

   fun bitsToString tm =
      BitsN.toString (destBitsLit tm)
      handle Fail "destBitsLit" => rawTermToString tm

   fun bitsToHexString tm =
      BitsN.toHexString (destBitsLit tm)
      handle Fail "destBitsLit" => rawTermToString tm

   fun bitsToPaddedHexString tm =
      let
         val i = destBitsLit tm
         val p = Nat.toInt (BitsN.size i) div 4
      in
         "0x" ^ StringCvt.padLeft #"0" p (BitsN.toHexString i)
      end
      handle Fail "destBitsLit" => rawTermToString tm

   exception TypeCheck of {loc: int, operation: string, args: term list,
                           valid_types: Type.ty list, message: string}

   local
      fun pick tms ty =
         let
            fun iter [] = raise Fail "pick"
              | iter (h :: t) =
                   let
                      val u = unify ty (mkFresh h)
                      val tms' = List.map (termTypeSubst u) tms
                                 handle Fail "termTypeSubst" =>
                                   raise Unify "Bad literal."
                   in
                      (u, range (typeSubst u ty), tms')
                   end
                   handle Unify e =>
                           (if List.null t then raise Unify e else iter t)
         in
            iter
         end

      fun pickUnifier (loc, s) tms ty l = pick tms ty l
         handle Unify e =>
            let
               val m = case l of
                          h :: _ :: _ => ((pick tms ty [h]; "")
                                         handle Unify e => e)
                        | _ => e
            in
               raise TypeCheck {loc = loc, operation = s, args = tms,
                                valid_types = l, message = m}
            end

      fun typeCheck1 u env (b, t) = b (Env.updateEnv u env) t
   in
      fun typeCheck loc_s env g f types =
         fn [] => raise Fail "typeCheck: empty"
          | h :: l =>
              let
                 val m = Type.freshMarker()
                 val (u, tms) =
                    List.foldl
                       (fn (x, (u, tms)) =>
                          let
                             val (u1, tm) = typeCheck1 u env x
                          in
                             (combineSubst u1 u,
                              tm :: List.map (termTypeSubst u1) tms)
                          end) ((I ## singleton) (typeCheck1 [] env h)) l
                 val tms = List.rev tms
                 val (lst, rst) = lastButlast tms
                 val ty = List.foldr (fn (t, ty) => g t ** ty) (g lst) rst
                 val (u1, ty2, tms2) =
                    pickUnifier loc_s tms (ty --> f tms) types
                 val u = combineSubst u1 u
              in
                 (Type.filterSubst m u, ty2, tms2)
              end
   end

   fun genUnknown (ty as (bty, c)) =
      case bty of
        Type.ConstType c =>
           (case Types.lookupConst c of
               SOME { def = Types.Record l, ... } =>
                 Comb ("!" ^ c, ty, List.map (genUnknown o snd) l)
             | SOME { def = Types.Constructors (Types.Construct m), ... } =>
                 (case hd (Stringmap.listItems m) of
                     (s, SOME ty1) => Comb (s, ty, [genUnknown ty1])
                   | (s, NONE) => Lit (Other (s, ty)))
             | SOME { def = Types.Constructors (Types.Enum e), ... } =>
                 Lit (Other (fst (hd (Stringmap.listItems e)), ty))
             | SOME { def = Types.Typedef ty2, ... } => genUnknown ty2
             | SOME { def = Types.BaseType, ... } =>
                 (case c of
                     "unit" => unitTm
                   | "bool" => mkBoolLit false
                   | "int" => mkIntLit 0
                   | "nat" => mkNatLit 0
                   | "string" => mkStringLit ""
                   | "bitstring" => mkBitstringLit (Bitstring.fromInt 0)
                   | _ => raise Fail ("genUnknown: " ^ c)
                 )
             | NONE => raise Fail "genUnknown")
      | Type.ParamType (Type.ListTy, lty) =>
           if Types.equalTy Type.charTy (lty, c)
              then Lit (String "")
           else Lit (Other ("Nil", ty))
      | Type.ParamType (Type.OptionTy, _) => Lit (Other ("None", ty))
      | Type.ParamType (Type.SetTy, _) => Lit (Other ("{}", ty))
      | Type.BV i => mkBitsLit (BitsN.zero (Nat.fromInt i))
      | Type.BVV _ => Comb ("[..]", ty, [mkNatLit 0])
      | Type.Arrow _ =>
           let
              val (ty1, ty2) = Type.domrng ty
           in
              absList [("_", ty1)] (genUnknown ty2)
           end
      | Type.Prod tys =>
           let
              val (ty1, ty2) = Type.fstsnd ty
           in
              mkPair (genUnknown ty1, genUnknown ty2)
           end
      | _ => raise Fail "genUnknown"

   local
      val vnum = ref 0

      val patterns = List.map fst o snd o destMatch

      fun newVar ty =
         Var ("v" ^ Int.toString (!vnum) before (vnum := !vnum + 1), ty)

      fun freshVs tm =
         case tm of
            Var (_, ty) => newVar ty
          | Abs (l, ty, b) => Abs (l, ty, freshVs b)
          | Comb (f, ty, l) => Comb (f, ty, List.map freshVs l)
          | _ => tm

      fun expandPattern t =
         case t of
            Var (_, ty) =>
               (let
                   val (ty1, ty2) = Types.destProd ty
                in
                   mkPair (expandPattern (Var ("_", ty1)),
                           expandPattern (Var ("_", ty2)))
                end
                handle Fail "destProd" => newVar ty)
          | Lit _ => t
          | Comb (":", _, [_, _]) => t
          | Comb (",", ty, [x, y]) =>
              Comb (",", ty, [expandPattern x, expandPattern y])
          | Comb (f, ty, [x]) => Comb (f, ty, [expandPattern x])
          | _ => raise Fail "expandPattern"

      val boolifyPattern =
         let
            fun iter t =
               case dTypeOf t of
                 Type.FixedBits i =>
                   (case t of
                      Lit (Bits x) => List.map mkBoolLit (BitsN.toList x)
                    | Var _ => List.tabulate (i, fn _ => newVar Type.boolTy)
                    | Comb (":", _, [a, b]) => iter a @ iter b
                    | _ => raise Fail "boolifyPattern")
               | _ => raise Fail "boolifyPattern: not fixed"
         in
            mkTuple o iter
         end

      val isBitPattern =
         fn Comb (":", _, [_, _]) => true
          | _ => false

      val isCons =
         fn Lit _ => true
          | Comb _ => true
          | _ => false

      fun consEqual (x, y) =
         case (x, y) of
            (Lit v1, Lit v2) => valueEqual (v1, v2)
          | (Lit (String s), Comb ("Cons", _, _)) => s <> ""
          | (Comb ("Cons", _, _), Lit (String s)) => s <> ""
          | (Lit (Bitstring s), Comb ("Cons", ty, _)) =>
              Bitstring.size s <> Nat.zero
          | (Comb ("Cons", ty, _), Lit (Bitstring s)) =>
              Bitstring.size s <> Nat.zero
          | (Comb (f, _, _), Comb (g, _, _)) => f = g
          | (Var _, Var _) => true
          | _ => false

      fun findP base (mx: 'a * 'a -> 'a) =
         let
            fun iter m =
               fn [] => m
                | h :: t => iter (mx (m, h)) t
         in
            iter base
         end

      val findVal =
         let
            fun iter n =
               fn [] => n
                | h :: t => if n = h then iter (n + 1) t else n
         in
            iter 0
         end

      val supremum = findP 0 Int.max

      fun newNumeric mk cs =
         let
            val ns = List.mapPartial
                       (fn Lit (Int i) => SOME i
                         | Lit (Nat i) => SOME (Nat.toInt i)
                         | _ => NONE) cs
         in
            mk (supremum ns + 1) :: cs
         end

      fun newBits i ns =
         let
            val new = findVal (msort Int.compare (List.map BitsN.toUInt ns))
         in
            mkBitsLit (BitsN.fromInt (new, Nat.fromInt i))
         end

      fun genConstructor ename ty cs (u: Types.cons_dict) =
         let
            val g = List.mapPartial
                      (fn Comb (s, _, _) => SOME s
                        | Lit (String "") => SOME "Nil"
                        | Lit (String _) => SOME "Cons"
                        | Lit (Bitstring s) =>
                             SOME (if Bitstring.size s = Nat.zero
                                      then "Nil"
                                   else "Cons")
                        | Lit (Enum (n, s)) => Types.revenum s n
                        | Lit (Other (s, _)) => SOME s
                        | _ => NONE) cs
            val a = Stringmap.listItems u
            val l = case List.partition (fn (s, _) => mem s g) a of
                      (l, []) => l
                    | (l, h :: _) => h :: l
            fun mklit s =
               Lit (case ename of
                       SOME e =>
                         (Enum (Option.valOf (Types.enum e s), e)
                          handle Option =>
                            raise Fail ("genConstructor: " ^ e ^ " " ^ s))
                     | NONE => Other (s, ty))
         in
            List.map
              (fn (s, NONE) => mklit s
                | (s, SOME ty2) =>
                  Comb (s, ty, [expandPattern (Var ("_", ty2))])) l
         end

      fun genCases ty cs =
         case Types.dest ty of
           Type.Other "" => raise Fail "genCases: other"
         | Type.Other "set" => raise Fail "genCases: set"
         | Type.Other "unit" => [unitTm]
         | Type.Other "bool" => [Lit (Bool false), Lit (Bool true)]
         | Type.Other "char" =>
            let
               val ns = List.mapPartial
                          (fn Lit (Char c) => SOME (Char.ord c)
                            | _ => NONE) cs
            in
               if List.length ns = 256
                  then cs
               else mkCharLit (Char.chr (supremum ns + 1)) :: cs
            end
         | Type.Other "nat" => newNumeric mkNatLit cs
         | Type.Other "int" => newNumeric mkIntLit cs
         | Type.Other c =>
           if Lib.mem c ["string", "bitstring", "list", "option"]
              then genConstructor NONE ty cs (Types.constructors ty)
           else (case Types.lookupConst c of
                    SOME {eq = true, def = Types.Constructors x, ...} =>
                      (case x of
                         Types.Enum e =>
                            genConstructor (SOME c) ty cs
                              (Stringmap.map (K (NONE: Type.ty option)) e)
                       | Types.Construct u => genConstructor NONE ty cs u)
                  | SOME {def = Types.Record x, ...} =>
                      [Comb (Tag.mkRecord c, ty,
                             List.map (fn (_, ty2) => Var ("_", ty2)) x)]
                  | _ => raise Fail "genCases: const")
         | Type.VarBits (v, s) =>
            let
               val i = PosIntSet.supremum s
            in
               if i < 1
                  then newNumeric
                         (fn n => Lit (Other ("?x" ^ Int.toHexString n, ty))) cs
               else let
                       val tyi = Type.fixedTy i
                       fun setType t =
                          List.map (fn Lit (Other (x, _)) => Lit (Other (x, t))
                                     | _ => raise Fail "genCases: not lit")
                    in
                       setType ty (genCases tyi (setType tyi cs))
                    end
            end
         | Type.FixedBits i =>
            let
               val ns =
                  List.mapPartial (fn Lit (Bits x) => SOME x | _ => NONE) cs
               val sz = IntInf.pow (2, i)
            in
               if List.length ns = sz
                  then cs
               else newBits i ns :: cs
            end

      fun instPat ctm varPat (q, j) =
         (inst1 (Option.valOf (varPat q), ctm) q, j)
         handle Option => raise Fail "checkCover"

      fun getCons template tm =
         List.find (isCons o snd)
            (Stringmap.listItems (fst (match template tm)))

      fun filterOptional (vs, (x, m)) ([], m1) = (vs, (x, m1 orelse m))
        | filterOptional (vs, (x, m)) (x1, m1) =
         let
            val vs1 = List.mapPartial
                        (fn (j, n) =>
                           if mem j x1
                              then if n < 2 then NONE else SOME (j, n - 1)
                           else SOME (j, n)) vs
            val l = List.mapPartial (fn (j, n) =>
                       if 1 < n andalso mem j x1 then SOME j else NONE) vs
            val x2 = List.filter (not o (fn j => mem j l)) x1
         in
            (vs1, (union x2 x, m1 orelse m))
         end

      fun splitMatches consPat =
         let
            fun iter (tms, l, r) =
               fn [] => (List.rev tms, List.rev l, List.rev r)
                | (h as (p, _))::t =>
                    (case consPat p of
                       SOME c => iter (c :: tms, h :: l, r) t
                     | NONE => iter (tms, l, h :: r) t)
         in
            iter ([], [], [])
         end

      val anonymize =
         depthconv
            (fn Var (_, ty) => Var ("_", ty)
              | Comb (",", ty, [Var _, Var _]) => Var ("_", ty)
              | t => t)

      fun cover template =
         fn [] => ([], (printn (PolyML.makestring (anonymize template)); true))
          | ps as (p, _)::t =>
             case getCons template p of
               SOME (v, tm) =>
                 let
                    fun consPat p =
                       case Stringmap.peek (fst (match template p), v) of
                         SOME c => if isCons c then SOME c else NONE
                       | _ => NONE
                    val (tms, l, r) = splitMatches consPat ps
                    val ty = typeOf tm
                 in
                    if List.exists isBitPattern tms
                       then let
                               val z = newVar ty
                               val ps' =
                                  List.map (fn (q, j) =>
                                     let
                                        val m = fst (match template q)
                                        val m' = Stringmap.map (fn (s, y) =>
                                                   if s = v then z else y) m
                                        val q' = inst m' template
                                        val e = boolifyPattern
                                                  (Stringmap.find (m, v))
                                     in
                                        (mkPair (e, q'), j)
                                     end) ps
                               val nty = Type.fstTy (primTypeOf (fst (hd ps')))
                               val template' = inst1 (v, z) template
                               val template' = mkPair (newVar nty, template')
                            in
                               cover (expandPattern template') ps'
                            end
                    else
                       let
                          fun varPat p =
                             case Stringmap.peek (fst (match template p), v) of
                               SOME (Var (w, _)) => SOME w
                             | _ => NONE
                          val tms = genCases ty (mkSetEq consEqual tms)
                          val n = List.length tms
                          val vs = List.mapPartial (fn (v, j) =>
                                     if Option.isSome (varPat v)
                                        then SOME (j, n)
                                     else NONE) r
                       in
                          List.foldl (fn (ctm, a) =>
                           let
                              val template' = inst1 (v, ctm) template
                              val f = List.filter (canMatch template' o fst) l
                              val g = List.map (instPat (freshVs ctm) varPat) r
                              val fg =
                                 Lib.merge (Int.compare o (snd ## snd)) (f, g)
                           in
                              filterOptional a (cover template' fg)
                           end) (vs, ([], false)) tms |> snd
                       end
                 end
             | NONE => (List.map snd t, false)

      fun createPattern ty =
         let
            val (ty1, ty2) = Type.fstsnd ty
         in
            mkPair (createPattern ty1, createPattern ty2)
         end
         handle Fail "fstsnd" => newVar ty

      fun checkCover pats =
        ( vnum := 0
        ; case pats of
             [] => ([], false)
           | l as p :: _ =>
               cover (createPattern (typeOf p))
                     (Lib.addIndex (List.map expandPattern l))
               |> (msort Int.compare ## I)
        )
   in
      val checkMatch = checkCover o patterns
   end


(*

val template = template';
val ps as (p, _)::t = fg
val SOME (v, tm) = getCons template p;

val ctm = hd tms;
val a = (vs, ([], false))

open Term

Parser.check_match false;
Parser.reset();

Parser.loadQ`
   construct c {
     cons1 :: int * int
     cons2 :: bool
     cons3 :: nat * bool
   }
   nat test (x::c) =
      match x {
        case cons1 (0i1, 0i2) => 0n1
        case cons2 (false) => 0n2
        case cons3 (0n2, true) => 0n3
        case _ => 0n4
      }`

val pats = patterns tm


PolyML.use "Parser.sml";
open Term Parser;
PolyML.print_depth 100;

val SOME (def, _) = Consts.lookupDefinition "test";
val tm = Term.apply def (Term.bvar def);
checkMatch tm

val _ = vnum := 0
val ps = List.map (expandPattern ## I) (patterns tm)
val ((p, _)::t) = ps
val template = createPattern (typeOf p)

val SOME (v, tm) = getCons template p;
val ctm = hd tms;

*)

end (* structure Term *)

val () = PolyML.addPrettyPrinter Term.printer

(* -------------------------------------------------------------------------
   Consts

   Database of built-in and user defined constants.
   Includes functions, exceptions and constructors
   ------------------------------------------------------------------------- *)

signature Consts =
sig
   type measure = (string * Term.term) option

   type defn = {def: Term.term,
                measure: measure,
                name: string,
                recursive: bool,
                user: bool}

   datatype const = Primitive of Type.ty list
                  | Destructor of (Term.term * Term.term * bool * int) list
                  | Constructor of Type.ty
                  | Accessor of Term.term * Term.term * int
                  | Exception of Type.ty option
                  | Definition of Term.term * measure * int
                  | Undefined

   val addAccessor: string * Term.term * Term.term -> unit
   val addConst: string * const -> unit
   val addConstructor: string * Type.ty -> unit
   val addDefinition: string * Term.term * measure -> unit
   val addDestructor: string * Term.term * Term.term * bool -> unit
   val addException: string * Type.ty option -> unit
   val allowExceptionOverload: bool ref
   val augmentAST: string list * Constrain.constraints * Type.ty option -> unit
   val buildDatatype:
      Env.env -> (string -> unit) ->
      string * (string * Type.ty option) list -> unit
   val defineRun: unit -> unit
   val delConst: string -> unit
   val isAccessor: string -> bool
   val isConst: string -> bool
   val isConstant: string -> bool
   val isConstructor: string -> bool
   val isDefinition: string -> bool
   val isDestructor: string -> bool
   val isEmptyAST: unit -> bool
   val isException: string -> bool
   val listConsts: unit -> (string * const) list
   val listDefinitions: unit -> defn list
   val listExceptions: unit -> (string * Type.ty option) list
   val lookupAccessor: string -> (Term.term * Term.term) option
   val lookupConst: string -> const
   val lookupConstant: string -> Type.ty option
   val lookupConstructor: string -> Type.ty option
   val lookupDefinition: string -> (Term.term * measure) option
   val lookupDestructor: string -> (Term.term * Term.term) list
   val lookupException: string -> Type.ty option option
   val lookupOperation: string -> Type.ty list option
   val pickDestructor: Type.ty -> const -> Term.term option
   val resetAST: unit -> unit
   val resetConsts: unit -> unit
   val restoreConsts: unit -> unit
   val runDefined: unit -> bool
   val saveConsts: unit -> unit
   val stats: unit -> unit
end

structure Consts :> Consts =
struct
   open Type

   type measure = (string * Term.term) option

   type defn = {def: Term.term,
                measure: measure,
                name: string,
                recursive: bool,
                user: bool}

   datatype const =
      Primitive of ty list
    | Destructor of (Term.term * Term.term * bool * int) list
                                                (* record/bit-field selector *)
    | Constructor of ty                         (* for enum, union, AST types *)
    | Accessor of Term.term * Term.term * int   (* for read/write operations *)
    | Exception of ty option
    | Definition of Term.term * measure * int
    | Undefined

   val binRel = [eqAlphaTy ** eqAlphaTy --> boolTy]
   val wordRel = [wordTy "a" ** wordTy "a" --> boolTy]
   val natRel = [natTy ** natTy --> boolTy]
   val intRel = [intTy ** intTy --> boolTy]

   val arithRel = wordRel @ natRel @ intRel
   val boolBinOpTy = [boolTy ** boolTy --> boolTy]
   val bitstringBinOpTy = [bitstringTy ** bitstringTy --> bitstringTy]
   val wordBinOpTy = [wordTy "a" ** wordTy "a" --> wordTy "a"]
   val natBinOpTy = [natTy ** natTy --> natTy]
   val intBinOpTy = [intTy ** intTy --> intTy]
   val arithBinOpTy = wordBinOpTy @ natBinOpTy @ intBinOpTy
   (* val setBinOpTy = [setTy "a" ** setTy "a" --> setTy "a"] *)
   val shiftOpTy = [wordTy "a" ** natTy --> wordTy "a"] @ wordBinOpTy @
                   [bitstringTy ** natTy --> bitstringTy]

   val boolUnaryOpTy = [boolTy --> boolTy]
   val wordUnaryOpTy = [wordTy "a" --> wordTy "a"]
   val natUnaryOpTy = [natTy --> natTy]
   val intUnaryOpTy = [intTy --> intTy]

   val float16Ty = fixedTy 16
   val float32Ty = fixedTy 32
   val float64Ty = fixedTy 64

   fun optionDef (s: string, some, none) =
      let
         val aTy = Type.alphaTy
         val oaTy = Type.optionTy aTy
         val x = Term.Var ("x", oaTy)
         val v = Term.Var ("v", aTy)
      in
        (s,
         Definition
            (Term.mkAbs (x,
                Term.mkMatch (x,
                  [(Term.Comb ("Some", oaTy, [v]), some v),
                   (Term.Lit (Term.Other ("None", oaTy)), none aTy)])),
             NONE, ~1))
      end

   val ValOf = optionDef ("ValOf", Lib.I, fn aTy => Term.unknown aTy)

   val IsSome =
      optionDef ("IsSome", Lib.K (Term.mkBoolLit true),
                           Lib.K (Term.mkBoolLit false))

   fun listDef (s: string, aTy, f, g) =
      let
         open Term
         val laTy = Type.listTy aTy
         val x = Term.Var ("x", laTy)
         val v1 = Term.Var ("h", aTy)
         val v2 = Term.Var ("t", laTy)
         val v = Term.mkPair (v1, v2)
      in
         (s,
          Definition
             (mkAbs (x,
                mkMatch (x,
                  [(Comb ("Cons", laTy, [v]), f (v1, v2)),
                   (Lit (Other ("Nil", laTy)), g (aTy, laTy))])), NONE, ~1))
      end

   val Length =
      let
         open Term
         val aTy = Type.alphaTy
         val laTy = Type.listTy aTy
         val nTy = Type.natTy
         val x = Term.Var ("x", laTy)
         val v1 = Term.Var ("h", aTy)
         val v2 = Term.Var ("t", laTy)
         val v = Term.mkPair (v1, v2)
      in
         ("Length",
          Definition
             (mkAbs (x,
                mkMatch (x,
                  [(Comb ("Cons", laTy, [v]),
                    Comb ("+", nTy,
                          [mkNatLit 1, Comb ("Length", nTy, [v2])])),
                   (Lit (Other ("Nil", laTy)), mkNatLit 0)])), NONE, ~1))
      end

   val Head = listDef ("Head", Type.alphaTy, fst, Term.unknown o fst)
   val Tail = listDef ("Tail", Type.alphaTy, snd, Term.unknown o snd)

   val SetOfList =
      let
         val ty = Type.setTy Type.eqAlphaTy
      in
         listDef ("SetOfList", Type.eqAlphaTy,
            fn (a, b) =>
              Term.Comb ("insert", ty, [a, Term.Comb ("SetOfList", ty, [b])]),
            Lib.K (Term.Lit (Term.Other ("{}", ty))))
      end

   val InitMap =
      let
         val aTy = Type.alphaTy
         val bTy = Type.betaTy
         val x = Term.Var ("_", aTy)
         val y = Term.Var ("y", bTy)
      in
         ("InitMap", Definition (Term.mkAbs (y, Term.mkAbs (x, y)), NONE, ~1))
      end

   val primConstructors = List.map (I ## Constructor)
      [("true", boolTy),
       ("false", boolTy),
       ("()", unitTy),
       ("{}", setTy eqAlphaTy),
       ("Nil", listTy alphaTy),
       ("Cons", alphaTy ** listTy alphaTy --> listTy alphaTy),
       ("None", optionTy alphaTy),
       ("Some", alphaTy --> optionTy alphaTy),
       ("roundTiesToEven", roundingTy),
       ("roundTowardPositive", roundingTy),
       ("roundTowardNegative", roundingTy),
       ("roundTowardZero", roundingTy)]

   val primOps = List.map (I ## Primitive)
      [("not", boolUnaryOpTy),
       ("or", boolBinOpTy),
       ("and", boolBinOpTy),
       ("==", binRel),
       ("<-", [alphaTy ** alphaTy --> unitTy]), (* assignment *)
       ("<.>", [wordTy "a" ** natTy --> boolTy,
                bitstringTy ** natTy --> boolTy]), (* w<n> *)
       (",", [alphaTy ** betaTy --> alphaTy ** betaTy]),
       ("'..'", wordUnaryOpTy), (* bit pattern *)
       ("<", arithRel),
       ("<+", wordRel),
       ("<=", arithRel),
       ("<=+", wordRel),
       (">", arithRel),
       (">+", wordRel),
       (">=", arithRel),
       (">=+", wordRel),
       ("in", [eqAlphaTy ** setTy eqAlphaTy --> boolTy]),
       ("insert", [eqAlphaTy ** setTy eqAlphaTy --> setTy eqAlphaTy]),
       ("~", wordUnaryOpTy),
       ("+", arithBinOpTy  @ bitstringBinOpTy),
       ("-", arithBinOpTy), (* unary treated as special case *)
       ("*", arithBinOpTy),
       ("quot", wordBinOpTy @ intBinOpTy),
       ("rem", wordBinOpTy @ intBinOpTy),
       ("QuotRem", [intTy ** intTy --> intTy ** intTy]),
       ("div", arithBinOpTy), (* / *)
       ("mod", arithBinOpTy), (* % *)
       ("Abs", wordUnaryOpTy @ intUnaryOpTy),
       ("Min", arithBinOpTy),
       ("Max", arithBinOpTy),
       ("SignedMin", wordBinOpTy),
       ("SignedMax", wordBinOpTy),
       ("Msb", [wordTy "a" --> boolTy]),
       ("||", wordBinOpTy @ bitstringBinOpTy),
       ("&&", wordBinOpTy @ bitstringBinOpTy),
       ("??", wordBinOpTy @ bitstringBinOpTy),
       ("Fst", [alphaTy ** betaTy --> alphaTy]),
       ("Snd", [alphaTy ** betaTy --> betaTy]),
       ("Cardinality", [setTy eqAlphaTy --> natTy]),
       ("IsSubset", [setTy eqAlphaTy ** setTy eqAlphaTy --> boolTy]),
       ("Union", [setTy eqAlphaTy ** setTy eqAlphaTy --> setTy eqAlphaTy]),
       ("Intersect", [setTy eqAlphaTy ** setTy eqAlphaTy --> setTy eqAlphaTy]),
       ("Difference", [setTy eqAlphaTy ** setTy eqAlphaTy --> setTy eqAlphaTy]),
       ("Reverse", [wordTy "a" --> wordTy "a",
                    listTy alphaTy --> listTy alphaTy]),
       ("Take", [natTy ** listTy alphaTy --> listTy alphaTy]),
       ("Drop", [natTy ** listTy alphaTy --> listTy alphaTy]),
       ("Update", [alphaTy ** natTy ** listTy alphaTy --> listTy alphaTy]),
       ("Element", [natTy ** listTy alphaTy --> alphaTy]),
       ("IndexOf", [eqAlphaTy ** listTy eqAlphaTy --> optionTy natTy]),
       ("IsMember", [eqAlphaTy ** listTy eqAlphaTy --> boolTy]),
       ("Remove", [listTy eqAlphaTy ** listTy eqAlphaTy --> listTy eqAlphaTy]),
       ("RemoveExcept",
          [listTy eqAlphaTy ** listTy eqAlphaTy --> listTy eqAlphaTy]),
       ("RemoveDuplicates", [listTy eqAlphaTy --> listTy eqAlphaTy]),
       ("ZeroExtend", [wordTy "a" --> wordTy "b"]),
       ("SignExtend", [wordTy "a" --> wordTy "b"]),
       ("Size", [wordTy "a" --> natTy]),
       ("Log2", [wordTy "a" --> wordTy "a",
                 natTy --> natTy]),
       ("^", [wordTy "a" ** natTy --> wordTy "b",
              bitstringTy ** natTy --> bitstringTy]),
       ("**", natBinOpTy @ [intTy ** natTy --> intTy]),
       ("<<", shiftOpTy),
       (">>", [wordTy "a" ** natTy --> wordTy "a"] @ wordBinOpTy),
       (">>+", shiftOpTy),
       ("#>>", shiftOpTy),
       ("#<<", [wordTy "a" ** natTy --> wordTy "a"] @ wordBinOpTy),
       (":", [wordTy "a" ** wordTy "b" --> wordTy "c",
              listTy alphaTy ** listTy alphaTy --> listTy alphaTy]),
       ("PadLeft", [alphaTy ** natTy ** listTy alphaTy --> listTy alphaTy]),
       ("PadRight", [alphaTy ** natTy ** listTy alphaTy --> listTy alphaTy]),
       ("Concat", [listTy (listTy alphaTy) --> listTy alphaTy]),
       ("ToLower", [Type.stringTy --> Type.stringTy]),
       ("ToUpper", [Type.stringTy --> Type.stringTy]),
       ("FromBinString", [Type.stringTy --> Type.optionTy Type.natTy]),
       ("FromDecString", [Type.stringTy --> Type.optionTy Type.natTy]),
       ("FromHexString", [Type.stringTy --> Type.optionTy Type.natTy]),
       ("IsAlpha", [Type.charTy --> Type.boolTy]),
       ("IsAlphaNum", [Type.charTy --> Type.boolTy]),
       ("IsDigit", [Type.charTy --> Type.boolTy]),
       ("IsHexDigit", [Type.charTy --> Type.boolTy]),
       ("IsLower", [Type.charTy --> Type.boolTy]),
       ("IsSpace", [Type.charTy --> Type.boolTy]),
       ("IsUpper", [Type.charTy --> Type.boolTy]),
       ("FP32_Abs", [float32Ty --> float32Ty]),
       ("FP32_Add", [roundingTy ** float32Ty ** float32Ty --> float32Ty]),
       ("FP32_Equal", [float32Ty ** float32Ty --> Type.boolTy]),
       ("FP32_IsNaN", [float32Ty --> Type.boolTy]),
       ("FP32_LessThan", [float32Ty ** float32Ty --> Type.boolTy]),
       ("FP32_Mul", [roundingTy ** float32Ty ** float32Ty --> float32Ty]),
       ("FP32_Neg", [float32Ty --> float32Ty]),
       ("FP32_Sub", [roundingTy ** float32Ty ** float32Ty --> float32Ty]),
       ("FP64_Abs", [float64Ty --> float64Ty]),
       ("FP64_Add", [roundingTy ** float64Ty ** float64Ty --> float64Ty]),
       ("FP64_Equal", [float64Ty ** float64Ty --> Type.boolTy]),
       ("FP64_IsNaN", [float64Ty --> Type.boolTy]),
       ("FP64_LessThan", [float64Ty ** float64Ty --> Type.boolTy]),
       ("FP64_Mul", [roundingTy ** float64Ty ** float64Ty --> float64Ty]),
       ("FP64_Neg", [float64Ty --> float64Ty]),
       ("FP64_Sub", [roundingTy ** float64Ty ** float64Ty --> float64Ty])
      ] @ [ValOf, IsSome, Head, Tail, Length, SetOfList, InitMap]
      (* special (hidden) functions:
         splitl, splitr:
            (charTy --> boolTy) ** stringTy --> stringTy ** stringTy
         fields, tokens: (charTy --> boolTy) ** stringTy --> listTy stringTy
         update-map : (a -> b) * a * b -> (a -> b)
         bit-field-insert : nat * nat * word a * word b -> word a
         <..> : nat * nat * word a -> word b
         bit-modify : (nat * bool -> bool) * word a -> word a
         i-t-e : bool * a * a -> a
         ; : unit * a -> a
         for : nat * nat * (nat -> unit)
         foreach : a * listTy a * ('a -> unit)
         abs-apply : (a -> b) * a -> b
         Run : instructionTy -> unitTy
      *)

   (*
   val primExceptions =
      [(Tag.mkException "ASSERT", Exception (SOME stringTy))]
   val initialConsts = primConstructors @ primOps @ primExceptions
   *)

   val initialConsts = primConstructors @ primOps
   val primList = List.map fst initialConsts
   val primConstrSet =
      Stringset.fromList (List.take (primList, List.length primConstructors))
   val initialConsts = Stringmap.fromList initialConsts
   val emptyConsts = Stringmap.empty: const Stringmap.dict

   val consts = ref initialConsts
   val save_consts = ref (!consts)
   val defn = ref 1
   val save_defn = ref (!defn)

   fun resetConsts () = (consts := initialConsts; defn := 1)
   fun saveConsts () = (save_consts := !consts; save_defn := !defn)
   fun restoreConsts () = (consts := !save_consts; defn := !save_defn)

   fun listConsts () =
      Stringmap.listItems (Stringmap.removeList (!consts, primList))

   fun pickDestructor ty (Destructor l) =
      let
         val eq = Types.equalTy ty o Term.primTypeOf
      in
         case List.find (fn (rd, _, _, _) => eq rd) l of
           SOME (rd, _, _, _) => SOME rd
         | NONE =>
             (case List.find (fn (_, wr, _, _) => eq wr) l of
                SOME (_, wr, _, _) => SOME wr
              | NONE => NONE)
      end
     | pickDestructor _ _ = raise Fail "pickDestructor"

   local
      fun nameRegDestructor (s, ty: Type.ty) =
         case (s, ty) of
           ("&", (Type.ConstType s2, _)) => "reg'" ^ s2
         | _ => "rec'" ^ s

      fun isRec s tm =
         case Lib.total Types.domainRange (Term.primTypeOf tm) of
           SOME (ty1, ty2) =>
             Term.findTerm
                  (fn Term.Comb (f, ty3, [a]) =>
                        f = s andalso Types.equalTy ty2 ty3 andalso
                        Types.equalTy ty1 (Term.primTypeOf a)
                    | _ => false) tm |> Option.isSome
         | NONE =>
             let
                val ty1 = Term.primTypeOf tm
             in
                Term.findTerm
                  (fn Term.Comb (f, ty2, []) =>
                        f = s andalso Types.equalTy ty1 ty2
                    | _ => false) tm |> Option.isSome
             end

      fun usrDefn n s d m =
         {user = true, recursive = isRec s d, def = d, measure = m,
          name = if Tag.isAST n then "dfn'" ^ Tag.remove n else n}: defn

      fun sys n d = {user = false,
                     measure = NONE,
                     name = n,
                     def = d,
                     recursive = false}: defn

      val destDefn =
         fn (s as "raise'exception", Definition (d, _, _)) =>
              [(~1, {user = true, measure = NONE, recursive = false, def = d,
                     name = s})]
          | (s, Definition (d, m, i)) =>
              if i < 0 then [] else [(i, usrDefn s s d m)]
          | (s, Accessor (rd, wr, i)) =>
              [(i, usrDefn s s rd NONE),
               (i + 1, usrDefn ("write'" ^ s) s wr NONE)]
          | (s, Destructor l) =>
              List.mapPartial
                (fn (rd, wr, register, i) =>
                   if register
                     then let
                             val ty = Type.dom (Term.typeOf rd)
                             val n = nameRegDestructor (s, ty)
                             val (i, j) =
                                if s = "&" then (i - 1, i + 1) else (i, i + 2)
                          in
                             SOME [(i, sys n rd), (j, sys ("write'" ^ n) wr)]
                          end
                   else NONE) l |> List.concat
          | _ => []
   in
      fun listDefinitions () =
         Stringmap.listItems (!consts)
           |> List.map destDefn
           |> List.concat
           |> msort (Int.compare o (fst ## fst))
           |> List.map snd
   end

   local
      val destExcept =
         fn (s, Exception oty) => SOME (Tag.remove s, oty)
          | _ => NONE
   in
      fun listExceptions () =
         List.mapPartial destExcept (Stringmap.listItems (!consts))
   end

   fun stats () =
      let
         val p = ref 0
         val d = ref 0
         val c = ref 0
         val a = ref 0
         val e = ref 0
         val d1 = ref 0
         val d2 = ref 0
         val u = ref 0
         fun get (s, y) =
            case y of
               Primitive _ => p
             | Destructor _ => d
             | Constructor _ =>
                 if Stringset.member (primConstrSet, s) then p else c
             | Accessor _ => a
             | Exception _ => e
             | Definition (_, _, i) =>
                 if i < 0 then p else if Tag.isAST s then d1 else d2
             | Undefined => u
         val () = List.app (inc o get) (Stringmap.listItems (!consts))
         fun pn s x = Lib.printn (s ^ Int.toString (!x))
      in
          pn "Primitives .............. " p
        ; pn "Destructors.............. " d
        ; pn "Constructors............. " c
        ; pn "Accessors ............... " a
        ; pn "Exceptions............... " e
        ; pn "User operations.......... " d2
        ; pn "Instruction definitions.. " d1
        ; if (!u) = 0 then () else pn "Undefined operations..... " u
      end

   fun lookupConst s =
      case Stringmap.peek (!consts, s) of
        NONE => Undefined
      | SOME x => x

   val defined =
      fn Undefined => false
       | _ => true

   val isConst = defined o lookupConst
   fun delConst s = consts := fst (Stringmap.remove (!consts, s))

   fun runDefined () = isConst "Run"

   fun lookupConstructor s =
      case lookupConst s of
         Constructor ty => SOME ty
       | _ => NONE

   fun lookupConstant s =
      case lookupConst s of
         Constructor ty =>
            (case fst (Types.expand ty) of
               Type.Arrow _ => NONE
             | _ => SOME ty)
       | _ => NONE

   fun lookupDestructor s =
      case lookupConst s of
         Destructor l => List.map (fn (rd, wr, _, _) => (rd, wr)) l
       | _ => []

   fun lookupAccessor s =
      case lookupConst s of
         Accessor (rd, wr, _) => SOME (rd, wr)
       | _ => NONE

   fun lookupException s =
      case lookupConst s of
         Exception tyo => SOME tyo
       | _ => NONE

   fun lookupDefinition s =
      case lookupConst s of
         Definition (tm, m, _) => SOME (tm, m)
       | Accessor (tm, _, _) => SOME (tm, NONE)
       | _ => NONE

   fun lookupOperation s =
      case lookupConst s of
         Primitive l => SOME l
       | Accessor (tm, _, _) => SOME [Term.primTypeOf tm]
       | Definition (tm, _, _) => SOME [Term.primTypeOf tm]
       | Destructor l =>
            SOME (List.map (fn (tm, _, _, _) => Term.primTypeOf tm) l)
       | Constructor ty => SOME [ty]
       | Exception (SOME ty) => SOME [ty --> freshTyVar()]
       | _ => NONE

   local
      fun primAddConst (s, x) = consts := Stringmap.insert (!consts, s, x)
      fun dom (tm, _, _, _) = Types.domain (Term.primTypeOf tm)
      val nullI = nullIntersection (uncurry Types.equalTy)
      fun safeMerge f l1 l2 =
         let
            val m = List.map f
         in
            if nullI (m l1) (m l2) then l1 @ l2 else raise Fail "safeMerge"
         end
   in
      val allowExceptionOverload = ref false
      fun overloadErr s = raise Fail ("Bad overload: " ^ s)
      fun addConst (s, x) =
         ( !allowExceptionOverload orelse
           not (isConst (if Tag.isException s
                            then Tag.remove s
                         else Tag.mkException s)) orelse overloadErr s
         ; (case (lookupConst s, x) of
               (Primitive l, Primitive l') =>
                  primAddConst (s, Primitive (safeMerge Types.expand l' l))
             | (Destructor l, Destructor l') =>
                  primAddConst (s, Destructor (safeMerge dom l' l))
             | (Undefined, _) => primAddConst (s, x)
             | _ => overloadErr s)
           handle Fail "safeMerge" => overloadErr s
         )
   end

   fun addConstructor (s, ty) = addConst (s, Constructor ty)
   fun addDestructor (s, tm1, tm2, b) =
      (addConst (s, Destructor [(tm1, tm2, b, !defn)]); inc2 defn)
   fun addException (s, ty) = addConst (Tag.mkException s, Exception ty)
   fun addDefinition (s, tm, m) =
      (addConst (s, Definition (tm, m, !defn)); inc defn)
   fun addAccessor (s, tm1, tm2) =
      (addConst (s, Accessor (tm1, tm2, !defn - 1)); inc defn)
      (* we get !defn - 1 here because the "read" operation is temporarily
         added as a definition to allow the "write" part to use it. This is
         then deleted prior to calling addAccessor, however the defn count
         doesn't go down upon deletion. *)

   val isConstant = Option.isSome o lookupConstant
   val isConstructor = Option.isSome o lookupConstructor
   val isDestructor = not o List.null o lookupDestructor
   val isAccessor = Option.isSome o lookupAccessor
   val isException = Option.isSome o lookupException
   val isDefinition = Option.isSome o lookupDefinition

   local
      val enums = Types.Enum o Stringmap.fromList o Lib.addIndex
      val constructs = Types.Construct o Stringmap.fromList
   in
      fun buildDatatype ast env err (name, l) =
         let
            val (names, tys) = ListPair.unzip l
            val () = Env.checkFreeList env err (List.map fst l)
            val enum = not ast andalso List.all (not o Option.isSome) tys
            val def = Types.Constructors
                         (if enum then enums names else constructs l)
            val tys = List.mapPartial I tys
            val () = List.app (Type.checkConstraint Constrain.empty) tys
            val ty = Type.mkConstType name
            val isEq = List.all Types.isEqType tys
            fun add (c, NONE) = addConstructor (c, ty)
              | add (c, SOME typ) = addConstructor (c, typ --> ty)
         in
             Types.addConst (name, {eq = isEq, def = def, ast = ast})
           ; if enum then Types.updateCastTypes () else ()
           ; List.app add l
         end
   end

   local
      datatype ast = Node of string * ast list
                   | Leaf of string * Type.ty option
      val emptyAST = Node ("instruction", [])
      val ast = ref emptyAST
      val astEntry = fn Leaf (n, oty) => (n, oty)
                      | Node (n, _) => (n, SOME (Type.mkConstType n))
   in
      fun resetAST () = ast := emptyAST

      fun isEmptyAST () =
         case !ast of
           Node ("instruction", []) => true
         | _ => false

      fun augmentAST (path, c, oty) =
         let
            val () =
               case oty of
                 SOME ty => Type.checkConstraint c ty
               | _ => ignore (Constrain.isEmpty c orelse
                              raise Fail ("Redundant type constraint: " ^
                                          Constrain.toString c))
            val (name, fnt) = Lib.lastButlast path
            fun newAST [] =
                (case Constrain.toList c of
                   [] => [Leaf (name, oty)]
                 | [(v, s)] =>
                     let
                        val ty = Option.valOf oty
                     in
                        List.map (fn i =>
                          let
                             val t = Type.typeSubst [v |=> Type.FixedBits i] ty
                          in
                             Leaf (name ^ Tag.mkAST (Int.toString i), SOME t)
                          end) (PosIntSet.toList s)
                     end
                 | _ => raise Fail "AST: Only one constraint allowed")
              | newAST (h :: t) =
                 if isConst h orelse Types.isConst h
                    then raise Fail ("bad overload: " ^ h)
                 else [Node (h, newAST t)]
            fun ins (Leaf _) = raise Fail "augmentInstructionType"
              | ins (Node (n, l)) =
                (fn [] => Node (n, newAST [] @ l)
                  | p as h :: r =>
                     (case Lib.pluck (fn Node (s, _) => s = h | _ => false) l of
                        SOME (t, rst) => Node (n, ins t r :: rst)
                      | NONE => Node (n, newAST p @ l)))
         in
            ast := ins (!ast) fnt
         end

      fun defineAST () =
         let
            val mkDatatype =
               buildDatatype true (Env.get ())
                  (fn s => raise Fail ("Bad name when defining AST: " ^ s))
            fun build t =
               case t of
                 Leaf _ => ()
               | Node (n, l) =>
                   let
                      val () = List.app build l
                   in
                      mkDatatype (n, List.map astEntry l)
                   end
         in
            build (!ast); resetAST ()
         end
   end

   local
      val vnum = ref 0
      fun var ty = Term.Var ("v" ^ Int.toString (!vnum), ty) before Lib.inc vnum

      fun mkLitCase ty s =
         (Term.Lit (Term.Other (s, ty)),
          Term.Comb (Tag.mkDefine s, Type.unitTy, []))

      fun mkBaseCase ty (s, sty) =
         let
            val v = var sty
         in
            (Term.Comb (s, ty, [v]),
             Term.Comb (Tag.mkDefine s, Type.unitTy, [v]))
         end

      fun getAstDef ty =
         case Types.dest ty of
           Type.Other "" => raise Fail "getAstDef"
         | Type.Other s =>
             (case Types.lookupConst s of
                SOME {def = Types.Constructors (Types.Construct d),
                      ast = true, ...} =>
                  Stringmap.listItems d
              | _ => raise Fail "getAstDef")
         | _ => raise Fail "getAstDef"

      fun isAstType ty = (getAstDef ty; true) handle Fail _ => false
   in
      fun defineRun () =
         let
            val () = defineAST ()
            val () = vnum := 0
            val v = var Type.instructionTy
            fun mkNodeCase ty (s, sty) =
               let
                  val v = var sty
               in
                  (Term.Comb (s, ty, [v]), build (v, sty))
               end
            and build (v, ty) =
               let
                  val d = getAstDef ty
                  val (l, r) = List.partition (Option.isSome o snd) d
                  val (t, l) = List.partition (isAstType o Option.valOf o snd) l
                  val t = List.map (mkNodeCase ty o (I ## Option.valOf)) t
                  val l = List.map (mkBaseCase ty o (I ## Option.valOf)) l
                  val r = List.map (mkLitCase ty o fst) r
               in
                  Term.mkMatch (v, r @ l @ t)
               end
            val def = Term.mkAbs (v, build (v, Type.instructionTy))
         in
            addDefinition ("Run", def, NONE)
         end
   end

   val buildDatatype = buildDatatype false

end (* structure Consts *)

(* -------------------------------------------------------------------------
   Pattern Variables

   Type hints (to avoid explicit annotation) for pattern matching variables
   ------------------------------------------------------------------------- *)

signature Patterns =
sig
   val addPatternList: (string * Type.ty) list -> unit
   val isPattern: string -> bool
   val listPatterns: unit -> (string * Type.ty) list
   val lookupPattern: string -> Type.ty option
   val removePatternList: string list -> unit
   val resetPatterns: unit -> unit
   val restorePatterns: unit -> unit
   val savePatterns: unit -> unit
end

structure Patterns :> Patterns =
struct
   val pats = ref (Stringmap.empty: Type.ty Stringmap.dict)
   val save_pats = ref (!pats)
   fun resetPatterns () = pats := Stringmap.empty
   fun lookupPattern v = Stringmap.peek (!pats, v)
   fun listPatterns () = Stringmap.listItems (!pats)
   val isPattern = Option.isSome o lookupPattern
   fun addPatternList l = pats := Stringmap.insertList (!pats, l)
   fun removePatternList l = pats := Stringmap.removeList (!pats, l)
   fun savePatterns () = save_pats := !pats
   fun restorePatterns () = pats := !save_pats
end (* structure Patterns *)
