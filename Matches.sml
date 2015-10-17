use "Parser.sml";

(* ------------------------------------------------------------------------
   Transformations to matches: explode bit-patterns and strings
   ------------------------------------------------------------------------ *)

signature Matches =
sig
   val boolifyMatches: Term.term -> Term.term
   val bpFree: Term.term -> Term.term
   val convertMatch:
      (Type.ty -> bool) ->
      (Term.term -> bool) ->
      (Term.term -> Term.term * (string * Term.term) list) ->
      (Term.term -> Term.term) -> Term.term -> Term.term
   val pureMatch: Term.term -> Term.term -> Term.term Stringmap.dict
   val smartMkMatch: Term.term * (Term.term * Term.term) list -> Term.term
   val stringExplodeMatches: Term.term -> Term.term
end

structure Matches =
struct

fun var i v ty = Term.Var (v ^ Int.toString (!i), ty) before Lib.inc i
val vnum = ref 0
val newVar = var vnum "v#"

fun genTuple genvar =
   let
      fun tuple ty =
         let
            val (t1, t2) = Type.fstsnd ty
         in
            Term.mkPair (tuple t1, tuple t2)
         end
         handle Fail "fstsnd" => genvar ty
   in
      fn ty => tuple (Types.expand ty)
   end

val newTupleVar = genTuple newVar

local
   val tnum = ref 0
   val tvar = var tnum "t#"
in
   fun tupleTemplate ty = (tnum := 0; genTuple tvar ty)
end

fun pureMatch a b =
   case Term.match a b of (m, []) => m | _ => raise Term.TermMatch

(* Attempt to build constructor patterns from a list of cases *)
local
   fun getConstructor tm =
      case tm of
         Term.Lit Term.Unit => SOME (tm, NONE)
       | Term.Lit (Term.Bitstring _) =>
            getConstructor (Term.expandBitstringLit tm)
       | Term.Lit (Term.String _) =>
            getConstructor (Term.expandStringLit tm)
       | Term.Lit (Term.Bool _) => SOME (tm, NONE)
       | Term.Lit (Term.Enum _) => SOME (tm, NONE)
       | Term.Lit (Term.Other (f, ty)) =>
           (case Consts.lookupConst f of
              Consts.Constructor _ => SOME (tm, NONE)
            | _ => NONE)
       | Term.Comb ("Cons", ty, [a]) =>
            let
               val d = Term.typeOf a
               val (d1, d2) = Types.destProd d
               val v = Term.mkPair (newVar d1, newVar d2)
            in
               SOME (Term.Comb ("Cons", ty, [v]), SOME d)
            end
       | Term.Comb (f, ty, [a]) =>
           (case Consts.lookupConst f of
              Consts.Constructor fty =>
                 let
                    val d = Term.typeOf a
                 in
                    SOME (Term.Comb (f, ty, [newVar d]), SOME d)
                 end
            | _ => NONE)
       | _ => NONE
in
   fun getConstructors l =
      let
         fun iter a =
            fn [] => List.rev a
             | h :: t =>
                 (case getConstructor h of
                    SOME (x as (c, _)) =>
                      iter (x :: a) (List.filter (not o Term.canMatch c) t)
                  | NONE => iter a t)
         val cl = iter [] l
      in
         if List.all (not o Option.isSome o snd) cl
            then []
         else cl
      end
end

val numberOfConstructors = Stringmap.numItems o Types.constructors

fun allConstructors ty =
   let
      val d = Stringmap.listItems (Types.constructors ty)
   in
      List.map
         (fn (c, oty) =>
             ( case oty of
                  SOME ty0 => Term.Comb (c, ty, [newTupleVar ty0])
                | NONE => Term.Lit (Term.Other (c, ty))
             , oty)) d
   end

fun splitByConstructors (cs : (Term.term * Term.term) list) =
   List.map (fn (p, oty) =>
     (p, List.mapPartial
            (fn (c, b) =>
                case oty of
                  SOME ty =>
                     (if Term.canMatch p c
                         then SOME (snd (Term.destApp c), b)
                      else case Lib.total Term.destVar c of
                             SOME ("_", _) => SOME (Term.anon ty, b)
                           | SOME (v, ty2) =>
                               let
                                  val v2 = newVar ty
                                  val f = fst (Term.destApp p)
                                  val e = Term.Comb (f, ty2, [v2])
                               in
                                  SOME (v2, Term.inst1 (v, e) b)
                               end
                           | NONE => NONE)
                | NONE =>
                     (case Lib.total Term.destVar c of
                         SOME ("_", _) => SOME (p, b)
                       | SOME (v, _) => SOME (p, Term.inst1 (v, p) b)
                       | NONE =>
                          if Term.equalTm p c then SOME (p, b) else NONE)) cs))

local
   fun smartMkLet ((v, e), b) =
      let
         val ty = Term.primTypeOf e
      in
         if Term.isVar e orelse Term.isLit e orelse
            not (Term.multipleOccs (v, ty) b)
            then Term.inst1 (v, e) b
         else Term.mkLet (Term.Var (v, ty), e, b)
      end
in
   val listMkLet = List.foldl smartMkLet
end

fun isAllVars tm =
   case tm of
     Term.Var _ => true
   | Term.Comb (",", _, l) => List.all isAllVars l
   | _ => false

local
   fun performMatch p m =
      let
         val s = pureMatch p m
      in
         if List.all (Term.isVar o snd) (Stringmap.listItems s)
            then SOME s
         else NONE
      end
      handle Term.TermMatch => NONE
   val universal =
      not o Option.isSome o
      Term.findTerm
        (fn Term.Var _ => false
          | Term.Comb (":", _, _) => false
          | Term.Comb (",", _, _) => false
          | _ => true)
in
   fun smartMkMatch (x as (m, [(p, b)])) =
      if isAllVars p
         then case performMatch p m of
                 SOME s => Term.inst s b
               | NONE =>
                 let
                    val freevars = List.map Term.Var (Term.freeVars b)
                    val patvars = List.map Term.Var (Term.freeVars p)
                    fun infreevars q = List.exists (Term.equalTm q) freevars
                 in
                    if List.exists infreevars patvars
                       then Term.mkMatch x
                    else b
                 end
      else Term.mkMatch x
     | smartMkMatch (m, cs) =
      case Lib.takeUntil (universal o fst) cs of
         l as [_] => smartMkMatch (m, l)
       | l => Term.mkMatch (m, l)
end

fun varCase (cs : (Term.term * Term.term) list) =
   case List.filter (Term.isVar o fst) cs of
      [] => []
    | [(c, b)] => [(c, b)]
    | _ => raise Fail "varCase"

fun splitPair tm = Term.destPair tm
   handle Fail "destPair" => (Term.mkFst tm, Term.mkSnd tm)

fun splitPatternPair (p, b) = (Term.destPair p, b)
   handle Fail "destPair" =>
     let
        val (t1, t2) = Types.destProd (Term.primTypeOf p)
        val vs = (newVar t1, newVar t2)
        val s = pureMatch p (Term.mkPair vs)
     in
        (vs, Term.inst s b)
     end

fun pack ((p1 : Term.term, p2), b) = (p1, Term.mkPair (p2, b))

fun unpack (p1, tm) =
   let
      val (p2, p3) = Term.destPair tm
   in
      (Term.mkPair (p1, p2), p3)
   end

(* Expand tuples *)
fun tuplePattern tm =
   case tm of
      Term.Var (v, ty) =>
        (let
            val f = if v = "_" then Term.anon else newVar
            val (ty1, ty2) = Types.destProd ty
         in
            Term.mkPair (tuplePattern (f ty1), tuplePattern (f ty2))
         end
         handle Fail "destProd" => tm)
    | Term.Comb (",", ty, [a, b]) =>
         Term.Comb (",", ty, [tuplePattern a, tuplePattern b])
    | _ => tm

(* Replace bit-patterns and literals with anonymous vars *)
fun bpFree tm =
   case tm of
      Term.Lit _ => Term.anon (Term.primTypeOf tm)
    | Term.Comb (":", ty, [_, _]) => Term.anon ty
    | Term.Comb (f, ty, l) => Term.Comb (f, ty, List.map bpFree l)
    | _ => tm

val arity = List.length o Term.destTuple

fun convertMatch is_convert_type problematic pfn mk =
   let
      fun hasUnsafeConstructor tm =
         case tm of
            Term.Comb (_, ty, [a]) =>
               not (is_convert_type ty) andalso problematic a
          | Term.Comb (_, _, l) => List.exists hasUnsafeConstructor l
          | _ => false
      fun matchWithT t (p, b) =
         let
            val tp = tuplePattern p
            val s0 = pureMatch (bpFree p) tp
            val s = pureMatch t tp
            val () = ignore (not (Stringmap.exists hasUnsafeConstructor s)
                             orelse raise Fail "hasUnsafeConstructor")
         in
            (s, listMkLet b (Stringmap.listItems s0))
         end
      fun matchWithTemplate (t, cs : (Term.term * Term.term) list) =
         let
            val save = !vnum
         in
            List.map (matchWithT t) cs
            handle Fail "hasUnsafeConstructor" =>
              (vnum := save; raise Fail "hasUnsafeConstructor")
         end
      fun hasProblematic v =
         List.exists
            (fn s =>
               case Stringmap.peek (s, v) of
                 SOME tm => problematic tm
               | _ => false)
      fun fixTupleCase t bset (d, b) =
         let
            val letlist = ref ([] : (string * Term.term) list)
            fun addlets x = letlist := x @ !letlist
            fun iter tm =
               case tm of
                 Term.Var (v, vty) =>
                    let
                       val x = Stringmap.find (d, v)
                    in
                       if Stringset.member (bset, v) then
                          let
                             val (p', ls) = pfn x
                             val () = addlets ls
                          in
                             p'
                          end
                       else x
                    end
               | Term.Comb (",", ty, [a, b]) => Term.mkPair (iter a, iter b)
               | _ => raise Fail "bad template"
         in
            (iter t, listMkLet b (!letlist))
         end
      fun fixTupleCases t (m, cs) =
         let
            val s = pureMatch t m
            val lcs = matchWithTemplate (t, cs)
            val l = List.map fst lcs
            val tofix = ref Stringset.empty
            fun addfix v = tofix := Stringset.add (!tofix, v)
            fun iter tm =
               case tm of
                 Term.Var (v, vty) =>
                    let
                       val x = Stringmap.find (s, v)
                    in
                       if is_convert_type vty andalso hasProblematic v l
                          then (addfix v; mk x)
                       else x
                    end
               | Term.Comb (",", _, [a, b]) => Term.mkPair (iter a, iter b)
               | _ => raise Fail "bad template"
            val mtch = iter t
            val ccs = List.map (fixTupleCase t (!tofix)) lcs
         in
            smartMkMatch (mtch, ccs)
         end
      fun convPairCase (m, cs) =
         let
            val (m1, m2) = splitPair m
            val pcs = List.map splitPatternPair cs
            val ps = List.map (fst o fst) pcs
            val ty = Term.typeOf m1
         in
            if not (is_convert_type ty) andalso List.exists problematic ps
               then if Type.isProdTy ty
                       then let
                               val epcs = List.map (fn ((p1, p2), b) =>
                                            let
                                               val ((p1a, p1b), pb) =
                                                  splitPatternPair (p1, b)
                                            in
                                               (Term.mkTuple [p1a, p1b, p2], pb)
                                            end) pcs
                               val (m1a, m1b) = splitPair m1
                            in
                               convPairCase (Term.mkTuple [m1a, m1b, m2], epcs)
                            end
                    else let (* must be Unsafe constructor *)
                            val cs2 = List.map pack pcs
                            val ccs =
                               splitByConstructors cs2 (allConstructors ty)
                            fun iter (p, tms) =
                               let
                                  val (m3, f) =
                                     case Lib.total Term.destApp p of
                                       SOME (_, v) =>
                                          (Term.mkPair (v, m2), unpack)
                                     | NONE => (m2, Term.destPair o snd)
                               in
                                  (p, convert (m3, List.map f tms))
                               end
                         in
                            smartMkMatch (m1, List.map iter ccs)
                         end
            else convPairCase
                   (Term.mkPair (m2, m1),
                    List.map
                      (fn ((p1, p2), b) => (Term.mkPair (p2, p1), b)) pcs)
         end
      and convert (m, cs) =
         if List.exists (problematic o fst) cs
            then let
                    val ty = Term.typeOf m
                    val l = getConstructors (List.map fst cs)
                 in
                    if List.null l orelse is_convert_type ty
                       then let
                               val t = tupleTemplate ty
                               (* possibly introduce a "let" to avoid
                                  repeat evaluation *)
                               val (m', f) =
                                  if arity m = arity t orelse isAllVars m
                                     then (m, Lib.I)
                                  else let
                                          val mt = newTupleVar ty
                                       in
                                          (mt, fn tm => Term.mkLet (mt, m, tm))
                                       end
                            in
                               f (fixTupleCases t (m', cs)
                                  handle Fail "hasUnsafeConstructor" =>
                                      convPairCase (m', cs))
                            end
                    else let
                            val ty = Term.typeOf m
                            fun cnv (p, c) =
                               (p, case Lib.total Term.destApp p of
                                     SOME (_, v) => convert (v, c)
                                   | NONE => snd (hd c))
                            val ccs = List.map cnv (splitByConstructors cs l)
                            val vcs = if numberOfConstructors ty = List.length l
                                         then []
                                      else varCase cs
                         in
                            smartMkMatch (m, ccs @ vcs)
                         end
                 end
         else smartMkMatch (m, cs)
      fun depthConvert tm =
         let
            val (m, cs) = Term.destMatch tm handle Fail _ => raise Term.NoConv
            val cs' =
               List.map (fn (p, b) => (p, Term.topconv depthConvert b)) cs
         in
            convert (m, cs')
         end
   in
      fn tm => (vnum := 0; Term.topconv depthConvert tm)
   end

(* - transformation of bit-patterns -------------------------------------- *)

fun hasBitPattern tm =
   case tm of
      Term.Comb (":", _, [_, _]) => true
    | Term.Comb (_, _, l) => List.exists hasBitPattern l
    | _ => false

(* Convert bit-pattern into Boolean pattern - variables get added to let
   expressions *)

local
   fun var v i = Term.Var (v ^ "'" ^ Int.toString i, Type.boolTy)
   fun boolify1 tm =
      case tm of
         Term.Var (v, ty) =>
           (case Type.bitsSize (Types.expand ty) of
               SOME n =>
                  if v = "_"
                     then (List.tabulate
                             (n, fn _ => Term.Var ("_", Type.boolTy)), [])
                  else let
                          val vs = List.rev (List.tabulate (n, var v))
                          val l = Term.mkList (Lib.I, Type.bitstringTy) vs
                       in
                          (vs, [(v, Term.Comb ("[..]", ty, [l]))])
                       end
             | NONE => ( printn (PolyML.makestring tm)
                       ; raise Fail "boolify: not bits var")
                       )
       | Term.Lit (Term.Bits n) =>
           (List.map Term.mkBoolLit (BitsN.toList n), [])
       | Term.Comb (":", _, [x, y]) =>
           let
              val (a, b) = boolify1 x
              val (c, d) = boolify1 y
           in
              (a @ c, b @ d)
           end
       | _ => (printn (PolyML.makestring tm); raise Fail "boolify")
in
   fun boolify tm =
      let
         val (l1, l2) = boolify1 tm
      in
         (Term.mkTuple l1, l2)
      end
end

fun mkBoolify tm =
   let
      val i = Option.valOf (Type.bitsSize (Term.typeOf tm))
      val bty = Type.foldProdList (List.tabulate (i, K Type.boolTy))
   in
      Term.Comb ("boolify'" ^ Int.toString i, bty, [tm])
   end

val boolifyMatches =
   convertMatch Types.isFixedBitsType hasBitPattern boolify mkBoolify

(* - transformation of string patterns ------------------------------------- *)

fun hasStringCons tm =
   case tm of
      Term.Comb ("Cons", ty, [a]) =>
         Types.equalTy Type.stringTy ty orelse hasStringCons a
    | Term.Comb (_, _, l) => List.exists hasStringCons l
    | _ => false

fun mkExplode tm = Term.Comb ("String.explode", Type.stringTy, [tm])

val isStringTy = Types.equalTy Type.stringTy

fun mkImplode tm =
   case tm of
      Term.Lit (Term.String s) => (Term.expandStringLit tm, [])
    | Term.Lit _ => (tm, [])
    | Term.Var (v, ty) =>
        (tm,
         if isStringTy ty
            then [(v, Term.Comb ("String.implode", ty, [tm]))]
         else [])
    | Term.Comb ("Cons", ty1, [Term.Comb (",", ty2, [h, t])]) =>
         let
            val (t', l) = mkImplode t
         in
            (Term.Comb ("Cons", ty1, [Term.Comb (",", ty2, [h, t'])]), l)
         end
    | _ => raise Fail "mkImplode"

val stringExplodeMatches =
   convertMatch isStringTy hasStringCons mkImplode mkExplode

end (* structure Matches *)
