use "Matches.sml";

(* ------------------------------------------------------------------------
   Replace exceptions with calls to a "raise" function that tags the state
   ------------------------------------------------------------------------ *)

signature Exception =
sig
   val exceptionTy : Type.ty
   val buildExceptionDatatype : unit -> unit
   val removeExceptionCalls : Term.term -> Term.term
end

structure Exception :> Exception =
struct
   val raisefn = "raise'exception"
   val exceptionTy = Type.mkConstType "exception"
   val exceptionVar = Term.Var ("exception", exceptionTy)
   fun exceptionLit s = Term.Lit (Term.Other (s, exceptionTy))
   val NoExceptionTm = exceptionLit "NoException"

   fun defineRaise () =
      let
         val e = Term.Var ("e", exceptionTy)
         val def =
            Term.mkAbs (e,
               Term.Comb (";", Type.alphaTy,
                 [Term.mkIfThen
                    (Term.mkBoolOp "==" (exceptionVar, NoExceptionTm),
                     Term.Comb ("<-", Type.unitTy, [exceptionVar, e]),
                     Term.unitTm), Term.unknown Type.alphaTy]))
      in
         Consts.addDefinition (raisefn, def, NONE)
      end

   fun buildExceptionDatatype () =
      if not (Option.isSome (Types.lookupConst "exception"))
         then let
                 val l = Consts.listExceptions ()
              in
                 if List.null l
                    then (if Consts.isConst raisefn
                             then Consts.delConst raisefn
                          else ()
                          ; Lib.warn "There are no exceptions")
                 else (if Consts.isConst raisefn then () else defineRaise ()
                       ; Consts.allowExceptionOverload := true
                       ; Parser.buildDatatype
                           ("exception", ("NoException", NONE) :: l)
                       ; Consts.allowExceptionOverload := false
                       ; Parser.addVar ("exception", exceptionTy)
                       ; Runtime.reset ())
              end
      else printn "Exception datatype already defined"

   fun mkCall ty c = Term.Comb (raisefn, ty, [c])

   local
      open Term
      fun removeExceptionCall tm =
         case tm of
            Comb (f, ty, []) =>
             if Tag.isException f
                then mkCall ty (exceptionLit (Tag.remove f))
             else raise NoConv
          | Comb (f, ty, [a]) =>
             if Tag.isException f
                then mkCall ty (Comb (Tag.remove f, exceptionTy,
                                      [topconv removeExceptionCall a]))
             else raise NoConv
          | _ => raise NoConv
   in
      val removeExceptionCalls = topconv removeExceptionCall
   end
end (* structure Exception *)

(* ------------------------------------------------------------------------
   Helper operations for building up a monadic version of an L3 specification
   ------------------------------------------------------------------------ *)

signature Monad =
sig
   val addFunctional : string * Type.ty -> unit
   val addMonadic : string * Type.ty -> unit
   val addPure : string * Type.ty -> unit
   val conversions :
      unit -> { bindConv : Term.term -> Term.term -> Term.term,
                readConv : Term.term -> Term.term -> Term.term,
                constConv : Term.term -> Term.term -> Term.term,
                writeConv : Term.term -> Term.term -> Term.term,
                extendConv : Term.term -> Term.term -> Term.term,
                unextendConv : Term.term -> Term.term -> Term.term }
   val destConst : Term.term -> Term.term
   val destMonadTy : Type.ty -> Type.ty * Type.ty
   val get : unit -> (Term.term * Term.term) Stringmap.dict * string
   val init : unit -> (Term.term * Term.term) Stringmap.dict * string
   val isFunctional : string * Type.ty -> bool
   val isMonadTy : Type.ty -> Type.ty -> bool
   val isMonadic : string * Type.ty -> bool
   val isPure : string * Type.ty -> bool
   val listFunctional : unit -> (string * Type.ty list) list
   val listMonadic : unit -> (string * Type.ty list) list
   val listPure : unit -> (string * Type.ty list) list
   val mkBind : Term.term * Term.term -> Term.term
   val mkBop :
      (Term.term * Term.term -> Term.term) * Term.term * Term.term -> Term.term
   val mkConj : Term.term * Term.term -> Term.term
   val mkConst : Type.ty -> Term.term -> Term.term
   val mkDisj : Term.term * Term.term -> Term.term
   val mkExtend : Term.term * Term.term -> Term.term
   val mkFiniteSet : Term.term list -> Term.term
   val mkForLoop : Term.term * Term.term * Term.term -> Term.term
   val mkForeachLoop : Term.term * Term.term -> Term.term
   val mkIfThenElse : Term.term * Term.term * Term.term -> Term.term
   val mkLetExpression : Term.term * Term.term * Term.term -> Term.term
   val mkMatchStatement : Term.term * (Term.term * Term.term) list -> Term.term
   val mkQop :
      (Term.term * Term.term * Term.term * Term.term -> Term.term) *
       Term.term * Term.term * Term.term * Term.term -> Term.term
   val mkRead : Term.term -> Term.term
   val mkTop :
      (Term.term * Term.term * Term.term -> Term.term) *
       Term.term * Term.term * Term.term -> Term.term
   val mkUnextend : Term.term * Type.ty -> Term.term
   val mkUop : (Term.term -> Term.term) * Term.term -> Term.term
   val mkWrite : Term.term * Term.term -> Term.term
   val monadTy : Type.ty -> Type.ty -> Type.ty
   val primMkExtend : Term.term * Term.term -> Term.term
   val primMkFor : Term.term * Term.term * Term.term -> Term.term
   val primMkForeach : Term.term * Term.term -> Term.term
   val primMkWrite : Term.term -> Term.term
   val removeFunctional : string * Type.ty -> unit
   val reset : unit -> unit
   val state : unit -> string
   val stateName : string -> unit
   val stateOf : Term.term -> Type.ty
   val stateTy : Type.ty
   val valueOf : Term.term -> Type.ty
end

structure Monad :> Monad =
struct
   val op |-> = Type.|->

   val const = "m'const"
   val bind = "m'bind"
   val for = "m'for"
   val foreach = "m'foreach"
   val read = "m'read"
   val write = "m'write"
   val extend = "m'extend"
   val unextend = "m'unextend"

   val gammaTy = Type.mkVarType "c"
   val stateTy = Type.mkVarType "state"
   fun monadTy stateTy ty = stateTy --> (ty ** stateTy)

   fun destMonadTy ty =
      let
         val (ty1, ty2) = Types.domainRange ty
         val ty2 as (_, ty3) = Types.destProd ty2
         val () = ignore (Types.equalTy ty1 ty3 orelse raise Fail "")
      in
         ty2
      end
      handle Fail _ => raise Fail "destMonadTy"

   fun isMonadTy sty ty = Types.equalTy sty (snd (destMonadTy ty))
                          handle Fail _ => false

   local
      open Term
   in
      fun mkITE (b, x, y) =
         case (x, y) of
           (Lit (Bool false), Lit (Bool false)) => mkBoolLit false
         | (Lit (Bool false), Lit (Bool true))  => mkNot b
         | (Lit (Bool true), Lit (Bool false)) => b
         | (Lit (Bool true), Lit (Bool true)) => mkBoolLit true
         | (Lit (Bool false), _) => mkBoolOp "and" (mkNot b, y)
         | (Lit (Bool true), _)  => mkBoolOp "or" (b, y)
         | (_, Lit (Bool false)) => mkBoolOp "and" (b, x)
         | (_, Lit (Bool true))  => mkBoolOp "or" (mkNot b, x)
         | _ => mkIfThen (b, x, y)
   end

   fun destUop f s tm =
      let
         fun err () = raise Fail ("dest" ^ s)
      in
         case tm of
           Term.Comb (g, _, [x]) => if g = f then x else err ()
         | _ => err ()
      end

   fun destBop f s tm =
      let
         fun err () = raise Fail ("dest" ^ s)
      in
         case tm of
           Term.Comb (g, ty, [x]) =>
              if g = f
                 then Term.destPair x handle Fail _ => err ()
              else err ()
         | _ => err ()
      end

   fun defineConst () =
      let
         val c = ("c", Type.alphaTy)
         val v = Term.Var c
         val s = Term.Var ("s", stateTy)
         val def = Term.absList [c] (Term.mkAbs (s, Term.mkPair (v, s)))
      in
         Consts.addDefinition (const, def, NONE)
      end

   fun defineBind () =
      let
         val v = Term.Var ("v", Type.alphaTy)
         val f = ("f", monadTy stateTy Type.alphaTy)
         val g = ("g", Type.alphaTy --> monadTy stateTy Type.betaTy)
         val s = Term.Var ("s", stateTy)
         val def =
            Term.absList [f, g]
              (Term.mkAbs (s,
                 Term.mkLet
                    (Term.mkPair (v, s),
                     Term.mkApply (Term.Var f, s),
                     Term.mkApply (Term.mkApply (Term.Var g, v), s))))
      in
         Consts.addDefinition (bind, def, NONE)
      end

   fun defineRead () =
      let
         val f = Term.Var ("f", stateTy --> Type.alphaTy)
         val s = Term.Var ("s", stateTy)
         val def = Term.mkAbs (f,
                      Term.mkAbs (s, Term.mkPair (Term.mkApply (f, s), s)))
      in
         Consts.addDefinition (read, def, NONE)
      end

   fun defineWrite () =
      let
         val f = Term.Var ("f", stateTy --> stateTy)
         val s = Term.Var ("s", stateTy)
         val def = Term.mkAbs (f,
                      Term.mkAbs (s,
                         Term.mkPair (Term.unitTm, Term.mkApply (f, s))))
      in
         Consts.addDefinition (write, def, NONE)
      end

   val monadTys = destMonadTy o Term.primTypeOf
   val stateOf = snd o monadTys
   val valueOf = fst o monadTys
   val destConst = destUop const "Const"
   val destBind = destBop bind "Bind"
   val tryDestConst = Lib.total destConst
   val tryDestBind = Lib.total destBind

   fun mkConst sTy c =
      let
         val cty = Term.primTypeOf c
      in
         Term.Comb (const, monadTy sTy cty, [c])
      end

   fun mkConstFor f = mkConst (stateOf f)
   fun monadTyFor f = monadTy (stateOf f)

   fun primMkBind (a, b) =
      let
         val (aty, sty1) = monadTys a
         val (ty1, ty2) = Types.domainRange (Term.primTypeOf b)
         val sty2 = snd (destMonadTy ty2)
         val () = ignore (Types.equalTy ty1 aty andalso Types.equalTy sty1 sty2
                          orelse raise Fail "")
      in
         Term.Comb (bind, ty2, [Term.mkPair (a, b)])
      end
      handle Fail _ => raise Fail "primMkBind"

   val destAbsConst = (I ## destConst) o Term.destAbs
   val tryDestAbsConst = Lib.total destAbsConst
   fun newVar l x = hd (Term.newVars l [x])
   fun twoNewVars l x1 x2 = Lib.pair (Term.newVars l [x1, x2])

   fun mkBind (a, b) =
      case tryDestConst a of
        SOME c =>
          (case tryDestAbsConst b of
             SOME (vs, body) => mkConstFor a (Term.mkLet (vs, c, body))
           | NONE => Term.mkApply (b, c))
      | NONE =>
         (case tryDestBind a of
            SOME (f, g) =>
               let
                  val ty = Types.domain (Term.primTypeOf g)
                  val v = newVar [g, b] ("v", ty)
               in
                  mkBind (f, Term.mkAbs (v, mkBind (Term.mkApply (g, v), b)))
               end
          | NONE => primMkBind (a, b))

   fun defineExtend () =
      let
         val v = Term.Var ("v", Type.alphaTy)
         val r = Term.Var ("r", Type.betaTy)
         val f = Term.Var ("f", monadTy (Type.alphaTy ** stateTy) Type.betaTy)
         val s0 = Term.Var ("s0", stateTy)
         val s1 = Term.Var ("s1", Type.alphaTy ** stateTy)
         val def =
            Term.mkAbs (Term.mkPair (v, f),
              (Term.mkAbs (s0,
                 Term.mkLet
                    (Term.mkPair (r, s1),
                     Term.mkApply (f, Term.mkPair (v, s0)),
                     Term.mkPair (r, Term.mkSnd s1)))))
      in
         Consts.addDefinition (extend, def, NONE)
      end

   fun defineUnextend () =
      let
         val v = Term.Var ("v", Type.alphaTy)
         val f = Term.Var ("f", monadTy stateTy Type.alphaTy)
         val s1 = Term.Var ("s1", Type.betaTy)
         val s2 = Term.Var ("s2", stateTy)
         val s3 = Term.Var ("s3", stateTy)
         val def =
            Term.mkAbs (f,
              (Term.mkAbs (Term.mkPair (s1, s2),
                 Term.mkLet
                    (Term.mkPair (v, s3),
                     Term.mkApply (f, s2),
                     Term.mkPair (v, Term.mkPair (s1, s3))))))
      in
         Consts.addDefinition (unextend, def, NONE)
      end

   fun define () =
      (defineConst ()
       ; defineBind ()
       ; defineRead ()
       ; defineWrite ()
       ; defineExtend ()
       ; defineUnextend ())

   fun mkIfThenElse (b, f, g) =
      let
         val mk = mkConstFor f
      in
         case (tryDestConst b, tryDestConst f, tryDestConst g) of
           (SOME p, SOME x, SOME y) => mk (mkITE (p, x, y))
         | (SOME p, _, _) => mkITE (p, f, g)
         | (NONE, SOME x, SOME y) =>
              let
                 val v = newVar [f, g] ("b", Type.boolTy)
              in
                 mkBind (b, Term.mkAbs (v, mk (mkITE (v, x, y))))
              end
         | (NONE, _, _) =>
              let
                 val v = newVar [f, g] ("b", Type.boolTy)
              in
                 mkBind (b, Term.mkAbs (v, mkITE (v, f, g)))
              end
      end

   fun mkMatchStatement (_, []) = raise Fail "mkMatchStatement: empty"
     | mkMatchStatement (p, l) =
         let
            val ys = Lib.total (List.map (I ## destConst)) l
         in
            case tryDestConst p of
              SOME x =>
               (case ys of
                  SOME y => mkConstFor (snd (hd l)) (Term.mkMatch (x, y))
                | NONE => Term.mkMatch (x, l))
            | NONE =>
                let
                   val ty = valueOf p
                   val v = newVar (p::List.map snd l) ("x", ty)
                in
                   mkBind (p, Term.mkAbs (v,
                     case ys of
                       SOME y => mkConstFor (snd (hd l)) (Term.mkMatch (v, y))
                     | NONE => Term.mkMatch (v, l)))
                end
         end

   fun mkNop (mk, l) =
      let
         val sty = stateOf (hd l)
         val vs = ref ([] : Term.term list)
         fun newV e =
            let
               val new = newVar (!vs @ l) ("v", valueOf e)
               val () = vs := new :: !vs
            in
               new
            end
         val vs = List.map (fn e => case tryDestConst e of
                                      SOME x => INL x
                                    | NONE => INR (e, newV e)) l
         val base = mk (List.map (fn INL x => x | INR (_, x) => x) vs)
         val base = if isMonadTy sty (Term.primTypeOf base)
                       then base
                    else mkConst sty base
      in
         List.foldr
            (fn (INL _, tm) => tm
              | (INR (e, v), tm) => mkBind (e, Term.mkAbs (v, tm))) base vs
      end
      handle List.Empty => raise Fail "mkNop : empty"

   fun mkUop (mk, a) = mkNop (mk o hd, [a]) handle Fail _ => raise Fail "mkUop"

   fun mkBop (mk, a, b) =
      mkNop (mk o Lib.pair, [a, b]) handle Fail _ => raise Fail "mkBop"

   fun mkTop (mk, a, b, c) =
      mkNop (mk o (fn [x,y,z] => (x,y,z) | _ => raise Fail ""), [a, b, c])
      handle Fail _ => raise Fail "mkTop"

   fun mkQop (mk, a, b, c, d) =
      mkNop (mk o (fn [w,x,y,z] => (w,x,y,z) | _ => raise Fail ""),
             [a, b, c, d])
      handle Fail _ => raise Fail "mkQop"

   fun mkConj (a, b) =
      let
         fun ite () = mkIfThenElse (a, b, mkConstFor a (Term.mkBoolLit false))
      in
         case a of
           Term.Comb (f, _, [_]) =>
             if f = const orelse f = read
                then mkBop (Term.mkBoolOp "and", a, b)
             else ite ()
         | _ => ite ()
      end

   fun mkDisj (a, b) =
      let
         fun ite () = mkIfThenElse (a, mkConstFor a (Term.mkBoolLit true), b)
      in
         case a of
           Term.Comb (f, _, [_]) =>
             if f = const orelse f = read
                then mkBop (Term.mkBoolOp "or", a, b)
             else ite ()
         | _ => ite ()
      end

   fun mkFiniteSet l =
      mkNop (fn l => Term.Comb ("{..}", Type.setTy (Term.primTypeOf (hd l)), l),
             l)
      handle Fail _ => raise Fail "mkFiniteSet"

   fun primMkExtend (v, f) =
      let
         val a = Term.primTypeOf v
         val (b, sty) = monadTys f
         val (c, sty) = Types.destProd sty
         val () = ignore (Types.equalTy a c orelse raise Fail "")
      in
         Term.Comb (extend, monadTy sty b, [Term.mkPair (v, f)])
      end
      handle Fail _ => raise Fail "primMkExtend"

   fun mkExtend (v, f) =
     (case tryDestConst v of
        SOME x => primMkExtend (x, f)
      | NONE => let
                   val e = newVar [f] ("v", valueOf v)
                in
                   mkBind (v, Term.mkAbs (e, primMkExtend (e, f)))
                end)
      handle Fail _ => raise Fail "mkExtend"

   fun mkUnextend (f, ty) =
      let
         val (aty, sty) = monadTys f
      in
         Term.Comb (unextend, monadTy (ty ** sty) aty, [f])
      end
      handle Fail _ => raise Fail "mkExtend"

   fun mkRead f =
      let
         val (sTy, ty) = Types.domainRange (Term.primTypeOf f)
      in
         Term.Comb (read, monadTy sTy ty, [f])
      end
      handle Fail _ => raise Fail "mkRead"

   fun primMkWrite f =
      let
         val ty = Types.domain (Term.primTypeOf f)
      in
         Term.Comb (write, monadTy ty Type.unitTy, [f])
      end
      handle Fail _ => raise Fail "mkPrimWrite"

   fun mkWrite (f, x) =
      let
         val s = fst (Term.destPair (fst (Term.destAbs f)))
      in
         primMkWrite (Term.mkAbs (s, Term.apply f (Term.mkPair (s, x))))
      end
      handle Fail _ => raise Fail "mkWrite"

   fun mkLetExpression (t, b, e) =
      let
         val ty = Term.primTypeOf b
         val (bty, sty) = destMonadTy ty
      in
         case (tryDestConst b, tryDestConst e) of
           (SOME x, SOME y) => mkConst sty (Term.mkLet (t, y, x))
         | (SOME x, NONE)   => mkBind (e, Term.mkAbs (t, mkConst sty x))
         | (NONE, SOME y)   => Term.mkLet (t, y, b)
         | (NONE, NONE)     => mkBind (e, Term.mkAbs (t, b))
      end
      handle Fail _ => raise Fail "mkLetExpression"

   fun primMkFor (i, j, a) =
      let
         val sty = snd (destMonadTy (Types.range (Term.primTypeOf a)))
      in
         Term.Comb (for, monadTy sty Type.unitTy, [Term.mkTuple [i, j, a]])
      end

   fun primMkForeach (i, a) =
      let
         val sty = snd (destMonadTy (Types.range (Term.primTypeOf a)))
      in
         Term.Comb (foreach, monadTy sty Type.unitTy, [Term.mkTuple [i, a]])
      end

   fun mkForLoop (i, j, a) =
      case (tryDestConst i, tryDestConst j) of
        (SOME x, SOME y) => primMkFor (x, y, a)
      | (SOME x, NONE) =>
          let
             val v = newVar [a] ("j", Type.natTy)
          in
             mkBind (j, Term.mkAbs (v, primMkFor (x, v, a)))
          end
      | (NONE, SOME y) =>
          let
             val v = newVar [a] ("i", Type.natTy)
          in
             mkBind (i, Term.mkAbs (v, primMkFor (v, y, a)))
          end
      | (NONE, NONE) =>
          let
             val (v1, v2) = twoNewVars [a] ("i", Type.natTy) ("j", Type.natTy)
          in
             mkBind (i, Term.mkAbs (v1,
               mkBind (i, Term.mkAbs (v2, primMkFor (v1, v2, a)))))
          end

   fun mkForeachLoop (i, a) =
      case tryDestConst i of
        SOME x => primMkForeach (x, a)
      | NONE =>
          let
             val v = newVar [a] ("i", Type.natTy)
          in
             mkBind (i, Term.mkAbs (v, primMkForeach (v, a)))
          end

   local
      val get = fst o Option.valOf o Consts.lookupDefinition
      val M = monadTy stateTy
      val aM = M Type.alphaTy
      val bM = M Type.betaTy
      val uM = M Type.unitTy

      fun rewrite (lhs, defn) f =
         let
            val (m, u) = Term.match lhs f
         in
            Term.apply (Term.inst m (Term.termTypeSubst u defn))
         end
         handle Term.TermMatch => raise Term.NoConv
              | Fail _ => raise Term.NoConv

      fun unary f = Term.apply (get f)
      fun binary f = unary f o Term.mkPair
      fun ternary f (a,b,c) = unary f (Term.mkTuple [a,b,c])
   in
      fun conversions () =
         { constConv = let
                          val v = Term.Var ("v", Type.alphaTy)
                       in
                          rewrite (mkConst stateTy v, unary const v)
                       end,
           bindConv = let
                        val f = Term.Var ("f", aM)
                        val g = Term.Var ("g", Type.alphaTy --> bM)
                     in
                        rewrite (mkBind (f, g), binary bind (f, g))
                     end,
           readConv = let
                         val f = Term.Var ("f", stateTy --> Type.alphaTy)
                      in
                         rewrite (mkRead f, unary read f)
                      end,
           writeConv = let
                          val f = Term.Var ("f", stateTy --> stateTy)
                       in
                          rewrite (primMkWrite f, unary write f)
                       end,
           extendConv = let
                           val v = Term.Var ("v", Type.alphaTy)
                           val ty = monadTy (Type.alphaTy ** stateTy)
                           val f = Term.Var ("f", ty Type.betaTy)
                        in
                           rewrite (primMkExtend (v, f), binary extend (v, f))
                        end,
           unextendConv = let
                             val f = Term.Var ("f", aM)
                          in
                             fn m => fn s =>
                               let
                                  val ty = Types.fstProd (Term.primTypeOf s)
                               in
                                  rewrite (mkUnextend (f, ty),
                                           unary unextend f) m s
                               end
                          end }
         handle Option.Option => raise Fail "Monad not initialized"
   end

   local
      val state_name = ref "state"
      val monadic = ref (Stringmap.empty : Type.ty list Stringmap.dict)
      val functional = ref (Stringmap.empty : Type.ty list Stringmap.dict)
      val pure = ref (Stringmap.empty : Type.ty list Stringmap.dict)
      val mutables = ref Stringmap.empty
      val ostate = ref (NONE : string option)

      fun fixName s =
         let
            val name = Lib.removePrefix "write'" s
         in
            if Tag.isAST name then "dfn'" ^ Tag.remove name else name
         end

      fun isX r (s, ty) =
         case Stringmap.peek (!r, fixName s) of
           SOME l => List.exists (fn t => Types.canMatch t ty) l
         | NONE => false

      fun addX r (s, ty) =
         let
            val name = fixName s
            val l = Option.getOpt (Stringmap.peek (!r, name), [])
         in
            r := Stringmap.insert (!r, name, ty :: l)
         end

      fun removeX r (s, ty) =
         let
            val name = fixName s
            val l = Option.getOpt (Stringmap.peek (!r, name), [])
         in
            case Lib.pluck (fn t => Types.canMatch t ty) l of
              SOME (_, []) => r := fst (Stringmap.remove (!r, name))
            | SOME (_, l') => r := Stringmap.insert (!r, name, l')
            | NONE => ()
         end

      fun listX r () = Stringmap.keys (!r)

      fun resetX r () = r := Stringmap.empty

      fun defineStateType () =
         let
            val () = Exception.buildExceptionDatatype ()
            val vs = Env.listVariables (Env.get ())
            val l = List.map (fn (s, {typ, ...}) => (s, typ)) vs
            val (s, sty) =
               if List.null l
                  then ("unit", Type.unitTy)
               else let
                       val typeNames = List.map fst (Types.listConsts ())
                       val s = indexVariant typeNames (!state_name)
                       val () = Parser.addRecord (s, l)
                    in
                       (s, Type.mkConstType s)
                    end
            val st = Term.Var ("s", sty)
            fun accesses (c, cty) =
               let
                  val ct = Term.Var ("c", cty)
                  val pt = Term.mkPair (st, ct)
                  val rd = Term.mkAbs (st, Term.Comb (c, cty, [st]))
                  val wr = Term.mkAbs (pt, Term.Comb (c, sty, [pt]))
               in
                  (c, (rd, wr))
               end
            val f = Term.Var ("f", monadTy sty Type.alphaTy)
            val thestate = ("the-state", (Term.mkAbs (f, f), Term.anon sty))
         in
            mutables := Stringmap.fromList (thestate :: List.map accesses l)
            ; ostate := SOME s
         end
   in
      val isMonadic = isX monadic
      val isFunctional = isX functional
      val isPure = isX pure
      val addMonadic = addX monadic
      val addFunctional = addX functional
      val addPure = addX pure
      val removeFunctional = removeX functional
      fun listMonadic () = Stringmap.listItems (!monadic)
      fun listFunctional () = Stringmap.listItems (!functional)
      fun listPure () = Stringmap.listItems (!pure)

      fun reset () =
          ( case !ostate of
              SOME s => if s <> "unit" andalso Types.isConst s
                           then (Lib.warn "reverting to saved state."
                                 ; Parser.undo ())
                        else ()
            | NONE => ()
            ; monadic := Stringmap.empty
            ; functional := Stringmap.empty
            ; pure := Stringmap.empty
            ; mutables := Stringmap.empty
            ; ostate := NONE )

      fun init () =
         ( reset ()
           ; if Option.isSome (Consts.lookupDefinition const)
               then ()
             else define ()
           ; Parser.save ()
           ; defineStateType ()
           ; (!mutables, Option.valOf (!ostate)) )

      fun get () = (!mutables, Option.valOf (!ostate))
      fun state () = Option.valOf (!ostate)
      fun stateName s = state_name := s
   end

end (* structure Monad *)

(* ------------------------------------------------------------------------
   Convert definitions to a monadic form and expand out into let-expressions
   ------------------------------------------------------------------------ *)

signature Monadify =
sig
   exception Monadify of string
   val monadifyDefn :
      (Term.term * Term.term) Stringmap.dict * Type.ty ->
       string * Term.term * bool -> Term.term
   val deMonadifyDefn : Type.ty -> Term.term -> Term.term
end

structure Monadify :> Monadify =
struct

exception Monadify of string

local
   val tryDestConst = Lib.total Monad.destConst

   fun checkArgs (l, immutable) =
      let
         fun checkArg tm =
            case tm of
              Term.Lit _ => true
            | Term.Var (v, _) => Stringset.member (immutable, v)
            | _ => false
      in
         List.all checkArg l
      end

   local
      fun updateAccessFns ty =
         let
            fun accessSnd (s, (rd, wr)) =
               if s = "the-state"
                  then let
                          val (v, body) = Term.destAbs rd
                       in
                          (Term.mkAbs (v, Monad.mkUnextend (body, ty)), wr)
                       end
               else let
                       val (ty1, ty2) = Types.domainRange (Term.primTypeOf rd)
                       val v = Term.Var ("v", ty2)
                       val s = Term.Var ("s", ty ** ty1)
                    in
                       (Term.mkAbs (s, Term.mkApply (rd, Term.mkSnd s)),
                        Term.mkAbs (Term.mkPair (s, v),
                          Term.mkPair (Term.mkFst s,
                             Term.mkApply (wr, Term.mkPair (Term.mkSnd s, v)))))
                    end
         in
            Stringmap.map accessSnd
         end
   in
      fun addMutable (name, ty) (mutable, sty) =
         let
            val nty = ty ** sty
            val v = Term.Var ("v", ty)
            val s = Term.Var ("s", nty)
            val rd = Term.mkAbs (s, Term.mkFst s)
            val wr = Term.mkAbs (Term.mkPair (s, v),
                                 Term.mkPair (v, Term.mkSnd s))
         in
            (Stringmap.insert (updateAccessFns ty mutable, name, (rd, wr)), nty)
         end
   end

   val vars =
      List.mapPartial (fn Term.Var ("_", _) => NONE
                        | Term.Var (v, _) => SOME v
                        | _ => NONE) o Term.destTuple

   fun unexpand (mutable, sty, ty, f) =
      case Stringmap.peek (mutable, "the-state") of
        SOME (unex, v) =>
          let
             val sty0 = Term.primTypeOf v
             val mty = Monad.monadTy sty0 ty
             val ety = Monad.monadTy sty ty
          in
             Term.mkMatchApply ety (unex, f mty)
          end
      | NONE => raise Fail "State not found"

   val globals = ref (Stringset.empty)
   val isfun = ref true

   fun monadify (st as (immutable,mutable,sty)) tm =
     (case tm of
        Term.Lit _ => Monad.mkConst sty tm
      | Term.BVar _ => raise Fail "bvar"
      | Term.Var (v, _) =>
          if Stringset.member (immutable, v)
             then Monad.mkConst sty tm
          else (case Stringmap.peek (mutable, v) of
                  SOME (r, _) => Monad.mkRead r
                | NONE => raise Fail ("Unknown state (read): " ^ v))
      | Term.Abs _ =>
          let
             val (t, b) = Term.destAbs tm
             val m =
                monadify (Stringset.addList (immutable, vars t), mutable, sty) b
          in
             case tryDestConst m of
               SOME x => Monad.mkConst sty (Term.mkAbs (t, x))
             | NONE => raise Fail "closure"
          end
      | Term.Comb ("abs-apply", _, [a as Term.Abs _, e]) =>
          let
             val (t, b) = Term.destAbs a
             val m =
                monadify (Stringset.addList (immutable, vars t), mutable, sty) b
          in
             Monad.mkLetExpression (t, m, monadify st e)
          end
      | Term.Comb ("var =", _, [Term.Var (v, ty), a, b]) =>
          let
             val (mut, nty) = addMutable (v, ty) (mutable, sty)
             val m = monadify (immutable,mut,nty) b
          in
             Monad.mkExtend (monadify st a, m)
          end
      | Term.Comb ("<-", _, [Term.Var (v, _), e]) =>
          let
             val () =
                isfun := (!isfun andalso not (Stringset.member (!globals, v)))
             val m = monadify st e
             val w = case Stringmap.peek (mutable, v) of
                       SOME (_, w) => w
                     | NONE => raise Fail ("Unknown state (write): " ^ v)
          in
             case tryDestConst m of
               SOME x => Monad.mkWrite (w, x)
             | NONE =>
                 let
                    val ty = Type.sndTy (Types.domain (Term.primTypeOf w))
                    val v = Term.Var ("v", ty)
                 in
                    Monad.mkBind (m, Term.mkAbs (v, Monad.mkWrite (w, v)))
                 end
          end
      | Term.Comb ("<-", _, _) => raise Fail "bad assigment"
      | Term.Comb ("update-map", ty, [m, i, e]) =>
          Monad.mkTop
             (fn (m, i, x) => Term.Comb ("update-map", ty, [m, i, x]),
              monadify st m, monadify st i, monadify st e)
      | Term.Comb ("bit-field-insert", ty, [h, l, w, v]) =>
          Monad.mkQop
             (fn (h, l, w, v) =>
                Term.Comb ("bit-field-insert", ty, [h, l, w, v]),
              monadify st h, monadify st l, monadify st w, monadify st v)
      | Term.Comb ("bit-modify", _, _) => raise Fail "bit-modify"
      | Term.Comb (";", _, [a, b]) =>
          Monad.mkBind (monadify st a,
                        Term.mkAbs (Term.anon Type.unitTy, monadify st b))
      | Term.Comb ("and", _, [a, b]) =>
          Monad.mkConj (monadify st a, monadify st b)
      | Term.Comb ("or", _, [a, b]) =>
          Monad.mkDisj (monadify st a, monadify st b)
      | Term.Comb ("{..}", _, l as _::_) =>
          Monad.mkFiniteSet (List.map (monadify st) l)
      | Term.Comb ("for", _, [i, j, a as Term.Abs _]) =>
          let
             val (t, b) = Term.destAbs a
             val m =
                monadify (Stringset.addList (immutable, vars t), mutable, sty) b
          in
             Monad.mkForLoop (monadify st i, monadify st j, Term.mkAbs (t, m))
          end
      | Term.Comb ("foreach", _, [i, a as Term.Abs _]) =>
          let
             val (t, b) = Term.destAbs a
             val m =
                monadify (Stringset.addList (immutable, vars t), mutable, sty) b
          in
             Monad.mkForeachLoop (monadify st i, Term.mkAbs (t, m))
          end
      | Term.Comb ("match", _, _) =>
          let
             val (m, cs) = Term.destMatch tm
             val l = List.map
                        (fn (p, c) =>
                           let
                              val vs = List.map fst (Term.freeVars p)
                              val imms = Stringset.addList (immutable, vs)
                           in
                              (p, monadify (imms, mutable, sty) c)
                           end) cs
          in
             Monad.mkMatchStatement (monadify st m, l)
          end
      | Term.Comb ("i-t-e", _, [b, t, e]) =>
          Monad.mkIfThenElse (monadify st b, monadify st t, monadify st e)
      | Term.Comb ("<..>", ty, [h, l, w]) =>
          Monad.mkTop (fn (a,b,c) => Term.Comb ("<..>", ty, [a,b,c]),
                       monadify st h, monadify st l, monadify st w)
      | Term.Comb (f, ty, []) =>
          if Monad.isMonadic (f, ty)
             then (isfun := (!isfun andalso Monad.isFunctional (f, ty))
                   ; unexpand
                       (mutable, sty, ty, fn typ => Term.Comb (f, typ, [])))
          else Monad.mkConst sty (Term.Comb (f, ty, []))
      | Term.Comb (f, ty, [a]) =>
          let
             val fty = (f, Term.primTypeOf a --> ty)
             val monadic = Monad.isMonadic fty
             val () =
                isfun := (!isfun andalso
                          (not monadic orelse Monad.isFunctional fty))
             fun mk b =
                if monadic
                   then unexpand
                          (mutable, sty, ty, fn typ => Term.Comb (f, typ, [b]))
                   else Term.Comb (f, ty, [b])
          in
             Monad.mkUop (mk, monadify st a)
          end
      | Term.Comb (f, ty, [a, b]) =>
          Monad.mkBop (fn (x, y) => Term.Comb (f, ty, [x, y]),
                       monadify st a, monadify st b)
      | _ => raise Fail "no match")
      handle Fail s =>
        (print "\n"
         ; Lib.pp (PolyML.prettyRepresentation (tm, 100))
         ; raise Monadify s)
in
   fun monadifyDefn (mutable, sty) (s, d, recursive) =
      let
         val () = globals := Stringset.fromList (Stringmap.keys mutable)
         val () = isfun := true
         val tm = Exception.removeExceptionCalls d
         val s_ty = (s, Term.primTypeOf tm)
         val () = Monad.addFunctional s_ty
      in
        (case Lib.total Term.destAbs tm of
           SOME (v, b) =>
              let
                 val immutable = Stringset.fromList (vars v)
                 val mdfy = monadify (immutable, mutable, sty)
                 val m = mdfy b
              in
                 if Option.isSome (tryDestConst m)
                    then (Monad.addPure s_ty; tm)
                 else (Monad.addMonadic s_ty
                       ; Term.mkAbs (v, if recursive then mdfy b else m))
              end
         | NONE =>
              let
                 val mdfy = monadify (Stringset.empty, mutable, sty)
                 val m = mdfy tm
              in
                 if Option.isSome (tryDestConst m)
                    then (Monad.addPure s_ty; tm)
                 else (Monad.addMonadic s_ty
                       ; if recursive then mdfy tm else m)
              end)
         before (if !isfun then () else Monad.removeFunctional s_ty)
      end
end

fun destForArg a =
   case Lib.total Term.destTuple a of
     SOME [i, j, a] => (i, j, a)
   | _ => raise Term.NoConv

fun destForeachArg a =
   case Lib.total Term.destTuple a of
     SOME [i, a] => (i, a)
   | _ => raise Term.NoConv

fun deMonadifyDefn sty =
   let
      val {constConv, bindConv, readConv, writeConv,
           extendConv, unextendConv, ...} = Monad.conversions ()
      fun applyMonadic sty =
         fn tm as Term.Comb ("abs-apply", ty, [a, b]) =>
            let
               fun eval f = evaluateMonad sty (Term.mkApply (f, b))
               fun app sty2 cnv = evaluateMonad sty2 (cnv a b)
            in
               case a of
                 Term.Abs (_, ty2, _) =>
                   if Types.equalTy sty (Term.primTypeOf b)
                      then app sty Term.apply
                   else raise Term.NoConv
               | Term.Comb ("m'const", _, [_])    => app sty constConv
               | Term.Comb ("m'bind", _, [_])     => app sty bindConv
               | Term.Comb ("m'read", _, [_])     => app sty readConv
               | Term.Comb ("m'write", _, [_])    => app sty writeConv
               | Term.Comb ("m'unextend", _, [_]) => app sty unextendConv
               | Term.Comb ("m'extend", _, [c]) =>
                    let
                       val sty2 = c |> Term.primTypeOf
                                    |> Types.sndProd
                                    |> Monad.destMonadTy
                                    |> snd
                    in
                       app sty2 extendConv
                    end
               | Term.Comb ("m'for", _, [c]) =>
                   if Types.equalTy sty (Term.primTypeOf b)
                      then let
                              val (i, j, l) = destForArg c
                              val f = Monad.primMkFor (i, j, deMonadify sty l)
                           in
                              Term.mkApply (f, b)
                           end
                      else raise Term.NoConv
               | Term.Comb ("m'foreach", _, [c]) =>
                   if Types.equalTy sty (Term.primTypeOf b)
                      then let
                              val (i, l) = destForeachArg c
                              val f = Monad.primMkForeach (i, deMonadify sty l)
                           in
                              Term.mkApply (f, b)
                           end
                      else raise Term.NoConv
               | Term.Comb ("abs-apply", _, [c as Term.Abs (_, _, d), e]) =>
                   if Types.equalTy sty (Term.primTypeOf b) andalso
                      Monad.isMonadTy sty (Term.primTypeOf d)
                      then let
                              val (vs, f) = Term.destAbs c
                           in
                              Term.mkLet (vs, e, eval f)
                           end
                   else raise Term.NoConv
               | Term.Comb ("i-t-e", ty2, [p, t, e]) =>
                   if Monad.isMonadTy sty ty2
                      then Term.Comb ("i-t-e", ty, [p, eval t, eval e])
                   else raise Term.NoConv
               | Term.Comb ("match", ty2, _) =>
                   if Monad.isMonadTy sty ty2
                      then let
                              val (m, l) = Term.destMatch a
                           in
                              Term.mkMatch (m, List.map (I ## eval) l)
                           end
                   else raise Term.NoConv
               | _ => raise Term.NoConv
            end
          | _ => raise Term.NoConv
      and evaluateMonad sty = Term.topconv (applyMonadic sty)
      and deMonadify sty tm =
         let
            val s = Term.Var ("state", sty)
            fun check x = Monad.isMonadTy sty (Term.primTypeOf x)
            fun eval x = Term.mkAbs (s, evaluateMonad sty (Term.mkApply (x, s)))
         in
            if check tm
               then eval tm
            else let
                    val (t, b) = Term.destAbs tm
                                 handle Fail _ =>
                                   raise Fail "deMonadify: expecting abs"
                 in
                    check b orelse
                    (print "\n"
                     ; Lib.pp (PolyML.prettyRepresentation (sty, 40))
                     ; Lib.pp (PolyML.prettyRepresentation (tm, 40))
                     ; raise Fail "deMonadify: not monadic")
                    ; Term.mkAbs (t, eval b)
                 end
         end
   in
      deMonadify sty
   end

end (* structure Monadify *)

(* ------------------------------------------------------------------------
   Convert definitions to a monadic form and expand out into let-expressions
   ------------------------------------------------------------------------ *)

signature Convert =
sig
   val boolMatchConv : Term.term -> Term.term
   val mergeAnonConv : Term.term -> Term.term
   val numericMatchConv : Term.term -> Term.term
   val recordMatchConv : Term.term -> Term.term
   val simpConv : Term.term -> Term.term (* only valid when pure *)
end

structure Convert :> Convert =
struct

val mergeAnonConv =
   Term.depthconv
      (fn Term.Comb (",", ty, [Term.Var ("_", _), Term.Var ("_", _)]) =>
              Term.Var ("_", ty)
        | _ => raise Term.NoConv)

local
   fun isAnon tm =
      case tm of
        Term.Var (s, _) => String.sub (s, 0) = #"_"
      | Term.Comb ("Fst", _, [a]) => isAnon a
      | Term.Comb ("Snd", _, [a]) => isAnon a
      | _ => false

   val bToInt = Option.valOf o Int.fromString o Tag.remove o Tag.remove

   val mkConj = Term.mkBoolOp "and"
   fun boolVar v = Term.Var (v, Type.boolTy)

   fun booLit (i, b) =
      let
         val v = boolVar ("b'" ^ Int.toString i)
      in
         if b then v else Term.mkNot v
      end

   fun cmp ((i, _ : bool), (j, _ : bool)) = Int.compare (i, j)

   fun mkBoolPredicate (ig, t) p =
      let
         val m = Stringmap.listItems (Matches.pureMatch t p)
         val m = List.filter (fn (v, _) => not (Stringset.member (ig, v))) m
         val (l, v) = List.partition (Term.isLit o snd) m
         val () = ignore (List.all (isAnon o snd) v orelse raise Term.NoConv)
         val l = Lib.msort cmp (List.map (bToInt ## Term.destBoolLit) l)
      in
         if List.null l
            then Term.mkBoolLit true
         else List.foldl (fn (x, t) => mkConj (booLit x, t))
                         (booLit (hd l)) (tl l)
      end
      handle Term.TermMatch => raise Fail "mkBoolPredicate"

   val tvars = List.mapPartial (Lib.total Term.destVar) o Term.destTuple

   val anonSubst =
      Stringmap.transform
         (fn t => if isAnon t then Term.anon (Term.primTypeOf t) else t)

   fun rm x = fst (Stringmap.remove x)

   fun examineBits (t, ncs : ((Term.term * Term.term) * int) list) =
      let
         val groups = List.map (fn (v, _) => (v, [], [], [])) (tvars t)
      in
         List.foldl (fn (((p, _), n), grps) =>
           let
              val m = Matches.pureMatch t p
           in
              List.map (fn (v, ts, fs, xs) =>
                 let
                    val r = Stringmap.find (m, v)
                 in
                    case Lib.total Term.destBoolLit r of
                      SOME true => (v, n :: ts, fs, xs)
                    | SOME false => (v, ts, n :: fs, xs)
                    | NONE =>
                       if isAnon r
                          then (v, ts, fs, (n, rm (anonSubst m, v)) :: xs)
                       else raise Term.NoConv
                 end) grps
           end) groups ncs
      end

   fun bestSplit half =
      Lib.pickP
        (fn (x as (_:string, ts1, fs1, xs1), y as (_, ts2, fs2, xs2)) =>
            List.length xs1 <= List.length xs2 andalso
            Int.abs (List.length ts1 - half) < Int.abs (List.length ts2 - half))

   val T = Term.mkBoolLit true
   val F = Term.mkBoolLit false

   val boolLit2 =
      fn (v,_::_,[],_) => boolVar v
       | (v,[],_::_,_) => Term.mkNot (boolVar v)
       | _ => raise Fail "boolLit2"

   fun build (t, ncs) =
      let
         val e = examineBits (t, ncs)
         val n = List.length ncs
         val (v, ts, fs, xs) = bestSplit (n div 2) e
      in
         if List.length xs = 1 andalso List.length ts > 3 andalso
            List.length fs > 3
            then let
                    val (x, m) = hd xs
                    fun mapTF tm =
                       List.map
                         (fn y as ((p, b), n) =>
                            if n = x then ((Term.inst m tm, b), n) else y)
                    fun inT n = Lib.mem n ts orelse n = x
                    fun inF n = Lib.mem n fs orelse n = x
                    val tt = Term.inst1 (v, T) t
                    val tf = Term.inst1 (v, F) t
                    val tts = mapTF tt (List.filter (inT o snd) ncs)
                    val tfs = mapTF tf (List.filter (inF o snd) ncs)
                 in
                    Term.mkIfThen (boolVar v, build (tt, tts), build (tf, tfs))
                 end
         else let
                 val df = snd (List.last ncs)
                 val us = List.filter
                             (fn (_,t,f,x) =>
                                (List.null t orelse List.null f) andalso
                                List.length x = 1 andalso fst (hd x) = df) e
                 val ig = List.map (fn (v,_,_,_) => v) us |> Stringset.fromList
                 val u = case List.rev us of
                           [] => NONE
                         | (h::t) =>
                             List.foldl (fn (x, tm) => mkConj (boolLit2 x, tm))
                                        (boolLit2 h) t |> SOME
                 val mkPred = mkBoolPredicate (ig, t)
                 val l = List.map (fn ((p, b), _) => (mkPred p, b)) ncs
                 val ((lstp,lstb), fnt) = Lib.lastButlast l
                 val catchall =
                    Option.getOpt (Lib.total Term.destBoolLit lstp, true)
                 val a = Term.anon (Term.primTypeOf lstb)
              in
                 case u of
                   NONE => if catchall then Term.mkIfThens (fnt, lstb)
                           else Term.mkIfThens (l, a)
                 | SOME p =>
                     Term.mkIfThen (p,
                       if catchall
                          then Term.mkIfThens (fnt, lstb)
                       else Term.mkIfThens (l, a),
                       if catchall then lstb else Term.mkIfThen (lstp, lstb, a))
              end
      end

   val bnum = ref 0

   fun mkBoolVar () = boolVar ("b'" ^ Int.toString (!bnum)) before Lib.inc bnum

   fun mkBoolPat ty =
      case ty of
        Type.ConstType "bool" => mkBoolVar ()
      | Type.Prod (ty1, ty2) =>
          let
             val r = mkBoolPat ty2
          in
             Term.mkPair (mkBoolPat ty1, r)
          end
      | _ => raise Term.NoConv

   val anonymize =
      Stringmap.transform (fn Term.Var (_, ty) => Term.Var ("_", ty) | t => t)

   fun boolMatchToIfThen tm =
      let
         val (m, cs) = Term.destMatch tm handle Fail _ => raise Term.NoConv
         val () = bnum := 0
         val t = mkBoolPat (fst (Term.typeOf m))
      in
         if 3 < !bnum andalso 1 < List.length cs
            then let
                    val cs' =
                       List.map
                          (fn (p, b) =>
                              let
                                 val m0 = Matches.pureMatch (Matches.bpFree p) t
                                 val m1 = anonymize m0
                              in
                                 (Term.inst m1 p, Term.inst m0 b)
                              end) cs
                 in
                    Term.mkLet (t, m, build (t, Lib.addIndex cs'))
                 end
         else raise Term.NoConv
      end
in
   val boolMatchConv = Term.depthconv boolMatchToIfThen
end

local
  fun isNumericType ty =
     case Types.dest ty of
        Type.Other "int" => true
      | Type.Other "nat" => true
      | Type.FixedBits _ => true
      | _ => false
  fun numberLit tm =
     case tm of
        Term.Lit (Term.Bits _) => true
      | Term.Lit (Term.Int _) => true
      | Term.Lit (Term.Nat _) => true
      | Term.Comb ("-", _, [t]) => numberLit t
      | _ => false
  fun problematic tm =
     case tm of
        Term.Lit (Term.Bits _) => true
      | Term.Lit (Term.Int _) => true
      | Term.Lit (Term.Nat _) => true
      | Term.Comb (_, _, l) => List.exists problematic l
      | _ => false
  fun condConv tm =
     case tm of
        Term.Comb ("i-t-e", _, [Term.Lit (Term.Bool true), a, _]) => a
      | Term.Comb ("i-t-e", ty, [b, x, y]) =>
           Term.Comb ("i-t-e", ty, [b, x, condConv y])
      | _ => tm
  fun canMatchPattern p1 p2 =
     (case Term.match p1 p2 of
        (d, []) => List.all (fn (_, t) => Term.isVar t orelse numberLit t)
                      (Stringmap.listItems d)
       | _ => false) handle Term.TermMatch => false
  val isAnon = fn Term.Var ("_", _) => true | _ => false
  fun genPattern (p, b) =
     let
        val avoid_terms = ref [p, b]
     in
        Term.depthconv
           (fn t => if numberLit t orelse isAnon t
                       then let
                               val v = hd (Term.newVars (!avoid_terms)
                                             [("v", Term.primTypeOf t)])
                            in
                               avoid_terms := v :: !avoid_terms; v
                            end
                    else t) p
     end
  fun mVar (a, b) = (Term.Var (a, Term.primTypeOf b), b)
  fun dVar (a, Term.Var (b, _)) = if b = "_" then NONE else SOME (b, a)
    | dVar _ = NONE
  fun convertToIfThens _ [] = raise Fail "convertToIfThens: empty"
    | convertToIfThens p l =
     (condConv o Term.mkIfThens)
       (List.mapPartial (fn pb as (pat, body) =>
           let
              val pat' = genPattern pb
           in
              case Term.match pat' p of
                 (d, []) =>
                    let
                       val dl = Stringmap.listItems (fst (Term.match pat' pat))
                       val dl = List.map mVar dl
                       val (dln, dl) = List.partition (numberLit o snd) dl
                       val dv = Stringmap.fromList (List.mapPartial dVar dl)
                       val cond =
                         if List.null dln
                            then Term.mkBoolLit true
                         else Term.mkFold (Term.mkBoolOp "and")
                                (List.map (Term.mkBoolOp "==") dln)
                    in
                       SOME (Term.inst d cond, Term.inst d (Term.inst dv body))
                    end
               | _ => NONE
           end handle Term.TermMatch => NONE) l,
        Term.unknown (Term.primTypeOf (snd (hd l))))
  fun patCompare (p1, p2) =
     if Term.canMatch p1 p2
        then if Term.canMatch p2 p1 then General.EQUAL else General.GREATER
     else if Term.canMatch p2 p1 then General.LESS else General.EQUAL
  val mkPatSet =
     Lib.mkSetEq
        (fn (p1, p2) => Term.canMatch p1 p2 andalso Term.canMatch p2 p1)
  fun processCases [] = raise Fail "processCases: empty"
    | processCases cs =
     let
        val pats = Lib.msort patCompare (mkPatSet (List.map genPattern cs))
     in
        List.map (fn p => (p, convertToIfThens p cs)) pats
     end
  fun numericConv tm =
     let
        val (m, cs) = Term.destMatch tm handle Fail _ => raise Term.NoConv
        val _ = List.exists (fn (p, _) => problematic p) cs orelse
                raise Term.NoConv
     in
        Matches.smartMkMatch (m, processCases cs)
     end
  val preConv =
     Matches.convertMatch isNumericType problematic (fn tm => (tm, [])) Lib.I
in
  val numericMatchConv = Term.depthconv numericConv o preConv
end

local
   fun checkDestructor ty tm =
      case tm of
         Term.Var (v, ty2) =>
            (Option.isSome
               (List.find (Types.equalTy (ty --> ty2) o Term.primTypeOf o fst)
                  (Consts.lookupDestructor v)) orelse raise Term.NoConv
            ; (v, ty2)
            )
       | _ => raise Term.NoConv
   fun recordMatchConv1 tm =
      case Lib.total Term.destMatch tm of
         SOME (m as Term.Var (_, ty), [(Term.Comb (c, _, l), b)]) =>
           if Types.isRecordType ty andalso Consts.isConstructor c
              then let
                      val f = checkDestructor ty
                      fun fnd (c, t) =
                         let
                            val (d, ty) = f c
                         in
                            Term.mkLet (c, Term.Comb (d, ty, [m]), t)
                         end
                   in
                      List.foldl fnd b l
                   end
           else raise Term.NoConv
       | _ => raise Term.NoConv
in
   val recordMatchConv = Term.depthconv recordMatchConv1
end

local
   val uCons =
      fn Term.Comb ("Cons", _, [Term.Var _]) => true
       | _ => false

   fun newVarPair (tm1, tm2, v, ty1, ty2) =
      case Term.newVars [tm1, tm2] [(v ^ "h", ty1), (v ^ "t", ty2)] of
         [v1, v2] => Term.mkPair (v1, v2)
       | _ => raise Fail "newVarPair"

   fun elimUncurried (tm1, tm2) =
      case Term.findTerm uCons tm1 of
         SOME (Term.Comb ("Cons", _, [Term.Var (v, ty)])) =>
           let
              val (ty1, ty2) = Types.destProd ty
              val sv = newVarPair (tm1, tm2, v, ty1, ty2)
              val f = Term.inst1 (v, sv)
           in
              elimUncurried (f tm1, f tm2)
           end
       | NONE => (tm1, tm2)
       | SOME _ => raise Fail "elimUncurried"

   fun curryConsConv1 tm =
      let
         val (m, cs) = Term.destMatch tm
      in
         Term.mkMatch (m, List.map elimUncurried cs)
      end
      handle Fail "destMatch" => raise Term.NoConv
in
   val curryConsConv = Term.depthconv curryConsConv1
end

local
   fun occs (v: string, ty) fvs =
      let
         fun eqt (v2, ty2) = v = v2 andalso Types.equalTy ty ty2
      in
         List.length (List.filter eqt fvs)
      end

   fun allVars tm =
      let
         val vs = ref []
      in
         Term.appTerm (fn Term.Var v => vs := v :: (!vs) | _ => ()) tm
         ; !vs
      end
   val isUnit = Types.equalTy Type.unitTy o Term.primTypeOf

   fun ditch fvs (s, tm) =
      s = "_" orelse isUnit tm orelse Term.isVar tm orelse
      (* Term.isLit tm orelse *) occs (s, Term.primTypeOf tm) fvs < 2

   fun toUnit (s, tm) =
      if s = "_" then NONE else SOME (s, if isUnit tm then Term.unitTm else tm)

   fun extractRedundant (fvs, l) =
      let
         val (go, keep) = List.partition (ditch fvs) l
         val m = Stringmap.fromList (List.mapPartial toUnit go)
      in
         (if List.null go then NONE else SOME m,
          if List.null keep
             then I
          else let
                  fun mkVar (s, tm) = Term.Var (s, Term.primTypeOf tm)
                  val t = Term.mkTuple (List.map mkVar keep)
                  val e = Term.mkTuple (List.map snd keep)
               in
                  fn tm => Term.mkLet (t, e, tm)
               end)
      end

   val simpleMatch =
      let
         fun iter a =
            fn (Term.Comb (",", _, [Term.Var (v, ty1), b]),
                Term.Comb (",", _, [t, c])) =>
                   if Types.equalTy ty1 (Term.primTypeOf t)
                      then iter ((v, t) :: a) (b, c)
                   else raise Term.NoConv
             | (Term.Comb (",", _, [Term.Var (v1, ty),
                                    Term.Var (v2, _)]), x) =>
                   if Types.equalTy Type.unitTy ty
                      then List.rev ((v1, Term.unitTm)::(v2, Term.mkSnd x)::a)
                   else raise Term.NoConv
             | (Term.Var (v, _), t) => List.rev ((v, t) :: a)
             | _ => raise Term.NoConv
      in
         iter []
      end

   val mkFstSnd =
      fn "Fst" => Term.mkFst
       | "Snd" => Term.mkSnd
       | _ => raise Fail "mkFstSnd"

   fun functionalConv tm =
      case tm of
        Term.Comb ("abs-apply", _, [a as Term.Comb (f, _, l), b]) =>
           let
              val rty = Monad.valueOf a handle Fail _ => raise Term.NoConv
              val origTy = case l of
                             [] => rty
                           | [a] => Term.primTypeOf a --> rty
                           | _ => raise Term.NoConv
           in
              if Monad.isFunctional (f, origTy)
                 then Term.mkPair (Term.mkFst tm, b)
              else raise Term.NoConv
           end
      | _ => raise Term.NoConv

   fun fstSndConv tm =
      case tm of
        Term.Comb ("Fst", _, [Term.Comb (",", _, [a, _])]) =>
           Term.topconv fstSndConv a
      | Term.Comb ("Snd", _, [Term.Comb (",", _, [_, a])]) =>
           Term.topconv fstSndConv a
      | Term.Comb (x, _, [tm as Term.Comb ("abs-apply", _, [Term.Abs _, _])]) =>
           if x = "Fst" orelse x = "Snd"
              then let
                      val (t, e, body) = Term.destLet tm
                      val cnv = Term.topconv fstSndConv o mkFstSnd x
                   in
                      Term.mkLet (t, e, cnv body)
                   end
                   handle Fail "destLet" => raise Term.NoConv
           else raise Term.NoConv
      | Term.Comb (x, _, [Term.Comb ("i-t-e", _, [b, t, e])]) =>
           if x = "Fst" orelse x = "Snd"
              then let
                      val cnv = Term.topconv fstSndConv o mkFstSnd x
                   in
                      Term.mkIfThen (b, cnv t, cnv e)
                   end
           else raise Term.NoConv
      | Term.Comb (x, _, [tm as Term.Comb ("match", _, _::l)]) =>
           if x = "Fst" orelse x = "Snd"
              then let
                      val (m, l) = Term.destMatch tm
                      val cnv = Term.topconv fstSndConv o mkFstSnd x
                   in
                      Term.mkMatch (m, List.map (I ## cnv) l)
                   end
           else raise Term.NoConv
      | _ => raise Term.NoConv

   fun condConv tm =
      case tm of
         Term.Comb ("i-t-e", _, [Term.Lit (Term.Bool true), a, _]) => a
       | Term.Comb ("i-t-e", _, [Term.Lit (Term.Bool false), _, a]) => a
       | Term.Comb ("i-t-e", _, [b, t, Term.Lit (Term.Bool false)]) =>
           Term.mkBoolOp "and" (b, t)
       | Term.Comb ("i-t-e", _, [b, Term.Lit (Term.Bool true), t]) =>
           Term.mkBoolOp "or" (b, t)
       | Term.Comb ("i-t-e", _,
            [b, Term.Comb (",", _, [t1, t2]),
                Term.Comb (",", _, [t3, t4])]) =>
           if Term.equalTm t1 t3
              then Term.mkPair (t1, Term.topconv condConv
                                      (Term.mkIfThen (b, t2, t4)))
           else if Term.equalTm t2 t4
              then Term.mkPair (Term.topconv condConv
                                   (Term.mkIfThen (b, t1, t3)), t2)
           else raise Term.NoConv
       | Term.Comb ("i-t-e", _, [b, t1, t2]) =>
           if Term.equalTm t1 t2 then t1 else raise Term.NoConv
       | _ => raise Term.NoConv
in
   val simpConv =
      let
         val cnv =
            fn tm as Term.Comb ("abs-apply", _, [Term.Abs _, _]) =>
                 let
                    val (t, e, body) =
                       Term.destLet tm
                       handle Fail "destLet" => raise Term.NoConv
                 in
                    case extractRedundant (allVars body, simpleMatch (t, e)) of
                      (SOME m, f) =>
                         Term.topconv fstSndConv
                            (Term.topconv functionalConv
                               (f (Term.inst m body)))
                    | _ => raise Term.NoConv
                 end
             | tm as Term.Comb ("Fst", _, [_]) => fstSndConv tm
             | tm as Term.Comb ("Snd", _, [_]) => fstSndConv tm
             | tm => condConv tm
      in
         Term.topconv fstSndConv o Term.depthconv cnv o curryConsConv
      end
end

end (* structure Convert *)

(* ------------------------------------------------------------------------
   Helper functions for common pretty-printing operations
   ------------------------------------------------------------------------ *)

signature PP =
sig
   val ppApp : string * PolyML.pretty -> PolyML.pretty
   val ppAppPair : string * PolyML.pretty * PolyML.pretty -> PolyML.pretty
   val ppAppQuad :
     string * PolyML.pretty * PolyML.pretty * PolyML.pretty *
     PolyML.pretty -> PolyML.pretty
   val ppAppQuintuple :
     string * PolyML.pretty * PolyML.pretty * PolyML.pretty *
     PolyML.pretty * PolyML.pretty -> PolyML.pretty
   val ppAppTriple :
     string * PolyML.pretty * PolyML.pretty * PolyML.pretty ->
     PolyML.pretty
   val ppB : int * int -> PolyML.pretty
   val ppBL : int * int * PolyML.pretty list -> PolyML.pretty
   val ppBracket : PolyML.pretty -> PolyML.pretty
   val ppFile : string -> PolyML.pretty
   val ppInfix : PolyML.pretty * string * PolyML.pretty -> PolyML.pretty
   val ppL : int * PolyML.pretty list -> PolyML.pretty
   val ppList : PolyML.pretty list -> PolyML.pretty
   val ppPair : PolyML.pretty * PolyML.pretty -> PolyML.pretty
   val ppParen :
     string * PolyML.pretty list * string -> PolyML.pretty list ->
     PolyML.pretty
   val ppQ : string -> PolyML.pretty
   val ppS : string -> PolyML.pretty
   val ppTuple : PolyML.pretty list -> PolyML.pretty
   val ppWidth : int ref
   val printPP : PolyML.pretty list -> unit
   val savePP : string -> PolyML.pretty list -> unit
   val sExpExport : bool -> unit
   val isSExp : unit -> bool
end

structure PP :> PP =
struct
   val sExp = ref false
   fun isSExp () = !sExp
   fun sExpExport b = sExp := b
   val ppWidth = ref 74

   fun outPP pw =
      fn [] => Lib.warn "outPP: nothing to print"
       | l => List.app (fn PolyML.PrettyString s => (fst pw) s
                         | p => PolyML.prettyPrint pw p) l

   val printPP = outPP (TextIO.print, !ppWidth)

   fun savePP filename l =
      let
         val screen = filename = ""
         val strm = if screen then TextIO.stdOut else TextIO.openOut filename
         fun pr s = TextIO.output (strm, s)
         fun close () = if screen then () else TextIO.closeOut strm
         val name = OS.Path.file filename
      in
         outPP (pr, !ppWidth) l handle Fail s => (close (); raise Fail s)
         ; close ()
         ; if screen then () else printn ("Created file: " ^ name)
      end

   fun ppL (i, l) = PolyML.PrettyBlock (i, false, [], l)
   val ppS = PolyML.PrettyString
   val ppB = PolyML.PrettyBreak
   val ppQ = ppS o quote

   fun ppFile name =
      let
         val strm = TextIO.openIn name
      in
         ppS (TextIO.inputAll strm before TextIO.closeIn strm)
      end

   fun ppBL (i, j, l) =
      PolyML.PrettyBlock (i, true, [], mapSeparate I [ppB (1,j)] l)

   local
      fun br p = ppL (1, [ppS "(", p, ppS ")"])
   in
      fun ppBracket p =
         case p of
            PolyML.PrettyString s =>
               if not (!sExp) andalso String.isSubstring "\"" s andalso
                  not (String.sub (s, 0) = #"#")
                  then br p
               else p
          | PolyML.PrettyBlock (_, _, _, PolyML.PrettyString b :: l) =>
              (case List.last l of
                  PolyML.PrettyString ")" =>
                     if b = "(" orelse !sExp andalso b = "(sqbkt "
                         then p
                     else br p
                | PolyML.PrettyString "}" => if b = "{" then p else br p
                | PolyML.PrettyString "]" => if b = "[" then p else br p
                | _ => br p)
          | _ => br p
   end

   fun ppInfix (a, b, c) =
      ppL (0, [ppBracket a, ppS b, ppB (1, 0), ppBracket c])

   fun ppParen (b, m, e) l =
      ppL (String.size b, [ppS b, ppL (0, mapSeparate I m l), ppS e])

   fun ppList l =
      if !sExp
         then ppParen ("(sqbkt ", [ppB (1, 0)], ")") l
      else ppParen ("[", [ppS ",", ppB (0, 0)], "]") l

   val ppTuple = ppParen ("(", [ppS ",", ppB (0,0)], ")")

   fun ppPair (a, b) =
      if !sExp
         then ppL (2, [ppS "(", ppBracket a, ppB (1, 0), ppBracket b, ppS ")"])
      else ppTuple [a, b]

   fun ppTriple (a, b, c) = ppTuple [a, b, c]
   fun ppQuad (a, b, c, d) = ppTuple [a, b, c, d]

   fun appSpace (s, b) =
      if String.isSubstring " " s
         then 1
      else case b of PolyML.PrettyString _ => 1 | _ => 0

   fun ppAppPrim (s, b) =
      if String.size s <= 3
         then case b of
                 PolyML.PrettyString _ => ppL (2, [ppS s, ppS " ", b])
               | _ => ppL (String.size s, [ppS s, b])
      else ppL (2, [ppS s, ppB (appSpace (s, b), 0), b])

   fun ppApp (s, b) =
      if !sExp
         then ppL (2, [ppS "(", ppS s, ppB (1, 0), ppBracket b, ppS ")"])
      else ppAppPrim (s, ppBracket b)

   fun ppAppPair (s, b, c) =
      if !sExp
         then ppL (2, [ppS "(", ppS s, ppB (1, 0), ppBracket b, ppB (1, 0),
                       ppBracket c, ppS ")"])
      else ppAppPrim (s, ppPair (b, c))

   fun ppAppTriple (s, b, c, d) =
      if !sExp
         then ppL (2, [ppS "(", ppS s, ppB (1,0), ppBracket b, ppB (1,0),
                       ppBracket c, ppB (1,0), ppBracket d, ppS ")"])
      else ppAppPrim (s, ppTriple (b, c, d))

   fun ppAppQuad (s, b, c, d, e) =
      if !sExp
         then ppL (2, [ppS "(", ppS s, ppB (1,0),
                       ppBracket b, ppB (1,0),
                       ppBracket c, ppB (1,0),
                       ppBracket d, ppB (1,0),
                       ppBracket e, ppS ")"])
      else ppAppPrim (s, ppQuad (b, c, d, e))

   fun ppAppQuintuple (s, b, c, d, e, f) =
      ppAppPrim (s, ppTuple [b, c, d, e, f])

end (* structure PP *)
