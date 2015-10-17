open updateLib tinyLib

val rhsc = boolSyntax.rhs o Thm.concl
val wordString = Arbnum.toString o wordsSyntax.dest_word_literal
val Next_tm = Term.prim_mk_const {Thy = "tiny", Name = "Next"}
fun mk_next s = pairSyntax.mk_snd (Term.mk_comb (Next_tm, s))
fun override_conv ty =
   Conv.DEPTH_CONV (updateLib.OVERRIDE_UPDATES_CONV ty wordsLib.word_EQ_CONV)

val eval =
   let
      val cmp = tinyLib.tiny_compset []
      val r_cnv = override_conv ``:word7 -> word32``
      val m_cnv = override_conv ``:word10 -> word32``
   in
      computeLib.CBV_CONV cmp
      THENC r_cnv
      THENC m_cnv
   end

val eval_rhs = rhsc o eval

val sort_cnv_rhs =
   rhsc o
   (Conv.DEPTH_CONV (updateLib.SORT_WORD_UPDATES_CONV ``:7``)
    THENC Conv.DEPTH_CONV (updateLib.SORT_WORD_UPDATES_CONV ``:10``))

(* ------------------------------------------------------------------------ *)

fun readPC s = eval_rhs ``^s.PC``
fun readStrobe s = eval_rhs ``^s.OutStrobe``

fun initialize p = eval_rhs ``SND (initialize ^p s)``

val trace = ref true
fun trace_print s = if !trace then print s else ()

fun run i =
   let
      val count = ref 0
      fun loop s =
         let
            val () = Portable.inc count
            val pc = readPC s
            val strobe = readStrobe s
            val () = trace_print (wordString pc)
            val ns = eval_rhs (mk_next s)
            val npc = readPC ns
            val nstrobe = readStrobe ns
            val () = if nstrobe <> strobe
                        then trace_print (" [" ^ wordString nstrobe ^ "]")
                     else ()
            val () = trace_print "\n"
         in
            if npc = pc then ns else loop ns
         end
      val s = if !count = 1 then "" else "s"
   in
      sort_cnv_rhs (loop i)
      before trace_print
                ("Done in " ^ Int.toString (!count) ^ " cycle" ^ s ^ ".\n")
   end

(* ------------------------------------------------------------------------ *)

val initial = Count.apply initialize ``test_prog``
val final = Count.apply run initial

fun ntimes f =
   let
      fun iter n =
         if n = 0 then () else (f(); iter (n - 1))
   in
      iter
   end

val test = ntimes (fn () => run initial)

(*
trace := false

Lib.time test 10

(35.0 * 10.0) / 17.920

19.5 ips

*)
