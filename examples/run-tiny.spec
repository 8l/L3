val () = Runtime.LoadF "tiny.spec";

(* ------------------------------------------------------------------------ *)

local
   fun regToString tm = "R(" ^ Term.bitsToString tm ^ ")"
   val evalS = Runtime.evalQ o Lib.stringToQuote
   val readBits = Lib.total Term.destBitsLit o evalS
   fun getBits s err =
      fn () => Option.valOf (readBits s) handle Option.Option => raise Fail err
in
   val readPC = getBits "PC" "readPC"
   val readStrobe = getBits "OutStrobe" "readStrobe"
   val printReg =
      Term.printMapDiff ("Register updates:", Lib.I, regToString,
                         Term.bitsToPaddedHexString, Term.bitsToString)
   val printMem =
      Term.printMapDiff
         ("Memory updates:", Lib.I, Term.bitsToPaddedHexString,
          Term.bitsToPaddedHexString, Term.bitsToHexString)
   val trace = ref true
   fun trace_print s = if !trace then print s else ()
   val doQ = General.ignore o Runtime.evalQ
end

(* ------------------------------------------------------------------------ *)

fun initialize () =
   General.ignore
     (Runtime.reset ()
      ; Runtime.evalQ `initialize (test_prog)`)

fun run () =
   let
      fun loop () =
         let
            val pc = readPC ()
         in
           (if !trace
               then let
                       val strobe = readStrobe ()
                       val () = (print (BitsN.toString pc); doQ `Next`)
                       val nstrobe = readStrobe ()
                    in
                       if nstrobe <> strobe
                          then Lib.printn
                                 (" [" ^ BitsN.toString nstrobe ^ "]")
                       else print "\n"
                    end
            else doQ `Next`)
            ; if readPC () = pc then () else loop ()
         end
   in
      loop(); trace_print "Done.\n"
   end

(* ------------------------------------------------------------------------ *)

(*

val () = Runtime.reset()
val () = initialize();
val r_init = ``R``
val m_init = ``DM``
val () = run()

val _ = printReg (``R``, r_init)
val _ = printMem (``DM``, m_init)
val _ = printMem (``IM``, ``InitMap (Encode (ReservedInstr))::memT``)

fun ntimes f =
   let
      fun iter n =
         if n = 0 then () else (f(); iter (n - 1))
   in
      iter
   end

val test = ntimes (fn () => initialize())
val test = ntimes (fn () => (initialize(); run()))

PolyML.timing true;
trace := false

test 1000
test 5000

(35.0 * 1000.0) / 6.3
(35.0 * 5000.0) / 26.5
(35.0 * 5000.0) / (26.5 - 4.1)

~6600 ips
~7800 ips without intitialise

*)
