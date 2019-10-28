 use "signatureLAMBDAFLX.sml" ; 
 (*use "structureFLX.sml";*)

structure LambdaFlx : LAMBDAFLX =
struct
    datatype lterm = term (* term from FLX *)
                   | VAR of string      (* variables *)
                   | Z                  (* zero *)
                   | T                  (* true *)
                   | F                  (* false *)
                   | P of lterm         (* Predecessor *)
                   | S of lterm         (* Successor *)
                   | ITE of lterm * lterm * lterm       (* If then else *)
                   | IZ of lterm        (* is zero *)
                   | GTZ of lterm       (* is greater than zero *)
                   | LAMBDA of lterm * lterm    (* lambda x [lterm] *)
                   | APP of lterm * lterm       (* application of lambda terms, i.e. (L M) *)
                                        
    exception Not_wellformed
    exception Not_nf
    exception Not_int
    exception Not_welltyped
                  
    fun fromInt 0 = Z
      | fromInt curr =
            if curr > 0 then S (fromInt(curr-1))
            else P (fromInt(curr+1)) ;

    fun toInt LTerm =
            let
                fun which_err(Z) = raise Not_nf
                  | which_err(P t) = which_err(t)
                  | which_err(S t) = which_err(t)
                  | which_err(_) = raise Not_int ;

                (* fun toInt_wr(Term, sign, curr) *)
                fun toInt_wr(Z, _, curr) = curr
                  | toInt_wr(P t, 1, _) = which_err(t)
                  | toInt_wr(S t, ~1, _) = which_err(t)
                  | toInt_wr(P t, _, curr) = toInt_wr(t, ~1, curr-1)
                  | toInt_wr(S t, _, curr) = toInt_wr(t, 1, curr+1)
                  | toInt_wr(_, _, _) = raise Not_int ;
            in
                toInt_wr(LTerm, 0, 0)
            end ;

    fun toString Term = 
            let
                fun toString_wr(VAR(x)) = x
                  | toString_wr(Z) = "Z"
                  | toString_wr(T) = "T"
                  | toString_wr(F) = "F"
                  | toString_wr(P t) = "(P " ^ toString_wr(t) ^ ")"
                  | toString_wr(S t) = "(S " ^ toString_wr(t) ^ ")"
                  | toString_wr(IZ t) = "(IZ " ^ toString_wr(t) ^ ")"
                  | toString_wr(GTZ t) = "(GTZ " ^ toString_wr(t) ^ ")"
                  | toString_wr(ITE(t0, t1, t2)) = "(ITE <" ^ toString_wr(t0) ^ "," ^ toString_wr(t1) ^ "," ^ toString_wr(t2) ^ ">)"
                  | toString_wr(LAMBDA(t0, t1)) = "LAMBDA " ^ toString_wr(t0) ^ "[" ^ toString_wr(t1) ^ "]"
                  | toString_wr(APP(t0, t1)) = "(" ^ toString_wr(t0) ^ " " ^ toString_wr(t1) ^ ")"
            in
                toString_wr(Term)
            end ;


end ; (* struct *)

open LambdaFlx;