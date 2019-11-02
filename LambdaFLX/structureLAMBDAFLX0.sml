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
            
    fun fromString str = 
            let
                fun find_terms([], [], [t], _) = t
                  | find_terms(#" "::left, tokens, terms, " ") = raise Not_wellformed
                  | find_terms(#" "::left, "(APP"::tokens, terms, _) = find_terms(left, "(APP"::tokens, terms, " ") (* Space between application *)
                  | find_terms(#"Z"::left, tokens, terms, _) = find_terms(left, tokens, (Z::terms), "Z")
                  | find_terms(#"T"::left, tokens, terms, _) = find_terms(left, tokens, (T::terms), "T")
                  | find_terms(#"F"::left, tokens, terms, _) = find_terms(left, tokens, (F::terms), "F")

                  | find_terms(#"(" :: #"P" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(P")::tokens, terms, " ")
                  | find_terms(#"(" :: #"S" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(S")::tokens, terms, " ")
                  | find_terms(#"(" :: #"I" :: #"Z" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(IZ")::tokens, terms, " ")
                  | find_terms(#"(" :: #"G" :: #"T" :: #"Z" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(GTZ")::tokens, terms, " ")
                  | find_terms(#"(" :: #"I" :: #"T" :: #"E" :: #" " :: #"<" :: left, tokens, terms, _) = find_terms(left, ("(ITE")::tokens, terms, "<")
                  | find_terms(#"L" :: #"A" :: #"M" :: #"B" :: #"D" :: #"A" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(L1")::tokens, terms, " ")
                  | find_terms(#"[" :: left, tokens, terms, _) = find_terms(left, ("(L2")::tokens, terms, "[")
                  | find_terms(#"(" :: #"(" :: left, tokens, terms, _) = find_terms(#"(" ::left, ("(APP")::tokens, terms, "(")
                  | find_terms(#"(" :: #"Z" :: left, tokens, terms, _) = find_terms(#"Z" ::left, ("(APP")::tokens, terms, "Z")
                  | find_terms(#"(" :: #"T" :: left, tokens, terms, _) = find_terms(#"T" ::left, ("(APP")::tokens, terms, "T")
                  | find_terms(#"(" :: #"F" :: left, tokens, terms, _) = find_terms(#"F" ::left, ("(APP")::tokens, terms, "F")
                  | find_terms(#"(" :: #"L" :: left, tokens, terms, _) = find_terms(#"L" ::left, ("(APP")::tokens, terms, "L")
                  | find_terms(#"(" :: c :: left, tokens, terms, _) = 
                            if Char.isLower(c) then find_terms( c::left, ("(APP")::tokens, terms, "")
                            else raise Not_wellformed

                  | find_terms(#")"::left, "(P"::tokens, t::terms, _) = find_terms(left, tokens, (P t)::terms, "P")
                  | find_terms(#")"::left, "(S"::tokens, t::terms, _) = find_terms(left, tokens, (S t)::terms, "S")
                  | find_terms(#")"::left, "(IZ"::tokens, t::terms, _) = find_terms(left, tokens, (IZ t)::terms, "IZ")
                  | find_terms(#")"::left, "(GTZ"::tokens, t::terms, _) = find_terms(left, tokens, (GTZ t)::terms, "GTZ")
                  | find_terms(#")"::left, "(APP"::tokens, t0::t1::terms, _) = find_terms(left, tokens, (APP(t1,t0))::terms, "APP")

                  | find_terms(#","::left, tokens, terms, ",") = raise Not_wellformed
                  | find_terms(#","::left, tokens, terms, _) = find_terms(left, tokens, terms, ",")
                  | find_terms(#">" :: #")"::left, "(ITE"::tokens, t0::t1::t2::terms, _) = find_terms(left, tokens, (ITE(t2,t1,t0))::terms, ">")
                  | find_terms(#"]"::left, "(L2"::"(L1"::tokens, t0::t1::terms, _) = find_terms(left, tokens, (LAMBDA(t1,t0))::terms, "]") (* if not var x is first term *)
                  | find_terms(c::left, tokens, (VAR t)::terms, "v") =
                            if Char.isLower(c) then find_terms(left, tokens, (VAR (t^Char.toString(c)))::terms, "v")
                            else raise Not_wellformed
                  | find_terms(c::left, tokens, terms, _) = (* We can change here to check if lterm0 is var or not *)
                            if Char.isLower(c) then find_terms(left, tokens, (VAR (Char.toString(c)))::terms, "v")
                            else raise Not_wellformed
                  | find_terms(_, _, _, _) = raise Not_wellformed ;

                val terms = find_terms(explode str, [], [], "")
            in
                 if (toString(terms))=str then terms
                 else raise Not_wellformed
            end ;
            
    fun betanf LTerm =
        let
            fun replace_term(L, v, M)=
                let
                    fun replace_wr(VAR x, VAR v, _) = 
                            if x=v then M
                            else VAR x
                      | replace_wr(Z, _, _) = Z
                      | replace_wr(T, _, _) = T
                      | replace_wr(F, _, _) = F
                      | replace_wr(P t, v, M) = P( replace_wr(t, v, M) )
                      | replace_wr(S t, v, M) = S( replace_wr(t, v, M) )
                      | replace_wr(IZ t, v, M) = IZ( replace_wr(t, v, M) )
                      | replace_wr(GTZ t, v, M) = GTZ( replace_wr(t, v, M) )
                      | replace_wr(ITE(t0, t1, t2), v, M) = ITE( replace_wr(t0, v, M), replace_wr(t1, v, M), replace_wr(t2, v, M) )
                      | replace_wr(LAMBDA(x, t), v, M) = LAMBDA( x, replace_wr(t, v, M) )
                      | replace_wr(APP(t0, t1), v, M) = APP( replace_wr(t0, v, M), replace_wr(t1, v, M) )
                in
                    replace_wr(L, v, M)
                end


            fun is_Present(x, []) = (x^"1", [(x,1)])
              | is_Present(x, (y, count)::taill) =
                    if x=y then (x^(Int.toString(count+1)), (y, count+1)::taill)
                    else
                        let val (v,c) = is_Present(x, taill) in (v, (y, count)::c) end

            fun preprocess(VAR x, unique) = (VAR x, unique)
              | preprocess(Z, unique) = (Z, unique)
              | preprocess(T, unique) = (T, unique)
              | preprocess(F, unique) = (F, unique)
              | preprocess(P t, unique) = 
                    let
                        val (Term, uniq) = preprocess(t, unique)
                        val usless = (print("At P :");print(toString(Term));print("\n"); 5)
                    in (P(Term), uniq) end
              | preprocess(S t, unique) = 
                    let
                        val (Term, uniq) = preprocess(t, unique)
                        val usless = (print("At S :");print(toString(Term));print("\n"); 5)
                    in (S(Term), uniq) end
              | preprocess(IZ t, unique) = 
                    let
                        val (Term, uniq) = preprocess(t, unique)
                        val usless = (print("At IZ :");print(toString(Term));print("\n"); 5)
                    in (IZ(Term), uniq) end
              | preprocess(GTZ t, unique) = 
                    let
                        val (Term, uniq) = preprocess(t, unique)
                        val usless = (print("At GTZ :");print(toString(Term));print("\n"); 5)
                    in (GTZ(Term), uniq) end
              | preprocess(ITE(t0, t1, t2), unique) = 
                    let
                        val (Term0, uniq0) = preprocess(t0, unique)
                        val (Term1, uniq1) = preprocess(t1, uniq0)
                        val (Term2, uniq2) = preprocess(t2, uniq1)
                        val usless = (print("At ITE :");print(toString(Term0));print("--");print(toString(Term1));print("--");print(toString(Term2));print("\n"); 5)
                    in (ITE(Term0, Term1, Term2), uniq2) end
              | preprocess(APP(t0, t1), unique) = 
                    let
                        val (Term0, uniq0) = preprocess(t0, unique)
                        val (Term1, uniq1) = preprocess(t1, uniq0)
                        val usless = (print("At APP :");print(toString(Term0));print("--");print(toString(Term1));print("\n"); 5)
                    in (APP(Term0, Term1), uniq1) end
              | preprocess(LAMBDA(VAR x, t), unique) = 
                    let
                        val (v, uniq) = is_Present(x, unique)
                        val half_processed = replace_term(t, VAR x, VAR v)
                        val usless = (print(toString(half_processed));print("\n"); 5)
                        val (Term, uniq1) = preprocess(half_processed, uniq)
                    in (LAMBDA(VAR v, Term), uniq1) end


            fun betanf_wr(VAR v) = VAR v
              | betanf_wr(Z) = Z
              | betanf_wr(T) = T
              | betanf_wr(F) = F
              | betanf_wr(P t) = P(betanf_wr(t))
              | betanf_wr(S t) = S(betanf_wr(t))
              | betanf_wr(IZ t) = IZ(betanf_wr(t))
              | betanf_wr(GTZ t) = GTZ(betanf_wr(t))
              | betanf_wr(ITE(t0, t1, t2)) = ITE( betanf_wr(t0), betanf_wr(t1), betanf_wr(t2) )
              | betanf_wr(LAMBDA(v, t)) = LAMBDA( v, betanf_wr(t) )
              | betanf_wr(APP( LAMBDA(VAR v, L), M )) = betanf_wr(replace_term(L, VAR v, M))
              | betanf_wr(APP( APP(x, y), M )) = betanf_wr( APP( betanf_wr(APP( x, y )), M) )

          
            
            val preprocessed_Term = #1(preprocess(LTerm, []))
        in
            (*betanf_wr(preprocessed_Term)*)
            preprocessed_Term
        end ;


end ; (* struct *)

open LambdaFlx;