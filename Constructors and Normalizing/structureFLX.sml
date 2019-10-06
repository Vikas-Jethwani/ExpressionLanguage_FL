use "signatureFLX.sml" ;
(* Author : Vikas Jethwani - MCS192573 *)
structure Flx : FLX =
struct
    (* DataType definitions and Exceptions *)
    datatype term = VAR of string   (* variable *)
                  | Z               (* zero *)
                  | T               (* true *)
                  | F               (* false *)
                  | P of term       (* Predecessor *)
                  | S of term       (* Successor *)
                  | ITE of term * term * term   (* If then else *)
                  | IZ of term      (* is zero *)
                  | GTZ of term     (* is greater than zero *)

    exception Not_wellformed ;
    exception Not_nf ;
    exception Not_int ;

    (* fromInt : int -> term *)
    fun fromInt 0 = Z
      | fromInt curr =
            if curr > 0 then S (fromInt(curr-1))
            else P (fromInt(curr+1)) ;

    (* toInt : term -> int *)
    fun toInt Term =
            let
                (* to determine type of exception : eg. toInt(P (P T)) *)
                fun which_err(Z) = raise Not_nf
                  | which_err(P t) = which_err(t)
                  | which_err(S t) = which_err(t)
                  | which_err(_) = raise Not_int ;

                (* toInt_wr(Term, sign, curr) *)
                fun toInt_wr(Z, _, curr) = curr
                  | toInt_wr(P t, 1, _) = which_err(t)
                  | toInt_wr(S t, ~1, _) = which_err(t)
                  | toInt_wr(P t, _, curr) = toInt_wr(t, ~1, curr-1)
                  | toInt_wr(S t, _, curr) = toInt_wr(t, 1, curr+1)
                  | toInt_wr(_, _, _) = raise Not_int ;
            in
                toInt_wr(Term, 0, 0)
            end ;

    (* toString : term -> string *)
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
            in
                toString_wr(Term)
            end ;
    
    (* fromString : string -> term *)
    fun fromString str = 
            let
                (* find_terms(char_list, tokens_processed, terms, prev_char) *)
                fun find_terms([], [], [t], _) = t
                  | find_terms(#"Z"::left, tokens, terms, _) = find_terms(left, tokens, (Z::terms), "Z")
                  | find_terms(#"T"::left, tokens, terms, _) = find_terms(left, tokens, (T::terms), "T")
                  | find_terms(#"F"::left, tokens, terms, _) = find_terms(left, tokens, (F::terms), "F")
                  
                  | find_terms(#"(" :: #"P" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(P")::tokens, terms, " ")
                  | find_terms(#"(" :: #"S" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(S")::tokens, terms, " ")
                  | find_terms(#"(" :: #"I" :: #"Z" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(IZ")::tokens, terms, " ")
                  | find_terms(#"(" :: #"G" :: #"T" :: #"Z" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(GTZ")::tokens, terms, " ")
                  | find_terms(#"(" :: #"I" :: #"T" :: #"E" :: #" " :: #"<" :: left, tokens, terms, _) = find_terms(left, ("(ITE")::tokens, terms, "<")
                  
                  | find_terms(#")"::left, "(P"::tokens, t::terms, _) = find_terms(left, tokens, (P t)::terms, "P")
                  | find_terms(#")"::left, "(S"::tokens, t::terms, _) = find_terms(left, tokens, (S t)::terms, "S")
                  | find_terms(#")"::left, "(IZ"::tokens, t::terms, _) = find_terms(left, tokens, (IZ t)::terms, "IZ")
                  | find_terms(#")"::left, "(GTZ"::tokens, t::terms, _) = find_terms(left, tokens, (GTZ t)::terms, "GTZ")
                  
                  | find_terms(#","::left, tokens, terms, ",") = raise Not_wellformed
                  | find_terms(#","::left, tokens, terms, _) = find_terms(left, tokens, terms, ",")
                  | find_terms(#">" :: #")"::left, "(ITE"::tokens, t0::t1::t2::terms, _) = find_terms(left, tokens, (ITE(t2,t1,t0))::terms, ">")
                  | find_terms(c::left, tokens, (VAR t)::terms, "v") =
                            if Char.isLower(c) then find_terms(left, tokens, (VAR (t^Char.toString(c)))::terms, "v")
                            else raise Not_wellformed
                  | find_terms(c::left, tokens, terms, _) =
                            if Char.isLower(c) then find_terms(left, tokens, (VAR (Char.toString(c)))::terms, "v")
                            else raise Not_wellformed
                  | find_terms(_, _, _, _) = raise Not_wellformed ;

                val terms = find_terms(explode str, [], [], "")
            in
                (* sanity check *)
                if (toString(terms))=str then terms
                else raise Not_wellformed
            end ;

    (* normalize : term -> term *)
    fun normalize Term =
            let
                (* for reduction in IZ and GTZ by seeing the first constructor *)
                fun checkConsistency(Z, _) = true
                  | checkConsistency(P( t ), "P") = checkConsistency(t, "P")
                  | checkConsistency(S( t ), "S") = checkConsistency(t, "S")
                  | checkConsistency(_, _) = false ;

                fun normalize_wr(Z) = Z
                  | normalize_wr(T) = T
                  | normalize_wr(F) = F
                  | normalize_wr(P( t )) =
                        let
                            val norm = normalize_wr(t)
                        in
                            ( case norm of
                                S term' => term'
                              | _       => P(norm)
                            )
                        end
                  | normalize_wr(S( t )) =
                        let
                            val norm = normalize_wr(t)
                        in
                            ( case norm of
                                P term' => term'
                              | _       => S(norm)
                            )
                        end
                  | normalize_wr(IZ( t )) = 
                        let
                            val norm = normalize_wr(t)
                        in
                            ( case norm of
                                Z       => T
                              | P term' => if checkConsistency(norm, "P") then F
                                           else IZ(norm)
                              | S term' => if checkConsistency(norm, "S") then F
                                           else IZ(norm)
                              | _       => IZ(norm)
                            )
                        end
                  | normalize_wr(GTZ( t )) = 
                    let
                        val norm = normalize_wr(t)
                    in
                        ( case norm of
                            Z       => F
                          | P term' => if checkConsistency(norm, "P") then F
                                       else GTZ(norm)
                          | S term' => if checkConsistency(norm, "S") then T
                                       else GTZ(norm)
                          | _       => GTZ(norm)
                        )
                    end
                  | normalize_wr(ITE( t0,t1,t2 )) = 
                        let
                            val norm0 = normalize_wr(t0)
                            val norm1 = normalize_wr(t1)
                            val norm2 = normalize_wr(t2)
                        in
                            ( case norm0 of
                                T       => norm1
                              | F       => norm2
                              | _       => if norm1=norm2 then norm1
                                           else ITE(norm0, norm1, norm2)
                            )
                        end
                  | normalize_wr(VAR t) = VAR t ;
            in
                normalize_wr(Term)
            end ;

end ; (* struct *)