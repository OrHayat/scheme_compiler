(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
type number =
  | Int of int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

  let rec for_all2 p l1 l2 =
    match (l1, l2) with
      ([], []) -> true
    | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
    | (_, _) -> false

  let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> for_all2 sexpr_eq l1 l2
  | _ -> false;;

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
open PC;;

let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;
  let _spaces_ = star nt_whitespace ;;
  let list_nth= fun lst n->
  if(n<0)then failwith "list_nth Invalid_argument" else
  let rec helper= fun lst n-> match (lst,n) with
                |[],_->failwith "list_nth"
                |x::_,0->x
                |x::t,k->helper t(k-1)
                in helper lst n;;
  let list_head= fun lst -> match lst with
  |[]->failwith "hd"
  |x::_->x;;
let ascii_0=int_of_char '0';;
let ascii_a=int_of_char 'a';;
let char_list_int lst base =List.fold_left (fun res a->res * base+a) 0 lst;;
let char_list_remainder lst base =List.fold_right (fun a res->((float_of_int a)+.res) /.base) lst 0.0;;
let rec read_sexprs_helper s =
  disj_list[_real_list_;real_vector;_balanced_sexprs_]s
and  allow_space nt = (pack(caten(caten (_skip_)(nt))(_skip_)) (fun ((_,x),_)->x))
and _balanced_sexprs_ s=  (disj_list[atomic_sexpr ;list_sexpr;quote_sexpr]) s
and atomic_sexpr s= disj_list [_boolean_;_number_;_symbol_;_char_;_string_] s
and list_sexpr s= disj_list[_balanced_list_;_balance_vector_] s
and quote_sexpr s= disj_list[_quoted_;_quasiQuoted_;_unquoted_;_unquoteAndSpliced_] s


and _unbalanced_sexprs s= disj_list[_balanced_sexprs_; unbalanced_list;_unbalance_vector_] s
and   _boolean_ s= let _false_ = (pack (word_ci "#f")(fun x->Bool (false))) in
    let _true_=pack (word_ci "#t") (fun x-> Bool (true)) in
    ((allow_space (not_followed_by(disj _true_ _false_) _symbolnospaces_))) s
and _number_ s=
    (allow_space(not_followed_by (pack (disj_list [_sientific_form_;_hex_float_;_float_ ;_integer_;_hex_integer_])  (fun x->Number(x)))_symbolnospaces_)) s
and  _symbolnospaces_ s=
 let _symbol_char_= (disj_list[(range '0' '9');(pack(range_ci 'A' 'Z')(fun x->lowercase_ascii x));(one_of ":!$^*-_=+<>/?")] )
 in  (diff(pack(plus _symbol_char_)(fun x->Symbol(list_to_string x)))_number_) s
and  _symbol_ s= (allow_space _symbolnospaces_ )s
and _digit_ s=(pack(range '0' '9')(fun nb -> (int_of_char nb)-ascii_0)) s
and _natural_ s=  (pack(plus _digit_)(fun x->char_list_int x 10)) s
and _sign_ s=
  (pack(maybe(disj(char '-')(char '+')))
  (fun sign->match sign with
  |Some('-')->(-1)
  |_->1
 ) ) s
and _integer_ s =
    (pack (caten _sign_ _natural_) (fun ((sign,nb))->Int(sign*nb))) s

and make_float_ ( signparser,int_nt,digit_nt,base) s =
  let _nb_= (caten signparser(caten(caten  int_nt (char '.'))(plus digit_nt)))
  in (pack _nb_ (fun (s,((x,_),y))->
    let p=char_list_remainder y base
      in Float((float_of_int s)*.(p+.(float_of_int x))))) s
and _float_ s=make_float_(_sign_,_natural_,_digit_,10.0) s

and _hex_digit_ s= disj _digit_ (pack (range_ci 'a' 'f')(fun x->10+int_of_char(lowercase_ascii x)-ascii_a)) s

and hex_prefix s=word_ci "#x" s

and _hex_natural_ s =
  let _hex_number = plus _hex_digit_ in
  (pack _hex_number  (fun nb-> char_list_int nb 16))s

and _hex_sign_ s= (pack(caten hex_prefix _sign_) (fun (_,x)->x))s

and _hex_integer_ s=
  let _hex_number=plus _hex_digit_ in
  (pack (caten _hex_sign_ _hex_natural_)
  (fun (sign,nb)->  Int(nb*sign)
  )) s

and sexp_comment s= (pack(caten (word "#;") read_sexprs_helper)((fun (x,y) -> x)))s

and _line_comment_ s=
  let _new_line_or_end_of_line = disj nt_end_of_input(pack (char '\n')(fun x->[x]))
  in  pack(caten_list[pack(char ';')(fun x->[x]);
                            (star(diff nt_any _new_line_or_end_of_line));
                            _new_line_or_end_of_line ])((fun (x) ->['c'] ))s

and _skip_ s= (star(disj_list [(pack nt_whitespace (fun (x) -> [x])) ;_line_comment_;sexp_comment]))s

and _sientific_form_ s=
  let _e_= word_ci "e" in
    let nt = (caten(caten (disj  _float_ _integer_) (_e_))
              (_integer_)) in
              (pack nt (fun ((h,_),t)->
              let n= match t with
              | Int(x)-> 10.0 ** (float_of_int x)
              |_->raise X_no_match
              in match h with
              |Float(f)->Float(f *. n)
              |Int(f)->Float((float_of_int f)*. n)
              )) s

and _hex_float_ s=make_float_(_hex_sign_,_hex_natural_,_hex_digit_,16.0) s
and _char_prefix_ s=(word "#\\") s
and _visable_simple_ s=(diff nt_any nt_whitespace) s
and _named_char_ s= (disj_list [pack(word_ci "nul")(fun x->(char_of_int 0));
                            pack(word_ci "newline")(fun x->(char_of_int 10));
                            pack(word_ci "return")(fun x-> (char_of_int 13));
                            pack(word_ci "tab")(fun x->(char_of_int 9));
                            pack (word_ci "page") (fun x->  (char_of_int 12));
                            pack (word_ci "space") (fun x->  (char_of_int 32))
                            ]) s
and _hex_char_ s= (pack (caten (char_ci 'x') (plus _hex_digit_)) (fun (_,y)->(char_of_int (char_list_int y 16)))) s
and _char_ s=(allow_space (pack(caten (_char_prefix_) (disj_list[_named_char_;_hex_char_;_visable_simple_]))(fun (x,y)-> Char(y))) ) s
and _string_literal_char_ s = (guard nt_any (fun x->match x with
                                            |'\"'->false
                                            |'\\'->false
                                            |_->true
                                            )) s
and _string_meta_char_ s= (disj_list [pack(word_ci "\\nul")(fun x->(char_of_int 0));
                               pack(word_ci "\\r")(fun x->(char_of_int 13));
                               pack(word_ci "\\n")(fun x->(char_of_int 10));
                               pack(word_ci "\\t")(fun x->(char_of_int 9));
                               pack(word_ci "\\f")(fun x->(char_of_int 12));
                               pack(word_ci "\\\\")(fun x->(char_of_int 92));
                               pack(word_ci "\\\"")(fun x->(char_of_int 34))
                              ]) s
and _string_hex_char_ s= (pack(caten_list[(word_ci"\\x");
                                  pack(plus _hex_digit_)
                                  (fun x->let n=char_list_int x 16 in
                                              [char_of_int n]
                                  )
                                  ;word ";"]
                            )
                            (fun x->List.hd (List.nth x 1))) s

and _string_ s= (allow_space (pack (caten_list[(pack (char '\"') (fun x->[x]));
star(disj_list [_string_literal_char_;_string_meta_char_;_string_hex_char_]);
(pack (char '\"')(fun x->[x])) ])
(fun x-> String(list_to_string( List.nth x 1)))) ) s

(*and _make_list_ ntlp ntrp ntsexpr s= (pack(caten(caten( (allow_space ntlp ))(star ntsexpr))(allow_space ntrp))(fun ((_,x),_)->(List.fold_right (fun a b-> Pair(a,b))x Nil ))) s*)


and make_list ntlp ntrp ntsexpr  s = let list_tail  = pack(ntrp)(fun x->None) in
                         let dotted_tail=(pack(caten(caten(allow_space(pack (char '.')(fun x->Char('.'))))ntsexpr)(ntrp))(fun ((_,sexpr),_)->Some(sexpr)))in
                         let list_hd  = (pack(caten (ntlp)(star ntsexpr )) (fun (_,hd)->hd))
                            in pack(caten list_hd (disj list_tail dotted_tail)) (fun (hd,tl)->let last=(match tl with
                                                                                      |None->Nil
                                                                                      |Some(sexpr)-> (match hd with
                                                                                                      |[]->raise X_no_match
                                                                                                      |_->sexpr
                                                                                                      )
                                                                                      )
                                                                                      in (List.fold_right (fun a b-> Pair (a,b)) hd last)
                                                                        ) s


and unbalanced_list s = let list_tail  =pack(nt_epsilon)(fun x->None) in
                         let dotted_tail=(pack(caten(allow_space(pack (char '.')(fun x-> Char('.'))))_unbalanced_sexprs)(fun (_,sexpr)->Some(sexpr)))in
                         let list_hd  = (pack(caten (all_left_brackets)(star _unbalanced_sexprs )) (fun (_,hd)->hd))
                            in pack(caten list_hd (disj dotted_tail list_tail)) (fun (hd,tl)->let last=(match tl with
                                                                                      |None->Nil
                                                                                      |Some(sexpr)-> (match hd with
                                                                                                      |[]->raise X_no_match
                                                                                                      |_->sexpr
                                                                                                      )
                                                                                      )
                                                                                      in (List.fold_right (fun a b-> Pair (a,b)) hd last)
                                                                                      ) s


and pack_balanced_ _lst_= (allow_space(pack (caten _lst_ (maybe (allow_space (pack (word "...") (fun x->String "...")) )  )) (fun (l,_)->l)))
and all_left_brackets s=(disj (allow_space(pack (char '(') (fun x-> Char( '(')))) (allow_space(pack (char '[') (fun x-> Char( '['))))) s
(*and unbalanced_list s= (allow_space(pack (caten all_left_brackets (star _unbalanced_sexprs ))
                    (fun (_,s2)->(List.fold_right (fun a b-> Pair(a,b))s2 Nil ))))s*)



and _balanced_list_ s = (allow_space(disj  (make_list (allow_space(pack (word "(") (fun x->String ("(")))) (allow_space(pack (word ")") (fun x-> String(")"))))_balanced_sexprs_)
                              (make_list (allow_space(pack (word "[")(fun x-> String("[")))) (allow_space(pack (word "]") (fun x-> String("]"))))_balanced_sexprs_ )))s
(*and _balancd_list_ s = (disj(_make_list_(pack (char '(') (fun x->Char('('))) (pack (char ')') (fun x->Char(')'))) _balanced_sexprs_)
             (_make_list_ (pack (char '[') (fun x->Char('['))) (pack (char ']') (fun x->Char(']')))_balanced_sexprs_)) s
*)
and _real_list_ s =   (allow_space(disj ( pack_balanced_ _balanced_list_)
                      (make_list (disj (allow_space(pack (word "(") (fun x-> String("(")))) (allow_space(pack(word "[") (fun x->String("["))))) (allow_space(pack (word "...") (fun x-> String("..."))))
                       _unbalanced_sexprs))) s (*(disj (pack_balanced_ _balanced_list_) (_make_list_
                              (disj (pack (char '(') (fun x-> Char('('))) (pack (char '[') (fun x->Char('['))))
                              (pack (word "...") (fun x-> String("...")))
                               _unbalanced_sexprs)) s*)
(*and make_dotted_list_ lp rp ntsexpr s=
        (pack(caten (allow_space lp) (caten (plus ntsexpr)( caten (allow_space (pack(word ".") (fun x-> Char('.')))) (caten (ntsexpr) (allow_space rp)))))
        (fun  ( _ ,(x , (_, (y , _))))->List.fold_right (fun a b -> Pair (a,b)) x y ))s
        *)

        (*
        and balance_dotted_list s=  (disj (make_dotted_list_ (pack (char '(') (fun x->Char('('))) (pack (char ')') (fun x->Char(')')))_balanced_sexprs_)
                            (make_dotted_list_ (pack (char '[') (fun x->Char('['))) (pack (char ']') (fun x->Char(']')))_balanced_sexprs_) ) s

and _real_list_dott s=
 (allow_space(disj (pack_balanced_ balance_dotted_list) (make_dotted_list_
                              all_left_brackets
                              (pack (word "...") (fun x-> String("...")))
                               _unbalanced_sexprs))) s

and unbalanced_dot s=  (allow_space(pack(caten  all_left_brackets
  (caten (plus _unbalanced_sexprs)(caten  (allow_space (pack  (word ".") (fun x-> String(".")))) _unbalanced_sexprs) ))
        (fun  ( _ ,(x , (_, y)))->List.fold_right (fun a b -> Pair (a,b)) x y ))) s
        *)
and _balance_vector_ s =
 (pack (caten
    (allow_space(pack (word "#(") (fun x->String("#("))))
    (caten
      (star _balanced_sexprs_)
      (allow_space(pack (char ')') (fun x->Char(')'))))))
 (fun (_,(x,_))-> Vector(x))
  )s

and _unbalance_vector_ s =
 (pack (caten
    (allow_space(pack (word "#(") (fun x->String("#("))))
      (star _unbalanced_sexprs)
    )
 (fun (_,x)-> Vector(x)))s

 and real_vector s=(disj (pack_balanced_ _balance_vector_)
   (pack (caten
    (allow_space(pack (word "#(") (fun x->String("#("))))
    (caten (star _unbalanced_sexprs)  (word_ci "...")))
  (fun (_,(x,_))->Vector(x))))s

and _make_quote_ (nt,name) s= (allow_space(pack (caten (nt) (read_sexprs_helper)) (fun (_, s) ->Pair(Symbol(name),Pair(s,Nil))))) s
and _quoted_ s= _make_quote_(word "\'","quote")s
and _quasiQuoted_ s= _make_quote_(word "`","quasiquote")s
and _unquoteAndSpliced_ s= _make_quote_(word",@","unquote-splicing")s
and _unquoted_ s=_make_quote_(word ",","unquote")s;;

let read_sexpr string =   fst((pack (caten (allow_space(read_sexprs_helper)) nt_end_of_input) (fun (x,y)->x)) (string_to_list string));;

let read_sexprs string = fst ((pack(caten (allow_space (pack(star(read_sexprs_helper))(fun x->Vector(x))))(nt_end_of_input)) (fun (x,_)->match x with
  |Vector(x)->x
  |_->raise X_no_match)) (string_to_list string));;

end;; (* struct Reader *)
