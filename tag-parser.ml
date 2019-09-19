(* tag-parser.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "reader.ml";;
 type constant =
 | Sexpr of sexpr
 | Void
 type expr =
 | Const of constant
 | Var of string
 | If of expr * expr * expr
 | Seq of expr list
 | Set of expr * expr
 | Def of expr * expr
 | Or of expr list
 | LambdaSimple of string list * expr
 | LambdaOpt of string list * string * expr
 | Applic of expr * (expr list);;



 let rec for_all2 p l1 l2 =
  match (l1, l2) with
    ([], []) -> true
  | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
  | (_, _) -> false

 let rec expr_eq e1 e2 =
 match e1, e2 with
 | Const Void, Const Void -> true
 | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
 | Var(v1), Var(v2) -> String.equal v1 v2
 | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
 (expr_eq th1 th2) &&
 (expr_eq el1 el2)
 | (Seq(l1), Seq(l2)
 | Or(l1), Or(l2)) -> for_all2 expr_eq l1 l2
 | (Set(var1, val1), Set(var2, val2)
 | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
 (expr_eq val1 val2)
 | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) -> (for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
 | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->(String.equal var1 var2) && (for_all2 String.equal vars1 vars2) &&
 (expr_eq body1 body2)
 | Applic(e1, args1), Applic(e2, args2) ->(expr_eq e1 e2) && (for_all2 expr_eq args1 args2)
 | _ -> false;;
 exception X_syntax_error;;
 module type TAG_PARSER = sig
 val tag_parse_expression : sexpr -> expr
 val tag_parse_expressions : sexpr list -> expr list
 end;; (* signature TAG_PARSER *)
 module Tag_Parser : TAG_PARSER = struct
 let reserved_word_list =
 ["and"; "begin"; "cond"; "define"; "else";
 "if"; "lambda"; "let"; "let*"; "letrec"; "or";
 "quasiquote"; "quote"; "set!"; "unquote";
 "unquote-splicing"];;
 (* work on the tag parser starts here *)



let whatever=Reader.read_sexpr "'whatever";;
let rec tag_parse sexpr= match sexpr with
(*const*)
| Bool _
| Char _
| Number _
| String _->Const(Sexpr sexpr)
| Pair(Symbol("quote"),Pair(x,Nil))->Const(Sexpr x)
|Pair(Symbol("quasiquote"),Pair(sexp,Nil))->tag_parse (expand_qq sexp)
(*var*)
| Symbol(x) ->if(reserved_word x) then raise X_syntax_error else Var(x)
(*if*)
| Pair(Symbol("if"),Pair(test,Pair(dit,dif)))->(match dif with
 |Nil->If(tag_parse test,tag_parse dit,Const(Void))
 |Pair(dif,Nil)->If(tag_parse test,tag_parse dit,tag_parse dif)
 |_->raise X_syntax_error)


|Pair(Symbol("cond"),expr)->(match expr with
 |Pair(Pair(Symbol("else"),body),rest)->(match rest with
 |Nil->tag_parse (Pair(Symbol("begin"),body))
 |_->raise X_syntax_error)
 |Pair(Pair(test, Pair(Symbol("=>"),Pair(body,Nil))),rest)->
 (match rest with
 |Nil->
 let _rest_=Nil
 in tag_parse (Pair(Symbol("let"),Pair(Pair(Pair(Symbol("value"),Pair(test,Nil)),
 Pair(Pair(Symbol("f"),Pair(Pair(Symbol("lambda"),Pair(Nil,Pair(body,Nil))),Nil)),Nil)),Pair
 (Pair(Symbol("if"),Pair(Symbol("value"),Pair(Pair(Pair(Symbol("f"),Nil),Pair(Symbol("value"),Nil)),Nil))),Nil))))


 |_->let _rest_ =Pair(Symbol("cond"),rest) in
 tag_parse( Pair(Symbol("let"),Pair(Pair(Pair(Symbol("value"),Pair(test,Nil)),
 Pair(Pair(Symbol("f"),Pair(Pair(Symbol("lambda"),Pair(Nil,Pair(body,Nil))),
 Nil)),Pair(Pair(Symbol("rest"),Pair(Pair(Symbol("lambda"),Pair(Nil,Pair(_rest_,Nil))),
 Nil)),Nil))),Pair(Pair(Symbol("if"),Pair(Symbol("value"),Pair(Pair(Pair(Symbol("f"),Nil),
 Pair(Symbol("value"),Nil)),Pair(Pair(Symbol("rest"),Nil),Nil)))),Nil)))))


 |Pair(Pair(test,body),rest)->
 let _rest_=(match rest with
 |Nil->rest
 |_->Pair(Pair(Symbol("cond"),rest),Nil))
 in tag_parse(Pair(Symbol("if"), Pair(test,Pair(Pair(Symbol("begin"), body),_rest_))))
 |_->raise X_not_yet_implemented
 )
 (*seq*)
| Pair(Symbol("begin"),exprs_list)->(let exprs=pair_to_list exprs_list in
 let expr_list =(List.map tag_parse exprs)
 in (match List.length expr_list with
 | 0 -> Const(Void)
 | 1 -> (List.hd expr_list)
 | _ -> Seq(expr_list)))

| Pair(Symbol("lambda"),Pair(params,body))->(match is_proper_list params with
 |false ->(match params with
 |Symbol(vs)->let _body_=_lambdabody_ body in
 LambdaOpt([],vs,_body_)
 |_->(match (is_improper_list params) with
 |false->raise X_syntax_error
 |true -> let rec pairs_to_list p = (match p with
 |Pair(Symbol(x),Symbol(y))->[x]
 |Pair(Symbol(x),(Pair(_,_) as next))->x::(pairs_to_list next)
 |_->raise X_syntax_error)
 in let rec last p =(match p with
 |Pair(Symbol(x),Symbol(y))->y
 |Pair(Symbol(_),(Pair(_,_)as next))->last next
 |_->raise X_syntax_error)
 in let param_list=pairs_to_list params
 in let _last_=last params
 in let lst=_last_::param_list
 in
 (match(duplicate String.compare lst) with
 |true->raise X_syntax_error
 |false -> let _body_= _lambdabody_ body in
 LambdaOpt( param_list,_last_ ,_body_))))
 |true -> let _params_=pair_to_list params
 in let _params_=(List.map (fun x-> match x with
 |Symbol(x)->x
 |_->raise X_syntax_error)_params_)
 in
 let duplicate_var=duplicate String.compare _params_
 in (match duplicate_var with
 |true->raise X_syntax_error
 |false->let _body_=_lambdabody_ body
 in LambdaSimple(_params_,_body_)
 )
 )



| Pair(Symbol("let"),Pair(ribs,body))->
 let bindings= pair_to_list ribs in
 let vars=(List.map
 (fun binding-> match binding with
 | Pair(var,Pair(_,Nil))-> var
 | _ -> raise X_syntax_error) bindings)
 in let values=(List.map (fun binding->match binding with
 | Pair(_,Pair(value,Nil))-> value
 | _ -> raise X_syntax_error)bindings)
 in tag_parse(Pair(Pair(Symbol("lambda"),Pair((list_to_pair vars),body)),(list_to_pair values)))



|Pair(Symbol("let*"),Pair(ribs,body))->
 (match ribs with
 |Nil
 |Pair(Pair(_,_),Nil)->tag_parse (Pair(Symbol("let"),Pair(ribs,body)))
 |_->(
 let bindings= pair_to_list ribs in
 (match bindings with
 |[]->raise X_syntax_error
 |_->let _body_=(Pair(Symbol("let*"),Pair(list_to_pair(List.tl bindings),body)))
 in tag_parse (Pair(Symbol("let"),Pair((list_to_pair[List.hd bindings]),Pair(_body_,Nil))))
 )))




|Pair(Symbol("letrec"),Pair(ribs,body))->
 let bindings= pair_to_list ribs in
 let vars=(List.map
 (fun binding-> match binding with
 | Pair(var,Pair(_,Nil))-> var
 | _ -> raise X_syntax_error) bindings)
 in let values=(List.map (fun binding->match binding with
 | Pair(_,Pair(value,Nil))-> value
 | _-> raise X_syntax_error)bindings)in
 let let_bindings=(List.map(fun x-> Pair(x,Pair(whatever,Nil))) vars) in
 let _body_=(List.map2( fun var value->Pair(Symbol("set!"),Pair(var,Pair(value,Nil)))) vars values) in
 tag_parse (Pair(Symbol("let"),Pair((list_to_pair let_bindings),((list_to_pair (List.append _body_ (pair_to_list body )))))))


(*set*)
| (Pair(Symbol("set!"),(Pair((Symbol(_)as var),Pair(value,Nil)))))->Set(tag_parse var,tag_parse value)
(*seq or*)
| Pair(Symbol("or"),variables)->
 let expr_lst=pair_to_list variables in
 let expr_list=List.map tag_parse expr_lst in
 (match expr_list with
 |[]->tag_parse(Bool(false))
 |[x]->x
 |_->Or(expr_list))

 | Pair(Symbol("and"),variables)->
 (match variables with
 |Nil-> tag_parse (Bool(true))
 |Pair(expr,Nil)-> tag_parse(expr)
 |Pair(expr1,(Pair(_,_) as next))-> tag_parse (Pair(Symbol("if"),Pair(expr1,Pair(Pair(Symbol("and"),next),Pair(Bool(false),Nil)))))
 |_->raise X_syntax_error)


|Pair(Symbol("define"),Pair((Symbol(_))as name,Pair(expr,Nil)))->Def(tag_parse name,tag_parse expr)
|Pair(Symbol("define"),Pair(lst,expr))->(match lst with
|Pair((Symbol(_))as name,(Symbol(_) as args))
|Pair((Symbol(_)as name),args)->tag_parse(Pair(Symbol("define"),Pair(name,Pair(Pair(Symbol("lambda"),Pair(args,expr)), Nil))))
|_->raise X_syntax_error)
(*application*)
| Pair(rator,rands)->
 (match (is_proper_list rands) with
 | false ->raise X_syntax_error
 | true -> let rands=pair_to_list rands in
 Applic(tag_parse rator,List.map tag_parse rands)
 )
|_ ->raise X_not_yet_implemented

and reserved_word w= List.mem w reserved_word_list



and _lambdabody_ body=let _body_=List.map tag_parse (pair_to_list body) in
 (match(is_proper_list body) with
 |false -> raise X_syntax_error
 |true->let _body_= (match _body_ with
 |[]->raise X_syntax_error
 |[x]->x
 |_->Seq(_body_)) in _body_ )

and pair_to_list p = match p with
 |Nil->[]
 |Pair(x,Nil)->[x]
 |Pair(x,y)->x::(pair_to_list y)
 |_->raise X_syntax_error

and list_to_pair lst= List.fold_right (fun a b-> Pair(a,b)) lst Nil
and is_proper_list pairs= match pairs with
 |Nil->true
 |Pair(_,cdr)->is_proper_list cdr
 |_->false
and is_improper_list pairs= match pairs with
 |Pair(x,y)->not (is_proper_list y)
 |_->false

and duplicate cmp lst = let tmp_list =List.sort cmp lst in
 let rec helper lst = match lst with
 |[]->false
 |[x]->false
 |x::((y::tail) as rest)->if x=y then true else helper rest
 in helper tmp_list

and expand_qq sexpr=(match sexpr with
 | Bool _
 | Char _
 | Number _
 | String _->sexpr
 |Pair(Symbol("unquote"), Pair(sexpr, Nil))->sexpr
 |Pair(Symbol("unquote-splicing"),Pair(sexp, Nil))->raise X_syntax_error
 |Nil->Pair(Symbol("quote"),Pair(Nil,Nil))
 |Symbol(x)as s->Pair(Symbol("quote"),Pair(s,Nil))
 |Vector(v)->Pair(Symbol("vector"),list_to_pair((List.map expand_qq v)))
 |Pair(car,cdr)->(match car with
 |Pair(Symbol("unquote-splicing"),Pair(sexp,Nil))->Pair(Symbol("append"),Pair( sexp,Pair((expand_qq cdr),Nil)))
 |_->(match cdr with
 |Pair(Symbol("unquote-splicing"),Pair (sexp,Nil))->Pair(Symbol("cons"), Pair((expand_qq car),Pair(sexp,Nil)))
 |_->Pair(Symbol("cons"),Pair((expand_qq car),Pair((expand_qq cdr),Nil))))));;
 let tag_parse_expression sexpr =tag_parse sexpr;;

let tag_parse_expressions sexpr =List.map tag_parse sexpr;;

end;; (* struct Tag_Parser *)
