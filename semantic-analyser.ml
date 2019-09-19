(* tag-parser.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "tag-parser.ml";;

 type var =
   | VarFree of string
   | VarParam of string * int
   | VarBound of string * int * int;;

 type expr' =
   | Const' of constant
   | Var' of var
   | Box' of var
   | BoxGet' of var
   | BoxSet' of var * expr'
   | If' of expr' * expr' * expr'
   | Seq' of expr' list
   | Set' of expr' * expr'
   | Def' of expr' * expr'
   | Or' of expr' list
   | LambdaSimple' of string list * expr'
   | LambdaOpt' of string list * string * expr'
   | Applic' of expr' * (expr' list)
   | ApplicTP' of expr' * (expr' list);;


   let rec for_all2 p l1 l2 =
    match (l1, l2) with
      ([], []) -> true
    | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
    | (_, _) -> false

 let rec expr'_eq e1 e2 =
   match e1, e2 with
   | Const' Void, Const' Void -> true
   | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
   | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
   | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
   | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
   | Box' (VarFree v1), Box' (VarFree v2) | BoxGet' (VarFree v1), Box' (VarFree v2) ->  String.equal v1 v2
   | Box' (VarParam (v1,mn1)), Box' (VarParam (v2,mn2))
   | BoxGet' (VarParam (v1,mn1)), BoxGet' (VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
   | Box' (VarBound (v1,mj1,mn1)), Box' (VarBound (v2,mj2,mn2))
   | BoxGet' (VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2))-> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2

   | BoxSet'(VarFree v1, e1), BoxSet'(VarFree v2, e2) -> expr'_eq e1 e2 && String.equal v1 v2
   | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2), e2) -> expr'_eq e1 e2 && String.equal v1 v2 && mn1 = mn2
   | BoxSet'(VarBound (v1,mj1,mn1), e1), BoxSet'(VarBound (v2,mj2,mn2), e2) ->
     expr'_eq e1 e2 && String.equal v1 v2 && mj1 = mj2  && mn1 = mn2

   | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                             (expr'_eq th1 th2) &&
                                               (expr'_eq el1 el2)
   | (Seq'(l1), Seq'(l2)
   | Or'(l1), Or'(l2)) -> for_all2 expr'_eq l1 l2
   | (Set'(var1, val1), Set'(var2, val2)
   | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                              (expr'_eq val1 val2)
   | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
      (for_all2 String.equal vars1 vars2) &&
        (expr'_eq body1 body2)
   | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (for_all2 String.equal vars1 vars2) &&
          (expr'_eq body1 body2)
   | Applic'(e1, args1), Applic'(e2, args2)
   | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
    (expr'_eq e1 e2) &&
      (for_all2 expr'_eq args1 args2)
   | _ -> false;;
 exception X_syntax_error;;
 module type SEMANTICS = sig
   val run_semantics : expr -> expr'
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
 end;;
 module Semantics : SEMANTICS = struct
   let rec lexical_address params env expr  =match expr with
           |Const(e)->Const'(e)
           |Var(name)->Var'((match (find_var_params params name) with
                     |Some(num)->VarParam(name,num)
                     |None->(match (find_var_env env name) with
                           |Some((major,minor))->VarBound(name,major,minor)
                           |None->VarFree(name) )))
           |Or(e)->Or'(List.map (lexical_address params env) e)
           |If(test,dit,dif)->If'(lexical_address params env test,lexical_address params env dit,lexical_address params env dif)
           |Def(var ,valu)-> Def'(lexical_address params env var, lexical_address params env valu)
           |Set(var,expr)->Set'(lexical_address params env var,lexical_address params env expr)
           |Seq(e)->Seq'(List.map (lexical_address params env) e)
           |Applic(operator, args)->Applic'(lexical_address params env operator,List.map (lexical_address params env) args)
           |LambdaSimple(lambda_params,body)->LambdaSimple'(lambda_params,lexical_address lambda_params  (List.cons params  env ) body)
           |LambdaOpt(lambda_params,opt , body)->LambdaOpt'(lambda_params, opt,lexical_address (List.append lambda_params [opt])(List.cons params env) body)
   and find_var_params  params_list name =let rec helper lst acc=(match lst with
                                                       |[]->None
                                                       |car::cdr->if (car=name) then (Some(acc)) else helper cdr (acc + 1)
                                                       )in helper params_list 0
   and find_var_env env name= let rec helper lst major=
                                       (match lst with
                                       |[]->None
                                       |car::cdr->let x=(find_var_params car name) in
                                       (match x with
                                                     |None->helper cdr(major+1)
                                                     |Some(minor)->Some(major,minor)))
                                       in helper env 0;;
 let annotate_lexical_addresses e = lexical_address [] [] e ;;
 let rec tail_call_annotate in_tp expr = match expr with
 |Const'(_)as exp->exp
 |Var'(_)as exp->exp
 |If'(test,dit,dif)->If'(tail_call_annotate false test,tail_call_annotate in_tp dit,tail_call_annotate in_tp dif)
 |Seq'(exp)->let rec helper lst=(match lst with
                       |[x]->[(tail_call_annotate in_tp x)]
                       |car::cdr->(tail_call_annotate false car )::(helper cdr)
                       |_->raise X_syntax_error)
                       in  Seq'(helper exp)
 |Set'(name,exp)->Set'(name,tail_call_annotate false exp)
 |Def'(name,exp)->Def'(name,tail_call_annotate false exp)
 |Or' (exp)->let rec helper lst=(match lst with
                       |[x]->[(tail_call_annotate in_tp x)]
                       |car::cdr->(tail_call_annotate false car)::(helper cdr)
                       |_->raise X_syntax_error)
                       in  Or'(helper exp)
 | LambdaSimple'(name,body)->LambdaSimple'(name,tail_call_annotate true body)
 | LambdaOpt'(name,name2,body)->LambdaOpt'(name,name2,tail_call_annotate true body)
 | Applic'(exp,body)->(match in_tp with
                       |true->ApplicTP'(tail_call_annotate false exp,(List.map (tail_call_annotate false)body))
                       |false->Applic'(tail_call_annotate false exp,(List.map (tail_call_annotate false)body)))
 |_->raise X_syntax_error

 let annotate_tail_calls e = tail_call_annotate false e;;
   type expr2' =
    | Const2' of constant
    | Var2' of var
    | Box2' of var
    | BoxGet2' of var
    | BoxSet2' of var * expr2'
    | If2' of expr2' * expr2' * expr2'
    | Seq2' of expr2' list
    | Set2' of expr2' * expr2'
    | Def2' of expr2' * expr2'
    | Or2' of expr2' list
    | LambdaSimple2' of int * string list * expr2'
    | LambdaOpt2' of int * string list * string * expr2'
    | Applic2' of expr2' * (expr2' list)
    | ApplicTP2' of expr2' * (expr2' list);;
    let rec convert_exp1_exp2 exp= let rec helper index exp=
                              (match exp with
                              |LambdaSimple'(param,exp)->let i=(!index) in index:=i+1; LambdaSimple2'(i,param,helper index exp)
                              |LambdaOpt'(param,opt,body)->let i=(!index) in index:=i+1 ;LambdaOpt2'(i,param,opt,helper index body)
                              |Const'(x)->Const2'(x)
                              |Var'(x)-> Var2'(x)
                              |Box'(x)-> Box2'(x)
                              |BoxGet'(x)->BoxGet2'(x)
                              |BoxSet'(x,y)->BoxSet2'(x,helper index y)
                              |If'(t,dit,dif)-> If2'(helper index t, helper index dit,helper index dif)
                              |Seq'(exprs)->Seq2'(List.map (fun x->helper index x) exprs)
                              |Set'(x, y)-> Set2'(helper index x, helper index y)
                              |Def'(x, y)-> Def2'(helper index x, helper index  y)
                              |Or'(x)-> Or2'(List.map (fun x->helper index x) x)
                              |Applic'(op,exp)->Applic2'(helper index op,List.map (fun x-> helper index x) exp)
                              |ApplicTP'(op,exp)->ApplicTP2'(helper index op,List.map (fun x-> helper index x) exp)
                              )
                              in let i=ref 0 in helper  i exp
    and is_get param body= let rec helper param body =
                    (match body with
                    |LambdaSimple2'(lambda_index,params , body)-> (match (List.mem param params) with
                    |true->[]
                    |false->let res =(helper  param body)
                              in (match res with
                              | [] -> []
                              |_ -> [lambda_index]))
                    |LambdaOpt2'(lambda_index,params, params2, body)->(match (List.mem param (List.append params [params2]) ) with
                    |true->[]
                    |false->let res=(helper  param body) in
                      (match res with
                              |[] ->[]
                              |_ -> [lambda_index]))
                    |Var2'(VarBound(para, maj, min))->(match (para=param) with
                                  |true-> [-1]
                                  |false->[])
                    |Var2'(VarParam(para, maj))->(match (para=param) with
                                  |true -> [-1]
                                  |false ->[])
                    |Set2'(Var2'(VarBound(para, maj, min)), expr)->(helper  param expr )
                    |Set2'(Var2'(VarParam(para, maj)), expr)-> (helper  param expr )
                    |Set2'(Var2'(VarFree(_)) , expr)-> (helper param expr)
                    |Set2'(exp,_)->raise  X_syntax_error
                    |BoxSet2'(var ,exp )-> (helper  param exp)
                    |If2'(test , dit, dif)-> ( helper  param test )@(helper  param dit )@( helper  param dif)
                    |Seq2'(exprs)->  List.fold_left (fun acc cur-> acc@(helper  param  cur )) [] exprs
                    |Def2'(var , valu)->(helper  param valu)
                    |Or2'(exprs)-> List.fold_left (fun acc cur-> acc@(helper  param  cur)) [] exprs
                    |Applic2'(op ,body)
                    |ApplicTP2'(op ,body)-> let first=(helper param op) in  List.fold_left (fun acc cur-> acc@(helper  param  cur)) first body
                    |Const2' _ | Box2' _ | BoxGet2' _ |Var2'(VarFree(_)) ->[])
                   in  helper param body
	and product' l1 l2 =
                     List.concat(List.map (fun x->List.map (fun y->(x,y))l2)l1)
	and is_set param body = let rec helper param body =
                    (match body with
                    |LambdaSimple2'(lambda_index,params , body)-> (match (List.mem param params) with
                    |true->[]
                    |false->let res =(helper  param body)
                              in (match res with
                              | [] -> []
                              |_ -> [lambda_index]))
                    |LambdaOpt2'(lambda_index,params, params2, body)->(match (List.mem param (List.append params [params2]) ) with
                    |true->[]
                    |false->let res=(helper param body) in
                      (match res with
                              | [] -> []
                              |_ -> [lambda_index]))
                    |Set2'(Var2'(VarBound(para, _, _)), expr)->(match para=param with
                                                                  |true->[-1]
                                                                  |false->helper param expr
                                                                  )
                    |Set2'(Var2'(VarParam(para, _)), expr)->(match para=param with
                                                                |true-> [-1]
                                                                |false->helper param expr
                                                              )
                    |Set2'(var , exp)->(helper param exp )
                    |BoxSet2'(var ,exp )->(helper param exp )
                    |If2'(test , dit, dif)-> ( helper  param test )@(helper  param dit )@( helper  param dif )
                    |Seq2'(exprs)->  List.fold_left (fun acc cur-> acc@(helper  param  cur )) [] exprs
                    |Def2'(var , valu)->(helper  param valu)
                    |Or2'(exprs)-> List.fold_left (fun acc cur-> acc@(helper  param  cur )) [] exprs
                    |Applic2'(op ,body)
                    |ApplicTP2'(op ,body)-> let first=(helper param op ) in  List.fold_left (fun acc cur-> acc@(helper  param  cur )) first body
                    |Const2' _ |Var2' _ |Box2' _ |BoxGet2' _ ->[])
                   in  helper param body
	and is_box var body=  let rec remove_duplicate lst =(match lst with
                                                      | a :: (b :: _ as t) -> if a = b then remove_duplicate t else a :: remove_duplicate t
                                                      | smaller -> smaller)
                      in
                      let is_get_list=is_get var body in
                      let is_set_list= is_set var body
                          in let remove_set=remove_duplicate(List.sort (fun x y-> x - y) is_set_list)
                      in let remove_get= remove_duplicate(List.sort (fun x y -> x - y) is_get_list) in
                      let product= product' remove_get remove_set
                      in let res= List.filter (fun (x,y)-> x<>y) product
                      in (match (List.length res) with
                         |0->false
                         |_->true
                         )
and box_helper exp = let rec helper exp env =(match exp with
                                           |Const2' _->exp
                                           |Box2' _->exp
                                           |BoxGet2' _->exp
                                           |Var2'(VarFree(_))->exp
                                           |Var2'(x)-> (match x with
                                                                 |VarBound(n,_,_)as var->(let is_box =(find_var_env env n) in
                                                                                     (match is_box with
                                                                                             |Some(false)->exp
                                                                                             |Some(true)->BoxGet2'(var)
                                                                                             |None->raise X_syntax_error
                                                                                     )
                                                                                   )
                                                                 | (VarParam(n,_)as var)->(let is_box =(find_var_env env n) in
                                                                                           (match is_box with
                                                                                                   |Some(false)->exp
                                                                                                   |Some(true)->BoxGet2'(var)
                                                                                                   |None->raise X_syntax_error
                                                                                           )
                                                                                         )
                                                                 |_->raise X_syntax_error
                                                                 )
                                           |Set2'(name,value)->(match name with
                                                                 |(Var2'((VarBound(n, _,_))as var) as var_all)->(let is_box=(find_var_env env n) in
                                                                                                   (match is_box with
                                                                                                           |Some(false)->Set2'(var_all,(helper value env))
                                                                                                           |Some(true)->BoxSet2'(var,helper value env  )
                                                                                                           |None->raise X_syntax_error))
                                                                 |(Var2'((VarParam(n ,_)) as var)as var_all)->(let is_box= (find_var_env env n) in
                                                                                                   (match is_box with
                                                                                                           |Some(false)-> Set2'(var_all,(helper value env))
                                                                                                           |Some(true)->BoxSet2'(var, helper value env )
                                                                                                           |None->raise X_syntax_error ))
                                                                 |(Var2'(VarFree(n))as set_nme)->Set2'(helper set_nme env,helper value env)
                                                                 |_->raise X_syntax_error
                                                                 )
                                           |BoxSet2'(name,value)->BoxSet2'(name,helper value env)
                                           |If2'(test,dit,dif)->If2'(helper test env,helper dit env,helper dif env)
                                           |Seq2'(exprs)->Seq2'(List.map (fun x->helper x env) exprs)
                                           |Or2'(exprs)->Or2'(List.map (fun x->helper x env) exprs)
                                           |Def2'(name,value)->Def2'(helper name env,helper value env)
                                           |LambdaSimple2'(index,args,body)->(let params=(List.map(fun x->(x,is_box x body)) args)  in
                                                                       let box_params=List.mapi( fun i x->(i,x)) params in
                                                                       let box_params=List.filter (fun (_,(_,boolean))->boolean) box_params in
                                                                       let box_params= List.map(fun (minor,(v,_))->
                                                                       Set2'(Var2'(VarParam(v, minor)), Box2'(VarParam(v, minor)))) box_params in
                                              let body=helper body (params::env) in
                                              let body=(match box_params with
                                                       | []->body
                                                       | _->Seq2'(box_params@[body]))
                                             in LambdaSimple2'(index,args,body))
                                           |LambdaOpt2'(index,args,opt,body)->(let params =List.map(fun x->(x,is_box x body)) (args@[opt])in
                                                                           let box_params=List.mapi( fun i x->(i,x)) params in
                                                                           let box_params=List.filter (fun (_,(_,boolean))->boolean) box_params in
                                                                           let box_params= List.map(fun (minor,(v,_))->
                                                                           Set2'(Var2'(VarParam(v, minor)), Box2'(VarParam(v, minor)))) box_params in
                                                                           let body=helper body (params::env) in
                                                                           let body=(match box_params with
                                                                           |[]->body
                                                                           |_-> Seq2'(box_params@[body]))
                                                                            in LambdaOpt2'(index,args,opt,body))
                                           |Applic2'(op,exprs)->Applic2'(helper op env,List.map(fun x-> helper x env) exprs)
                                           |ApplicTP2'(op,exprs)->ApplicTP2'(helper op env,List.map(fun x-> helper x env) exprs)
                                             )
                                             in let exp1 = convert_exp1_exp2 exp in let exp= (helper exp1 [])
                                             in convert_exp2_exp1 exp
and find_var_env env name = let rec helper2 env =
                                                   (match env with
                                                   | []->None
                                                   |car::cdr ->
                                                                       (match (find_rec car name)with
                                                                       | (Some(z) as res) -> res
                                                                       | None->helper2 cdr
                                                                       )
                                                   )
                                                   in helper2 env
and find_rec env name = let rec helper3 env=(match env with
                                           |[]->None
                                           |(car,boolean)::cdr when name=car->Some(boolean)
                                           |car::cdr->helper3 cdr
                                           )
                                           in helper3 env
 and convert_exp2_exp1 exp=
                              (match exp with
                              |LambdaSimple2'(i,param,exp)-> LambdaSimple'(param,convert_exp2_exp1  exp)
                              |LambdaOpt2'(i,param,opt,body)->LambdaOpt'(param,opt,convert_exp2_exp1  body)
                              |Const2'(x)->Const'(x)
                              |Var2'(x)-> Var'(x)
                              |Box2'(x)-> Box'(x)
                              |BoxGet2'(x)->BoxGet'(x)
                              |BoxSet2'(x,y)->BoxSet'(x,convert_exp2_exp1 y)
                              |If2'(t,dit,dif)-> If'(convert_exp2_exp1 t, convert_exp2_exp1 dit,convert_exp2_exp1 dif)
                              |Seq2'(exprs)->Seq'(List.map (fun x->convert_exp2_exp1 x) exprs)
                              |Set2'(x, y)-> Set'(convert_exp2_exp1 x, convert_exp2_exp1 y)
                              |Def2'(x, y)-> Def'(convert_exp2_exp1 x,convert_exp2_exp1  y)
                              |Or2'(x)-> Or'(List.map (fun x->convert_exp2_exp1 x) x)
                              |Applic2'(op,exp)->Applic'(convert_exp2_exp1 op,List.map (fun x-> convert_exp2_exp1 x) exp)
                              |ApplicTP2'(op,exp)->ApplicTP'(convert_exp2_exp1 op,List.map (fun x->convert_exp2_exp1 x) exp)
                              );;
 let box_set e = box_helper e ;;
 let run_semantics expr =
   box_set
     (annotate_tail_calls
        (annotate_lexical_addresses expr));;
 end;;
