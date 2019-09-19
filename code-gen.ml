#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (string * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (string * string)) list -> (string * int) list -> expr' -> string
  val primitive_names_to_labels: (string*string) list
end;;

module Code_Gen : CODE_GEN = struct


  let make_label str= let i=ref 0 in  let label () = ( let index = (!i) in i:=1+(!i);Printf.sprintf"%s%d"str index ) in label;;
  let int_label=make_label "const_int";;
  let float_label=make_label "const_float";;
  let string_label=make_label "const_string";;
  let symbol_label=make_label "const_symbol";;
  let char_label=make_label "const_char";;
  let pair_label=make_label "const_pair";;
  let vector_label=make_label "const_vector";;
  let (exit_if_label,else_label)= (make_label"then",make_label"else");;
  let or_exit=make_label "or_exit";;
  let (extend_env_loop,extend_env_exit)=(make_label"extend_env_loop",make_label"extend_env_exit");;
  let (param_env_loop,param_env_exit)=(make_label"param_env_loop",make_label"param_env_exit");;
  let (lambda_body,lambda_exit)=(make_label "lambda_body",make_label "lambda_exit")
  let lambda_error=make_label "lambda_error"
  let (lambda_opt_body,lambda_opt_exit)=(make_label "lambda_opt_body",make_label "lambda_opt_exit")
  let (extend_env_loop_opt,extend_env_exit_opt)=(make_label"extend_env_loop_opt",make_label"extend_env_exit_opt");;
  let lambda_opt_error=make_label "lambda_opt_error"
  let (param_env_loop_opt,param_env_exit_opt)=(make_label"param_env_loop_opt",make_label"param_env_exit_opt");;
  let (opt_loop_params,opt_loop_exit_params )=(make_label "opt_loop_params",make_label "opt_loop_exit_params" );;
  let done_fixed_opt_params=make_label "done_fixed_opt_params";;
  let fix_opt_loop=make_label "fix_params_loop";;



  let get_label label= label()


  let rec collect_constants asts= let rec collect_const ast =
                        (match ast with
                        |Const'(x)->[x]
                        |Var' _
                        |Box' _
                        |BoxGet' _->[]
                        |BoxSet'(_,exp)->collect_const exp
                        |If'(test,dit,dif)->collect_const test@ collect_const dit @collect_const dif
                        |Set'(_,exp)->collect_const exp
                        |Def'(name,exp)->collect_const name @ collect_const exp
                        |Or'(exprs)
                        |Seq'(exprs)->List.fold_left( fun acc a -> acc@(collect_const a) ) [] exprs
                        |LambdaSimple'(_,body)->collect_const body
                        |LambdaOpt'(_,_,body)->collect_const body
                        |Applic'(op,exprs)
                        |ApplicTP'(op,exprs)->collect_const op@List.fold_left( fun  acc a-> acc@(collect_const a)  ) [] exprs
                          )
                          in let init=[Void;Sexpr(Nil);Sexpr(Bool(false));Sexpr(Bool(true))]
                          in  expand_exprs(remove_duplicate (List.fold_left (fun acc a->acc@(collect_const a)) init asts))
   and const_eq e1 e2=(match e1,e2 with
   |  Void,  Void -> true
   | (Sexpr s1), (Sexpr s2) -> sexpr_eq s1 s2
   | _->false)

   and remove_duplicate lst =let rec remove lst acc =
                          (match lst with
                          |[]->acc
                          |car::cdr->(match (List.exists (const_eq car) acc) with
                                      |true->remove cdr acc
                                      |false->remove cdr (acc@[car])
                                      )
                          )
                          in remove lst []
    and  expand_exprs exprs= let rec expand exp=
    (match exp with
    |Sexpr(expr)->(match expr with
                  |Symbol(x)-> [Sexpr(String(x));exp]
                  |Pair(car,cdr)->(expand (Sexpr(car))) @ (expand (Sexpr(cdr))) @[exp]
                  |Vector(lst)->(List.fold_left (fun acc a-> acc@(expand (Sexpr a)) ) [] lst) @ [exp]
                  |_-> [exp])
    |Void->[Void])
    in remove_duplicate(List.fold_right (fun a acc-> (expand a)@acc) exprs []);;







let first (a,b)=a;;
let calc table item=(match item with
                              |Void->(Printf.sprintf"%s:MAKE_VOID" "const_void","const_void")
                              |Sexpr(item)->(match item with
                                            |Nil->(Printf.sprintf"%s:MAKE_NIL" "const_nil","const_nil")
                                            |Char(c)->let label=get_label char_label in((Printf.sprintf "%s:MAKE_LITERAL_CHAR(%d)" label (int_of_char c), label))
                                            |Number(Int(n))->let label=get_label int_label in((Printf.sprintf "%s:MAKE_LITERAL_INT(%d)"label n),label)
                                            |Number(Float(n))->let label=get_label float_label in ((Printf.sprintf "%s:MAKE_LITERAL_FLOAT(%f)"label n),label)
                                            |String(s)->let label=get_label string_label in let str_lst=string_to_list s in let len=List.length str_lst in
                                            let s=(List.fold_left (fun (acc,index) cur ->(match index=(len-1) with
                                                                                  |true-> (acc^(Printf.sprintf"%d"(int_of_char cur)),index+1)
                                                                                  |false->(acc^(Printf.sprintf"%d, "( int_of_char cur)),index+1)))  ("",0) str_lst) in ((Printf.sprintf "%s:MAKE_LITERAL_STRING %s"label (first s)), label)
                                            |Bool(false)->(Printf.sprintf "%s:MAKE_BOOL(%d)"("bool_false") 0, "bool_false")
                                            |Bool(true)->(Printf.sprintf "%s:MAKE_BOOL(%d)""bool_true" 1, "bool_true")
                                            |Symbol(x)->let label= get_label symbol_label in (Printf.sprintf ("%s:MAKE_LITERAL_SYMBOL(%s)")(label)(first(List.assoc (Sexpr(String(x))) table)),label)
                                            |Pair(car,cdr)->let label= get_label pair_label in (Printf.sprintf("%s:MAKE_LITERAL_PAIR(%s,%s)")
                                            (label)
                                            (first(List.assoc(Sexpr(car)) table ))
                                            (first(List.assoc(Sexpr(cdr)) table))
                                            ,label)
                                            |Vector(lst)->let label= get_label vector_label in let len=List.length lst in(first(List.fold_left(fun (acc,index) cur->
                                                                                                      (match index=(len-1) with
                                                                                                      |true->(acc^(Printf.sprintf"%s")(first(List.assoc(Sexpr(cur))table)),index+1)
                                                                                                      |false->(acc^(Printf.sprintf"%s, ")(first(List.assoc(Sexpr(cur))table )),index+1)
                                                                                                      )
                                              ) (Printf.sprintf"%s:MAKE_LITERAL_VECTOR "label,0)(lst)),label)
                                            )
                              )
let  make_table lst= List.fold_left (fun acc a->let (asm_val,label)= (calc acc a) in
                                                               acc@[(a,(label,asm_val))])  [] lst;;
  let make_consts_tbl asts =(make_table(collect_constants asts));;


  let primitive_names_to_labels =
    ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
     "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
     "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
     "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
     "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
     "make-vector", "make_vector"; "symbol->string", "symbol_to_string";
     "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
     "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ"
  (* you can add yours here *)
  ;("car","car");("cdr","cdr");("cons","cons");("set-car!","set_car");("set-cdr!","set_cdr");("apply","apply")];;
  let primatives_free=List.map(fun(x,y)->x) primitive_names_to_labels;;


  let rec make_free_var_helper asts  =let rec make_free_var lst ast=
  (match ast with
  |Const'(var)-> lst
  |BoxGet'(var)->lst
  |Var'(VarFree(x))->(match (List.exists (String.equal x) lst) with
                                   |false-> lst@[x]
                                   |true->lst
                                 )
  |Var'(VarParam(s,_))-> lst
  |Var'(VarBound(s,_,_))->lst
  |Box'(var)-> lst
  |BoxSet'(var, exp)->make_free_var lst exp
  |If'(test, dit, dif)->let res1=(make_free_var lst test)in let res2=(make_free_var res1 dit)in (make_free_var res2 dif)
  |Seq'(exprs)->List.fold_left(fun acc curr->  (make_free_var acc curr)) lst exprs
  |Set'(var,exp)-> let res1=(make_free_var lst var) in (make_free_var res1 exp)
  |Def'(var, exp)-> let res1=(make_free_var lst var)in (make_free_var res1 exp)
  |Or'(exprs)-> List.fold_left (fun acc curr->(make_free_var acc curr)) lst exprs
  |LambdaSimple'(params, body)-> make_free_var lst body
  |LambdaOpt'(params, op , body)-> make_free_var lst body
  |Applic'(exp, exprs)
  |ApplicTP'(exp, exprs)->let res1=(make_free_var lst exp) in List.fold_left( fun  acc a-> (make_free_var acc a)  ) res1 exprs
  )
  in (List.mapi(fun i x->(x,i)) (List.fold_left (fun acc cur-> make_free_var acc cur) primatives_free asts))
  and free_var_equal x y=(match (x,y) with
                     |Var'(VarFree(a)),Var'(VarFree(b)) when a = b->true
                     |_->false
                     );;
  let make_fvars_tbl asts = make_free_var_helper asts ;;

  let rec find_addres_const consts_tbl const= (match consts_tbl with
  |[]-> failwith "Failed"
  |(exp, (add,_))::tl-> if(exp=const) then add else find_addres_const tl const )



  let rec find_index_in_tbl fvars_tbl const=(match fvars_tbl with
  |[]-> failwith "Failed"
  |(exp,add)::tl->if(exp=const) then add else find_index_in_tbl tl const )

  let  generate consts fvars e =let rec generate_code expr depth envsize= (match expr with
                                                            |Const'(expr)->Printf.sprintf"\tmov rax,%s\n"(find_addres_const consts expr)
                                                            |Seq'(expr_list)->List.fold_left (fun acc cur->acc^(Printf.sprintf ("%s ;seq part\n") (generate_code cur depth envsize))) "" expr_list
                                                            |Def'(name,expr)->(match name with
                                                                                              |Var'(VarFree(name))->let expr=(generate_code expr depth envsize)
                                                                                                in let fvar_index=find_index_in_tbl fvars name
                                                                                                in Printf.sprintf("%s\tmov qword Get_FVAR(%d),rax;defining %s\n\tmov rax,SOB_VOID_ADDRESS\n")(expr)(fvar_index) (name)
                                                                                              |_->raise X_syntax_error
                                                                                                )
                                                            |Set'(v,expr)->(match v with
                                                                            |Var'(VarFree(name))->let expr=(generate_code expr depth envsize)
                                                                                            in let fvar_index=find_index_in_tbl fvars name
                                                                                            in Printf.sprintf("%s\tmov qword Get_FVAR(%d),rax;;setting %s\n\tmov rax,SOB_VOID_ADDRESS\n")(expr)(fvar_index)(name)
                                                                            |Var'(VarParam(name,minor))->let expr=(generate_code expr depth envsize)in
                                                                                                      Printf.sprintf"%s\tmov [rbp+8*(4+%d)],rax;;setting %s\n\tmov rax,SOB_VOID_ADDRESS\n"(expr)(minor) (name)
                                                                            |Var'(VarBound(name,major,minor))->let expr=(generate_code expr depth envsize)in
                                                                                                      Printf.sprintf"%s\tmov rbx,[rbp+8*2];getting env\n\tmov rbx,[rbx+8*%d];getting major\n\tmov [rbx+8*%d],rax;setting %s\n\tmov rax,SOB_VOID_ADDRESS\n"expr major minor name
                                                                            |_->raise X_syntax_error
                                                                            )
                                                            |BoxSet'(name,expr)->Printf.sprintf"%s\tpush rax\n\t%spop qword [rax]\n\tmov rax,SOB_VOID_ADDRESS\n"(generate_code expr depth envsize) (generate_code (Var'(name)) depth envsize)
                                                            |BoxGet'(name)->Printf.sprintf"%s\tmov rax,qword[rax];getting box done\n"(generate_code (Var'(name)) depth envsize)
                                                            |Box'(x)->Printf.sprintf"\t%s mov rcx,rax\n\tMALLOC rax,WORD_SIZE\n\t mov [rax],rcx;done box\n"(generate_code (Var'(x)) depth envsize)
                                                            |Var'(VarFree(name))->Printf.sprintf("\tmov rax,qword Get_FVAR(%d);;getting %s\n")(find_index_in_tbl fvars name)(name)
                                                            |Var'(VarParam(name,minor))->Printf.sprintf "\tmov rax,[rbp + 8 *(4 + %d)];%s\n" minor name
                                                            |Var'(VarBound(name,major,minor))->Printf.sprintf"\tmov rax,qword[rbp+8*2];getting env\n\tmov rax,qword[rax+8*%d]\n\t;getting major vector\n\tmov rax,qword[rax+8*%d];getting %s\n"major minor name
                                                            |If'(test,dit,dif)->let (exit_if_name,else_name)=(exit_if_label(),else_label())
                                                                                                                in let (test,dit,dif)=(generate_code test depth envsize,generate_code dit depth envsize,generate_code dif depth envsize)
                                                                                                                in Printf.sprintf";;doing i--f\n%s\tcmp rax,SOB_FALSE_ADDRESS\n\tje %s\n%s\tjmp %s\n%s:\n%s%s:\n"(test) (else_name)(dit)(exit_if_name)(else_name)(dif)(exit_if_name)
                                                            |Or'(exprs)->let or_exit_label=get_label or_exit in
                                                                                let or_exp= List.fold_left (fun acc a->Printf.sprintf "%s%s\tcmp rax,SOB_FALSE_ADDRESS\n\tjne %s\n" acc (generate_code a depth envsize)  or_exit_label ) "" exprs
                                                                                in Printf.sprintf"%s\n\t%s:\n"or_exp or_exit_label
                                                            |Applic'(proc, args)->
                                                                (
                                                                let magic= "push qword SOB_NIL_ADDRESS;magic_applic\n"in
                                                                let params=List.fold_right(fun a acc->acc^Printf.sprintf "%s\n\tpush rax;pushing parameter for applic\n" (generate_code a depth envsize) ) args "" in let body=Printf.sprintf "\tpush %d; pushing argument count for application\n"(List.length args)
                                                                in let body=body^Printf.sprintf"%s\n"(generate_code proc depth envsize)
                                                                in let body=body^"\tcall check_if_closure\n"
                                                                in let call_applic="\t CLOSURE_ENV rbx,rax\n\t push rbx ; pushing applic env\n\tCLOSURE_CODE rax,rax\n\tcall rax ; calling applic\n"
                                                                in let _end_="\tadd rsp,8; pop env\n\tpop rbx; pop arg count\n\tinc rbx;m\n\t shl rbx,3;rbx=rbx*8\n\t add rsp,rbx;pop args\n"
                                                                in magic^params^body^call_applic^_end_

                                                                )
                                                            |ApplicTP'(proc,args)->
                                                            (let magic= "push qword SOB_NIL_ADDRESS;magic_applictp\n"in
                                                              let params=List.fold_right(fun a acc->acc^Printf.sprintf "%s\n\tpush rax;pushing parameter for applic\n" (generate_code a depth envsize) ) args "" in let body=Printf.sprintf "\tpush %d; pushing argument count for application\n"(List.length args)
                                                              in let body=body^Printf.sprintf"%s\n"(generate_code proc depth envsize)
                                                              in let body=body^"\tcall check_if_closure\n"
                                                              in let fix_stack="\tCLOSURE_ENV rbx,rax\n\tpush rbx\n\tpush qword[rbp+8*1];old ret address\n\tpush qword [rbp]\n"
                                                              in let fix_stack=fix_stack^(Printf.sprintf"\tSHIFT_FRAME %d\n"(5+(List.length args)))
                                                              in let call_code= "\tpop rbp\n\tCLOSURE_CODE rax,rax\n\tjmp rax\n"
                                                              in magic^params^body^fix_stack^call_code
                                                              )

                                                              |LambdaOpt'(param,opt,expr)->(
                                                                                      let params_count=List.length param in
                                                                                      let done_fixed_params=get_label done_fixed_opt_params in
                                                                                      let fix_param=get_label fix_opt_loop in
                                                                                      let lambda_body=get_label lambda_body in
                                                                                      let lambda_exit_name=get_label lambda_exit in
                                                                                      let copy_env_name=get_label extend_env_loop in
                                                                                      let copy_env_exit=get_label extend_env_exit in
                                                                                      let lambda_error=get_label lambda_error in
                                                                                      let param_env_name=get_label param_env_loop in
                                                                                      let param_env_exit=get_label param_env_exit in
                                                                                      let body=Printf.sprintf"\t%s:\n"lambda_body in
                                                                                      let body=body^"\tpush rbp;starting lambda_body\n" in
                                                                                      let body=body^"\tmov rbp,rsp\n" in
                                                                                      let body=body^(Printf.sprintf"\tmov r9,%d \n"(params_count)) in
                                                                                      let body=body^"\tmov rbx,PARAM_COUNT\n" in
                                                                                      let body=body^"\tcmp rbx,r9\n"in
                                                                                      let body=body^Printf.sprintf"\tjb %s\n"lambda_error in
                                                                                      let body=body^Printf.sprintf"\tmov rdx,SOB_NIL_ADDRESS\n"in
                                                                                      let body=body^Printf.sprintf"%s:\n" fix_param in
                                                                                      let body=body^"\tcmp r9,rbx\n"in
                                                                                      let body=body^Printf.sprintf"\tjge %s\n" done_fixed_params in
                                                                                      let body=body^"\tdec rbx\n" in
                                                                                      let body=body^"\tmov r8,[rbp+8*(4+rbx)]\n"in
                                                                                      let body=body^Printf.sprintf"\tMAKE_PAIR(rax,r8,rdx)\n" in
                                                                                      let body=body^"\tmov rdx,rax\n"in
                                                                                      let body=body^Printf.sprintf"\tjmp %s\n" fix_param in
                                                                                      let body=body^Printf.sprintf"%s:\n" done_fixed_params in
                                                                                      let body=body^Printf.sprintf"mov [rbp+8*(4+%d)],rdx\n" (params_count) in
                                                                                      let body=body^Printf.sprintf"%s" (generate_code expr (depth+1) (params_count+1))in
                                                                                      let body=body^"\tleave\n\tret\n" in
                                                                                      let _end_=Printf.sprintf"%s:\n"lambda_error in
                                                                                      let _end_=_end_^Printf.sprintf"\tmov rsi,r9\n mov rdx,PARAM_COUNT\n"in
                                                                                      let _end_=_end_^"\tcall error_exit_call\n"in
                                                                                      let _end_=_end_^Printf.sprintf"%s:\n"lambda_exit_name in
                                                                                      let extend_env=Printf.sprintf"\tmov rax,WORD_SIZE*%d\n"(depth+1) in
                                                                                      let extend_env=extend_env^"\tMALLOC rax,rax; memory for new env\n"in
                                                                                      let extend_env=extend_env^"\tmov rcx,0\n" in
                                                                                      let extend_env=extend_env^"\tmov r9,qword[rbp+8*2]\n"in
                                                                                      let extend_env=extend_env^Printf.sprintf"\tmov rdx,%d\n"depth in
                                                                                      let extend_env=extend_env^Printf.sprintf"%s:\n"copy_env_name in
                                                                                      let extend_env=extend_env^"\tcmp rcx,rdx\n"in
                                                                                      let extend_env=extend_env^Printf.sprintf"\tjge %s\n"copy_env_exit in
                                                                                      let extend_env=extend_env^"\tmov rbx,[r9+8*rcx]\n"in
                                                                                      let extend_env=extend_env^"\tmov[rax+8+rcx*8],rbx\n"in
                                                                                      let extend_env=extend_env^Printf.sprintf"\tinc rcx\n"in
                                                                                      let extend_env=extend_env^Printf.sprintf"\tjmp %s\n"copy_env_name in
                                                                                      let extend_env=extend_env^Printf.sprintf"%s:\n"copy_env_exit in
                                                                                      let copy_params="\tmov rcx,0\n"in
                                                                                      let copy_params=copy_params^ Printf.sprintf"\tmov rdx,%d ;[rbp+8*3]\n" (envsize) in
                                                                                      let copy_params=copy_params^"\tmov r11 ,rdx\n " in
                                                                                      let copy_params=copy_params^"\tshl rdx,3\n" in
                                                                                      let copy_params=copy_params^"\tMALLOC r9,rdx\n"in
                                                                                      let copy_params=copy_params^Printf.sprintf"%s:\n"param_env_name in
                                                                                      let copy_params=copy_params^"\tcmp rcx,r11\n"in
                                                                                      let copy_params=copy_params^Printf.sprintf"\tjge %s\n"param_env_exit in
                                                                                      let copy_params=copy_params^"\tmov rbx,[rbp+8*2];old env\n"in
                                                                                      let copy_params=copy_params^"\tmov r10,[rbp+8*(4+rcx)]\n" in
                                                                                      let copy_params=copy_params^"mov [r9+rcx*8],r10\n"in
                                                                                      let copy_params=copy_params^"\tinc rcx\n"in
                                                                                      let copy_params=copy_params^Printf.sprintf"\tjmp %s\n"param_env_name in
                                                                                      let copy_params=copy_params^Printf.sprintf"%s:\n"param_env_exit in
                                                                                      let copy_params=copy_params^"\tmov [rax],r9\n"in
                                                                                      let make_closure=Printf.sprintf"\tMAKE_CLOSURE (rbx,rax,%s)\n"lambda_body in
                                                                                      let make_closure=make_closure^"\tmov rax,rbx\n" in
                                                                                      let make_closure=make_closure^Printf.sprintf"\tjmp %s\n"lambda_exit_name in
                                                                                      extend_env^copy_params^make_closure^body^_end_)
                                                            |LambdaSimple'(param,expr)->(
                                                                                      let next_env_size=List.length param in
                                                                                      let lambda_body=get_label lambda_body in
                                                                                      let lambda_exit_name=get_label lambda_exit in
                                                                                      let copy_env_name=get_label extend_env_loop in
                                                                                      let copy_env_exit=get_label extend_env_exit in
                                                                                      let lambda_error=get_label lambda_error in
                                                                                      let param_env_name=get_label param_env_loop in
                                                                                      let param_env_exit=get_label param_env_exit in
                                                                                      let body=Printf.sprintf"\t%s:\n"lambda_body in
                                                                                      let body=body^"\tpush rbp;starting lambda_body\n" in
                                                                                      let body=body^"\tmov rbp,rsp\n" in
                                                                                      let body=body^(Printf.sprintf"\tmov r9,%d \n"(next_env_size)) in
                                                                                      let body=body^"\tcmp r9,PARAM_COUNT\n"in
                                                                                      let body=body^Printf.sprintf"\tjne %s\n"lambda_error in
                                                                                      let body=body^Printf.sprintf"%s" (generate_code expr (depth+1) next_env_size)in
                                                                                      let body=body^"\tleave\n\tret\n" in
                                                                                      let _end_=Printf.sprintf"%s:\n"lambda_error in
                                                                                      let _end_=_end_^Printf.sprintf"\tmov rsi,r9\n mov rdx,PARAM_COUNT\n"in
                                                                                      let _end_=_end_^"\tcall error_exit_call\n"in
                                                                                      let _end_=_end_^Printf.sprintf"%s:\n"lambda_exit_name in
                                                                                      let extend_env=Printf.sprintf"\tmov rax,WORD_SIZE*%d\n"(depth+1) in
                                                                                      let extend_env=extend_env^"\tMALLOC rax,rax; memory for new env\n"in
                                                                                      let extend_env=extend_env^"\tmov rcx,0\n" in
                                                                                      let extend_env=extend_env^"\tmov r9,qword[rbp+8*2]\n"in
                                                                                      let extend_env=extend_env^Printf.sprintf"\tmov rdx,%d\n"depth in
                                                                                      let extend_env=extend_env^Printf.sprintf"%s:\n"copy_env_name in
                                                                                      let extend_env=extend_env^"\tcmp rcx,rdx\n"in
                                                                                      let extend_env=extend_env^Printf.sprintf"\tjge %s\n"copy_env_exit in
                                                                                      let extend_env=extend_env^"\tmov rbx,[r9+8*rcx]\n"in
                                                                                      let extend_env=extend_env^"\tmov[rax+8+rcx*8],rbx\n"in
                                                                                      let extend_env=extend_env^Printf.sprintf"\tinc rcx\n"in
                                                                                      let extend_env=extend_env^Printf.sprintf"\tjmp %s\n"copy_env_name in
                                                                                      let extend_env=extend_env^Printf.sprintf"%s:\n"copy_env_exit in
                                                                                      let copy_params="\tmov rcx,0\n"in
                                                                                      let copy_params=copy_params^ Printf.sprintf"\tmov rdx,%d ;[rbp+8*3]\n" (envsize) in
                                                                                      let copy_params=copy_params^"\tmov r11,rdx\n"in
                                                                                      let copy_params=copy_params^"\tshl rdx,3\n" in
                                                                                      let copy_params=copy_params^"\tMALLOC r9,rdx\n"in
                                                                                      let copy_params=copy_params^Printf.sprintf"%s:\n"param_env_name in
                                                                                      let copy_params=copy_params^"\tcmp rcx,r11\n"in
                                                                                      let copy_params=copy_params^Printf.sprintf"\tjge %s\n"param_env_exit in
                                                                                      let copy_params=copy_params^"\tmov rbx,[rbp+8*2];old env\n"in
                                                                                      let copy_params=copy_params^"\tmov r10,[rbp+8*(4+rcx)]\n" in
                                                                                      let copy_params=copy_params^"mov [r9+rcx*8],r10\n"in
                                                                                      let copy_params=copy_params^"\tinc rcx\n"in
                                                                                      let copy_params=copy_params^Printf.sprintf"\tjmp %s\n"param_env_name in
                                                                                      let copy_params=copy_params^Printf.sprintf"%s:\n"param_env_exit in
                                                                                      let copy_params=copy_params^"\tmov [rax],r9\n"in
                                                                                      let make_closure=Printf.sprintf"\tMAKE_CLOSURE (rbx,rax,%s)\n"lambda_body in
                                                                                      let make_closure=make_closure^"\tmov rax,rbx\n" in
                                                                                      let make_closure=make_closure^Printf.sprintf"\tjmp %s\n"lambda_exit_name in
                                                                                      extend_env^copy_params^make_closure^body^_end_)
                                                            )
                                    in generate_code e 0 0;;
end;;
