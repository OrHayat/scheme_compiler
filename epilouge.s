section .text

car:
              push rbp
              mov rbp, rsp
              mov rdx,PARAM_COUNT
              mov rsi,1
              cmp rsi,rdx
              jne error_exit_call
              mov rdi, PVAR(0)
              cmp TYPE(rdi),T_PAIR
              jne .error_car
              CAR rax, rdi
              leave
              ret
.error_car:
    push rdi
    mov rdi,.error_msg_car
    mov rax,0
    call printf
    pop rsi
    call write_sob
    mov rdi,not_pair_msg
    mov rax,0
    call printf
    mov rdi,-1
    call exit
section .data
.error_msg_car: db "error in car ",0

cdr:
              push rbp
              mov rbp, rsp
              mov rdx,PARAM_COUNT
              mov rsi,1
              cmp rsi,rdx
              jne error_exit_call
              mov rdi, PVAR(0)
              cmp TYPE(rdi),T_PAIR
              jne .error_cdr
              CDR rax, rdi
              leave
              ret
.error_cdr:
    push rdi
    mov rdi,.error_msg_cdr
    mov rax,0
    call printf
    pop rsi
    call write_sob
    mov rdi,not_pair_msg
    mov rax,0
    call printf
    mov rdi,-1
    call exit

section .data
.error_msg_cdr: db "error in cdr ",0
not_pair_msg: db " is not a pair",10,0
section .text
cons:
              push rbp
              mov rbp, rsp
              mov rdx,PARAM_COUNT
              mov rsi,2;expect 2 params
              cmp rsi,rdx
              jne error_exit_call
              mov rsi , PVAR(1)
              mov rdi, PVAR(0)
              MAKE_PAIR(rax,rdi,rsi)
              leave
              ret
set_car:
              push rbp
              mov rbp, rsp
              mov rdx,PARAM_COUNT
              mov rsi,2;expect 2 params
              cmp rsi,rdx
              jne error_exit_call
              mov rcx , PVAR(1)
              mov rdi, PVAR(0)
              cmp TYPE(rdi),T_PAIR
              jne .error_set_car
              GET_CAR_ADDRESS rax,rdi
              mov [rax],rcx
              mov rax,SOB_VOID_ADDRESS
              leave
              ret
.error_set_car:
    push rdi
    mov rdi,.error_msg_set_car
    mov rax,0
    call printf
    pop rsi
    call write_sob
    mov rdi,not_pair_msg
    mov rax,0
    call printf
    mov rdi,-1
    call exit
section .data
.error_msg_set_car: db "error in set-car! ",0

section .text


set_cdr:
              push rbp
              mov rbp, rsp
              mov rdx,PARAM_COUNT
              mov rsi,2;expect 2 params
              cmp rsi,rdx
              jne error_exit_call
              mov rcx , PVAR(1)
              mov rdi, PVAR(0)
              cmp TYPE(rdi),T_PAIR
              jne .error_set_cdr
              GET_CDR_ADDRESS rax,rdi
              mov [rax],rcx
              mov rax,SOB_VOID_ADDRESS
              leave
              ret
.error_set_cdr:
    push rdi
    mov rdi,.error_msg_set_cdr
    mov rax,0
    call printf
    pop rsi
    call write_sob
    mov rdi,not_pair_msg
    mov rax,0
    call printf
    mov rdi,-1
    call exit
section .data
.error_msg_set_cdr: db "error in set-cdr! ",0

section .text



apply:
    push rbp
    mov rbp,rsp
    mov rsi,PARAM_COUNT
    cmp rsi,1
    ja .param_count_ok
    mov rdi,.worng_param_count_msg
    mov rax,0
    call printf
    mov rdi,-1
    call exit
.param_count_ok:
    mov rdi,PVAR(0)
    mov r8,rbp;remove
    cmp TYPE(rdi),T_CLOSURE
    je .closure_ok
    mov rdi,.expected_closure_msg
    mov rax,0
    call printf
    mov rsi,PVAR(0)
    call write_sob
    mov rdi,-1
    call exit
.closure_ok:
    dec rsi
    mov rdi,PVAR(rsi)
    call .is_proper_list_check
    cmp rax,1
    je .do_apply
    mov rax,0
    mov rdi,.expected_proper_list_msg
    call printf
    mov rsi,PARAM_COUNT
    dec rsi
    mov rsi,PVAR(rsi)
    call write_sob
    mov rdi,.not_proper_list_msg
    mov rax,0
    call printf
    mov rdi,-1
    call exit
.is_proper_list_check:
    push rbp
    mov rbp,rsp
    cmp TYPE(rdi),T_NIL
    jne .next
    mov rax,1
    leave
    ret
.next:
    cmp TYPE(rdi),T_PAIR
    je .check_list
    mov rax, 0
    leave
    ret
.check_list:
    CDR rdi,rdi
    call .is_proper_list_check
    leave
    ret

.do_apply:
    mov r8,rbp;remove

    mov rbx,PARAM_COUNT
    dec rbx;subtract list
    mov rdi,PVAR(rbx)
    dec rbx;subtract closure
;   call write_sob
    mov rax,0
    push rdi
    call .lst_length_main;length in rax
    add rax,rbx;rax counter length of list
    pop rdi;rdi=list
    push MAGIC
    mov rdx,rax;all params
    mov r11, rdx
    ;add rdx,rax;list length
    shl rdx,3
    mov r10, rdx
    sub rsp,rdx
    mov rcx,0
    mov rdx,1
    .loop_args:
    cmp rcx,rbx
    jge .exit_loop_args
    mov r9, PVAR(rdx)
    mov qword[rsp],r9
    add rsp,WORD_SIZE
    inc rcx
    inc rdx
    jmp .loop_args
    .exit_loop_args:
    .loop_list:
    cmp TYPE(rdi),T_NIL
    je .exit_loop_list
    CAR r9,rdi
    mov qword[rsp],r9
    add rsp,WORD_SIZE
    CDR rdi,rdi
    jmp .loop_list
    .exit_loop_list:
        mov r8,rbp;remove
    sub rsp, r10
    push r11;n
        mov r8,rbp;remove

    mov rax,PVAR(0)
        mov r8,rbp;remove

    CLOSURE_ENV r10, rax
    push r10
    push qword[rbp+8*1]
    push qword[rbp]
    CLOSURE_CODE rax,rax
    add r11,5
    SHIFT_FRAME_APPLIC r11
    pop rbp
    jmp rax


.lst_length_main:
    push rbp
    mov rbp,rsp
.lst_length:
    cmp TYPE(rdi),T_NIL
    jne .next_len
    leave
    ret
    .next_len:
    inc rax
    CDR rdi,rdi
    jmp .lst_length

section .data
.worng_param_count_msg:db "incorrect argument count in call expected at least 2 while got %d"
.expected_closure_msg:db "attemped to apply no-procdure ",0
.expected_proper_list_msg:db "error in apply ",0
.not_proper_list_msg:db " is not a proper list",10,0
