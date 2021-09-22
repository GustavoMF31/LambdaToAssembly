global main
extern printf

section .text

copy_env:
    xor rdx, rdx
.loop:
    cmp rdx, r10
    je .done
    mov rbx, [r9 + rdx]
    mov qword [rcx], rbx
    add rcx, 8
    inc rdx
    jmp .loop
.done:
    ret

; (\f -> \x -> \y -> f y x) (\x -> \y -> x) 4 5

lambda_1: ; \x -> \y -> x
    mov rax, rcx
    mov qword [rcx], lambda_0
    add rcx, 16
    mov r10, 1
    call copy_env
    ret
lambda_0: ; \y -> x
    mov rax, [r9 + 8]
    ret

lambda_4: ; \f x y -> f y x
    mov rax, rcx
    mov qword [rcx], lambda_3
    add rcx, 16
    mov r10, 1
    call copy_env
    ret
lambda_3: ; \x y -> f y x
    mov rax, rcx
    mov qword [rcx], lambda_2
    add rcx, 16
    mov r10, 2
    call copy_env
    ret
lambda_2: ; \y -> f y x
    ; r9 + 16 must have been broken here
    ; (Maybe `f` was not captured properly)
    ; Conclusion: r9 is bad when the call to lambda_2 happens
    mov rax, [r9 + 16] ; f
    push rax ; This rax becomes the rdx that segfaults
    mov rax, [r9 + 0] ; y
    pop rdx
                       ; rdx must have been a bad pointer
    mov [rdx + 8], rax ; This mov segfaults!
    push r9
    lea r9, [rdx + 8]
    call qword [rdx]
    pop r9

    push rax
    mov rax, [r9 + 8] ; x
    pop rdx
    mov [rdx + 8], rax
    push r9
    lea r9, [rdx + 8]
    call qword [rdx]
    pop r9

    ret

main:
    ; Initialize
    mov rcx, heap_base

    ; Create the closure for lambda_4, the cardinal, (captures nothing)
    mov rax, rcx
    mov qword [rcx], lambda_4
    add rcx, 16
    mov r10, 0
    call copy_env

    ; Create the closure for lambda_1, the kestrel, (also captures nothing)
    push rax
    mov rax, rcx
    mov qword [rcx], lambda_1
    add rcx, 16
    mov r10, 0
    call copy_env

    ; Compute the kite (the cardinal of the kestrel)
    pop rdx
    mov [rdx + 8], rax
    push r9
    lea r9, [rdx + 8]
    call qword [rdx]
    pop r9

    ; Apply the kite to 4
    push rax
    mov rax, 4
    pop rdx
    mov [rdx + 8], rax
    push r9
    lea r9, [rdx + 8]
    call qword [rdx]
    pop r9

    ; Then to 5
    ; That's the call that makes it segfault
    push rax ; Save the closure-ptr on the stack
    mov rax, 5 ; Load the argument 5
    pop rdx ; Get the closure-ptr back
    mov [rdx + 8], rax ; Write the argument to the closure's environment
    push r9 ; Save the current env-ptr
    lea r9, [rdx + 8] ; Load the environment of the kite's closure
    call qword [rdx] ; Call the kite
    pop r9 ; Restore the previous (empty) env-ptr

    mov rdi, digit_formatter
    mov rsi, rax
    xor rax, rax
    call printf
    ret

section .data
digit_formatter:
    db "%llu", 10
section .bss
heap_base:
    resb 800
