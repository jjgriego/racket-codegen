#lang racket

(require "asm.rkt")

(define default-register-spec
  '((gp . (rax rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r14 r15))
    (sf . (sf))
    (spill . #f)))

(define-syntax (define-physregs stx)
  (syntax-case stx ()
    [(_ set-name (name ...))
     #'(begin
         (define name (vreg #f (~a 'name)))
         ...
         (define set-name `((name . ,name) ...)))]))

(define-physregs x64-physregs
  [rax rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r14 r15
       sf flags
       rsp rbp rip])

(struct mem (base offset index scale) #:transparent #:mutable
  #:methods gen:mem
  [(define (mem-srcs m)
     (filter identity (list (mem-offset m)
                            (mem-index))))])

(define (stack-access n)
  (mem (* 8 n) rbp 0 1))

(define-instruction (movi imm dst))
(define-instruction (add src src dst))
(define-instruction (mov src dst))
(define-instruction (store src mem))
(define-instruction (load mem dst))
(define-instruction (jcc src imm target))
(define-instruction (cmp src src dst))
(define-instruction (ret src))

(define (instr-storage-classes op visit)
  (match op
    ;; jcc and cmp operate on the sf register only
    [(jcc src _ _)
     (visit src 'sf)]
    [(cmp s0 s1 dst)
     (visit s0 'gp)
     (visit s1 'gp)
     (visit dst 'sf)]
    ;; copy is the special snowflake that can move between
    ;; gp and spill space
    [(copy src dst)
     (visit src 'word)
     (visit dst 'word)]
    ;; phis are really copies we'd like to be able to optimize away--in
    ;; particular it's possible for a spilled vreg to be the dst or a
    ;; src of a phi
    [(phi dst _)
     (visit dst 'word)]
    ;; phijmps permit spills also for the same reason
    [(phijmp _ srcs)
     (for ([src srcs]) (visit src 'word))]
    ;; unless otherwise specified, instructions operate on gps
    [ins
     (for ([src (instr-srcs ins)])
       (visit src 'gp))
     (for ([src (instr-dsts ins)])
       (visit src 'gp))]))

(define (lower-copies u)
  (unit-map-instrs! u
                    (lambda (op)
                      (match op
                        [(copy (virtual-reg 'spill n) (virtual-reg 'spill m))
                         ;; oops uh oh
                         (assert #f)]
                        [(copy (virtual-reg 'spill n) dst)
                         (load (stack-access n) dst)]
                        [(copy src (virtual-reg 'spill n))
                         (store src (stack-access n))]
                        [(copy src dst)
                         (mov src dst)]
                        [_ op]))))

(module+ test
  (define u (asm-unit
             (n a b n0 a0 b0 t0 sf0 t1 n1 sum)
             (entry (conjure n)
                    (movi 1 a)
                    (movi 1 b)
                    (phijmp loop-header (list n a b)))
             (loop-header (phi n0 0)
                          (phi a0 1)
                          (phi b0 2)
                          (movi 0 t0)
                          (cmp t0 n0 sf0)
                          (jcc sf0 'Z done)
                          (jmp loop-body))
             (loop-body (movi -1 t1)
                        (add n0 t1 n1)
                        (add a0 b0 sum)
                        (phijmp loop-header (list n1 b0 sum)))
             (done (ret a0))))
  (show-unit u)
  (define allocs (regalloc u default-register-spec instr-storage-classes))
  (unphi u
         default-register-spec
         (liveness u)
         allocs
         (phi-registers u))
  (show-unit u allocs)
  (collapse-phys-regs u allocs x64-physregs)
  (lower-copies u)
  (show-unit u)
  )



