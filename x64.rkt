#lang racket

(require "asm.rkt")

(provide movi add* sub* mov store load jcc cmp call* ret* push pop
         enter-frame leave-frame
         lower-x64 (struct-out mem))

(define default-register-spec
  '((gp . (rax rcx rdx r8 r9 r10 r11 rsi rdi))
    (sf . (sf))
    (spill . #f)))

(define-syntax (define-physregs stx)
  (syntax-case stx ()
    [(_ set-name (name ...))
     #'(begin
         (define name (vreg #f (~a 'name) #t))
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
                            (mem-index m))))
   (define (mem-visit-operands m f)
     (f 'imm (mem-base m) (lambda (v) (set-mem-base! m v)))
     (when (mem-offset m)
       (f 'src (mem-offset m) (lambda (v) (set-mem-offset! m v))))
     (when (mem-index m)
       (f 'src (mem-index m) (lambda (v) (set-mem-index! m v))))
     (when (mem-scale m)
       (f 'imm (mem-scale m) (lambda (v) (set-mem-scale! m v)))))])

(define (stack-access n)
  (mem (* -8 (add1 n)) rbp #f #f))

(define-instruction (movi imm dst))
(define-instruction (add* src src dst))
(define-instruction (sub* src src dst))
(define-instruction (mov src dst))
(define-instruction (store src mem))
(define-instruction (load mem dst))
(define-instruction (jcc src imm target))
(define-instruction (cmp src src dst))
(define-instruction (call* imm src dst))
(define-instruction (ret* src))
(define-instruction (ret))
(define-instruction (push src))
(define-instruction (pop dst))

(define-instruction (sub dst src))
(define-instruction (subi dst imm))
(define-instruction (add dst src))
(define-instruction (addi dst imm))
(define-instruction (call imm))

;; pseudo-instructions
(define-syntax instr:enter-frame '((listof dst)))
(struct enter-frame (dsts) #:mutable #:transparent
  #:methods gen:instr
  [(define (instr-mneumonic _) 'enter-frame)
   (define (instr-operands i) (enter-frame-dsts i))
   (define (instr-srcs i) '())
   (define (instr-dsts i) (enter-frame-dsts i))
   (define (instr-imms i) '())
   (define (instr-targets i) '())
   (define (instr-visit-operands i f)
     (define ((update-dsts-at! idx) x)
       (set-enter-frame-dsts! i (list-set (enter-frame-dsts i) idx x)))
     (for ([dst (enter-frame-dsts i)]
           [i (in-naturals)])
       (f 'dst dst (update-dsts-at! i))))])

(define-instruction (leave-frame))



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

(define (count-spill-slots u registers-ed)
  (define-values (register set-register!) (use-extra-data registers-ed))
  (define access-idxs (map virtual-reg-idx
                           (filter (lambda (alloc)
                                     (and (virtual-reg? alloc)
                                          (eq? (virtual-reg-cls alloc) 'spill)))
                                   (map register (unit-vregs u)))))
  (if (empty? access-idxs)
      0
      (add1 (apply max access-idxs))))

(define (frame-register-constraints u)
  (or (for*/first ([b (unit-blocks u)]
                   [i (block-instrs b)]
                   #:when (enter-frame? (vinstr-op i)))
        (match (vinstr-op i)
          [(enter-frame dsts)
           (for/list ([r dsts]
                      [pr '(rdi rsi rdx rcx r8 r9)])
             (cons r pr))]))
      '()))


(define (lower-frame u registers)
  (define spill-slots (count-spill-slots u registers))

  (unit-replace-instrs! u (lambda (op replace!)
                            (match (vinstr-op op)
                              [(enter-frame dsts)
                               (replace! (list
                                          (push rbp)
                                          (mov rsp rbp)
                                          (subi rsp (* 8 spill-slots))
                                          ))]
                              [(leave-frame)
                               (replace! (list
                                          (mov rbp rsp)
                                          (pop rbp)))]
                              [_ (void)]))))

(define (lower-call* u registers-ed)
  (define-values (register set-register!) (use-extra-data registers-ed))
  (define-values (instr-live-out set-instr-live-out!) (use-extra-data (instr-liveness u)))

  (define (find-spills live-allocs needed)
    (define occupied (list->set (filter-map (lambda (a)
                                              (and (virtual-reg? a)
                                                   (eq? (virtual-reg-cls a) 'spill)
                                                   (virtual-reg-idx a)))
                                            live-allocs)))
    (let loop ([idx 0]
               [needed needed]
               [selected '()])
      (cond
        [(= 0 needed)
         selected]
        [(set-member? occupied idx)
         (loop (add1 idx) needed selected)]
        [else
         (loop (add1 idx) (sub1 needed) (cons (virtual-reg 'spill idx) selected))])))

  (unit-replace-instrs! u
                        (lambda (i replace!)
                          (match (vinstr-op i)
                            [(call* f src dst)
                             (define live-out (instr-live-out i))
                             (define caller-save '(rax rcx rdx r8 r9 r10 r11))
                             (define live-allocs
                               (map register (set->list live-out)))
                             (define spilled
                               (filter (lambda (r)
                                         (memq (register r) caller-save))
                                       (set->list live-out)))
                             (define slots (map (lambda (a)
                                                  (define r (vreg! u))
                                                  (set-register! r a)
                                                  r)
                                                (find-spills live-allocs (length spilled))))

                             (define saves (map (lambda (r slot)
                                                  (copy r slot))
                                                spilled
                                                slots))
                             (define restores (map (lambda (r slot)
                                                     (copy slot r))
                                                   spilled
                                                   slots))

                             (replace! `(,@saves
                                         ,(mov src rdi)
                                         ,(call f)
                                         ,(mov rax dst)
                                         ,@restores))
                             ]
                            [_ (void)]))))

(define (lower-three-address u)
  (unit-replace-instrs! u
                        (lambda (op replace!)
                          (match (vinstr-op op)
                            [(add* s0 s1 dst)
                             (replace! (list
                                        (add s0 s1)
                                        (mov s0 dst)))]
                            [(sub* s0 s1 dst)
                             (replace! (list
                                        (add s0 s1)
                                        (mov s0 dst)))]
                            [_ (void)]))))

(define (lower-return u)
  (unit-replace-instrs! u (lambda (op replace!)
                            (match (vinstr-op op)
                              [(ret* src)
                               (replace! (list (mov src rax)
                                               (ret)))]
                              [_ (void)]))))

(define (trivial-mov u)
  (unit-replace-instrs! u (lambda (op replace!)
                            (match (vinstr-op op)
                              [(mov r r) (replace! '())]
                              [_ (void)]))))

(define (lower-copies u registers-ed)
  (define-values (register set-register!) (use-extra-data registers-ed))
  (unit-map-instrs! u
                    (lambda (op)
                      (match op
                        [(copy src dst)
                         (match* ((register src) (register dst))
                           [((virtual-reg 'spill n) (virtual-reg 'spill m))
                            ;;; XXX this really shouldn't be allowed to happen
                            ;;; but nothing prevents it rn
                            (assert #f)]
                           [((virtual-reg 'spill n) _)
                            (load (stack-access n) dst)]
                           [(_ (virtual-reg 'spill n))
                            (store src (stack-access n))]
                           [(_ _)
                            (mov src dst)])]
                        [_ op]))))

(define (write-unit-asm u)

  ;; choose local label names
  (define label-name-ed (make-extra-label-data u))
  (define-values (label-name set-label-name!) (use-extra-data label-name-ed))
  (for ([l (unit-labels u)])
    (set-label-name! l (gensym '.L)))

  (define (write-instr op)
    (define (reg r)
      (assert (vreg-physical? r))
      (format "%~a" (vreg-display r)))
    (define (target t)
      (~a (label-name t)))
    (define (imm i)
      (format "$~a" i))
    (define (memory m)
      (match m
        [(mem base #f #f #f)
         (format "~a" base)]
        [(mem base offset #f #f)
         (format "~a(~a)" base (reg offset))]))
    (match op
      [(push src) (printf "push ~a" (reg src))]
      [(pop dst) (printf "pop ~a" (reg dst))]
      [(mov src dst) (printf "mov ~a, ~a" (reg src) (reg dst))]
      [(add inout s1) (printf "add ~a, ~a" (reg s1) (reg inout))]
      [(sub inout s1) (printf "sub ~a, ~a" (reg s1) (reg inout))]
      [(subi inout i) (printf "sub ~a, ~a" (imm i) (reg inout))]
      [(subi inout i) (printf "add ~a, ~a" (imm i) (reg inout))]
      [(movi i dst) (printf "mov ~a, ~a" (imm i) (reg dst))]
      [(cmp s0 s1 _) (printf "cmp ~a, ~a" (reg s0) (reg s1))]
      [(store src dst) (printf "mov ~a, ~a" (reg src) (memory dst))]
      [(load src dst) (printf "mov ~a, ~a" (memory src) (reg dst))]
      [(call t) (printf "call ~a" t)]
      [(jcc _ 'Z t) (printf "jz ~a" (target t))]
      [(jmp t) (printf "jmp ~a" (target t))]
      [(ret) (printf "ret")]))

  (for ([l (unit-labels u)])
    (printf "~a:\n" (label-name l))
    (for ([i (block-instrs (label-block l))])
      (display "  ")
      (write-instr (vinstr-op i))
      (display "\n"))))

(define (lower-x64 u)
  (define must-colors (frame-register-constraints u))
  (define allocs (regalloc u default-register-spec must-colors instr-storage-classes))
  (unphi u
         default-register-spec
         (liveness u)
         allocs
         (phi-registers u))
  (lower-call* u allocs)
  (lower-frame u allocs)
  (lower-copies u allocs)
  (collapse-phys-regs u allocs x64-physregs)
  (lower-return u)
  (lower-three-address u)
  (trivial-mov u))

#;(module+ test
  (define u (asm-unit
             (n a b n0 a0 b0 t0 sf0 t1 n1 sum trash)
             (entry
              (enter-frame (list n))
              (movi 1 a)
              (movi 1 b)
              (phijmp loop-header (list n a b)))
             (loop-header
              (phi n0 0)
              (phi a0 1)
              (phi b0 2)
              (movi 0 t0)
              (cmp t0 n0 sf0)
              (jcc sf0 'Z done)
              (jmp loop-body))
             (loop-body
              (movi -1 t1)
              (add* n0 t1 n1)
              (add* a0 b0 sum)
              (phijmp loop-header (list n1 b0 sum)))
             (done
              (leave-frame)
              (ret* a0))))
  (show-unit u)
  (lower-x64 u)
  (show-unit u)
  (write-unit-asm u))



