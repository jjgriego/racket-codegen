#lang racket

(require "x64.rkt" (except-in "asm.rkt" mem?))

(struct cfg (unit active-block) #:transparent #:mutable)

(define (empty-cfg)
  (define u (empty-unit))
  (cfg u (block! u (unit-entry u))))

(define (cfg-vreg! c)
  (vreg! (cfg-unit c)))

(define (cfg-append! c instr)
  (assert (cfg-active-block c))
  (block-append-instr! (cfg-unit c)
                       (cfg-active-block c)
                       instr))

(define (cfg-label! c [arity 0])
  (define u (empty-unit))
  (label! (cfg-unit c) arity))

(define (cfg-block! c l)
  (define b (block! (cfg-unit c) l))
  (set-cfg-active-block! c b)
  b)

(define (cfg-join! c c2 label)
  (assert (or (not (label-block label))
              (empty? (block-instrs (label-block label)))))
  (set-label-block! label (label-block (unit-entry (cfg-unit c2))))
  (unit-merge! (cfg-unit c)
               (cfg-unit c2))
  c)

(define (cfg-concat! c c2)
  (assert (cfg-active-block c))
  (cfg-append! c (jmp (unit-entry (cfg-unit c2))))
  (unit-merge! (cfg-unit c)
               (cfg-unit c2))
  c)

(define (alphatize expr env)
  (match expr
    [(? number? n) n]
    [(? symbol? x)
     (let ([r (assq x env)])
       (unless r
         (error 'alphatize "not in scope: ~a" x))
       (cdr r))]
    [(list '+ e1 e2)
     `(+ ,(alphatize e1 env) ,(alphatize e2 env))]
    [(list 'lambda param body)
     (define param* (gensym param))
     (list 'lambda param* (alphatize body (cons (cons param param*) env)))]
    [(list 'ifz e1 e2 e3)
     `(ifz ,(alphatize e1 env)
           ,(alphatize e2 env)
           ,(alphatize e3 env))]))

(define (free-vars expr)
  (match expr
    [(? symbol? x) (seteq x)]
    [(? number? n) (seteq)]
    [(list '+ e1 e2)
     (set-union (free-vars e1) (free-vars e2))]
    [(list 'lambda param body)
     (set-remove (free-vars body) param)]
    [(list 'ifz e1 e2 e3)
     (set-union (free-vars e1) (free-vars e2) (free-vars e3))]))

(struct top-level-fn (param closure-vars body) #:transparent)
(define (closure-convert expr)
  (define top-level (make-hasheq))
  (define (convert expr)
    (match expr
      [(? number? n) n]
      [(? symbol? x) x]
      [(list '+ e1 e2)
       (list '+ (convert e1) (convert e2))]
      [(list 'ifz e1 e2 e3)
       (list 'ifz (convert e1) (convert e2) (convert e3))]
      [(list 'lambda x body)
       (define f (gensym 'f))
       (define closure-vars (set->list (free-vars expr)))
       (hash-set! top-level f (top-level-fn x closure-vars (convert body)))
       (list 'make-closure f closure-vars)]))
  (cons (convert expr) top-level))


(define (compile-expr c expr env)
  (match expr
    [(? number? n)
     (let ([r (cfg-vreg! c)])
       (cfg-append! c (movi n r))
       r)]

    [(? symbol? x)
     ((dict-ref env x) c)]

    [(list 'make-closure ptr vars)

     (define size (* 8 (add1 (length vars))))

     (define size-reg (cfg-vreg! c))
     (define fn-reg (cfg-vreg! c))
     (define closure-reg (cfg-vreg! c))
     (cfg-append! c (movi size size-reg))
     (cfg-append! c (call* 'malloc size-reg closure-reg))
     (cfg-append! c (movi ptr fn-reg))
     (cfg-append! c (store fn-reg (mem 0 closure-reg #f #f)))

     (for ([v vars]
           [i (in-naturals)])
       (cfg-append! c (store (compile-expr c v env)
                             (mem (* 8 (add1 i)) closure-reg #f #f))))
     closure-reg]

    [(list 'ifz e1 e2 e3)

     (define t (cfg-label! c))
     (define f (cfg-label! c))
     (define cont (cfg-label! c 1))

     (let ([zero (cfg-vreg! c)]
           [sf (cfg-vreg! c)]
           [res (compile-expr c e1 env)])
       (cfg-append! c (movi 0 zero))
       (cfg-append! c (cmp zero res sf))
       (cfg-append! c (jcc sf 'Z f))
       (cfg-append! c (jmp t)))

     (cfg-block! c t)
     (cfg-append! c (phijmp cont (list (compile-expr c e2 env))))

     (cfg-block! c f)
     (cfg-append! c (phijmp cont (list (compile-expr c e3 env))))

     (cfg-block! c cont)
     (define ret (cfg-vreg! c))
     (cfg-append! c (phi ret 0))
     ret]

    [(list '+ e1 e2)
     (let* ([r1 (compile-expr c e1 env)]
            [r2 (compile-expr c e2 env)]
            [r (cfg-vreg! c)])
       (cfg-append! c (add* r1 r2 r))
       r)]))

(define (compile-function f)
  (match f
    [(top-level-fn param-name closure-vars body)
     (define c (empty-cfg))
     (define closure (cfg-vreg! c))
     (define param (cfg-vreg! c))

     (define ((access-closure-var idx) c)
       (define r (cfg-vreg! c))
       (cfg-append! c (load (mem (* 8 (add1 idx)) closure #f #f) r))
       r)

     (define env (hash-set (for/hasheq ([var closure-vars]
                                        [idx (in-naturals)])
                             (values var (access-closure-var idx)))
                           param-name
                           (lambda (c) param)))

     (cfg-append! c (enter-frame (list closure param)))
     (define r (compile-expr c body env))
     (cfg-append! c (leave-frame))
     (cfg-append! c (ret* r))
     c]))

(define (compile program)
  (define program* (closure-convert (alphatize program '())))

  (for ([(name f) (in-dict (cdr program*))])
    (printf "Function ~a\n~a\n" name f)
    (define u (cfg-unit (compile-function f)))
    (lower-x64 u)
    (show-unit u))

  (displayln "top level:")
  (define u (cfg-unit (compile-function (top-level-fn (gensym) '() (car program*)))))
  (lower-x64 u)
  (show-unit u))







