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
    [(list (and binop (or '+ '-)) e1 e2)
     `(,binop ,(alphatize e1 env) ,(alphatize e2 env))]
    [(list 'lambda param body)
     (define param* (gensym param))
     (list 'lambda param* (alphatize body (cons (cons param param*) env)))]
    [(list 'ifz e1 e2 e3)
     `(ifz ,(alphatize e1 env)
           ,(alphatize e2 env)
           ,(alphatize e3 env))]
    [(list fn arg)
     `(,(alphatize fn env)
       ,(alphatize arg env))]))

(define (free-vars expr)
  (match expr
    [(? symbol? x) (seteq x)]
    [(? number? n) (seteq)]
    [(list (or '+ '-) e1 e2)
     (set-union (free-vars e1) (free-vars e2))]
    [(list 'lambda param body)
     (set-remove (free-vars body) param)]
    [(list 'ifz e1 e2 e3)
     (set-union (free-vars e1) (free-vars e2) (free-vars e3))]
    [(list fn arg)
     (set-union (free-vars fn) (free-vars arg))]))

(struct top-level-fn (param closure-vars body) #:transparent)
(define (closure-convert expr)
  (define top-level (make-hasheq))
  (define (convert expr)
    (match expr
      [(? number? n) n]
      [(? symbol? x) x]
      [(list (and binop (or '+ '-)) e1 e2)
       (list binop (convert e1) (convert e2))]
      [(list 'ifz e1 e2 e3)
       (list 'ifz (convert e1) (convert e2) (convert e3))]
      [(list 'lambda x body)
       (define f (gensym 'f))
       (define closure-vars (set->list (free-vars expr)))
       (hash-set! top-level f (top-level-fn x closure-vars (convert body)))
       (list 'make-closure f closure-vars)]
      [(list fn arg)
       (list (convert fn) (convert arg))]))
  (cons (convert expr) top-level))


(define (compile-expr c expr env)
  (match expr
    [(? number? n)
     (let ([r (cfg-vreg! c)])
       (cfg-append! c (movi n r))
       r)]

    [(? symbol? x)
     ((dict-ref env x) c)]

    [(list 'make-closure impl vars)
     (define size (* 8 (add1 (length vars))))
     (define size-reg (cfg-vreg! c))
     (define fn-reg (cfg-vreg! c))
     (define closure-reg (cfg-vreg! c))
     (cfg-append! c (movi size size-reg))
     (cfg-append! c (calli* 'malloc (list size-reg) closure-reg))
     (cfg-append! c (lea (mem impl #f #f #f) fn-reg))
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
       (cfg-append! c (jcc sf 'Z t))
       (cfg-append! c (jmp f)))

     (cfg-block! c t)
     (cfg-append! c (phijmp cont (list (compile-expr c e2 env))))

     (cfg-block! c f)
     (cfg-append! c (phijmp cont (list (compile-expr c e3 env))))

     (cfg-block! c cont)
     (define ret (cfg-vreg! c))
     (cfg-append! c (phi ret 0))
     ret]

    [(list (and binop (or '+ '-)) e1 e2)
     (let* ([r1 (compile-expr c e1 env)]
            [r2 (compile-expr c e2 env)]
            [r (cfg-vreg! c)])
       (match binop
         ['+ (cfg-append! c (add* r1 r2 r))]
         ['- (cfg-append! c (sub* r1 r2 r))])
       r)]

    [(list fn arg)

     (define f (compile-expr c fn env))
     (define x (compile-expr c arg env))
     (define dst (cfg-vreg! c))

     (define impl (cfg-vreg! c))
     (cfg-append! c (load (mem 0 f #f #f) impl))
     (cfg-append! c (call* impl (list f x) dst))
     dst]))

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

#;(struct compilation-unit (syms) #:transparent #:mutable)
(struct link-symbol (name export? annotation value) #:transparent)

(define (write-compilation-unit syms)
  (define (write-code name exported? comment u)
    (when exported?
      (printf ".global ~a\n" name))
    (when comment
      (printf "# ~a\n" comment))
    (printf "~a:\n" name)
    (write-unit-asm u)
    (printf "\n\n"))

  (for ([s syms])
    (match s
      [(link-symbol name exported? comment (? unit? u))
       (write-code name #t comment u)])))

(define (compile program)
  (define program* (closure-convert (alphatize program '())))

  (define closures
    (for/list ([(name f) (in-dict (cdr program*))])
      (define u (cfg-unit (compile-function f)))
      (lower-x64 u)
      (link-symbol name #f (~v f) u)))

  (define fn (top-level-fn (gensym) '() (car program*)))
  (define u (cfg-unit (compile-function fn)))
  (lower-x64 u)
  (define syms (cons (link-symbol 'main #t (~v fn) u) closures))
  (write-compilation-unit syms))

(module+ test

  (require rackunit
           rackunit/text-ui)

  (define (make-temporary-dir)
    (string-trim (with-output-to-string (lambda () (assert (system "mktemp -dt compile.XXXXX"))))))

  (define (run program #:keep? [keep? #f])
    (define dir (make-temporary-dir))
    (define asm (build-path dir "test.s"))
    (define obj (build-path dir "test.o"))
    (define exec (build-path dir "test"))

    (with-output-to-file (build-path dir "test.s")
      (lambda () (compile program)))
    ;; assemble it
    (assert (system (format "nix-shell -p gcc --command 'gcc -c ~a -o ~a'" asm obj)))
    ;; link it
    (assert (system (format "nix-shell -p gcc --command 'gcc ~a -o ~a'" obj exec)))
    ;; run it
    (define-values (proc out in err) (subprocess (current-output-port)
                                                 #f
                                                 (current-error-port)
                                                 exec))

    (begin0 (let ([result (sync/timeout 5 proc)])
                  (cond
                    [(subprocess? result)
                     (subprocess-status result)]
                    [(false? result)
                     #f]))
      (close-output-port in)
      (cond
        [keep?
         (printf "keeping output directory: ~a\n" dir)]
        [else
         (delete-directory/files dir)])))

  (define (run-test-case program expected-ret)
    (test-case (~a program)
      (define result (run program))
      (check-eq? (or result 'timeout) expected-ret)))

  (define Y '(lambda f ((lambda x (lambda y ((f (x x)) y)))
                        (lambda x (lambda y ((f (x x)) y))))))
  #;(run `((lambda x (+ x 2)) 42) #:keep? #t)
  (run-tests
   (test-suite
    "toy tests"
    (run-test-case '(+ 1 2) 3)
    (run-test-case '(- 2 1) 1)
    (run-test-case '((lambda x (+ x 45)) 1) 46)
    (run-test-case '((lambda x (- x 1)) 64) 63)
    (run-test-case '((lambda x x) 24) 24)
    (run-test-case '((lambda x (x x)) (lambda x (x x))) 139) ; segfault
    (run-test-case '(((lambda x (lambda y x)) 4) 2) 4)
    (run-test-case '(ifz 0 24 42) 24)
    (run-test-case '(ifz 1 24 42) 42)
    (run-test-case `((,Y (lambda f (lambda x 120))) 2) 120)
    (run-test-case `((,Y (lambda f (lambda x
                                     (ifz x
                                          120
                                          (f (- x 1))))))
                     42) 120)
    ;; triangular numbers
    (for ([(in out) (in-dict '((0 . 0)
                               (1 . 1)
                               (2 . 3)
                               (3 . 6)
                               (4 . 10)
                               (5 . 15)
                               (6 . 21)))])
      (run-test-case `((,Y (lambda f (lambda x
                                       (ifz x
                                            0
                                            (+ x (f (- x 1)))))))
                       ,in)
                     out))
    )))










