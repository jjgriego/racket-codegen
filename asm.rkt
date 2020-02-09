#lang racket

(require racket/generic
         [for-syntax
          racket
          racket/syntax
          syntax/parse]
         "graph-color.rkt")

(define-generics instr
  (instr-mneumonic instr)
  (instr-operands instr)
  (instr-srcs instr)
  (instr-dsts instr)
  (instr-imms instr)
  (instr-targets instr))

(define-syntax (assert stx)
  (syntax-case stx ()
    [(_ expr)
     #'(when (not expr)
         (error 'assert "Assert failed: ~a" 'expr))]))

(define-syntax (define-instruction stx)
  (syntax-parse stx
    #:datum-literals (src imm dst target)
    [(_ (name:id
         (~and (~or src imm dst target)
               type) ...))

     (define fields (syntax->datum #'(type ...)))
     (define field-names (generate-temporaries #'(type ...)))
     (define field-accessors (for/list ([field field-names])
                               (format-id #'name "~a-~a" #'name field)))

     (define (filter-accessors which)
       (for/list ([type fields]
                  [acc field-accessors]
                  #:when (eq? type which))
         acc))

     (with-syntax ([(field-name ...) field-names]
                   [(accessor ...) field-accessors]
                   [(src-accessor ...) (filter-accessors 'src)]
                   [(dst-accessor ...) (filter-accessors 'dst)]
                   [(imm-accessor ...) (filter-accessors 'imm)]
                   [(target-accessor ...) (filter-accessors 'target)])
       #'(struct name (field-name ...) #:mutable #:transparent
           #:methods gen:instr
           [(define (instr-mneumonic i) 'name)
            (define (instr-operands i) (list (accessor i) ...))
            (define (instr-srcs i) (list (src-accessor i) ...))
            (define (instr-dsts i) (list (dst-accessor i) ...))
            (define (instr-imms i) (list (imm-accessor i) ...))
            (define (instr-targets i) (list (target-accessor i) ...))]))]))

(define-instruction (conjure dst))
(define-instruction (i64 dst imm))
(define-instruction (add src src dst))
(define-instruction (cmp src src dst))
(define-instruction (jcc src imm target))
(define-instruction (jmp target))
(define-instruction (copy src dst))
(define-instruction (ret src))

;; ssa-specific nonsense
(struct phi (dst idx srcs) #:mutable #:transparent
  #:methods gen:instr
  [(define (instr-mneumonic _) 'phi)
   (define (instr-operands i) (list* (phi-dst i) (phi-srcs i)))
   (define (instr-srcs i) (phi-srcs i))
   (define (instr-dsts i) (list (phi-dst i)))
   (define (instr-imms i) (list (phi-idx i)))
   (define (instr-targets i) '())])
(struct phijmp (target srcs) #:mutable #:transparent
  #:methods gen:instr
  [(define (instr-mneumonic _) 'phijmp)
   (define (instr-operands i) (list* (phijmp-target i) (phijmp-srcs i)))
   (define (instr-srcs i) (phijmp-srcs i))
   (define (instr-dsts i) '())
   (define (instr-imms i) '())
   (define (instr-targets i) (list (phijmp-target i)))])

;; vasm datastructure
(struct unit (labels blocks vregs instrs) #:transparent #:mutable)
(struct block (id instrs) #:transparent #:mutable)
(struct vinstr (id op) #:transparent #:mutable)
(struct label (block arity) #:transparent #:mutable)
(struct vreg (id display) #:transparent #:mutable)


;; extra data
(struct extra-data (kind guard struct-id contents) #:transparent #:mutable)

(define (make-extra-block-data u [default-value #f])
  (extra-data 'block
              block?
              block-id
              (build-list (length (unit-blocks u)) (lambda (_) (box default-value)))))

(define (make-extra-instr-data u [default-value #f])
  (extra-data 'instr
              vinstr?
              vinstr-id
              (build-list (length (unit-instrs u)) (lambda (_) (box default-value)))))

(define (make-extra-vreg-data u [default-value #f])
  (extra-data 'vreg
              vreg?
              vreg-id
              (build-list (length (unit-vregs u)) (lambda (_) (box default-value)))))

(define (extra-data-ref xd x)
  (unless ((extra-data-guard xd) x)
    (error 'extra-data "failed extra-data guard"))
  (unbox (list-ref (extra-data-contents xd) ((extra-data-struct-id xd) x))))

(define (extra-data-set! xd x val)
  (unless ((extra-data-guard xd) x)
    (error 'extra-data-set! "failed extra-data guard"))
  (set-box! (list-ref (extra-data-contents xd) ((extra-data-struct-id xd) x))
            val))

(define (use-extra-data xd)
  (values (lambda (x) (extra-data-ref xd x))
          (lambda (x v) (extra-data-set! xd x v))))

(define ((use-extra-data-ref xd) x)
  (extra-data-ref xd x))

;; building units

(define (empty-unit) (unit (list (label #f 0))
                           '() ; blocks
                           '() ; vregs 
                           '() ; instrs
                           ))

(define (unit-entry unit)
  (car (unit-labels unit)))

(define current-unit (make-parameter #f))

(define (block! unit . labels)
  (define blocks (unit-blocks unit))
  (define new-block (block (length blocks) '()))
  (for ([label labels])
    (set-label-block! label new-block))
  (set-unit-blocks! unit (append blocks (list new-block)))
  new-block)

(define (vreg! unit [display-name #f])
  (define vregs (unit-vregs unit))
  (define new-vreg (vreg (length vregs)
                         (or display-name
                             (format "x~a" (length vregs)))))
  (set-unit-vregs! unit (append vregs (list new-vreg)))
  new-vreg)

(define (label! unit [arity 0])
  (define labels (unit-labels unit))
  (define new-label (label #f arity))
  (set-unit-labels! unit (append labels (list new-label)))
  new-label)

(define (instr! unit block ins)
  (define all-instrs (unit-instrs unit))
  (define instrs (block-instrs block))
  (define new-instr (vinstr (length all-instrs) ins))
  (set-block-instrs! block (append instrs (list new-instr)))
  (set-unit-instrs! unit (append all-instrs (list new-instr))))

(define (block-successors block)
  (sequence-map label-block (apply sequence-append (map (compose instr-targets vinstr-op) (block-instrs block)))))

(define (predecessors unit)
  (define preds-ed (make-extra-block-data unit '()))
  (define-values (preds set-preds!) (use-extra-data preds-ed))
  (for ([block (unit-blocks unit)])
    (for ([succ (block-successors block)])
      (unless (memq block (preds succ))
        (set-preds! succ (cons block (preds succ))))))
  preds-ed)

(define (blocks-postorder unit)
  (define visited (mutable-seteq))
  (define (dfs queue)
    (match queue
      ['() empty-stream]
      [(cons block more)
       #:when (not (set-member? visited block))
       (set-add! visited block)
       (define queue* (append (filter-not (lambda (b) (set-member? visited b))
                                          (sequence->list (block-successors block))) more))
       (sequence-append (dfs queue*)
                        (list block))]
      [(cons _ more)
       (dfs more)]))

  (match (unit-labels unit)
    ['() empty-stream]
    [(list entry _ ...)
     (dfs (list (label-block entry)))]))

(define (blocks-reverse-postorder unit)
  (reverse (sequence->list (blocks-postorder unit))))

(define (blocks-fixpoint unit block-dependents initial compute-block [result-< #f] [iter-limit 1000])
  ;; this fn is written really naively and is probably very slow but it ought to work anyways
  (define result (make-extra-block-data unit initial))
  (define-values (result-of set-result!) (use-extra-data result))
  (define-values (dirty? set-dirty!) (use-extra-data (make-extra-block-data unit #t)))
  (let loop ([iters 0])
    (define block (for/first ([block (unit-blocks unit)]
                              #:when (dirty? block))
                    block))
    (when (> iters iter-limit)
      (error 'blocks-fixpoint "failed to reach a fixpoint after ~a iterations" iter-limit))
    (unless (false? block)
      (define old-value (result-of block))
      (define new-value (compute-block block result-of))
      (when (not (equal? old-value new-value))
        (when result-<
          (unless (result-< new-value old-value)
            (error 'blocks-fixpoint "monotonicity violated in block ~a:\nNew: ~a\n Old: ~a"
                   block
                   new-value
                   old-value)))
        (set-result! block new-value)
        (for ([dep (block-dependents block)])
          (set-dirty! dep #t)))
      (set-dirty! block #f)
      (loop (add1 iters))))
  result)

;; instr-liveness : Vinstr -> Seteq Vreg -> Extra-Data Block (Maybe (Seteq Vreg))
(define (instr-liveness instr live-out block-live-in)
  (match (vinstr-op instr)
    [(ret reg)
     ;; if we're returning from this block (which must be the last instruction)
     ;; then only the result register is live
     (seteq reg)]
    [(phi dst idx srcs)
     ;; phis only mark their dest as dead beforehand--the phijmp is the src that
     ;; will mark the input register(s) as live beforehand
     (set-remove live-out dst)]
    [_ ;; ... for all other instructions...
     (set-subtract (apply set-union
                          live-out
                          ;; mark regs used as a src live
                          (list->seteq (instr-srcs (vinstr-op instr)))
                          ;; merge in the regs live at entry to any targets
                          (map (lambda (l) (or (block-live-in (label-block l))
                                               (seteq)))
                               (instr-targets (vinstr-op instr))))
                   ;; kill any regs used as a dst
                   (list->seteq (instr-dsts (vinstr-op instr))))]))


(define (liveness unit [preds-ed (predecessors unit)])
  (define preds (use-extra-data-ref preds-ed))
  (blocks-fixpoint unit preds #f
                   (lambda (block block-live-regs)
                     (for/fold ([live (seteq)])
                               ([instr (reverse (block-instrs block))])
                       (instr-liveness instr live block-live-regs)))))

;; vregs have one of the following storage classes, which form a lattice as
;; follows
;;            top
;;       _____/|
;;      /      |
;;    word     |
;;   /   \     |
;;  gp  spill  sf
;;   \__ | ___/
;;      \|/
;;       #f
;;
(define (storage-classes u [storage-class-ed (make-extra-vreg-data u 'top)])
  (define-values (storage-class set-storage-class!) (use-extra-data storage-class-ed))

  (define (intersect-storage-class s1 s2)
    (match* (s1 s2)
      [('top x) x]
      [(x 'top) x]
      [(#f x) #f]
      [(x #f) #f]
      [('sf 'sf) 'sf]
      [('sf x) #f]
      [(x 'sf) #f]
      [('word x) x]
      [(x 'word) x]
      [('gp    'gp)    'gp]
      [('spill 'spill) 'spill]
      [(_ _) #f]))

  (define (refine! v sc)
    (define sc* (intersect-storage-class (storage-class v) sc))
    (assert sc*)
    (set-storage-class! v sc*))

  (for ([block (unit-blocks u)])
    (for ([instr (block-instrs block)])
      (match (vinstr-op instr)
        ;; jcc and cmp operate on the sf register only
        [(jcc src _ _)
         (refine! src 'sf)]
        [(cmp s0 s1 dst)
         (refine! s0 'gp)
         (refine! s1 'gp)
         (refine! dst 'sf)]
        ;; copy is the special snowflake that can move between
        ;; gp and spill space
        [(copy src dst)
         (refine! src 'word)
         (refine! dst 'word)]
        ;; phis are really copies we'd like to be able to optimize away--in
        ;; particular it's possible for a spilled vreg to be the dst or a
        ;; src of a phi
        [(phi dst _ srcs)
         (refine! dst 'word)
         (for ([src srcs])
           (refine! src 'word))]
        ;; phijmps permit spills also for the same reason
        [(phijmp _ srcs)
         (for ([src srcs]) (refine! src 'word))]
        ;; unless otherwise specified, instructions operate on gps
        [ins
         (for ([src (instr-srcs ins)])
           (refine! src 'gp))
         (for ([src (instr-dsts ins)])
           (refine! src 'gp))])))
  storage-class-ed)

#;(define (spill u spilled storage-class-ed)
  (define-values (storage-class set-storage-class!) (use-extra-data storage-class-ed))
  (define spill-regs (build-list (length spilled) (lambda () (vreg! u))))
  (set-storage-class! spill-reg 'spill)

  ;; the def of the spilled vreg is followed by a copy into the spill register

  ;; each use of the spilled vreg is replaced with a copy from the spill reg to a fresh reg
  )

(define (regalloc unit
                  available-regs
                  [preds-ed (predecessors unit)]
                  [live-ed (liveness unit preds-ed)])
  (define alloc-ed (make-extra-vreg-data unit))
  (define-values (allocs set-alloc!) (use-extra-data alloc-ed))

  (define interference (make-vector (length (unit-vregs unit)) (list)))
  (define chromatic-number 0)
  ;; mark two vregs as being live at the same moment
  (define (add!-interferes-with v w)
    (when (not (eq? v w))
      (vector-set! interference (vreg-id v) (set-add (vector-ref interference (vreg-id v)) (vreg-id w)))
      (vector-set! interference (vreg-id w) (set-add (vector-ref interference (vreg-id w)) (vreg-id v)))))
  (define (add!-live-interference regs)
    (define size (set-count regs))
    (set! chromatic-number (max chromatic-number size))
    (for* ([v regs] [w regs]) (add!-interferes-with v w)))
  (define block-live-regs (use-extra-data-ref live-ed))
  (for ([block (unit-blocks unit)])
    ;; we're going to walk the instructions in the block backwards
    ;; and materialize the interference graph as we go--
    (define block-live-in
      (for/fold ([live-out (seteq)])
                ([instr (reverse (block-instrs block))])
        (define live-in (instr-liveness instr live-out block-live-regs))
        ;; all regs live out of the instr interfere with one another
        (add!-live-interference live-out)
        live-in))
    ;; we should have reached the same result as the
    ;; block-level liveness analysis
    (assert (equal? block-live-in (block-live-regs block)))
    ;; all vregs live at block entry interfere
    (add!-live-interference block-live-in))

  (assert (< chromatic-number (length available-regs)))
  (define colors (color interference (length available-regs)))
  (for ([i (in-naturals)]
        [c colors])
    (set-alloc! (list-ref (unit-vregs unit) i)
                (list-ref available-regs c)))
  alloc-ed)




(define (show-unit u . extra-datas)
  (define vreg-extra-data (filter (lambda (ed) (eq? 'vreg (extra-data-kind ed))) extra-datas))
  (define instr-extra-data (filter (lambda (ed) (eq? 'instr (extra-data-kind ed))) extra-datas))
  (define block-extra-data (filter (lambda (ed) (eq? 'block (extra-data-kind ed))) extra-datas))

  (define (show-extra-data x eds delim)
    (string-join (map (lambda (ed)
                        (~a (extra-data-ref ed x)))
                      eds)
                 delim))

  (define (show-instr i)
    (define (format-operand o)
      (cond
        [(vreg? o)
         (string-normalize-spaces
          (string-append
           (vreg-display o)
           (if (empty? vreg-extra-data) "" ":")
           (show-extra-data o vreg-extra-data ":")))]
        [(label? o) (format "-> B~a" (block-id (label-block o)))]
        [else (format "~a" o)]))

    (displayln
     (string-normalize-spaces
      (string-append
       (format "~a " (instr-mneumonic i))
       (string-join (map format-operand (instr-operands i))
                    " ")
       (show-extra-data i instr-extra-data " ")))))

  (define (show-block b)
    (when (empty? (block-instrs b))
      (printf "  (empty)\n"))
    (unless (empty? block-extra-data)
      (displayln (show-extra-data b block-extra-data "\n")))
    (for ([instr (block-instrs b)])
      (printf "  ")
      (show-instr (vinstr-op instr)))
    (printf "\n"))

  (define (show-label l)
    (printf "Block B~a " (block-id (label-block l)))

    (printf "\n")
    (show-block (label-block l)))

  (for ([label (unit-labels u)]) (show-label label)))


(define-syntax (define-vregs stx)
  (syntax-case stx ()
    [(_ unit name ...)
     #'(begin
         (define u unit)
         (define name (vreg! u)) ...)]))

(define-syntax (in-block stx)
  (syntax-case stx ()
    [(_ unit label-expr instr ...)
     #'(begin
         (define u unit)
         (define b (block! u label-expr))
         (instr! u b instr) ...)]))


(module+ test
  (begin
    (define u (empty-unit))
    (define loop-header (label! u 3))
    (define loop-body (label! u))
    (define done (label! u))
    (define-vregs u n0 u0 v0)
    (define-vregs u n1 n2 u1 v1 next x0 x1 sf0)

    (in-block
     u (unit-entry u)
     (conjure n0)
     (i64 u0 1)
     (i64 v0 1)
     (phijmp loop-header (list n0 u0 v0)))

    (define b1 (block! u loop-header))
    (instr! u b1 (phi n1 0 (list n0 n2)))
    (instr! u b1 (phi u1 1 (list u0 v1)))
    (instr! u b1 (phi v1 2 (list v0 next)))
    (instr! u b1 (i64 x0 0))
    (instr! u b1 (cmp n1 x0 sf0))
    (instr! u b1 (jcc sf0 'Z done))
    (instr! u b1 (jmp loop-body))

    (define b3 (block! u loop-body))
    (instr! u b3 (i64 x1 -1))
    (instr! u b3 (add x1 n1 n2))
    (instr! u b3 (add u1 v1 next))
    (instr! u b3 (phijmp loop-header (list n2 v1 next)))

    (define b4 (block! u done))
    (instr! u b4 (ret v1))
    (show-unit u)

    #;(for ([block (stream-take (blocks-postorder u) 10)])
      (displayln (block-id block)))

    (for ([block (blocks-reverse-postorder u)])
      (displayln (block-id block)))

    (define live-in (liveness u))
    (define st-classes (storage-classes u))
    (define allocs (regalloc u '(rax rbx rcx rdx rsi rdx r8 r9 r10)))

    (show-unit u st-classes live-in allocs)
    ))




