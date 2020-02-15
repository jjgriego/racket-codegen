#lang racket

(require racket/generic
         racket/control
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
  (instr-targets instr)
  (instr-visit-operands instr f))

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
     (define field-setters (for/list ([field field-names])
                               (format-id #'name "set-~a-~a!" #'name field)))

     (define (filter-accessors which)
       (for/list ([type fields]
                  [acc field-accessors]
                  #:when (eq? type which))
         acc))

     (with-syntax ([(field-name ...) field-names]
                   [(accessor ...) field-accessors]
                   [(setter ...) field-setters]
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
            (define (instr-visit-operands i f)
              (f 'type (accessor i) (lambda (x) (setter i x))) ...)
            (define (instr-targets i) (list (target-accessor i) ...))]))]))

(define-instruction (conjure dst))
(define-instruction (i64 dst imm))
(define-instruction (add src src dst))
(define-instruction (cmp src src dst))
(define-instruction (jcc src imm target))
(define-instruction (jmp target))
(define-instruction (copy src dst))
(define-instruction (ret src))
(define-instruction (phi dst imm))

;; ssa-specific nonsense
(struct phijmp (target srcs) #:mutable #:transparent
  #:methods gen:instr
  [(define (instr-mneumonic _) 'phijmp)
   (define (instr-operands i) (list* (phijmp-target i) (phijmp-srcs i)))
   (define (instr-srcs i) (phijmp-srcs i))
   (define (instr-dsts i) '())
   (define (instr-imms i) '())
   (define (instr-targets i) (list (phijmp-target i)))
   (define (instr-visit-operands i f)
     (f 'target (phijmp-target i) (lambda (x) (set-phijmp-target! i x)))
     (define ((update-srcs-at! idx) x)
       (set-phijmp-srcs! i (list-set (phijmp-srcs i) idx x)))
     (for ([src (phijmp-srcs i)]
           [i (in-naturals)])
       (f 'src src (update-srcs-at! i))))])

(define (instr-rename-vreg! ins old-reg new-reg)
  (instr-visit-operands ins
                        (lambda (type val set-val!)
                          (when (and (vreg? val) (eq? old-reg val))
                            (set-val! new-reg)))))


;; vasm datastructure
(struct unit (labels blocks vregs instrs) #:transparent #:mutable)
(struct block (id instrs) #:transparent #:mutable)
(struct vinstr (id op) #:transparent #:mutable)
(struct label (block arity) #:transparent #:mutable)
(struct vreg (id display) #:transparent #:mutable)


;; extra data
(struct extra-data (kind guard struct-id contents default) #:transparent #:mutable)

(define (make-extra-block-data u [default-value #f])
  (extra-data 'block
              block?
              block-id
              (build-list (length (unit-blocks u)) (lambda (_) (box default-value)))
              default-value))

(define (make-extra-instr-data u [default-value #f])
  (extra-data 'instr
              vinstr?
              vinstr-id
              (build-list (length (unit-instrs u)) (lambda (_) (box default-value)))
              default-value))

(define (make-extra-vreg-data u [default-value #f])
  (extra-data 'vreg
              vreg?
              vreg-id
              (build-list (length (unit-vregs u)) (lambda (_) (box default-value)))
              default-value))

(define (extra-data-ref-raw xd x)
  (match xd
    [(extra-data kind pred? struct-id contents default)
     (unless (pred? x)
       (error 'extra-data "failed extra-data guard"))
     (define id (struct-id x))
     (cond
       [(< id (length contents)) (list-ref contents id)]
       [else
        (define difference (- (add1 id) (length contents)))
        (define contents* (append contents (build-list difference (lambda (_) (box default)))))
        (set-extra-data-contents! xd contents*)
        (list-ref contents* id)])]))

(define (extra-data-ref xd x)
  (unbox (extra-data-ref-raw xd x)))

(define (extra-data-set! xd x val)
  (set-box! (extra-data-ref-raw xd x) val))

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

(define (instr-raw! unit ins)
  (define all-instrs (unit-instrs unit))
  (define new-instr (vinstr (length all-instrs) ins))
  (set-unit-instrs! unit (append all-instrs (list new-instr)))
  new-instr)

(define (instr! unit block ins)
  (define instrs (block-instrs block))
  (define new-instr (instr-raw! unit ins))
  (set-block-instrs! block (append instrs (list new-instr)))
  new-instr)

(define (block-insert-instr! u block instr [i 0])
  (define-values (before after) (split-at (block-instrs block) i))
  (define new-instr (instr-raw! u instr))
  (define instrs (append before (cons new-instr after)))
  (set-block-instrs! block instrs)
  new-instr)

(define (block-append-instr! u block instr)
  (define new-instr (instr-raw! u instr))
  (define instrs (append (block-instrs block) (list new-instr)))
  (set-block-instrs! block instrs)
  new-instr)

(define (block-delete-instr! block instr)
  (set-block-instrs! block (filter-not (lambda (i) (eq? i instr)) (block-instrs block))))

(define (block-instr-idx block instr)
  (index-where
   (block-instrs block)
   (lambda (i) (eq? i instr))))

(define (find-def u reg)
  (for/or ([block (unit-blocks u)])
    (for/first ([instr (block-instrs block)]
                #:when (memq reg (instr-dsts (vinstr-op instr))))
      (cons block instr))))

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
    [(phi dst idx)
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
        [(phi dst _)
         (refine! dst 'word)]
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

;; visit all the blocks reachable from this one
(define (reachable-blocks u block)
  (define queue (list block))
  (define visited (mutable-seteq block))
  (let loop ([queue (list block)])
    (match queue
      [(cons b bs)
       (set! queue bs)
       (for ([instr (block-instrs b)])
         (for ([target (instr-targets (vinstr-op instr))])
           (define block* (label-block target))
           (when (not (set-member? visited block*))
             (set-add! visited block*)
             (set! queue (append queue (list block*))))))
       (stream-cons b (loop queue))]
      [_ empty-stream])))

(define (spill u spilled storage-class-ed)
  (define-values (storage-class set-storage-class!) (use-extra-data storage-class-ed))


  (define (spilled-vregs regs)
    (filter (lambda (reg)
              (define idx (index-where spilled
                                       (lambda (spill-reg)
                                         (eq? spill-reg reg))))
              (and idx (cons reg idx)))
            regs))

  ;; the def of the spilled vreg is followed by a copy into the spill register
  (for ([spilled-reg spilled])
    (define def-location (find-def u spilled-reg))
    (assert def-location)
    (define def-block (car def-location))
    (define def-instr (cdr def-location))

    (define slot (vreg! u))
    (set-storage-class! slot 'spill)

    ;; immediately after the dst (or in the dst if it's a copy or phi)
    ;; copy to the spill slot
    (define def-idx (block-instr-idx def-block def-instr))
    (define spill-instr
      (let ([i (vinstr-op def-instr)])
        (match i
          [(phi dst _)
           #:when (eq? dst spilled-reg)
           (instr-rename-vreg! i dst slot)
           def-instr]
          [(copy _ dst)
           #:when (eq? dst spilled-reg)
           (instr-rename-vreg! i dst slot)
           def-instr]
          [_
           #:when (memq spilled-reg (instr-dsts i))
           (block-insert-instr! u def-block
                                (copy spilled-reg slot)
                                (add1 def-idx))]
          [_ #f])))
    (assert spill-instr)

    (define (fix-instr! b idx)
      (define vi (list-ref (block-instrs b) idx))
      (define ins (vinstr-op vi))
      (unless (eq? spill-instr vi)
        (match ins
          ;; phijmp and copy can just substitute the src
          [(phijmp _ srcs)
          #:when (memq spilled-reg srcs)
          (instr-rename-vreg! ins spilled-reg slot)]
          [(copy src _ )
          #:when (eq? src spilled-reg)
          (instr-rename-vreg! ins spilled-reg slot)]
          ;; other instructions using the spilled reg as a slot
          ;; need to have a copy inserted to reload the spill
          [_
          #:when (memq spilled-reg (instr-srcs ins))
          (define r (vreg! u))
          (block-insert-instr! u b (copy slot r) idx)
          (instr-rename-vreg! ins spilled-reg r)]
          [_ (void)])))

    ;; XXX: kludgy iteration b/c we modify the block as we traverse it
    (define (fix-block! b [start 0])
      (for ([idx (in-naturals start)])
        #:break (>= idx (length (block-instrs b)))
        (fix-instr! b idx)))

    (for ([block (unit-blocks u)])
      (fix-block! block))))

;; the graph coloring failed for immediately following the
;; provided instruction, or at block entry if instr is #f
(struct alloc-failure (block instr cls live-regs spills-needed) #:transparent)

(struct virtual-reg (cls idx) #:prefab)

(define (try-regalloc u
                      available-regs
                      [preds-ed (predecessors u)]
                      [live-ed (liveness u preds-ed)]
                      [storage-class-ed (storage-classes u)])
  (define-values (storage-class set-storage-class!) (use-extra-data storage-class-ed))

  (struct iference-graph (label->idx adjacency chromatic-number) #:transparent #:mutable)

  ;; construct an interference graph for each register class
  (define interference-graphs
    (for/hasheq ([(cls spec) (in-dict available-regs)])
      ;; empty list is an invalid register spec
      (assert (or (false? spec) (not (empty? spec))))
      ;; if there's only a single register of this class, don't bother
      ;; with the graph coloring algorithm--just assert that only one is live at a time

      (cond
        [(and spec (= 1 (length spec)))
         (values cls #f)]
        [else
         (define members (filter (lambda (r) (eq? cls (storage-class r))) (unit-vregs u)))
         (define lookup (for/hasheq ([r members]
                                   [idx (in-naturals)])
                          (values r idx)))
         (values cls (iference-graph lookup (make-vector (length members) (list)) 1))])))

  ;; mark two vregs as being live at the same moment
  (define (add!-interferes-with graph v w)
    (define (idx r) (hash-ref (iference-graph-label->idx graph) r))
    (define adj (iference-graph-adjacency graph))
    (when (not (eq? v w))
      (vector-set! adj (idx v) (set-add (vector-ref adj (idx v)) (idx w)))
      (vector-set! adj (idx w) (set-add (vector-ref adj (idx w)) (idx v)))))

  (define (visit-live regs block instr)
    (define (live-regs-with-class cls)
      (filter (lambda (r) (eq? cls (storage-class r)))
              (set->list regs)))

    (define (interference-set regs graph)
      (set-iference-graph-chromatic-number! graph
                                            (max (length regs)
                                                 (iference-graph-chromatic-number graph)))
      (for* ([v regs] [w regs]) (add!-interferes-with graph v w)))

    ;; for each register class
    (for ([(cls spec) (in-dict available-regs)])
      (define live-set (live-regs-with-class cls))
      (define graph (hash-ref interference-graphs cls))
      (cond
        [(false? spec)
         ;; the number of registers here is unbounded, just color them
         (interference-set live-set graph)]
        [(= 1 (length spec))
         ;; we have exactly one register so don't fuck around w/ the graph
         (when (> (length live-set) 1)
           (abort (alloc-failure block instr cls live-set (sub1 (length live-set)))))]
        [else
         (when (> (length live-set) (length spec))
           (abort (alloc-failure block instr cls live-set (-  (length live-set) (length spec)))))
         (interference-set live-set graph)])))

  ;; visit the whole unit and track liveness
  (define block-live-regs (use-extra-data-ref live-ed))
  (prompt
   (for ([block (unit-blocks u)])
     ;; we're going to walk the instructions in the block backwards
     ;; and materialize the interference graph as we go--
     (define block-live-in
       (for/fold ([live-out (seteq)])
                 ([instr (reverse (block-instrs block))])
         (define live-in (instr-liveness instr live-out block-live-regs))
         ;; all regs live out of the instr interfere with one another
         (visit-live live-out block instr)
         live-in))
     ;; we should have reached the same result as the
     ;; block-level liveness analysis
     (assert (equal? block-live-in (block-live-regs block)))
     ;; all vregs live at block entry interfere
     (visit-live block-live-in block #f))

   ;; now color every register
   (define register-ed (make-extra-vreg-data u))
   (define-values (register set-register!) (use-extra-data register-ed))

   (define (assign-registers graph num-colors color->register)
     (match graph
       [(iference-graph label->idx adjacency chromatic-number)
        (assert (<= chromatic-number num-colors))
        (define colors (color adjacency num-colors))
        (for ([(vreg idx) label->idx])
          (set-register! vreg (color->register (vector-ref colors idx))))]))

   (for ([(cls spec) (in-dict available-regs)])
     (cond
       [(false? spec)
        (define graph (hash-ref interference-graphs cls))
        (assign-registers graph (iference-graph-chromatic-number graph)
                          (lambda (i) (virtual-reg cls i)))]
       [(= 1 (length spec))
        (for ([reg (unit-vregs u)]
              #:when (eq? (storage-class reg) cls))
          (set-register! reg (car spec)))]
       [else
        (assign-registers (hash-ref interference-graphs cls)
                          (length spec)
                          (lambda (i) (list-ref spec i)))]))

   register-ed))



(define (regalloc u available-regs
                  [preds-ed (predecessors u)]
                  [live-ed (liveness u preds-ed)]
                  [storage-classes-ed (storage-classes u)])
  ;; update our storage class knowledge
  (storage-classes u storage-classes-ed)
  (let loop ([live-ed live-ed])
    (define (spill-and-retry choices)
      (printf "Spilling and retrying register allocation:\n")
      (for ([spill choices])
        (printf "  - ~a\n" (vreg-display spill)))
      (spill u choices storage-classes-ed)
      (storage-classes u storage-classes-ed)
      (define live-ed* (liveness u preds-ed))
      (show-unit u live-ed* storage-classes-ed)
      (loop live-ed*))
    (match (try-regalloc u
                         available-regs
                         preds-ed
                         live-ed
                         storage-classes-ed)
      [(alloc-failure block instr cls regs num-to-spill)
       (assert (not (eq? cls 'sf)))
       ;; we can't spill any register that's def'd by the given instruction (that would be bad)
       ;; or any register that's immediately src'd by the following instruction
       ;; (that would be counterproductive [unless that instruction allows the src to be spill]
       (define idx (block-instr-idx block instr))
       (define succ (and (< (add1 idx) (length (block-instrs block)))
                         (let ([i (list-ref (block-instrs block) (add1 idx))])
                           (and (not (phijmp? (vinstr-op i)))
                                (not (copy? (vinstr-op i)))
                                i))))
       (define eligible-regs (filter-not (lambda (r)
                                           (or (and succ (memq r (instr-srcs (vinstr-op succ))))
                                               (and instr (memq r (instr-dsts (vinstr-op instr))))))
                                         (set->list regs)))
       (printf "Failed to allocate in B~a at instr ~a (live set ~a)\n"
               (block-id block)
               (vinstr-id instr)
               (map vreg-display (set->list regs)))
       ;; we also don't have anything intelligent to do right now, so just spill some arbitrary set
       ;; of eligible registers to bring us down to the requred threshold
       (spill-and-retry
        (take eligible-regs num-to-spill))]
      [register-assignments register-assignments])))

(define (phi-registers u)
  (define phi-regs-ed (make-extra-block-data u))
  (define-values (phi-regs set-phi-regs!) (use-extra-data phi-regs-ed))

  (for ([label (unit-labels u)])
    (define block (label-block label))
    (set-phi-regs! block (make-vector (label-arity label) #f)))

  (for ([block (unit-blocks u)])
    (for ([instr (block-instrs block)])
      (match (vinstr-op instr)
        [(phi dst idx)
         (assert (< idx (vector-length (phi-regs block))))
         (vector-set! (phi-regs block) idx dst)]
        [_ #f])))

  phi-regs-ed)

(define (shuffle make-spare register regs-in regs-out)
  (define renames (for/list ([in regs-in] [out regs-out])
                    (cons in out)))
  (define spare (box #f))
  (let loop ([renames renames]
             [rev-order '()])

    (define (spare-reg)
      (or (unbox spare)
          (let ([sp (make-spare)])
            (set-box! spare sp)
            sp)))

    (define (next-cycle remaining candidate chain)
      ;; candidate: D->A
      ;; chain: A->B B->C C->D
      (define conflict
        (for/or ([r renames])
          (and (not (eq? r candidate))
               (equal? (register (car r))
                       (register (cdr candidate)))
               r)))
      (cond
        [(and conflict
              (not (empty? chain))
              (eq? (car chain) conflict))
         ;; we have a cycle--allocate the spare register if we need
         (define spare (spare-reg))
         ;; move the conflict's src to the spare,
         ;; then exec the candidate, then (after the rest of the cycle is resolved)
         ;; move the spare to the conflict's dest
         (values remaining
                 (append
                  (list (cons spare (cdr (car chain))))
                  (cdr chain)
                  (list
                   candidate
                   (cons (car (car chain)) spare))))]
        [conflict
         ;; we have a conflict but it doesn't form a cycle
         (next-cycle (remove conflict remaining eq?)
                     conflict
                     (append chain (list candidate)))]
        [else
         ;; no conflict--we can execute the current chain of renames
         (values
          remaining
          (append
           chain
           (list candidate)))]))

    (match renames
      ['()
       (for/list ([r (reverse rev-order)]
                  #:when (not (equal? (register (car r))
                                      (register (cdr r)))))
         (copy (car r) (cdr r)))]
      [(cons r rs)
       (define-values (remaining cyc) (next-cycle rs r '()))
       (loop remaining
             (append cyc rev-order))])))

(define (unphi u
               available-regs
               block-live-ed
               registers-ed
               phi-regs-ed)
  (define-values (block-live set-block-live!) (use-extra-data block-live-ed))
  (define-values (register set-register!) (use-extra-data registers-ed))
  (define-values (phi-regs set-phi-regs!) (use-extra-data phi-regs-ed))

  (for ([block (unit-blocks u)])
    ;; delete all the leading phis
    (for ([instr (block-instrs block)])
      #:break (not (phi? (vinstr-op instr)))
      (block-delete-instr! block instr))

    ;; delete the trailing phijmp
    (unless (empty? (block-instrs block))
      (for ([instr (block-instrs block)]
            [idx (in-range (sub1 (length (block-instrs block))))])
        (assert (not (phijmp? (vinstr-op instr))))))
    (define last-i (last (block-instrs block)))
    (match (vinstr-op last-i)
      [(phijmp label srcs)
       (define regs (phi-regs (label-block label)))
       (assert (= (vector-length regs) (length srcs)))
       (block-delete-instr! block last-i)
       ;; select a spare vreg for this block
       (define (make-spare)
         (define (find-free)
          (define gps (dict-ref available-regs 'gp))
          ;; this is overly pessimistic since we might be able to use one of the dst
          ;; registers if only part of the shuffle is a permutation, but alas
          (define live (set-union (for/set ([r (block-live (label-block label))]) (register r))
                                  (list->set (map register srcs))
                                  (for/set ([dst regs]) (register dst))))
          (match (for/first ([r gps]
                              #:when (not (set-member? live r)))
                    r)
            [#f
              ;; fine! we'll use a spill
             (for/first ([idx (in-naturals)]
                                     #:when (not (set-member? live (virtual-reg 'spill idx))))
                          (virtual-reg 'spill idx))]
            [gp gp]))
         (define vreg (vreg! u))
         (set-register! vreg (find-free))
         vreg)
       (for ([cpy (shuffle make-spare register srcs regs)])
         (block-append-instr! u block cpy))
       (block-append-instr! u block (jmp label))]
      [_ #f])))

(define (trivial-copy u registers-ed)
  (define-values (register set-register!) (use-extra-data registers-ed))
  (define (trivial? instr)
    (match (vinstr-op instr)
      [(copy src dst)
       (equal? (register src) (register dst))]
      [_ #f]))
  (for* ([block (unit-blocks u)]
         [instr (block-instrs block)])
    (when (trivial? instr)
      (block-delete-instr! block instr))))








(define (show-unit u . extra-datas)
  (printf "-------------------------------------------\n")
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
    (instr! u b1 (phi n1 0))
    (instr! u b1 (phi u1 1))
    (instr! u b1 (phi v1 2))
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

    #;(for ([block (blocks-reverse-postorder u)])
      (displayln (block-id block)))


    (define live-in (liveness u))
    (define st-classes (storage-classes u))
    #;(spill u (list (spill-spec n1 b1)) st-classes)
    (storage-classes u st-classes)
    (show-unit u st-classes)
    (define available-regs '((sf . (sf))
                             (gp . (rax rbx rcx))
                             (spill . #f)))
    (define allocs (regalloc u available-regs))
    (show-unit u allocs)
    (unphi u available-regs (liveness u) allocs (phi-registers u))
    (show-unit u allocs)
    #;(trivial-copy u allocs)
    #;(show-unit u allocs)
    ))




