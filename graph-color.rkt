#lang racket

(require "qcheck.rkt")

(provide color)

(define (neighbors g v)
  (vector-ref g v))

(define (reverse-lex-bfs g)
  (define g-sets
    (vector-map (lambda (l) (list->seteq l)) g))
  (define (neighbors-set v)
    (vector-ref g-sets v))
  (define n (vector-length g))

  (if (= 0 n)
      '()
      (let loop ([sets (list (list->seteq (sequence->list (in-range n))))])
        (if (empty? sets)
            empty-stream
            (let* ([v (set-first (first sets))]
                   [neighbors (neighbors-set v)]
                   [new-sets
                    (filter-not set-empty?
                                (append* (for/list ([set sets])
                                           (list (set-intersect set neighbors)
                                                 (set-subtract set neighbors (seteq v))))))])
              (stream-cons v (loop new-sets)))))))

(define (color g n)
  (define available-colors (build-vector (vector-length g) (lambda (_) (for/mutable-seteq ([color (in-range n)]) color))))
  (define colors (make-vector (vector-length g) #f))

  (for ([v (reverse-lex-bfs g)])
    (define available (vector-ref available-colors v))
    (when (set-empty? available)
      (error 'color "Could not ~a-color graph: ~a" n g))
    (define c (set-first available))
    (set-clear! available)
    (for ([neigh (neighbors g v)])
      (set-remove! (vector-ref available-colors neigh) c))
    (vector-set! colors v c))

  colors)


;; -----------------------------------------------------------------------------
;; Literally everything else in the file is for testing purposes .... :(
;; -----------------------------------------------------------------------------

(define (make-chordal-graph n)
  ;; the strategy is that we make a chordal graph by adding new vertices
  ;; by connecting them to an entire connected subset of the graph
  ;; that way, any cycles formed will be triangulated from the outset
  (define graph (make-vector n (seteq)))

  (define (add-edge n m)
    (vector-set! graph n (set-add (vector-ref graph n) m))
    (vector-set! graph m (set-add (vector-ref graph m) n)))

  (define (find-connected-vertices n goal)
    ;; (nb) if goal is 1, we generate trees !
    (define start (random n))
    (define visited (mutable-seteq start))
    (define adjacent (list->mutable-seteq (vector-ref graph start)))

    (for ([_ (in-range (sub1 goal))])
      (unless (set-empty? adjacent)
        (define new (first (shuffle (set->list adjacent))))
        (set-remove! adjacent new)
        (set-add! visited new)
        (set-union! adjacent (set-subtract (list->seteq (vector-ref graph new))
                                           visited))))
    (in-set visited))
  (for ([v (in-range n)] #:when (> v 0))
    (for ([neighbor (find-connected-vertices v (random v))])
      (add-edge v neighbor)))

  (vector-map set->list graph))

(define (shrink-chordal-graph g)
  ;; we can _always_ generate a chordal graph from another by removing a vertex in its entirety
  (define (remove-vertex g removed)
    (define n (vector-length g))
    (define (map-vertex v)
      (if (< v removed)
          v
          (sub1 v)))
    (for/vector #:length (sub1 n)
      ([v (in-range n)]
       #:when (not (= v removed)))
      (map map-vertex (filter-not (lambda (v) (= v removed)) (vector-ref g v)))))
  (if (not (vector-empty? g))
      (let ([g2 (remove-vertex g (random (vector-length g)))])
        (stream-cons g2 (shrink-chordal-graph g2)))
      '()))

(define (cliques g)
  (define (connected? u v)
    (member v (vector-ref g u)))
  ;; dumb naive thing b/c can't be fucked to do otherwise
  (define (n-cliques g n-1-cliques)
    (cond
      [(false? n-1-cliques)
       (for/list ([v (in-range (vector-length g))])
         (seteq v))]
      [else
       (for*/list ([c n-1-cliques]
                   [v (in-range (vector-length g))]
                   #:when (and (not (set-member? c v))
                               (for/and ([u c])
                                 (and (< v u)
                                      (connected? v u)))))
         (set-add c v))]))
  (let loop ([c #f])
    (define next (n-cliques g c))
    (if (empty? next)
        '()
        (stream-cons next (loop next)))))


(define arbitrary-chordal-graph (arbitrary (lambda () (make-chordal-graph (random 3 (max (current-size) 4))))
                                           shrink-chordal-graph))

#;(check ([graph arbitrary-chordal-graph])
       (color graph (max-clique graph)))

(module+ test
  (define g0
    (vector '(1 2 3)
            '(0 2 3)
            '(0 1)
            '(0 1)))

  (displayln (sequence->list (reverse-lex-bfs g0)))
  (displayln (color g0 3)))
