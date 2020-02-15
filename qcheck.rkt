#lang racket

(provide (all-defined-out))

(struct arbitrary (gen shrink))

(define current-size (make-parameter 40 positive-integer?))

(define (check-property arb property
                        #:trials [trial-count 100]
                        #:shrink-attempts [shrink-attempts 100]
                        #:shrink? [shrink? #t])
  (define gen (arbitrary-gen arb))
  (define shrink (arbitrary-shrink arb))

  (define (test v)
    (define tag (make-continuation-prompt-tag))
    (call-with-continuation-prompt
     (lambda ()
       (call-with-exception-handler (lambda (exn)
                                      (abort-current-continuation tag #f))
                                    (lambda () (property v))))
     tag
     identity
     ))

  (define (report-failure val n [more #f])
    (error 'check-property "Check failed on example ~a after ~a trials ~a"
           val
           n
           (or (and more (string-append ": "more)) "")))

  (define (report-try-shrink val trial [n 0])
    (when (not shrink?)
      (report-failure val trial "(shrinking not attempted"))
    (when (>= n shrink-attempts)
      (report-failure val trial (format "Could not shrink further (reached limit at iter ~a)" n)))
    
    (define shrunken-values (shrink val))
    (when (stream-empty? shrunken-values)
      (report-try-shrink val trial (add1 n)))
    
    (define shrunken (stream-filter (lambda (v) (not (test v))) shrunken-values))
    (when (stream-empty? shrunken)
      (report-try-shrink val trial (add1 n)))
    
    (report-try-shrink (for/last ([v shrunken]) v)
                       trial
                       (add1 n)))
  
  (for ([trial (in-range trial-count)])
    (define val ((arbitrary-gen arb)))
    (unless (test val)
      (displayln (format "failed: ~a" val))
      (report-try-shrink val trial))))

(define (arbitrary-values . arbs)
  (arbitrary
   (lambda ()
     (map (lambda (a) ((arbitrary-gen a))) arbs))
   (lambda (vals)
     (apply cartesian-product (for/list ([val vals]
                                   [arb arbs])
                          (stream->list ((arbitrary-shrink arb) val)))))))

(define arbitrary-natural
  (arbitrary
   (lambda ()
     (random 0 (current-size)))
   (lambda (n)
     (if (> n 0)
         (in-range (- n 1) -1 -1)
         '()))))

(define (arbitrary-in lower upper)
  (arbitrary
   (lambda ()
     (random lower upper))
   (lambda (n)
     (if (> n lower)
         (in-range (- n 1) (- lower 1) -1)
         '()))))

(define-syntax (check stx)
  (syntax-case stx ()
    [(_ ([id arb] ...) body ...)
     #'(let ([arbitrary-val (arbitrary-values arb ...)])
       (check-property arbitrary-val
                       (lambda (v)
                         (match v
                           [(list id ...)
                            (begin
                              body ...)]))))]))