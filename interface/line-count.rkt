#lang racket

(require racket/cmdline
         csv-reading
         file/glob
         syntax/moddep
         setup/dirs
         pkg/path
         racket/path)

(define (invoke-cloc args)
  (define s (with-output-to-string
              (λ () (apply system* (find-executable-path "cloc") "--csv" args))))

  (first (filter-map
          (λ (line)
            (match line
              [`(,_ "Racket" ,_ ,_ ,total) (string->number total)]
              [_ #f]))
          (csv->list s))))

(define (path-prefix? a b)
  (string-prefix? (path->string (resolve-path a))
                  (path->string (resolve-path b))))

(define (trace entry-path)
  (define the-mod
    (cond
      [(module-declared? `(submod ,entry-path line-count) #t)
       `(submod ,entry-path line-count)]
      [else entry-path]))

  (define current-paths (mutable-set))

  (define (check path)
    (match path
      [`(submod ,path ,_) (check path)]
      [_
       (cond
         [(not (path? path)) (void)]
         [(path-prefix? path (find-collects-dir)) (void)]
         [else
          (match (path->pkg path)
            [#f (set-add! current-paths path)]
            [_ (void)])])]))

  (show-import-tree
   the-mod
   #:dag? #t
   #:show (λ (indent path require-mode phase) (check path)))
  (set->list current-paths))

(define touched-path (make-hash))

(define (count-line name entry-path)
  (define paths (if entry-path
                    (for/list ([path (trace entry-path)])
                      (~a (find-relative-path (current-directory) path)))
                    (for/list ([path (glob (string-append name "/**/*.rkt"))])
                      (~a (find-relative-path (current-directory) path)))))
  (hash-set! touched-path name paths)
  (invoke-cloc paths))

(define z3 "Z3")
(define cvc4 "CVC4")
(define boolector "Boolector")

(define BENCHMARKS
  `(["bagpipe"     "bagpipe/setups/textbook/run.rkt" ,z3]
    ["bonsai"      "bonsai/nanoscala.rkt" ,boolector]
    ["cosette"     "cosette/cidr-benchmarks/oracle-12c-bug.rkt" ,z3]
    ["ferrite"     "ferrite/rename.rkt" ,z3]
    ["fluidics"    "fluidics/ex2.rkt" ,z3]
    ["greenthumb"  "greenthumb/GA/output/0/driver-0.rkt" ,boolector]
    ["memsynth"    "memsynth/case-studies/synthesis/ppc/ppc0.rkt" ,z3]
    ["neutrons"    "neutrons/filterWedgeProp.rkt" ,z3]
    ["nonograms"   "nonograms/puzzle/src/run-batch-learn-rules.rkt" ,z3]
    ["quivela"     "quivela/test-inc-arg.rkt" ,z3]
    ["rtr"         "rtr/benchmarks/all.rkt" ,cvc4]
    ["wallingford" "wallingford/tests/all-tests.rkt" ,z3]
    ["jitterbug"   #f ,boolector]
    ["ifcl"        "ifcl/test.rkt" ,boolector]
    ["synthcl"     "synthcl/examples/sobelFilter/test.rkt" ,boolector]
    ["websynth"    "websynth/test/all-tests.rkt" ,z3]))

(module+ main
  (define current-diff? #f)

  (define where #f)
  (define mode #f)

  (command-line
   #:args (what)
   (set! mode what)
   (match what
     ["rosette-4"
      (set! current-diff? #t)
      (set! where "../rosette-benchmarks-4")]
     ["rosette-3"
      (set! where "../rosette-benchmarks-3")]
     [_ (error "expect either rosette-3 or rosette-4")]))

  (define current-diff-file (simple-form-path "workspace/diff.csv"))
  (define current-loc-file (simple-form-path (format "workspace/~a-total.csv" mode)))

  (current-directory where)

  (with-output-to-file current-loc-file
    #:exists 'replace
    void)

  (for ([benchmark BENCHMARKS])
    (define v (count-line (first benchmark) (second benchmark)))
    (define (output)
      (printf "~a,~a\n" (first benchmark) v))
    (with-output-to-file current-loc-file
      #:exists 'append
      output)
    (output))

  (when current-diff?
    (with-output-to-file current-diff-file
      #:exists 'replace
      void)

    (for ([benchmark BENCHMARKS])
      (define outs
        (with-output-to-string
          (λ () (system*
                 (find-executable-path "git")
                 "diff"
                 "--no-index"
                 "--ignore-blank-lines"
                 "-w"
                 "-b"
                 "--diff-filter=A"
                 (first benchmark)
                 (string-append "../rosette-benchmarks-3/" (first benchmark))))))

      (define-values (+diffs -diffs)
        (cond
          [(non-empty-string? outs)
           (define outl (string-split outs "\n"))
           (define +diff (- (count (λ (s) (regexp-match #px"^\\+.*$" s)) outl)
                            (count (λ (s) (regexp-match #px"^\\+ *(;.*)?$" s)) outl)
                            (count (λ (s) (regexp-match #px"^\\+\\+\\+.*$" s)) outl)))
           (define -diff (- (count (λ (s) (regexp-match #px"^-.*$" s)) outl)
                            (count (λ (s) (regexp-match #px"^- *(;.*)?$" s)) outl)
                            (count (λ (s) (regexp-match #px"^---.*$" s)) outl)))
           (values +diff -diff)]
          [else (values 0 0)]))

      (define offset 0)

      (define out
        (string-split
         (with-output-to-string
           (λ ()
             (for ([f (hash-ref touched-path (first benchmark))])
               (cond
                 [(file-exists? (string-append "../rosette-benchmarks-3/" f))
                  (unless (equal? (file->string f) (file->string (string-append "../rosette-benchmarks-3/" f)))
                    (system*
                     (find-executable-path "git")
                     "diff"
                     "--no-index"
                     "--ignore-blank-lines"
                     "-w"
                     "-b"
                     f
                     (string-append "../rosette-benchmarks-3/" f)))]
                 [else (set! offset (+ offset (length (filter (λ (s) (non-empty-string? (string-trim s)))
                                                              (file->lines f)))))]))))
         "\n"))

      (define +diff (- (count (λ (s) (regexp-match #px"^\\+.*$" s)) out)
                       (count (λ (s) (regexp-match #px"^\\+ *(;.*)?$" s)) out)
                       (count (λ (s) (regexp-match #px"^\\+\\+\\+.*$" s)) out)))
      (define -diff (- (count (λ (s) (regexp-match #px"^-.*$" s)) out)
                       (count (λ (s) (regexp-match #px"^- *(;.*)?$" s)) out)
                       (count (λ (s) (regexp-match #px"^---.*$" s)) out)))

      (define (output)
        (printf "~a,~a,~a,~a\n"
                (first benchmark)
                (+ -diff -diffs offset)
                (+ +diff +diffs)
                (third benchmark)))

      (with-output-to-file current-diff-file
        #:exists 'append
        output)

      (output))))
