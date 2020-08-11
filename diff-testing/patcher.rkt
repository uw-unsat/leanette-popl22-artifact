#lang racket

(require racket/cmdline
         "tester.rkt")

(define git (find-executable-path "git"))
(define patch (find-executable-path "patch"))

(define (get-unstaged)
  (system* git "status" "-s" "-uno"))

(define unstaged (with-output-to-string get-unstaged))

(when (non-empty-string? unstaged)
  (displayln "error: the worktree is dirty.")
  (get-unstaged)
  (exit 1))

(define-values (patch-path progs)
  (command-line
   #:once-any
   [("--timeout") t "Timeout"
                  (current-timeout t)]
   #:args (patch-path . progs)
   (values
    patch-path
    (filter
     (λ (p) (string-suffix? p ".rkt"))
     (append*
      (for/list ([prog progs])
        (match (file-or-directory-type prog #t)
          ['file (list prog)]
          ['directory (map ~a (directory-list prog #:build? #t))])))))))

(unless (system* patch "-p1" "-d" ".." "-i" (simple-form-path patch-path))
  (raise-user-error "error: patch file malformed"))

(match-define-values [_ name/ext _] (split-path patch-path))
(define name (path-replace-extension name/ext ".rktd"))

(system* "./precompile")

(current-output (build-path "workspace" name))

(main progs)
