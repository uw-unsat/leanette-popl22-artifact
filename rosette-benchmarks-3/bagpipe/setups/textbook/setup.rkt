(define ((scenario0 broken) r i o p ai al al* ae)
  (and (not broken)
    (implies (available? ai) 
             (eq? (announcement-pref (current ai)) 100))))

(define (break-scenario0) void)

(define ((scenario1 _) r i o p ai al al* ae)
  (implies (and (internal? o) 
                (available? al*)
                (external? (second (reverse (path al*)))))
                  (available? ae)))

(define (break-scenario1)
  (system* "/usr/bin/env" "sed" "-i.bak" "s|then accept|then reject|" "scenario1/R1.bgp"))

(define ((scenario2 _) r i o p ai al al* ae)
  (implies (prefix-compare 'orlonger (cidr (ip 0 0 0 0) 8) p)
    (not (available? al*))))

(define (break-scenario2)
  (system* "/usr/bin/env" "sed" "-i.bak" "s|route-filter 0.0.0.0/8|route-filter 0.0.0.0/9|" "scenario2/R2.bgp"))

(define ((scenario3 _) r i o p ai al al* ae)
  (implies (and (available? al*) (prefix-compare 'orlonger (cidr (ip 0 0 0 0) 0) p))
    (available? ae)))

(define (break-scenario3)
  (system* "/usr/bin/env" "sed" "-i.bak" "s|then accept|then reject|" "scenario3/ISP.bgp"))

(define ((scenario4 _) r i o p ai al al* ae)
  (define large (and (<= (prefix-length p) 18)
                     (prefix-compare 'orlonger (cidr (ip 172 16 0 0) 16) p)))
  (define small (and (<= 19 (prefix-length p)) (<= (prefix-length p) 24)
                     (prefix-compare 'orlonger (cidr (ip 172 16 0 0) 16) p)))
  (implies (and 
    (available? al*)
    (eq? (router-addr r) (ip 192 168 0 1))
    (if (eq? (router-addr o) (ip 10 1 0 6)) small (or large small)))
      (available? ae)))

(define (break-scenario4)
  (system* "/usr/bin/env" "sed" "-i.bak" "s|then accept|then reject|" "scenario4/R1.bgp"))

(define ((scenario5 _) r i o p ai al al* ae)
  (implies (and 
    (available? al*) 
    (eq? (router-addr (first (path al*))) (router-addr o)))
      (available? ae)))

(define (break-scenario5)
  (system* "/usr/bin/env" "sed" "-i.bak" "s|then accept|then reject|" "scenario5/R2.bgp"))

(define ((scenario6 _) r i o p ai al al* ae)
  (define ps (list (cidr (ip 172 16 1 16) 28) (cidr (ip 172 16 1 32) 28)
                   (cidr (ip 172 16 1 48) 28) (cidr (ip 172 16 1 64) 28)
                   (cidr (ip 172 16 2 16) 28) (cidr (ip 172 16 2 32) 28)
                   (cidr (ip 172 16 2 48) 28) (cidr (ip 172 16 2 64) 28)
                   (cidr (ip 172 16 3 16) 28) (cidr (ip 172 16 3 32) 28)
                   (cidr (ip 172 16 3 48) 28) (cidr (ip 172 16 3 64) 28)))
  (implies (eq? (ip 192 168 0 1) (router-addr r))
    (eq? (available? ae)
         (and (available? al*)
              (or (not (eq? (ip 10 1 0 6) (router-addr o)))
                  (ormap (curry prefix-compare 'exact p) ps))))))

(define (break-scenario6)
  (system* "/usr/bin/env" "sed" "-i.bak" "s|172.16.1.48/28|1.2.3.4/5|" "scenario6/R1.bgp"))

(define ((scenario7 _) r i o p ai al al* ae)
  (define (assertion sucks great)
    (eq? (announcement-pref (current ai))
      (if (announcement-community-test (current ai) sucks) 50
        (if (announcement-community-test (current ai) great) 200 100))))
  (implies (and (available? ai) (eq? (ip 192 168 0 2) (router-addr r))) (cond
    [(eq? (ip 192 168 0 1) (router-addr i)) (assertion 'from-R3 'from-R1)]
    [(eq? (ip 192 168 0 3) (router-addr i)) (assertion 'from-R1 'from-R3)])))

(define (break-scenario7)
  (system* "/usr/bin/env" "sed" "-i.bak" "s| 50| 250|" "scenario7/R1.bgp"))

(define ((scenario8 _)  r i o p ai al al* ae)
  (implies (available? al*)
    (not (or (announcement-aspath-test (current al*) 'orig-in-64513)
             (announcement-aspath-test (current al*) 'orig-in-64514)))))

(define (break-scenario8)
  (system* "/usr/bin/env" "sed" "-i.bak" "s|then reject|then accept|" "scenario8/R6.bgp"))

(define ((scenario9 _) r i o p ai al al* ae)
  (define ns (list (ip 10 10 10 2) (ip 10 10 10 6) (ip 10 10 10 10) (ip 10 21 7 2)))
  (and (member (router-addr i) ns)
       (member (router-addr o) ns)))

(define (break-scenario9)
  (system* "/usr/bin/env" "sed" "-i.bak" "s|10.21.7.2|10.21.7.3|" "scenario9/R1.bgp"))

(define (driver args) 'all)

(define (policy args)
  (define broken (and (>= (length args) 2) (equal? (second args) "broken")))
  (cond
    [(equal? (first args) "scenario0") (scenario0 broken)]
    [(equal? (first args) "scenario1") (scenario1 broken)]
    [(equal? (first args) "scenario2") (scenario2 broken)]
    [(equal? (first args) "scenario3") (scenario3 broken)]
    [(equal? (first args) "scenario4") (scenario4 broken)]
    [(equal? (first args) "scenario5") (scenario5 broken)]
    [(equal? (first args) "scenario6") (scenario6 broken)]
    [(equal? (first args) "scenario7") (scenario7 broken)]
    [(equal? (first args) "scenario8") (scenario8 broken)]
    [(equal? (first args) "scenario9") (scenario9 broken)]))

(define (break args)
  (if (and (>= (length args) 2) (equal? (second args) "broken"))
    (cond
      [(equal? (first args) "scenario0") (break-scenario0)]
      [(equal? (first args) "scenario1") (break-scenario1)]
      [(equal? (first args) "scenario2") (break-scenario2)]
      [(equal? (first args) "scenario3") (break-scenario3)]
      [(equal? (first args) "scenario4") (break-scenario4)]
      [(equal? (first args) "scenario5") (break-scenario5)]
      [(equal? (first args) "scenario6") (break-scenario6)]
      [(equal? (first args) "scenario7") (break-scenario7)]
      [(equal? (first args) "scenario8") (break-scenario8)]
      [(equal? (first args) "scenario9") (break-scenario9)])
    '()))

(define (as args)
  (define dir (first args))
  (define files 
    (filter (lambda (p) (string-suffix? p ".bgp"))
            (map [lambda (p) (string-append dir "/" (path->string p))] (directory-list dir))))
  (break args)
  (define conf (as-from-configs 'juniper files))
  (write-string (~a conf))
  (flush-output)
  conf)
