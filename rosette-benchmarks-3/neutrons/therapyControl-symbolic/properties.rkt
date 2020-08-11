
(define (watchDogProp)
  (define oldval (get-field "CYC:WatchdogAOK:Control" "VAL"))
  (process "CYC:WatchdogAOK:Calc")
  (define newval (get-field "CYC:WatchdogAOK:Control" "VAL"))
  (printf "old: ~s\n" oldval)
  (printf "new: ~s\n" newval)

  ; CYCWatchdogAOKCalc processes periodically. Every time it does,
  ; CYCWatchdogAOKControl.VAL should alternate between 0 and 1.
  ; This isn't exactly that property, but it's close.
  (assert (not (eq? (zero? oldval) (zero? newval)))))

(define (couchInterlockProp)
  ; When turntable motion is enabled, the therapy sum interlock should be 0.
  (define inpval (get-field "Iso:GantryCouch:Turntable:DriveEnabled" "RVAL"))
  (process "Iso:GantryCouch:Turntable:DriveEnabled")
  (define intlk (get-field "CYC:TherapySumIntlkRelayAOK:Control" "VAL"))

  (printf "drive enabled:        ~s\n" inpval)
  (printf "therapysum interlock: ~s\n" intlk)

  (assert (=> (= inpval 0) (= intlk 0))))

(define (diff v1 v2)
  (abs (- v1 v2)))

(define (readiness-invariant)
  ; Iso:GantryCouch:Settings:Readiness uses the MIN(...) function to fail
  ; if any of these fail. For that to work, they must all be >= 0.
  (and
    (>= (get-field "Iso:GantryCouch:Gantry:Readiness"     "VAL") 0)
    (>= (get-field "Iso:GantryCouch:Collimator:Readiness" "VAL") 0)))

(define (binary-records-have-binary-values)
  (define res #t)
  (for/list ([rname all-records])
    (if (or (equal? (record-type rname) "bo") (equal? (record-type rname) "bi"))
      (set! res (and res (or
        (= (get-field rname "VAL") 0)
        (= (get-field rname "VAL") 1))))
      '()))
  res)

; This is our central result about the beam turning off when any external
; motion is out of alignment.
(define (externalMotionTolerancesProp)
  (define gantry-prescribed     (get-field "Iso:GantryCouch:Gantry:Prescribed" "VAL"))
  (define gantry-actual         (get-field "Iso:GantryCouch:Gantry:Actual" "VAL"))
  (define gantry-tolerance      (get-field "Iso:GantryCouch:Gantry:Tolerance" "VAL"))
  (define gantry-override       (get-field "Iso:GantryCouch:Gantry:Override" "VAL"))

  (define turntable-prescribed  (get-field "Iso:GantryCouch:Turntable:Prescribed" "VAL"))
  (define turntable-actual      (get-field "Iso:GantryCouch:Turntable:Actual" "VAL"))
  (define turntable-tolerance   (get-field "Iso:GantryCouch:Turntable:Tolerance" "VAL"))
  (define turntable-override    (get-field "Iso:GantryCouch:Turntable:Override" "VAL"))

  (define collimator-prescribed (get-field "Iso:GantryCouch:Collimator:Prescribed" "VAL"))
  (define collimator-actual     (get-field "Iso:GantryCouch:Collimator:Actual" "VAL"))
  (define collimator-tolerance  (get-field "Iso:GantryCouch:Collimator:Tolerance" "VAL"))
  (define collimator-override   (get-field "Iso:GantryCouch:Collimator:Override" "VAL"))

  (define session-mode          (get-field "Iso:Session:Mode" "VAL"))

  (define precond (and
    (or
      (and (> (diff gantry-prescribed gantry-actual) gantry-tolerance)
           (= gantry-override 0))
      (and (> (diff turntable-prescribed turntable-actual) turntable-tolerance)
           (= turntable-override 0))
      (and (> (diff collimator-prescribed collimator-actual) collimator-tolerance)
           (= collimator-override 0)))
    (= session-mode 0)  ; Not in experiment mode
    ))

  ; ...then the beam turns off the next time
  ; Iso:GantryCouch:Turntable:Actual is processed!
  (process "Iso:GantryCouch:Gantry:Actual")
  (process "Iso:GantryCouch:Turntable:Actual")
  (process "Iso:GantryCouch:Collimator:Actual")
  (assert (=> precond (= (vector-ref (get-field "MOD1:Waveform:Calc" "AVAL") 1) 0))))

; This is our central result about the beam turning off when collimator leaf #0
; is out of alignment.
(define (leaf-record leaf kind)
  (string-append "Iso:Collimator:" leaf ":" kind))

(define (leaf-name n)
  (string-append "Leaf"
                 (~a n #:min-width 2 #:align 'right #:left-pad-string "0")))

(define all-leaves
  (map leaf-name (range 0 40)))

(define (process-all-leaves)
  (for-each (lambda (l) (process (leaf-record l "Actual"))) all-leaves))

(define (leafTolerancesProp num)
  (define quad (quotient num 10))
  (define opp-quad (- 3 quad))
  (define opp-num (+ (remainder num 10) (* 10 opp-quad)))

  (define leaf (leaf-name num))
  (define oppositeLeaf (leaf-name opp-num))

  (define prescribed   (get-field (leaf-record leaf "Prescribed") "VAL"))
  (define actual       (get-field (leaf-record leaf "Actual") "VAL"))

  (define oppPresc     (get-field (leaf-record oppositeLeaf "Prescribed") "VAL"))
  (define motionTol    (get-field "Iso:Collimator:LeafMotion:Tolerance" "VAL"))
  (define closedTol    (get-field "Iso:Collimator:LeafMotion:ClosedTolerance" "VAL"))

  ; If leaf #0 is close to leaf #30, then the prescription calls for that row
  ; of the collimator to be completely closed, and we use a different
  ; tolerance.
  ;
  ; The `tolerance` value here corresponds to `Leaf00_Chosen_Tolerance` in the
  ; Alloy model.
  (define tolerance    (if (< (diff prescribed oppPresc) motionTol) closedTol motionTol))

  (define precond (and
    ; If couch position is out of tolerance...
    (> (diff prescribed actual) tolerance)
    ; ...and override is disabled...
    (= (get-field (leaf-record leaf "Override") "VAL") 0)
    ; ...and mode == therapy...
    (= (get-field "Iso:Session:Mode" "VAL") 0)
    ))

  ; ...then the beam turns off the next time
  ; Iso:GantryCouch:Turntable:Actual is processed!
  ; Process every leaf.
  (process-all-leaves)
  (assert (=> precond (= (vector-ref (get-field "MOD1:Waveform:Calc" "AVAL") 1) 0)))
)


(define (filterWedgeProp)
  (define (part-ok part variants)
    (define prescribed-val    (get-field (string-append "Iso:FilterWedge:" part ":Prescribed") "VAL"))
    (define prescribed-bit    (<< 1 prescribed-val))
    ; Bit mask indicating the actual variant(s) where "Achieved" is non-zero.
    (define actual-bits
      (apply bvor
             (map (lambda (variant i)
                    (define val (get-field (string-append "Iso:FilterWedge:" part variant ":Achieved") "VAL"))
                    (if (not (= val 0)) (<< 1 i) 0))
                  variants
                  (range (length variants)))))

    ; Number of variants with "Achieved" set to non-zero.
    (define actual-count
      (apply +
             (map (lambda (variant)
                    (define val (get-field (string-append "Iso:FilterWedge:" part variant ":Achieved") "VAL"))
                    (if (not (= val 0)) 1 0))
                  variants)))

    (define precond
      (and
        ; Assumption: At most one variant is "achieved", all the rest have
        ; their "Achieved" field set to zero.  If this is not included, Rosette
        ; finds counterexamples in which both the desired variant and a
        ; different, undesired variant are marked "Achieved".  This happens
        ; because the FilterWedge:*:Decode record returns only the index of
        ; first achieved variant.
        (<= actual-count 1)

        ; Assumption: The prescribed value is one of the legal values.  This is
        ; necessary because the EPICS code uses one more than the highest legal
        ; value to indicate an error condition (such as all "Achieved" bits set
        ; to 0).
        (< prescribed-val (length variants))

        (not (= actual-bits prescribed-bit))
        (= (get-field (string-append "Iso:FilterWedge:" part ":Override") "VAL") 0)
        (= (get-field "Iso:Session:Mode" "VAL") 0)))
    (=> precond (= (vector-ref (get-field "MOD1:Waveform:Calc" "AVAL") 1) 0))
  )

  (define part-info (list (cons "WedgeType" '("None" "30" "45" "60"))
                          (cons "WedgeRot" '("0" "90" "180" "270"))
                          (cons "FlatFilter" '("None" "Large" "Small"))
                          ))

  ; Process all FilterWedge:*:Achieved input records.
  (for-each
    (lambda (info)
      (define part (car info))
      (define variants (cdr info))
      (for-each
        (lambda (variant) (process (string-append "Iso:FilterWedge:" part variant ":Achieved")))
        variants))
    part-info)

  ; Assert that all the parts are OK
  (for-each
    (lambda (info)
      (define part (car info))
      (define variants (cdr info))
      (assert (part-ok part variants)))
    part-info)
)
