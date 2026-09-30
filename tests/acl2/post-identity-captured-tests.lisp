; Literal witnesses for the bounded confirmation components.  Actual
; selected provider/POST reachability is owed by the assembled host tests.
(in-package "ACL2")
(include-book "../../books/post-identity-captured")

(defmacro pic-test-run (s fuel)
  (list 'mv-list 3 (list 'fn-pic-groups-advance s fuel)))

; Positive: the complete antecedent and conclusion of the groups keystone.
(assert-event
 (let ((left '("fn.docs" "fn.announce")) (right '("fn.docs" "fn.announce")))
   (and (equal (mv-nth 0 (pic-test-run
                          (fn-pic-groups-begin left right) 32)) :equal)
        (equal left right))))
; Hypothesis removal: zero fuel confirms nothing, and the conclusion fails.
(assert-event
 (let ((left '("fn.docs")) (right '("fn.docx")))
   (and (not (equal (mv-nth 0 (pic-test-run
                               (fn-pic-groups-begin left right) 0)) :equal))
        (not (equal left right)))))
; Negative: every retained hypothesis and conclusion hold literally.
(assert-event
 (let ((left '("fn.docs" "fn.announce")) (right '("fn.docs" "fn.announcf")))
   (and (fn-pic-string-listp left) (fn-pic-string-listp right)
        (equal (mv-nth 0 (pic-test-run
                          (fn-pic-groups-begin left right) 32)) :different)
        (not (equal left right)))))
 ; Hypothesis removal for rejection: equal groups at zero fuel are pending.
(assert-event
 (let ((left '("fn.docs")) (right '("fn.docs")))
   (and (not (equal (mv-nth 0 (pic-test-run
                              (fn-pic-groups-begin left right) 0)) :different))
        (equal left right))))
; Equal-length and unequal-length differences, reordered groups, empty.
(assert-event
 (and (equal (mv-nth 0 (pic-test-run
                        (fn-pic-groups-begin '("a") '("b")) 2)) :different)
      (equal (mv-nth 0 (pic-test-run
                        (fn-pic-groups-begin '("a") '("aa")) 1)) :different)
      (equal (mv-nth 0 (pic-test-run
                        (fn-pic-groups-begin '("a" "b") '("b" "a")) 1)) :different)
      (equal (mv-nth 0 (pic-test-run
                        (fn-pic-groups-begin nil nil) 1)) :equal)))
; Yield/resume preserves the exact remaining character cursor and fuel.
(assert-event
 (let* ((start (fn-pic-groups-begin '("abcdef" "gh") '("abcdef" "gh")))
        (part (mv-nth 1 (pic-test-run start 3))))
   (and (equal (mv-nth 0 (pic-test-run start 3)) :yield)
        (equal (fn-pic-at 3 part) 3)
        (equal (mv-nth 2 (pic-test-run start 3)) 0)
        (equal (mv-nth 0 (pic-test-run part 8)) :equal)
        (equal (mv-nth 2 (pic-test-run part 8)) 0))))
; Corrupted continuation: invalid groups remain a separate refusal.
(assert-event
 (equal (mv-nth 0 (pic-test-run
                   (fn-pic-groups-begin '(9) '(9)) 3)) :invalid-groups))
; A v3 virtual source skips only the agent insertion [A,B); suffix is v2.
(assert-event
 (and (fn-pic-spanp '(1 3 5) 8)
      (equal (fn-pic-span-length '(1 3 5) 8) 5)
      (equal (fn-pic-span-value '(1 3 5) '(0 1 2 3 4 5 6 7)) '(1 2 5 6 7))
      (equal (fn-pic-span-offset '(1 3 5) 1) 2)
      (equal (fn-pic-span-offset '(1 3 5) 2) 5)
      (equal (fn-pic-span-value '(3 3 3) '(0 1 2 3 4 5)) '(3 4 5))))
; The block crosses the virtual splice; readonly input is unchanged.
(defun pic-test-readonly-block ()
 (declare (xargs :guard t))
 (with-local-stobj fn-octets
   (mv-let (ok fn-octets)
     (let ((fn-octets (fn-octets-from-list '(0 1 2 3 4 5 6 7) fn-octets)))
       (mv (and (fn-pic-spanp '(1 3 5) (fn-octets-len fn-octets))
                (equal (fn-pic-incoming-block '(1 3 5) 1 3 fn-octets) '(2 5 6))
                (equal (fn-octets-list fn-octets) '(0 1 2 3 4 5 6 7)))
           fn-octets))
     ok)))
(assert-event (pic-test-readonly-block))

; Controller literals use exact typed effects. The fixture is proof/test-only;
; the host boundary reads the SAME provider-selected handle under its lease.
(defun pic-test-drive (c incoming held fuel)
  (declare (xargs :measure (nfix fuel) :guard (true-listp c) :verify-guards nil))
  (if (or (zp fuel) (equal (fn-pic-get phase c) :done)) c
    (let* ((d (fn-pic-demand c)) (i (fn-pic-at 1 d))
           (observation
            (cond ((equal d :control) :control)
                  ((equal d :held-length)
                   (list :payload-length (fn-pic-get selected c) (fn-pic-get grant c)
                         (fn-record-payload (fn-pic-get held c)) (len held)))
                  ((equal (fn-pic-at 0 d) :held)
                   (list :payload-byte (fn-pic-get selected c) (fn-pic-get grant c)
                         (fn-record-payload (fn-pic-get held c)) i (nth i held)))
                  ((equal (fn-pic-at 0 d) :incoming)
                   (list :incoming-byte (fn-pic-get incoming-token c) i (nth i incoming)))
                  (t nil))))
      (pic-test-drive (fn-pic-feed c observation) incoming held (1- fuel)))))
(defun pic-test-held (msgid groups binding)
  (append (list 0 0 0 msgid 0 groups "" "" "" 0 "")
          (list nil nil nil nil binding)))
(defconst *pic-test-binding*
  (fn-ab-make :post-d25 (append *fn-ab-subject-head* (make-list 32 :initial-element 0))))
(defconst *pic-test-selected* '(:index-selected (:index-query 3 0 0 1) 0 7))
(defconst *pic-test-grant* '(:query-payload 9 0 1 0 1 0))
(defconst *pic-test-incoming* '(:incoming 4))
(defun pic-test-begin (groups held-groups)
  (fn-pic-begin *pic-test-selected* *pic-test-grant*
    (pic-test-held "<m>" held-groups *pic-test-binding*)
    *pic-test-incoming* 3 "<m>" *pic-test-binding* groups))
(assert-event
 (let* ((c (pic-test-begin '("g") '("g")))
        (done (pic-test-drive c '(65 66 67) '(65 66 67) 500)))
   (and (equal (fn-pic-get phase c) :held-length)
        (equal (fn-pic-get result done) :duplicate))))
(assert-event
 (equal (fn-pic-get result
   (pic-test-drive (pic-test-begin '("g") '("h")) '(65 66 67) '(65 66 67) 500)) :conflict))
(assert-event
 (equal (fn-pic-get result
   (pic-test-drive (pic-test-begin '("g") '("g")) '(65 66 67) '(65 66 68) 500)) :conflict))
; Binding failure returns before requesting length, payload, parser or groups.
(assert-event
 (let ((c (fn-pic-begin *pic-test-selected* *pic-test-grant*
           (pic-test-held "<m>" '("g") *pic-test-binding*) *pic-test-incoming*
           3 "<m>" nil '("g"))))
   (and (equal (fn-pic-get result c) :invalid-binding)
        (equal (fn-pic-demand c) :none))))
; Mutation witness: an otherwise typed observation from another selection.
(assert-event
 (let* ((c (pic-test-begin '("g") '("g")))
        (other (list :payload-length '(:index-selected (:index-query 3 0 0 1) 1 7)
                     *pic-test-grant* 0 3)))
   (and (not (fn-pic-observation-okp c :held-length other))
        (equal (fn-pic-get result (fn-pic-feed c other)) :refused))))
(assert-event
 (let* ((c (pic-test-begin '("g") '("g")))
        (obs (list :payload-length *pic-test-selected* *pic-test-grant* 0 3))
        (yielded (mv-list 3 (fn-pic-feed-funded c obs 0))))
   (and (fn-pic-observation-okp c :held-length obs)
        (equal yielded (list :yield c 0)))))

(defun pic-test-block-context (pos block)
  (fn-pic-set pos pos (fn-pic-set block block
    (fn-pic-set block-start 1 (fn-pic-set block-count 3
      (fn-pic-set digest-desc '(1 3 5) (make-list 23 :initial-element nil)))))))
; Actual collector keystone: complete antecedent and conclusion.
(assert-event
 (let* ((incoming '(0 1 2 3 4 5 6 7)) (c (pic-test-block-context 0 nil)) (byte 2))
   (and (fn-pic-block-prefixp c incoming)
        (< (fn-pic-get pos c) (fn-pic-get block-count c))
        (equal byte (nth (+ (fn-pic-get block-start c) (fn-pic-get pos c))
                      (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))
        (fn-pic-block-prefixp (fn-pic-block-add c byte) incoming))))
; Hypothesis removal: corrupt initial buffer; both other hypotheses hold.
(assert-event
 (let* ((incoming '(0 1 2 3 4 5 6 7)) (c (pic-test-block-context 0 '(7))) (byte 2))
   (and (not (fn-pic-block-prefixp c incoming))
        (< (fn-pic-get pos c) (fn-pic-get block-count c))
        (equal byte (nth (+ (fn-pic-get block-start c) (fn-pic-get pos c))
                      (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))
        (not (fn-pic-block-prefixp (fn-pic-block-add c byte) incoming)))))
; Hypothesis removal: read past the completed block, correct source byte.
(assert-event
 (let* ((incoming '(0 1 2 3 4 5 6 7)) (c (pic-test-block-context 3 '(6 5 2))) (byte 7))
   (and (fn-pic-block-prefixp c incoming)
        (not (< (fn-pic-get pos c) (fn-pic-get block-count c)))
        (equal byte (nth (+ (fn-pic-get block-start c) (fn-pic-get pos c))
                      (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))
        (not (fn-pic-block-prefixp (fn-pic-block-add c byte) incoming)))))
; Mutation witness: wrong supplied byte, all other hypotheses affirmative.
(assert-event
 (let* ((incoming '(0 1 2 3 4 5 6 7)) (c (pic-test-block-context 0 nil)) (byte 99))
   (and (fn-pic-block-prefixp c incoming)
        (< (fn-pic-get pos c) (fn-pic-get block-count c))
        (not (equal byte (nth (+ (fn-pic-get block-start c) (fn-pic-get pos c))
                           (fn-pic-span-value (fn-pic-get digest-desc c) incoming))))
        (not (fn-pic-block-prefixp (fn-pic-block-add c byte) incoming)))))
; Actual digest formatter keystone's full antecedent and full32-bit block.
(assert-event
 (let* ((incoming '(0 1 2 3 4 5 6 7)) (c (pic-test-block-context 3 '(6 5 2))))
   (and (fn-pic-block-prefixp c incoming)
        (equal (fn-pic-get pos c) (fn-pic-get block-count c))
        (equal (fn-pic-digest-block c)
          (fn-b3-words 16 (take (fn-pic-get block-count c)
            (nthcdr (fn-pic-get block-start c)
              (fn-pic-span-value (fn-pic-get digest-desc c) incoming))))))))
; Formatter hypothesis removal: a valid incomplete prefix is not a full block.
(assert-event
 (let* ((incoming '(0 1 2 3 4 5 6 7)) (c (pic-test-block-context 1 '(2))))
   (and (fn-pic-block-prefixp c incoming)
        (not (equal (fn-pic-get pos c) (fn-pic-get block-count c)))
        (not (equal (fn-pic-digest-block c)
          (fn-b3-words 16 (take (fn-pic-get block-count c)
            (nthcdr (fn-pic-get block-start c)
              (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))))))))
; The actual feed retains every captured authority field, while advancing.
(assert-event
 (let* ((c (pic-test-begin '("g") '("g")))
        (obs (list :payload-length *pic-test-selected* *pic-test-grant* 0 3))
        (next (fn-pic-feed c obs)))
   (and (equal (fn-pic-get phase c) :held-length)
        (fn-pic-observation-okp c :held-length obs)
        (not (equal next c))
        (equal (fn-pic-captured-context next) (fn-pic-captured-context c)))))

; End-to-end fixtures call the actual mutating digest adapter. Fixture
; provider effects are local literals; live provider reachability is separate.
(defun pic-test-digest-drive (c incoming held fuel pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t :verify-guards nil
                  :measure (nfix fuel)))
  (if (or (zp fuel) (equal (fn-pic-get phase c) :done))
      (mv c pgs-digest-state)
    (if (member-eq (fn-pic-get phase c) '(:digest-begin :digest-next :digest-commit))
        (mv-let (status next left pgs-digest-state)
          (fn-pic-digest-next c 2 pgs-digest-state)
          (declare (ignore status left))
          (pic-test-digest-drive next incoming held (1- fuel) pgs-digest-state))
      (pic-test-digest-drive (pic-test-drive c incoming held 1)
                            incoming held (1- fuel) pgs-digest-state))))
(defun pic-test-tomb (flag octet-hash source-hash agent)
  (append *fn-rcl-magic* (list flag) octet-hash source-hash
          (make-list (- *fn-rcl-tombstone-fixed* 73) :initial-element 0) agent))
(defun pic-test-digest-confirm (incoming held)
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (done pgs-digest-state)
      (pic-test-digest-drive
        (fn-pic-begin *pic-test-selected* *pic-test-grant*
          (pic-test-held "<m>" nil *pic-test-binding*) *pic-test-incoming*
          (len incoming) "<m>" *pic-test-binding* nil)
        incoming held 3000 pgs-digest-state)
      (fn-pic-get result done))))
(defconst *pic-test-abc-hash*
 '(100 55 179 172 56 70 81 51 255 182 59 117 39 58 141 181
   72 197 88 70 93 121 219 3 253 53 156 108 213 189 157 133))
; A tombstone with valid magic/fixed prefix uses the whole original hash
; when the incoming injection inverse is absent, even if source flag is1.
(assert-event
 (and (equal (fn-blake3 '(97 98 99)) *pic-test-abc-hash*)
      (equal (pic-test-digest-confirm '(97 98 99)
        (pic-test-tomb 1 *pic-test-abc-hash*
                       (make-list 32 :initial-element 0) nil)) :duplicate)))
(assert-event
 (equal (pic-test-digest-confirm '(97 98 100)
   (pic-test-tomb 0 *pic-test-abc-hash*
                  (make-list 32 :initial-element 0) nil)) :conflict))
; A shortened RCL2 prefix and obsolete RCL1 magic are ordinary live data.
(assert-event
 (and (equal (pic-test-digest-confirm '(97 98 99)
               (take 144 (pic-test-tomb 0 *pic-test-abc-hash*
                                    (make-list 32 :initial-element 0) nil))) :conflict)
      (equal (pic-test-digest-confirm '(97 98 99)
               (update-nth 7 49 (pic-test-tomb 0 *pic-test-abc-hash*
                                    (make-list 32 :initial-element 0) nil))) :conflict)))
(defun pic-test-digest-reserve ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (ok pgs-digest-state)
      (let ((c (fn-pic-hash-start nil (pic-test-begin nil nil)))
            (before (pgs-dc-mode pgs-digest-state)))
        (mv-let (status next left pgs-digest-state)
          (fn-pic-digest-next c 1 pgs-digest-state)
          (mv (and (equal status :yield) (equal c next) (equal left 1)
                   (equal before (pgs-dc-mode pgs-digest-state)))
              pgs-digest-state)))
      ok)))
(assert-event (pic-test-digest-reserve))
(defconst *pic-test-source-agent* '(97 98 99))
(defconst *pic-test-source* '(88 58 32 89 13 10 13 10 0 255))
(defconst *pic-test-stamped*
 (append (fn-inj-path-line *pic-test-source-agent*)
         (fn-inj-injection-info-line *pic-test-source-agent*) *pic-test-source*))
; Same incoming-derived agent selects the source hash, ignoring the unrelated
; whole hash and all metadata that the actual recognizer ignores.
(assert-event
 (equal (pic-test-digest-confirm *pic-test-stamped*
          (pic-test-tomb 1 (make-list 32 :initial-element 0)
                         (fn-blake3 *pic-test-source*) *pic-test-source-agent*)) :duplicate))
; A different retained agent takes the whole-octet fallback.
(assert-event
 (equal (pic-test-digest-confirm *pic-test-stamped*
          (pic-test-tomb 1 (fn-blake3 *pic-test-stamped*)
                         (make-list 32 :initial-element 0) '(97 98 100))) :duplicate))
; More than one block is consumed without duplicating a committed block.
(assert-event
 (let ((incoming (make-list 130 :initial-element 97)))
   (equal (pic-test-digest-confirm incoming
            (pic-test-tomb 0 (fn-blake3 incoming)
                           (make-list 32 :initial-element 0) nil)) :duplicate)))
(defun pic-test-until-commit (c incoming held fuel pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t :verify-guards nil
                  :measure (nfix fuel)))
  (if (or (zp fuel) (and (equal (fn-pic-get phase c) :digest-commit)
                         (< 0 (nfix (fn-pic-get block-count c)))))
      (mv c pgs-digest-state)
    (if (member-eq (fn-pic-get phase c) '(:digest-begin :digest-next :digest-commit))
        (mv-let (status next left pgs-digest-state)
          (fn-pic-digest-next c 2 pgs-digest-state)
          (declare (ignore status left))
          (pic-test-until-commit next incoming held (1- fuel) pgs-digest-state))
      (pic-test-until-commit (pic-test-drive c incoming held 1)
                            incoming held (1- fuel) pgs-digest-state))))
(defun pic-test-digest-commit-resume ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (ok pgs-digest-state)
      (let ((held (pic-test-tomb 0 *pic-test-abc-hash*
                               (make-list 32 :initial-element 0) nil)))
        (mv-let (commit pgs-digest-state)
          (pic-test-until-commit (fn-pic-hash-start nil
                                  (fn-pic-set held-n (len held) (pic-test-begin nil nil)))
                                '(97 98 99) held 300 pgs-digest-state)
          (let ((before (pgs-dc-mode pgs-digest-state)))
            (mv-let (yielded same remaining pgs-digest-state)
              (fn-pic-digest-next commit 1 pgs-digest-state)
              (let ((unchanged (and (equal yielded :yield) (equal same commit)
                                   (equal remaining 1)
                                   (equal (pgs-dc-mode pgs-digest-state) before))))
                (mv-let (stepped next left pgs-digest-state)
                  (fn-pic-digest-next same 2 pgs-digest-state)
                  (let ((once (and (equal stepped :continue) (equal left 0)
                                   (equal before :chunk)
                                   (equal (fn-pic-get phase next) :digest-next)
                                   (equal (pgs-dc-mode pgs-digest-state) :return))))
                    (mv-let (done pgs-digest-state)
                      (pic-test-digest-drive next '(97 98 99) held 300 pgs-digest-state)
                      (mv (and unchanged once
                               (equal (fn-pic-get result done) :duplicate)
                               (equal (fn-pic-get digest done) *pic-test-abc-hash*))
                          pgs-digest-state)))))))))
      ok)))
(assert-event (pic-test-digest-commit-resume))

; Actual incoming entry boundary: complete context/fuel conclusions plus a
; productive readonly continuation, and a separate malformed fuel witness.
(defun pic-test-next-boundary ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (ok fn-octets)
      (let* ((fn-octets (fn-octets-from-list '(65 66 67) fn-octets))
             (c (fn-pic-feed (pic-test-begin nil nil)
                  (list :payload-length *pic-test-selected* *pic-test-grant* 0 3))))
        (mv-let (status next left)
          (fn-pic-next c 2 fn-octets)
          (mv (and (natp 2) (equal status :continue) (not (equal c next))
                   (natp left) (<= left 2)
                   (equal (fn-pic-captured-context next) (fn-pic-captured-context c))
                   (equal (fn-octets-list fn-octets) '(65 66 67))) fn-octets)))
      ok)))
(assert-event (pic-test-next-boundary))
(defun pic-test-next-fuel-removal ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (ok fn-octets)
      (let ((c (fn-pic-finish :duplicate (pic-test-begin nil nil))))
        (mv-let (status next left)
          (ec-call (fn-pic-next c -1 fn-octets))
          (declare (ignore status next))
          (mv (and (not (natp -1)) (not (and (natp left) (<= left -1)))) fn-octets)))
      ok)))
(assert-event (with-guard-checking :none (pic-test-next-fuel-removal)))
(defun pic-test-digest-boundary ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (ok pgs-digest-state)
      (let ((c (fn-pic-hash-start nil (pic-test-begin nil nil))))
        (mv-let (status next left pgs-digest-state)
          (fn-pic-digest-next c 2 pgs-digest-state)
          (mv (and (natp 2) (equal status :continue) (not (equal c next))
                   (natp left) (<= left 2)
                   (equal (fn-pic-captured-context next) (fn-pic-captured-context c)))
              pgs-digest-state)))
      ok)))
(assert-event (pic-test-digest-boundary))
(defun pic-test-digest-fuel-removal ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (ok pgs-digest-state)
      (let ((c (fn-pic-hash-start nil (pic-test-begin nil nil))))
        (mv-let (status next left pgs-digest-state)
          (ec-call (fn-pic-digest-next c -1 pgs-digest-state))
          (declare (ignore status next))
          (mv (and (not (natp -1)) (not (and (natp left) (<= left -1)))) pgs-digest-state)))
      ok)))
(assert-event (with-guard-checking :none (pic-test-digest-fuel-removal)))
