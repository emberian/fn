; OVER pool-lease witnesses, draft 3b. Actual live stobj observations.
; WITH-GUARD-CHECKING-EVENT exercises the logical refusal arms outside
; verified BASE/LIMIT guards for the accepted premise-removal teeth.
; All assertion predicates and closed scene arguments remain unchanged.
(in-package "ACL2")
(include-book "../../books/over-render-lease")

(set-verify-guards-eagerness 0)


(set-ignore-ok t)

(set-irrelevant-formals-ok t)

(defconst *ovrs-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))

(defconst *ovrs-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))

(defconst *ovrs-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))

(defconst *ovrs-w0* (fn-record-make 0 1 1 "<a@x>" *ovrs-p0* '("fn.test") "o" "s" "e" 1 5))

(defconst *ovrs-w1* (fn-record-make 1 2 2 "<b@x>" *ovrs-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))

(defconst *ovrs-w2* (fn-record-make 2 3 3 "<c@x>" *ovrs-p2* '("fn.test") "o" "s" "e" 1 5))

(defun ovrs-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defconst *ovrs-a* (list *ovrs-p0* *ovrs-p1* *ovrs-p2*))

(defconst *ovrs-r0* (fn-cat-assign (ovrs-held *ovrs-w0* 0 nil) nil))

(defconst *ovrs-r1* (fn-cat-assign (ovrs-held *ovrs-w1* 1 nil) (list *ovrs-r0*)))

(defconst *ovrs-r2* (fn-cat-assign (ovrs-held *ovrs-w2* 2 nil) (list *ovrs-r0* *ovrs-r1*)))

(defconst *ovrs-c* (list *ovrs-r0* *ovrs-r1* *ovrs-r2*))

(defun ovrs-session (group)
  (fn-nntp-make-session t group nil t))

(defmacro ovrs-start (group token legacyp server)
  `(mv-nth 1 (fn-ovw-start (ovrs-session ,group) 3 (fn-record-string-octets ,token) ,legacyp ,server *ovrs-c*)))

(defun ovrbt-crlf () (coerce '(#\Return #\Newline) 'string))

(defun ovrbt-article (newsgroups subject body)
  (fn-record-string-octets
   (concatenate 'string "Newsgroups: " newsgroups (ovrbt-crlf) "Subject: " subject (ovrbt-crlf)
                (ovrbt-crlf) body (ovrbt-crlf))))

(defconst *ovrbt-tomb* (append *fn-rcl-magic* (make-list 137 :initial-element 0)))

(defun ovrbt-held (seq spec)
  (let* ((msgid (nth 0 spec)) (payload (nth 1 spec)) (groups (nth 2 spec)) (kind (nth 3 spec))
         (w (fn-record-make seq (+ 1 seq) (+ 1 seq) msgid payload groups "o" "s" "e" 1 5)))
    (if (eq kind :plain)
        (fn-held-plain w seq)
      (let ((facts-bytes (if (consp kind) (cadr kind) payload)))
        (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                      (fn-record-msgid w) seq (fn-record-groups w) (fn-record-obligation-id w)
                      (fn-record-content-subject w) (fn-record-release-evidence w)
                      (fn-record-charge w) (fn-record-stamp w)
                      (fn-held-facts-of facts-bytes)
                      (fn-held-context-of facts-bytes nil 0) nil nil)))))

(defun ovrbt-cat-from (seq specs rows)
  (declare (xargs :measure (len specs)))
  (if (consp specs)
      (ovrbt-cat-from (+ 1 seq) (cdr specs)
                      (append rows (list (fn-cat-assign (ovrbt-held seq (car specs)) rows))))
    rows))

(defun ovrbt-arena (specs)
  (if (consp specs) (cons (nth 1 (car specs)) (ovrbt-arena (cdr specs))) nil))

(defun ovrbt-max-probe (group k top server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (<= k (nfix top)))
      (max (fn-ovr-probe-len group k server v fn-arena fn-cat)
           (ovrbt-max-probe group (+ 1 k) top server v fn-arena fn-cat))
    0))

(defconst *ovrbt-specs*
  (list (list "<a@x>" (ovrbt-article "fn.test" "a" "A") '("fn.test") :column)
        (list "<b@x>" (ovrbt-article "fn.test,fn.other" "bb" "B") '("fn.test" "fn.other") :column)
        (list "<d@x>" (ovrbt-article "fn.test" "plain" "D") '("fn.test") :plain)
        (list "<e@x>" *ovrbt-tomb* '("fn.test") :column)))

(defconst *ovrbt-a* (ovrbt-arena *ovrbt-specs*))

(defconst *ovrbt-c* (ovrbt-cat-from 0 *ovrbt-specs* nil))

(defconst *ovrbt-server* '(110 102))

(defconst *ovrbt-limits* (fn-article-limits 10 10 100))

(set-verify-guards-eagerness 2)

(defun pc1-m-init () (declare (xargs :guard t)) nil)

(defun pc1-m-static-init (j) (declare (xargs :guard t) (ignore j)) nil)

(defun pc1-m-step (m ev pool q) (declare (xargs :guard t) (ignore m ev pool q)) (mv nil nil 0))

(defun pc1-m-committedp (m) (declare (xargs :guard t) (ignore m)) nil)

(defun pc1-m-c () (declare (xargs :guard t)) 0)

(defun pc1-m-max-reqs () (declare (xargs :guard t)) 0)

(defun pc1-m-max-state () (declare (xargs :guard t)) 1)

(set-verify-guards-eagerness 0)

(make-event
 (let* ((machine '((fn-rtc-m-init . pc1-m-init) (fn-rtc-m-static-init . pc1-m-static-init)
                   (fn-rtc-m-step . pc1-m-step) (fn-rtc-m-committedp . pc1-m-committedp)
                   (fn-rtc-m-c . pc1-m-c) (fn-rtc-m-max-reqs . pc1-m-max-reqs)
                   (fn-rtc-m-max-state . pc1-m-max-state)))
        (copies (fn-rtc-layer-alist 'pc1-model *fn-rtc-layer-spec-fns*))
        (alist (append machine copies)))
   (cons 'progn (fn-rtc-layer-copies *fn-rtc-layer-spec-fns* :spec alist (w state)))))

(defun pc1-scol-okp (i fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (fn-cat-count fn-cat) (nfix i)))))
  (and (fn-arena-p fn-arena)
       (if (and (natp i) (< i (fn-cat-count fn-cat)))
           (and (fn-scol-row-okp (fn-cat-at i fn-cat) fn-arena)
                (pc1-scol-okp (+ 1 i) fn-arena fn-cat)) t)))

(defun pc1-rows-within (i a limits fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (fn-cat-count fn-cat) (nfix i)))))
  (if (and (natp i) (< i (fn-cat-count fn-cat)))
      (let* ((article (fn-cat-row-article i fn-arena fn-cat))
             (payload (fn-nntp-article-bytes article fn-arena)))
        (and (or (fn-nntp-article-tombstonep article fn-arena)
                 (and (fn-o1-article-within-headerp article payload)
                      (fn-article-result-okp (fn-article-parse-under payload limits))
                      (<= (len payload) (nfix a))))
             (pc1-rows-within (+ 1 i) a limits fn-arena fn-cat)))
    t))

(defun pc1-pad (xs n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil (cons (if (consp xs) (car xs) 0) (pc1-pad (cdr xs) (- n 1)))))

(defun pc1-cbytes (h n s)
  (declare (xargs :measure (nfix (- (nfix n) (nfix h)))))
  (if (and (natp h) (< h (nfix n)))
      (append (pc1-pad (fn-rtc-b-bytes (fn-rtc-buffer h s)) (fn-rtc-buf-cap h (fn-rtc-config s)))
              (pc1-cbytes (+ 1 h) n s)) nil))

(defun pc1-cmeta (pool)
  (if (consp pool)
      (cons (list (fn-rtc-get 0 (car pool)) (fn-rtc-get 1 (car pool)) (len (fn-rtc-get 2 (car pool))))
            (pc1-cmeta (cdr pool))) nil))

(defun pc1-c-of (s)
  (list (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-mstates s) (pc1-cmeta (fn-rtc-pool s))
        (pc1-cbytes 0 (fn-rtc-nbufs (fn-rtc-config s)) s) (fn-rtc-uses s) (fn-rtc-next-op s)))

(defun pc1-KL1-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list (fn-ovw-cursorp cur) (fn-rtc-st$ap s))
        (let ((n (nth 0 q)) (next (nth 1 q)) (j (nth 2 q)) (s2 (nth 3 q)))
  (let ((step (mv-list 2 (fn-ovw-step cur n fn-arena fn-cat))))
    (if (posp n)
        (and (equal s2 (fn-rtc-st$a-splice h base (mv-nth 0 step) s))
             (equal j (+ (nfix base) (len (mv-nth 0 step))))
             (equal next (mv-nth 1 step)))
      (and (equal s2 s) (equal j (nfix base)) (equal next cur)))))))

(defun pc1-KL1v-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list (fn-ovw-cursorp cur) (pc1-model-invp s) (fn-hl-render-ready-p h id inc s))
        (let ((n (nth 0 q)) (next (nth 1 q)) (j (nth 2 q)) (s2 (nth 3 q)))
  (declare (ignorable n next j s2))
  (if (posp n)
      (and (equal (fn-dsw-view h base j s2)
                  (mv-nth 0 (mv-list 2 (fn-ovw-step cur n fn-arena fn-cat))))
           (if (< base j)
               (equal s2
                      (mv-nth 0
                              (mv-list 4
                                       (fn-rtc-req-write (list :write h
                                                               (fn-rtc-get 0 (fn-rtc-buffer h s))
                                                               base
                                                               (fn-dsw-view h base j s2))
                                                         id
                                                         inc
                                                         s))))
             t)
           (pc1-model-invp s2))
    t))))

(defun pc1-KL2-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list (<= (nfix base) (nfix limit)))
        (<= (mv-nth 2 q) (nfix limit))))

(defun pc1-KL3-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list)
        (<= (mv-nth 0 q) (if (posp w) w 1))))

(defun pc1-KL4-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list (fn-ovw-cursorp cur)
      (consp cur)
      (not (nth 7 cur))
      (fn-cbor-octet-listp (nth 6 cur))
      (natp base)
      (unsigned-byte-p 59 limit)
      (fn-rtc-st$ap s)
      (fn-hl-render-ready-p h id inc s)
      (<= base (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))
      (<= (nfix limit) (fn-rtc-buf-cap h (fn-rtc-config s))))
        (let* ((n (mv-nth 0 q))
       (room (- (nfix limit) base))
       (wmax (+ 1 (- (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w) (nfix (nth 1 cur))))))
  (and (if (and (<= base (nfix limit))
                (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                (<= (len (mv-nth 0 (mv-list 2 (fn-ovw-step cur 1 fn-arena fn-cat)))) room))
           (posp n)
         t)
       (if (and (posp n) (< n wmax))
           (< room (len (mv-nth 0 (mv-list 2 (fn-ovw-step cur (+ 1 n) fn-arena fn-cat)))))
         t)))))

(defun pc1-KL5a-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list (fn-ovw-cursorp cur)
      (fn-hl-render-ready-p h id inc s)
      (fn-rtc-live-p id inc s)
      (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s))))
        (let ((n (nth 0 q)) (next (nth 1 q)) (j (nth 2 q)) (s2 (nth 3 q)))
  (declare (ignorable n next j s2))
  (let ((out (mv-nth 0 (mv-list 2 (fn-ovw-step cur n fn-arena fn-cat)))))
    (if (and (posp n) (< 0 j) (fn-rtc-st$corr c (fn-hl-quantum-state h out id inc s)))
        (and (member-equal (list :send id
                                 inc
                                 (fn-rtc-next-op s)
                                 (list h (fn-rtc-get 0 (fn-rtc-buffer h s)) 0 j))
                           (fn-rtc-uses (fn-hl-quantum-state h out id inc s)))
             (equal (fn-rtc-c-octets (fn-rtc-buf-base h (fn-rtc-config s))
                                     j
                                     (nth *fn-rtc-c-bytesi* c))
                    out))
      t)))))

(defun pc1-KL12-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list (fn-hll-invp s))
        (fn-hll-invp (mv-nth 4 lq))))

(defun pc1-KL5-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list (fn-hll-invp s)
      (fn-hl-render-ready-p h id inc s)
      (fn-rtc-live-p id inc s)
      (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
      (fn-ovw-cursorp cur)
      (mv-nth 0 run))
        (equal (mv-nth 1 run) (fn-ovw-run cur w fn-arena fn-cat))))

(defun pc1-KL6-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list (fn-hll-invp s)
      (fn-hl-render-ready-p h id inc s)
      (fn-rtc-live-p id inc s)
      (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
      (fn-ovw-cursorp cur)
      (not (nth 7 cur))
      (fn-cbor-octet-listp (nth 6 cur))
      (unsigned-byte-p 59 (fn-rtc-buf-cap h (fn-rtc-config s)))
      (fn-ovr-probes-within (nth 0 cur)
                            (nfix (nth 1 cur))
                            (nfix (nth 2 cur))
                            (nth 6 cur)
                            (nfix (nth 3 cur))
                            l
                            fn-arena
                            fn-cat)
      (<= (+ (nfix l) (fn-ovr-frame-max)) (fn-rtc-buf-cap h (fn-rtc-config s)))
      (< (fn-ovw-remaining cur) (nfix k)))
        (mv-nth 0 run)))

(defun pc1-KL7-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list (fn-hll-invp s)
      (fn-hl-render-ready-p h id inc s)
      (fn-rtc-live-p id inc s)
      (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
      (fn-ovw-cursorp cur)
      (not (nth 7 cur))
      (fn-cbor-octet-listp (nth 6 cur))
      (pc1-scol-okp 0 fn-arena fn-cat)
      (pc1-rows-within 0 a limits fn-arena fn-cat)
      (<= (nfix (fn-article-limit-octets limits)) (nfix hdr))
      (unsigned-byte-p 59 (fn-rtc-buf-cap h (fn-rtc-config s)))
      (<= (fn-ovr-over-capl hdr a (len (nth 6 cur))) (fn-rtc-buf-cap h (fn-rtc-config s)))
      (< (fn-ovw-remaining cur) (nfix k)))
        (mv-nth 0 run)))

; CEILING is logically total; DEFCONST insists on its nonzero-divisor guard.
; The only zero-divisor bound exercised below is this closed form.
(thm (equal (ceiling 3 0) 0))
(defun pc1-ceiling-total (x y)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal y 0) 0 (ceiling x y)))

(defun pc1-KL11-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (list (fn-hll-invp s)
      (fn-hl-render-ready-p h id inc s)
      (fn-rtc-live-p id inc s)
      (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
      (fn-ovw-cursorp cur)
      (consp cur)
      (not (nth 7 cur))
      (fn-cbor-octet-listp (nth 6 cur))
      (unsigned-byte-p 59 (fn-rtc-buf-cap h (fn-rtc-config s)))
      (posp l)
      (fn-ovr-probes-within (nth 0 cur)
                            (nfix (nth 1 cur))
                            (nfix (nth 2 cur))
                            (nth 6 cur)
                            (nfix (nth 3 cur))
                            l
                            fn-arena
                            fn-cat)
      (<= (+ l (fn-ovr-frame-max)) (fn-rtc-buf-cap h (fn-rtc-config s)))
      (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
      (< (fn-ovw-remaining cur) (nfix k)))
        (<= (mv-nth 0 quanta)
    (pc1-ceiling-total (+ 1 (- (nfix (nth 2 cur)) (nfix (nth 1 cur))))
             (min (if (posp w) w 1)
                  (floor (- (fn-rtc-buf-cap h (fn-rtc-config s)) (fn-ovr-frame-max)) l))))))

(defun pc1-KL4-draft2-check (cur w h base limit s id inc c l k hdr a limits q lq run quanta fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (list (and (fn-ovw-cursorp cur)
     (consp cur)
     (not (nth 7 cur))
     (fn-cbor-octet-listp (nth 6 cur))
     (natp base)
     (unsigned-byte-p 59 limit)) (let* ((n (mv-nth 0 q))
       (room (- (nfix limit) base))
       (wmax (+ 1
                (- (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w)
                   (nfix (nth 1 cur))))))
  (and (if (and (<= base (nfix limit))
                (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                (<= (len (mv-nth 0 (mv-list 2 (fn-ovw-step cur 1 fn-arena fn-cat))))
                    room))
           (posp n)
         t)
       (if (and (posp n) (< n wmax))
           (< room
              (len (mv-nth 0 (mv-list 2 (fn-ovw-step cur (+ 1 n) fn-arena fn-cat)))))
         t)))))

(defun pc1-seed (payloads rows fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (consp payloads)
      (let* ((fn-arena (fn-arena-seal-list (car payloads) fn-arena))
             (fn-cat (fn-cat-commit (car rows) fn-cat)))
        (pc1-seed (cdr payloads) (cdr rows) fn-arena fn-cat))
    (mv fn-arena fn-cat)))

(defun pc1-boot (cap scenario fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil))
  (mv-let (fn-rtc-st acts) (fn-hll-x-init (if (eq scenario :other-send) (list 3 3 cap 1 1 1 cap) (list 3 1 0 1 0 1 cap)) fn-rtc-st)
    (mv-let (fn-rtc-st left) (fn-hld-settle acts 100 fn-rtc-st)
      (declare (ignore left))
      (mv-let (fn-rtc-st id inc left) (fn-hld-begin 7 fn-rtc-st)
        (declare (ignore left))
        (mv id inc fn-rtc-st)))))

(defun pc1-mutate (scenario id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil))
  (case scenario
    (:free (fn-rtc-st-reset 0 (fn-rtc-st-gen 0 fn-rtc-st) '(:free) fn-rtc-st))
    (:closing
     (mv-let (fn-rtc-st acts refused cost) (fn-rtc-x-request '(:close) id inc fn-rtc-st)
       (declare (ignore acts refused cost)) fn-rtc-st))
    (:bad-mstate (fn-rtc-st-set-mstate id '(1 2) fn-rtc-st))
    (:prefix
     (mv-let (sig j fn-rtc-st) (fn-dsw-append 0 0 (make-list 200 :initial-element 77) fn-rtc-st)
       (declare (ignore sig j)) fn-rtc-st))
    (:bad-use (fn-rtc-st-set-uses (cons '(:send 9 9 9 (0 2 0 1)) (fn-rtc-st-uses fn-rtc-st)) fn-rtc-st))
    (:other-send
     (mv-let (fn-rtc-st acts refused cost) (fn-rtc-x-request '(:acquire 1) id inc fn-rtc-st)
       (declare (ignore acts refused cost))
       (let ((fn-rtc-st (fn-rtc-st-put 1 0 65 fn-rtc-st)))
         (mv-let (fn-rtc-st acts refused cost)
           (fn-rtc-x-request (list :submit :send (list 1 (fn-rtc-st-gen 1 fn-rtc-st) 0 1) nil) id inc fn-rtc-st)
           (declare (ignore acts refused cost)) fn-rtc-st))))
    (:recv
     (mv-let (fn-rtc-st acts refused cost)
       (fn-rtc-x-request (list :submit :recv (list 0 (fn-rtc-st-gen 0 fn-rtc-st) 0
                                                (fn-rtc-buf-cap 0 (fn-rtc-st-config fn-rtc-st))) nil)
                         id inc fn-rtc-st)
       (declare (ignore acts refused cost)) fn-rtc-st))
    (:send
     (let ((fn-rtc-st (fn-rtc-st-put 0 0 65 fn-rtc-st)))
       (mv-let (fn-rtc-st acts refused cost)
         (fn-rtc-x-request (list :submit :send (list 0 (fn-rtc-st-gen 0 fn-rtc-st) 0 1) nil)
                           id inc fn-rtc-st)
         (declare (ignore acts refused cost)) fn-rtc-st)))
    (otherwise fn-rtc-st)))

(defun pc1-observe (kind scenario cap cur w base limit l k hdr a limits fn-rtc-st fn-arena fn-cat)
  (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil))
  (mv-let (id inc fn-rtc-st) (pc1-boot cap scenario fn-rtc-st)
    (let* ((h (if (eq scenario :other-send) 2 0))
           (fn-rtc-st (pc1-mutate scenario id inc fn-rtc-st))
           (s (fn-rtc-x-state fn-rtc-st)))
      (case kind
        (:run
         (mv-let (ok out fn-rtc-st) (fn-ovr-lease-run cur w k h id inc fn-rtc-st fn-arena fn-cat)
           (let ((run (list ok out (fn-rtc-x-state fn-rtc-st))))
             (mv (list
                   (pc1-KL5-check cur w h base limit s id inc nil l k hdr a limits nil nil run nil fn-arena fn-cat)
                   (pc1-KL6-check cur w h base limit s id inc nil l k hdr a limits nil nil run nil fn-arena fn-cat)
                   (pc1-KL7-check cur w h base limit s id inc nil l k hdr a limits nil nil run nil fn-arena fn-cat)
                   run s)
                 fn-rtc-st))))
        
        (:quanta
         (mv-let (m fn-rtc-st) (fn-ovr-lease-run-quanta cur w k h id inc fn-rtc-st fn-arena fn-cat)
           (let ((quanta (list m (fn-rtc-x-state fn-rtc-st))))
             (mv (list (pc1-KL11-check cur w h base limit s id inc nil l k hdr a limits nil nil nil quanta fn-arena fn-cat)
                       m s) fn-rtc-st))))
        (:lease
         (mv-let (n next j op fn-rtc-st) (fn-ovr-lease-quantum cur w h id inc fn-rtc-st fn-arena fn-cat)
           (let ((lq (list n next j op (fn-rtc-x-state fn-rtc-st))))
             (mv (list (pc1-KL12-check cur w h base limit s id inc nil l k hdr a limits nil lq nil nil fn-arena fn-cat)
                       lq s) fn-rtc-st))))
        (otherwise
         (mv-let (n next j fn-rtc-st) (fn-ovr-quantum cur w h base limit fn-rtc-st fn-arena fn-cat)
           (let* ((q (list n next j (fn-rtc-x-state fn-rtc-st)))
                  (out (mv-nth 0 (mv-list 2 (fn-ovw-step cur n fn-arena fn-cat))))
                  (c (pc1-c-of (fn-hl-quantum-state h out id inc s)))
                  (c (if (eq scenario :bad-c)
                         (fn-rtc-set *fn-rtc-c-bytesi* (cons 0 (cdr (nth *fn-rtc-c-bytesi* c))) c) c)))
             (mv (list
                   (pc1-KL1-check cur w h base limit s id inc c l k hdr a limits q nil nil nil fn-arena fn-cat)
                   (pc1-KL1v-check cur w h base limit s id inc c l k hdr a limits q nil nil nil fn-arena fn-cat)
                   (pc1-KL2-check cur w h base limit s id inc c l k hdr a limits q nil nil nil fn-arena fn-cat)
                   (pc1-KL3-check cur w h base limit s id inc c l k hdr a limits q nil nil nil fn-arena fn-cat)
                   (pc1-KL4-check cur w h base limit s id inc c l k hdr a limits q nil nil nil fn-arena fn-cat)
                   (pc1-KL5a-check cur w h base limit s id inc c l k hdr a limits q nil nil nil fn-arena fn-cat)
                   q s (pc1-KL4-draft2-check cur w h base limit s id inc c l k hdr a limits q nil nil nil fn-arena fn-cat)
                   (list (posp n) (< 0 j) (fn-rtc-st$corr c (fn-hl-quantum-state h out id inc s)))
                   (and (member-equal (list :send id inc (fn-rtc-next-op s)
                                            (list h (fn-rtc-get 0 (fn-rtc-buffer h s)) 0 j))
                                      (fn-rtc-uses (fn-hl-quantum-state h out id inc s)))
                        (equal (fn-rtc-c-octets (fn-rtc-buf-base h (fn-rtc-config s)) j
                                                (nth *fn-rtc-c-bytesi* c)) out)))
                 fn-rtc-st))))))))

(defmacro pc1-scene (kind scenario cap cur w base limit l k hdr a limits payloads rows)
  `(with-local-stobj fn-arena
     (mv-let (result fn-arena)
       (with-local-stobj fn-cat
         (mv-let (result fn-arena fn-cat)
           (mv-let (fn-arena fn-cat) (pc1-seed ,payloads ,rows fn-arena fn-cat)
             (with-local-stobj fn-rtc-st
               (mv-let (result fn-rtc-st)
                 (pc1-observe ,kind ,scenario ,cap ,cur ,w ,base ,limit ,l ,k ,hdr ,a ,limits fn-rtc-st fn-arena fn-cat)
                 (mv result fn-arena fn-cat))))
           (mv result fn-arena)))
       result)))

(defun pc1-run-scene (kind scenario cap cur w base limit l k hdr a limits payloads rows)
  (declare (xargs :verify-guards nil))
  (pc1-scene kind scenario cap cur w base limit l k hdr a limits payloads rows))

(defun pc1-all-true (xs)
  (if (consp xs) (and (car xs) (pc1-all-true (cdr xs))) t))

(defun pc1-positive (check) (and (pc1-all-true (car check)) (cadr check)))

(defun pc1-removal (check i)
  (and (not (nth i (car check)))
       (pc1-all-true (update-nth i t (car check)))
       (not (cadr check))))

(with-guard-checking-event nil
 (defconst *pc1-cur* (fn-ovw-cursor "fn.test" 1 3 3 nil t '(110 102))))

(with-guard-checking-event nil
 (defconst *pc1-q* (pc1-run-scene :quantum nil 1000 *pc1-cur* 3 0 1000 100 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(value-triple (list :quantum *pc1-q*))

(assert-event (and (posp (nth 0 (nth 6 *pc1-q*)))
                   (pc1-positive (nth 0 *pc1-q*)) (pc1-positive (nth 1 *pc1-q*))
                   (pc1-positive (nth 2 *pc1-q*)) (pc1-positive (nth 3 *pc1-q*))
                   (pc1-positive (nth 4 *pc1-q*)) (pc1-positive (nth 5 *pc1-q*))))

(with-guard-checking-event nil
 (defconst *pc1-free* (pc1-run-scene :quantum :free 1000 *pc1-cur* 3 0 1000 100 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(value-triple (list :draft2-counterexample *pc1-free*))

(assert-event (and (car (nth 8 *pc1-free*)) (not (cadr (nth 8 *pc1-free*)))))

(assert-event (pc1-removal (nth 4 *pc1-free*) 7))

(with-guard-checking-event nil
 (defconst *pc1-base-past* (pc1-run-scene :quantum nil 1000 *pc1-cur* 3 1 1000 100 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 4 *pc1-base-past*) 8))

(with-guard-checking-event nil
 (defconst *pc1-KL2-tooth* (pc1-run-scene :quantum nil 1000 *pc1-cur* 3 1 0 100 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 2 *pc1-KL2-tooth*) 0))

(with-guard-checking-event nil
 (defconst *pc1-header* (pc1-run-scene :quantum nil 1000 (append *pc1-cur* '(t)) 3 0 1000 100 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(value-triple (list :header *pc1-header*))

(assert-event (pc1-removal (nth 4 *pc1-header*) 2))

(with-guard-checking-event nil
 (defconst *pc1-bad-server* (pc1-run-scene :quantum nil 1000 (update-nth 6 '(300) *pc1-cur*) 3 0 1000 100 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 4 *pc1-bad-server*) 3))

(with-guard-checking-event nil
 (defconst *pc1-run* (pc1-run-scene :run nil 1000 *pc1-cur* 1 0 1000 100 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(value-triple (list :run *pc1-run*))

(assert-event (and (pc1-positive (nth 0 *pc1-run*)) (pc1-positive (nth 1 *pc1-run*))))

(with-guard-checking-event nil
 (defconst *pc1-lease* (pc1-run-scene :lease nil 1000 *pc1-cur* 3 0 1000 100 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (and (posp (car (nth 1 *pc1-lease*))) (pc1-positive (nth 0 *pc1-lease*))))

(with-guard-checking-event nil
 (defconst *pc1-bound-run*
  (pc1-run-scene :run nil 10000 (fn-ovw-cursor "fn.test" 1 4 4 nil t *ovrbt-server*) 3
              0 10000 100 10 100 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*)))

(value-triple (list :KL7 *pc1-bound-run*))

(assert-event (pc1-positive (nth 2 *pc1-bound-run*)))

(with-guard-checking-event nil
 (defconst *pc1-one* (fn-ovw-cursor "fn.test" 1 1 3 nil t '(110 102))))

(with-guard-checking-event nil
 (defconst *pc1-first-len*
  (fn-ovr-column-line-len 1 (fn-hf-nov (fn-held-facts *ovrs-r0*)) (len *ovrs-p0*)
                          (fn-hf-body-lines (fn-held-facts *ovrs-r0*)) '(110 102)
                          (fn-held-numbers *ovrs-r0*) t)))

(with-guard-checking-event nil
 (defconst *pc1-tight-cap* (+ *pc1-first-len* (len (fn-ovr-status-octets)) 3 -1)))

(with-guard-checking-event nil
 (defconst *pc1-cap-tooth*
  (pc1-run-scene :run nil *pc1-tight-cap* *pc1-one* 3 0 *pc1-tight-cap* *pc1-first-len* 10
              100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(value-triple (list :first-line *pc1-first-len* :tight-cap *pc1-tight-cap* :KL6-cap *pc1-cap-tooth*))

(assert-event (pc1-removal (nth 1 *pc1-cap-tooth*) 9))

(with-guard-checking-event nil
 (defconst *pc1-limit-past-cap*
  (pc1-run-scene :quantum nil *pc1-tight-cap* *pc1-one* 3 0 (+ *pc1-tight-cap* *pc1-first-len*)
              *pc1-first-len* 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 4 *pc1-limit-past-cap*) 9))

(assert-event (pc1-positive (nth 1 *pc1-limit-past-cap*)))

(assert-event (and (equal (car (nth 6 *pc1-free*)) 0)
                   (not (nth 2 (car (nth 1 *pc1-free*)))) (cadr (nth 1 *pc1-free*))))

(assert-event (pc1-positive (nth 1 *pc1-base-past*)))

(with-guard-checking-event nil
 (defconst *pc1-probe-tooth*
  (pc1-run-scene :run nil (+ 1 (fn-ovr-frame-max)) *pc1-one* 3 0 (+ 1 (fn-ovr-frame-max)) 1 10
              100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 1 *pc1-probe-tooth*) 8))

(with-guard-checking-event nil
 (defconst *pc1-recv*
  (pc1-run-scene :quantum :recv 1000 *pc1-cur* 3 0 1000 100 10 100 100
              (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(value-triple (list :KL1v-recv *pc1-recv*))

(assert-event (pc1-removal (nth 1 *pc1-recv*) 2))

(with-guard-checking-event nil
 (defconst *pc1-send*
  (pc1-run-scene :quantum :send 1000 *pc1-cur* 3 0 1000 100 10 100 100
              (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (and (pc1-all-true (update-nth 2 t (car (nth 1 *pc1-send*))))
                   (not (nth 2 (car (nth 1 *pc1-send*))))
                   (equal (car (nth 6 *pc1-send*)) 0) (cadr (nth 1 *pc1-send*))))

(with-guard-checking-event nil
 (defconst *pc1-KL12-tooth*
  (pc1-run-scene :lease :bad-mstate 1000 *pc1-cur* 3 0 1000 100 10 100 100
              (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (car *pc1-KL12-tooth*) 0))

(with-guard-checking-event nil
 (defconst *pc1-base-negative*
  (pc1-run-scene :quantum nil 1000 *pc1-cur* 3 -1 1000 100 10 100 100
              (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 4 *pc1-base-negative*) 4))

(with-guard-checking-event nil
 (defconst *pc1-limit-nonnat*
  (pc1-run-scene :quantum nil 1000 (fn-ovw-cursor "fn.missing" 1 3 3 nil nil nil) 1 0 "x" 100 10 100 100
              (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 4 *pc1-limit-nonnat*) 5))

(with-guard-checking-event nil
 (defconst *pc1-KL6-header*
  (pc1-run-scene :run nil 1000 (append *pc1-cur* '(t)) 3 0 1000 100 10 100 100
              (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 1 *pc1-KL6-header*) 5))

(with-guard-checking-event nil
 (defconst *pc1-KL6-server*
  (pc1-run-scene :run nil 1000 (update-nth 6 '(300) *pc1-cur*) 3 0 1000 100 10 100 100
              (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 1 *pc1-KL6-server*) 6))

(with-guard-checking-event nil
 (defconst *pc1-KL6-k*
  (pc1-run-scene :run nil 1000 *pc1-cur* 1 0 1000 100 1 100 100
              (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 1 *pc1-KL6-k*) 10))

(with-guard-checking-event nil
 (defconst *pc1-KL7-header*
  (pc1-run-scene :run nil 10000 (append (fn-ovw-cursor "fn.test" 1 4 4 nil t *ovrbt-server*) '(t)) 3
              0 10000 100 10 100 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*)))

(assert-event (pc1-removal (nth 2 *pc1-KL7-header*) 5))

(with-guard-checking-event nil
 (defconst *pc1-KL7-server*
  (pc1-run-scene :run nil 10000 (fn-ovw-cursor "fn.test" 1 4 4 nil t '(300)) 3
              0 10000 100 10 100 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*)))

(assert-event (pc1-removal (nth 2 *pc1-KL7-server*) 6))

(with-guard-checking-event nil
 (defconst *pc1-KL7-cap*
  (pc1-run-scene :run nil 1 (fn-ovw-cursor "fn.test" 1 4 4 nil t *ovrbt-server*) 3
              0 1 100 10 100 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*)))

(assert-event (pc1-removal (nth 2 *pc1-KL7-cap*) 11))

(with-guard-checking-event nil
 (defconst *pc1-KL7-k*
  (pc1-run-scene :run nil 10000 (fn-ovw-cursor "fn.test" 1 4 4 nil t *ovrbt-server*) 1
              0 10000 100 1 100 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*)))

(assert-event (pc1-removal (nth 2 *pc1-KL7-k*) 12))

(with-guard-checking-event nil
 (defconst *pc1-long-payload* (ovrbt-article "fn.test" (coerce (make-list 500 :initial-element #\s) 'string) "A")))

(with-guard-checking-event nil
 (defconst *pc1-long-specs* (list (list "<long@x>" *pc1-long-payload* '("fn.test") :column))))

(with-guard-checking-event nil
 (defconst *pc1-long-a* (ovrbt-arena *pc1-long-specs*)))

(with-guard-checking-event nil
 (defconst *pc1-long-c* (ovrbt-cat-from 0 *pc1-long-specs* nil)))

(with-guard-checking-event nil
 (defconst *pc1-KL7-row*
  (pc1-run-scene :run nil (fn-ovr-over-capl 0 1000 2) (fn-ovw-cursor "fn.test" 1 1 1 nil t *ovrbt-server*) 1
              0 (fn-ovr-over-capl 0 1000 2) 1000 10 0 1000 (fn-article-limits 10 10 0) *pc1-long-a* *pc1-long-c*)))

(value-triple (list :KL7-overlong-row *pc1-KL7-row*))

(assert-event (pc1-removal (nth 2 *pc1-KL7-row*) 8))

(with-guard-checking-event nil
 (defconst *pc1-cursor-tooth*
  (pc1-run-scene :quantum nil 1000 (update-nth 3 -1 *pc1-cur*) 1 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) nil nil)))

(assert-event (pc1-removal (nth 0 *pc1-cursor-tooth*) 0))

(with-guard-checking-event nil
 (defconst *pc1-prefix*
  (pc1-run-scene :quantum :prefix 1000 *pc1-cur* 3 0 80 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (and (posp (car (nth 6 *pc1-prefix*)))
                   (< (nth 2 (nth 6 *pc1-prefix*)) 200)
                   (equal (len (fn-rtc-b-bytes (fn-rtc-buffer 0 (nth 3 (nth 6 *pc1-prefix*))))) 200)
                   (pc1-positive (nth 0 *pc1-prefix*)) (pc1-positive (nth 1 *pc1-prefix*))
                   (pc1-positive (nth 2 *pc1-prefix*)) (pc1-positive (nth 3 *pc1-prefix*))
                   (pc1-positive (nth 4 *pc1-prefix*))))

(with-guard-checking-event nil
 (defconst *pc1-positive-without-LIMIT-premise*
  (pc1-run-scene :quantum nil 1000 *pc1-cur* 3 0 1001 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-positive (nth 1 *pc1-positive-without-LIMIT-premise*)))

(with-guard-checking-event nil
 (defconst *pc1-invp-tooth*
  (pc1-run-scene :quantum :bad-use 1000 *pc1-cur* 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(value-triple (list :KL1v-invp *pc1-invp-tooth*))

(assert-event (pc1-removal (nth 1 *pc1-invp-tooth*) 1))

(with-guard-checking-event nil
 (defconst *pc1-run-other-send*
  (pc1-run-scene :run :other-send 1000 *pc1-cur* 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(value-triple (list :KL6-other-send *pc1-run-other-send*))

(assert-event (pc1-removal (nth 1 *pc1-run-other-send*) 3))

(with-guard-checking-event nil
 (defconst *pc1-bound-other-send*
  (pc1-run-scene :run :other-send 10000 (fn-ovw-cursor "fn.test" 1 4 4 nil t *ovrbt-server*) 3
                0 10000 100 10 100 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*)))

(assert-event (pc1-removal (nth 2 *pc1-bound-other-send*) 3))

(value-triple (list :DRAFT2-KL4 (nth 8 *pc1-free*) :N (car (nth 6 *pc1-free*))
                    :J (nth 2 (nth 6 *pc1-free*))
                    :UNCHANGED (equal (nth 3 (nth 6 *pc1-free*)) (nth 7 *pc1-free*))))

(assert-event (pc1-removal (nth 0 *pc1-KL6-k*) 5))

(with-guard-checking-event nil
 (defconst *pc1-frame-less-one*
  (pc1-run-scene :run nil (+ *pc1-first-len* (fn-ovr-frame-max) -1) *pc1-one* 3
                0 (+ *pc1-first-len* (fn-ovr-frame-max) -1) *pc1-first-len* 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (and (not (nth 9 (car (nth 1 *pc1-frame-less-one*))))
                   (pc1-all-true (update-nth 9 t (car (nth 1 *pc1-frame-less-one*))))
                   (cadr (nth 1 *pc1-frame-less-one*))))

(value-triple (list :LINE *pc1-first-len* :FRAME-MAX (fn-ovr-frame-max)
                    :EXACT-WINDOW (+ *pc1-first-len* (len (fn-ovr-status-octets)) 3)
                    :STALL-CAP *pc1-tight-cap* :FRAME-LESS-ONE-PROGRESSES (cadr (nth 1 *pc1-frame-less-one*))))

(assert-event (and (pc1-all-true (nth 9 *pc1-q*)) (nth 10 *pc1-q*)))

(with-guard-checking-event nil
 (defconst *pc1-KL5a-corr-tooth*
  (pc1-run-scene :quantum :bad-c 1000 *pc1-cur* 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (and (pc1-all-true (car (nth 5 *pc1-KL5a-corr-tooth*)))
                   (pc1-removal (list (nth 9 *pc1-KL5a-corr-tooth*) (nth 10 *pc1-KL5a-corr-tooth*)) 2)))

(with-guard-checking-event nil
 (defconst *pc1-KL5a-empty-window*
  (pc1-run-scene :quantum nil 1000 (fn-ovw-cursor "missing" 1 3 3 nil nil nil) 1 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (and (pc1-all-true (car (nth 5 *pc1-KL5a-empty-window*)))
                   (not (nth 1 (nth 9 *pc1-KL5a-empty-window*)))
                   (pc1-all-true (update-nth 1 t (nth 9 *pc1-KL5a-empty-window*)))
                   (nth 10 *pc1-KL5a-empty-window*)))

(value-triple (list :KL5a-positive (nth 9 *pc1-q*) (nth 10 *pc1-q*)
                    :KL5a-corr-removal (nth 9 *pc1-KL5a-corr-tooth*) (nth 10 *pc1-KL5a-corr-tooth*)
                    :KL5a-empty (nth 9 *pc1-KL5a-empty-window*) (nth 10 *pc1-KL5a-empty-window*)))

(assert-event (pc1-removal (nth 5 *pc1-recv*) 1))

(with-guard-checking-event nil
 (defconst *pc1-KL5a-other-send*
  (pc1-run-scene :quantum :other-send 1000 *pc1-cur* 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 5 *pc1-KL5a-other-send*) 3))

(with-guard-checking-event nil
 (defconst *pc1-KL5a-closing*
  (pc1-run-scene :quantum :closing 1000 *pc1-cur* 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(assert-event (pc1-removal (nth 5 *pc1-KL5a-closing*) 2))

(with-guard-checking-event nil
 (defconst *pc1-KL6-closing*
  (pc1-run-scene :run :closing 1000 *pc1-cur* 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))

(value-triple (list :KL6-closing *pc1-KL6-closing*))

(assert-event (pc1-removal (nth 1 *pc1-KL6-closing*) 2))

(with-guard-checking-event nil
 (defconst *pc1-KL7-closing*
  (pc1-run-scene :run :closing 10000 (fn-ovw-cursor "fn.test" 1 4 4 nil t *ovrbt-server*) 3
                0 10000 100 10 100 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*)))

(assert-event (pc1-removal (nth 2 *pc1-KL7-closing*) 2))

(assert-event (pc1-positive (nth 5 *pc1-positive-without-LIMIT-premise*)))

(assert-event (and (not (nth 0 (car (nth 1 *pc1-cursor-tooth*))))
                   (pc1-all-true (update-nth 0 t (car (nth 1 *pc1-cursor-tooth*))))
                   (cadr (nth 1 *pc1-cursor-tooth*))))

(assert-event (pc1-positive (nth 1 *pc1-base-negative*)))

(assert-event (and (not (nth 0 (car (nth 4 *pc1-cursor-tooth*))))
                   (pc1-all-true (update-nth 0 t (car (nth 4 *pc1-cursor-tooth*))))
                   (cadr (nth 4 *pc1-cursor-tooth*))))

; extra-invariant-witnesses.lisp
(with-guard-checking-event nil
 (defconst *pc1-KL6-invp*
  (pc1-run-scene :run :bad-use 1000 *pc1-cur* 1 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(value-triple (list :KL6-invp *pc1-KL6-invp*))
(assert-event (pc1-removal (nth 1 *pc1-KL6-invp*) 0))
(with-guard-checking-event nil
 (defconst *pc1-KL7-invp*
  (pc1-run-scene :run :bad-use 10000 (fn-ovw-cursor "fn.test" 1 4 4 nil t *ovrbt-server*) 1
                0 10000 100 10 100 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*)))
(assert-event (pc1-removal (nth 2 *pc1-KL7-invp*) 0))
(with-guard-checking-event nil
 (defconst *pc1-KL5-no-invp*
  (pc1-run-scene :run :bad-mstate 1000 *pc1-cur* 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(assert-event (and (not (nth 0 (car (nth 0 *pc1-KL5-no-invp*))))
                   (pc1-all-true (update-nth 0 t (car (nth 0 *pc1-KL5-no-invp*))))
                   (cadr (nth 0 *pc1-KL5-no-invp*))))

; extra-bound-fixed.lisp
(with-guard-checking-event nil
 (defconst *pc1-lie2-base* (ovrbt-held 0 (list "<a@x>" (ovrbt-article "fn.test" "a" "A") '("fn.test") :column))))
(with-guard-checking-event nil
 (defconst *pc1-lie2-facts*
  (let ((f (fn-held-facts *pc1-lie2-base*)))
    (fn-hf-make (fn-hf-octets f) (fn-hf-body-start f) (fn-hf-body-lines f)
                (fn-hf-control-with-nov (fn-hf-control f)
                  (fn-hnov-make nil t (coerce (make-list 2000 :initial-element #\s) 'string) "" "" "" ""))))))
(with-guard-checking-event nil
 (defconst *pc1-lie2-row* (update-nth 11 *pc1-lie2-facts* *pc1-lie2-base*)))
(with-guard-checking-event nil
 (defconst *pc1-lie2-a* (list (ovrbt-article "fn.test" "a" "A"))))
(with-guard-checking-event nil
 (defconst *pc1-lie2-c* (list (fn-cat-assign *pc1-lie2-row* nil))))
(with-guard-checking-event nil
 (defconst *pc1-KL7-F2*
  (pc1-run-scene :run nil (fn-ovr-over-capl 100 100 2) (fn-ovw-cursor "fn.test" 1 1 1 nil t *ovrbt-server*) 1
                0 (fn-ovr-over-capl 100 100 2) 100 10 100 100 *ovrbt-limits* *pc1-lie2-a* *pc1-lie2-c*)))
(value-triple (list :KL7-F2 *pc1-KL7-F2*))
(assert-event (pc1-removal (nth 2 *pc1-KL7-F2*) 7))
(with-guard-checking-event nil
 (defconst *pc1-header2-specs* (list (list "<a@x>" *pc1-long-payload* '("fn.test") :column))))
(with-guard-checking-event nil
 (defconst *pc1-header2-a* (ovrbt-arena *pc1-header2-specs*)))
(with-guard-checking-event nil
 (defconst *pc1-header2-c* (ovrbt-cat-from 0 *pc1-header2-specs* nil)))
(with-guard-checking-event nil
 (defconst *pc1-KL7-HDR2*
  (pc1-run-scene :run nil (fn-ovr-over-capl 0 5000 2) (fn-ovw-cursor "fn.test" 1 1 1 nil t *ovrbt-server*) 1
                0 (fn-ovr-over-capl 0 5000 2) 5000 10 0 5000 (fn-article-limits 10 10 4000) *pc1-header2-a* *pc1-header2-c*)))
(value-triple (list :KL7-HDR2 *pc1-KL7-HDR2*))
(assert-event (pc1-removal (nth 2 *pc1-KL7-HDR2*) 9))
(with-guard-checking-event nil
 (defconst *pc1-KL6-free*
  (pc1-run-scene :run :free 1000 *pc1-cur* 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(assert-event (pc1-removal (nth 1 *pc1-KL6-free*) 1))
(with-guard-checking-event nil
 (defconst *pc1-KL7-free*
  (pc1-run-scene :run :free 10000 (fn-ovw-cursor "fn.test" 1 4 4 nil t *ovrbt-server*) 3
                0 10000 100 10 100 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*)))
(assert-event (pc1-removal (nth 2 *pc1-KL7-free*) 1))

; extra-empty-witnesses.lisp
(with-guard-checking-event nil
 (defconst *pc1-empty-range*
  (pc1-run-scene :quantum nil 1000 (fn-ovw-cursor "fn.test" 5 3 3 nil t '(110 102)) 3
                0 1000 100 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(assert-event (and (equal (car (nth 6 *pc1-empty-range*)) 1)
                   (null (nth 1 (nth 6 *pc1-empty-range*)))
                   (pc1-positive (nth 0 *pc1-empty-range*))
                   (pc1-positive (nth 1 *pc1-empty-range*))
                   (pc1-positive (nth 2 *pc1-empty-range*))
                   (pc1-positive (nth 3 *pc1-empty-range*))
                   (pc1-all-true (nth 9 *pc1-empty-range*))
                   (nth 10 *pc1-empty-range*)))
(value-triple (list :EMPTY-RANGE (take 3 (nth 6 *pc1-empty-range*))))

; Closed draft-2 counterexample, evaluated afresh against its six-premise text.
(value-triple
 (let ((r (pc1-run-scene :quantum :free 1000
                         (fn-ovw-cursor "fn.test" 1 3 3 nil t '(110 102))
                         3 0 1000 100 10 100 100 (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
   (list :DRAFT2-KL4 (nth 8 r) :N (car (nth 6 r)) :J (nth 2 (nth 6 r))
         :UNCHANGED (equal (nth 3 (nth 6 r)) (nth 7 r)))))

; Draft 3 count model: actual leased executor, with the stobj returned.
(with-guard-checking-event nil
 (defconst *pc1-Q-W1*
  (pc1-run-scene :quanta nil 1000 *pc1-cur* 1 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(value-triple (list :KL11-W1 (car *pc1-Q-W1*) :COUNT (cadr *pc1-Q-W1*)))
(with-guard-checking-event nil
 (defconst *pc1-Q-W3*
  (pc1-run-scene :quanta nil 1000 *pc1-cur* 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(value-triple (list :KL11-W3 (car *pc1-Q-W3*) :COUNT (cadr *pc1-Q-W3*)))
(assert-event (and (pc1-positive (car *pc1-Q-W1*)) (pc1-positive (car *pc1-Q-W3*))
                   (equal (cadr *pc1-Q-W1*) 3) (equal (cadr *pc1-Q-W3*) 1)
                   (< (ceiling 3 3) (cadr *pc1-Q-W1*))))
; Actual maximum row is 44 octets, including Xref: nf fn.test:2 fn.other:1.
; Capacity=44+65 permits one-row-with-framing, but is below L=100+65.
(with-guard-checking-event nil
 (defconst *pc1-Q-capacity*
  (pc1-run-scene :quanta nil (+ 44 (fn-ovr-frame-max)) *pc1-cur* 3 0 (+ 44 (fn-ovr-frame-max)) 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(value-triple (list :KL11-capacity (car *pc1-Q-capacity*) :COUNT (cadr *pc1-Q-capacity*)))
(assert-event (pc1-removal (car *pc1-Q-capacity*) 11))
(with-guard-checking-event nil
 (defconst *pc1-Q-inv*
  (pc1-run-scene :quanta :bad-use 1000 *pc1-cur* 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(value-triple (list :KL11-inv (car *pc1-Q-inv*) :COUNT (cadr *pc1-Q-inv*)))
(assert-event (and (not (nth 0 (caar *pc1-Q-inv*)))
                   (pc1-all-true (update-nth 0 t (caar *pc1-Q-inv*)))
                   (cadar *pc1-Q-inv*)))
(with-guard-checking-event nil
 (defconst *pc1-Q-probe*
  (pc1-run-scene :quanta nil 100 *pc1-cur* 3 0 100 1 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(value-triple (list :KL11-probe (car *pc1-Q-probe*) :COUNT (cadr *pc1-Q-probe*)))
(assert-event (pc1-removal (car *pc1-Q-probe*) 10))
(with-guard-checking-event nil
 (defconst *pc1-Q-range*
  (pc1-run-scene :quanta nil 1000 (fn-ovw-cursor "fn.test" 5 3 3 nil t '(110 102)) 3 0 1000 100 10 100 100
                (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(value-triple (list :KL11-range (car *pc1-Q-range*) :COUNT (cadr *pc1-Q-range*)))
(assert-event (pc1-removal (car *pc1-Q-range*) 12))
(value-triple (list :DRAFT3B-KL1v (nth 1 *pc1-q*) :DRAFT3B-KL5a (nth 5 *pc1-q*)
                    :INNER-PREMISES (nth 9 *pc1-q*) :N (car (nth 6 *pc1-q*))))
(assert-event (and (pc1-positive (nth 1 *pc1-q*)) (pc1-positive (nth 5 *pc1-q*))
                   (pc1-all-true (nth 9 *pc1-q*)) (posp (car (nth 6 *pc1-q*)))))

(with-guard-checking-event nil
 (defconst *pc1-Q-negative-L*
  (pc1-run-scene :quanta nil 1000 *pc1-cur* 3 0 1000 -1 10 100 100
                (fn-article-limits 10 10 100) nil nil)))
(value-triple (list :KL11-L (car *pc1-Q-negative-L*) :COUNT (cadr *pc1-Q-negative-L*)))
(assert-event (pc1-removal (car *pc1-Q-negative-L*) 9))

; KL1o: the entire antecedent and conclusion, then removal of inner POSP N.
(defun pc1-observe-admission (kind scenario cap cur w base limit l k hdr a limits fn-rtc-st fn-arena fn-cat)
 (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil)
          (ignore kind l k hdr a limits))
 (mv-let (id inc fn-rtc-st) (pc1-boot cap scenario fn-rtc-st)
  (let* ((fn-rtc-st (pc1-mutate scenario id inc fn-rtc-st)) (s (fn-rtc-x-state fn-rtc-st)))
   (mv-let (n next j fn-rtc-st) (fn-ovr-quantum cur w 0 base limit fn-rtc-st fn-arena fn-cat)
    (declare (ignore next j))
    (let* ((out (mv-nth 0 (mv-list 2 (fn-ovw-step cur n fn-arena fn-cat))))
           (ok (fn-rtc-splice-okp 0 base out s)))
     (mv (list (fn-ovw-cursorp cur) (fn-rtc-st$ap s) (posp n) ok
               (if (posp n) ok t) n (len out)) fn-rtc-st))))))
(defmacro pc1-admission-scene (kind scenario cap cur w base limit l k hdr a limits payloads rows)
  `(with-local-stobj fn-arena
     (mv-let (result fn-arena)
       (with-local-stobj fn-cat
         (mv-let (result fn-arena fn-cat)
           (mv-let (fn-arena fn-cat) (pc1-seed ,payloads ,rows fn-arena fn-cat)
             (with-local-stobj fn-rtc-st
               (mv-let (result fn-rtc-st)
                 (pc1-observe-admission ,kind ,scenario ,cap ,cur ,w ,base ,limit ,l ,k ,hdr ,a ,limits fn-rtc-st fn-arena fn-cat)
                 (mv result fn-arena fn-cat))))
           (mv result fn-arena)))
       result)))
(defun pc1-admission-run-scene (kind scenario cap cur w base limit l k hdr a limits payloads rows)
  (declare (xargs :verify-guards nil))
  (pc1-admission-scene kind scenario cap cur w base limit l k hdr a limits payloads rows))
(with-guard-checking-event nil
 (defconst *pc1-KL1o-positive*
 (pc1-admission-run-scene :quantum nil 1000 *pc1-cur* 3 0 1000 100 10 100 100
  (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(value-triple (list :KL1o-positive *pc1-KL1o-positive*))
(with-guard-checking-event nil
 (defconst *pc1-KL1o-free*
 (pc1-admission-run-scene :quantum :free 1000 *pc1-cur* 3 0 1000 100 10 100 100
  (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(value-triple (list :KL1o-free *pc1-KL1o-free*))
(with-guard-checking-event nil
 (defconst *pc1-KL1o-past-fill*
 (pc1-admission-run-scene :quantum nil 1000 *pc1-cur* 3 1 1000 100 10 100 100
  (fn-article-limits 10 10 100) *ovrs-a* *ovrs-c*)))
(value-triple (list :KL1o-past-fill *pc1-KL1o-past-fill*))
(assert-event (and (nth 0 *pc1-KL1o-positive*) (nth 1 *pc1-KL1o-positive*)
 (nth 2 *pc1-KL1o-positive*) (nth 3 *pc1-KL1o-positive*) (nth 4 *pc1-KL1o-positive*)))
(assert-event (and (nth 0 *pc1-KL1o-free*) (nth 1 *pc1-KL1o-free*)
 (not (nth 2 *pc1-KL1o-free*)) (not (nth 3 *pc1-KL1o-free*)) (nth 4 *pc1-KL1o-free*)))
(assert-event (and (nth 0 *pc1-KL1o-past-fill*) (nth 1 *pc1-KL1o-past-fill*)
 (not (nth 2 *pc1-KL1o-past-fill*)) (not (nth 3 *pc1-KL1o-past-fill*)) (nth 4 *pc1-KL1o-past-fill*)))
