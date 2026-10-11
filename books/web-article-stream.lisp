; Bounded ARTICLE metadata scanner over replayable logical NNTP plans.
; The guards are verified; the reference comparison is executable evidence,
; not a refinement claim. Offsets name the immutable virtual reply.
(in-package "ACL2")
(include-book "web-list-stream")
(include-book "web-page-cursor")

(defun fn-was-get (key x)
  (declare (xargs :guard (and (symbolp key) (alistp x))))
  (cdr (assoc-eq key x)))
(defun fn-was-put (key value x)
  (declare (xargs :guard (alistp x)))
  (if (consp x)
      (if (equal key (caar x)) (cons (cons key value) (cdr x))
        (cons (car x) (fn-was-put key value (cdr x))))
    (list (cons key value))))
(defthm fn-was-alistp-of-put
  (implies (alistp x) (alistp (fn-was-put key value x))))

(defthm fn-was-get-of-put
  (implies (and key k2)
           (equal (fn-was-get key (fn-was-put k2 v x))
                  (if (equal key k2) v (fn-was-get key x)))))

(defun fn-was-start (login)
  (declare (xargs :guard (true-listp login)))
  (list (cons :kind :article) (cons :phase :group) (cons :at 0) (cons :ls 0) (cons :prefix nil)
        (cons :last nil) (cons :slot nil) (cons :vs nil) (cons :fe 0)
        (cons :name nil) (cons :colon nil) (cons :skipping nil)
        (cons :fields (list nil nil nil nil nil)) (cons :body nil) (cons :be nil)
        (cons :status-end nil) (cons :pattern (append (list 60) login (list 64)))
        (cons :tail nil) (cons :own nil)))
;; What fn-was-octet reads of the scan state: positions and counters are
;; naturals, the buffers are lists, and the open field's slot and value start
;; are naturals when set.
(defun fn-was-statep (x)
  (declare (xargs :guard t))
  (and (alistp x)
       (natp (fn-was-get :at x)) (natp (fn-was-get :ls x)) (natp (fn-was-get :fe x))
       (true-listp (fn-was-get :prefix x)) (true-listp (fn-was-get :name x))
       (true-listp (fn-was-get :tail x)) (true-listp (fn-was-get :pattern x))
       (or (null (fn-was-get :vs x)) (natp (fn-was-get :vs x)))
       (or (null (fn-was-get :slot x)) (natp (fn-was-get :slot x)))))

;; The facts the guards read off a scan state, and a put keeps them.
(defthm fn-was-statep-facts
  (implies (fn-was-statep x)
           (and (alistp x)
                (natp (fn-was-get :at x)) (natp (fn-was-get :ls x)) (natp (fn-was-get :fe x))
                (true-listp (fn-was-get :prefix x)) (true-listp (fn-was-get :name x))
                (true-listp (fn-was-get :tail x)) (true-listp (fn-was-get :pattern x))
                (or (null (fn-was-get :vs x)) (natp (fn-was-get :vs x)))
                (or (null (fn-was-get :slot x)) (natp (fn-was-get :slot x)))))
  :rule-classes :forward-chaining)

(defun fn-was-field-okp (key v)
  (declare (xargs :guard t))
  (case key
    ((:at :ls :fe) (natp v))
    ((:prefix :name :tail :pattern) (true-listp v))
    ((:vs :slot) (or (null v) (natp v)))
    (otherwise t)))

(defthm fn-was-statep-of-put
  (implies (and (fn-was-statep x) key (symbolp key) (fn-was-field-okp key v))
           (fn-was-statep (fn-was-put key v x)))
  :hints (("Goal" :in-theory (enable fn-was-statep fn-was-field-okp)
                  :use (fn-was-statep-facts))))

(defun fn-was-commit (x)
  (declare (xargs :guard (fn-was-statep x)))
  (let ((slot (fn-was-get :slot x)) (vs (fn-was-get :vs x)))
    (if (and slot vs)
        (fn-was-put :fields (fn-wss-put-span slot (cons vs (fn-was-get :fe x))
                                            (fn-was-get :fields x)) x)
      x)))
(defun fn-was-code (prefix)
  (declare (xargs :guard (true-listp prefix)))
  (let ((a (car prefix)) (b (cadr prefix)) (c (caddr prefix)))
    (and (fn-ot-digitp a) (fn-ot-digitp b) (fn-ot-digitp c)
         (+ (* 100 (- a 48)) (* 10 (- b 48)) (- c 48)))))
(defun fn-was-octet (o x)
  (declare (xargs :guard (fn-was-statep x)
                  :guard-hints (("Goal" :in-theory (disable fn-was-get fn-was-put fn-was-statep
                                                            (:executable-counterpart tau-system))))))
  (let* ((at (fn-was-get :at x)) (ls (fn-was-get :ls x))
         (phase (fn-was-get :phase x)) (first (equal at ls))
         (prefix (fn-was-get :prefix x))
         (x (fn-was-put :at (1+ at) x)))
    ; A new non-continuation line settles the preceding field. Only the
    ; first occurrence is selected, as in fn-wss-headers.
    (let* ((x (if (and (equal phase :headers) first (not (member o '(32 9))))
                  (fn-was-put :tail nil (fn-was-put :vs nil (fn-was-put :slot nil
                    (fn-was-put :colon nil (fn-was-put :name nil (fn-was-commit x)))))) x))
           (x (if (< (len prefix) 17) (fn-was-put :prefix (append prefix (list o)) x) x))
           (x (if (and (equal phase :headers) (not (fn-was-get :colon x))
                       (not (and first (member o '(32 9)))))
                  (if (equal o 58)
                      (let* ((name (fn-was-get :name x))
                             (slot (and (<= (len name) 16)
                                        (fn-wss-field-index name *fn-wss-shown-fields* 0))))
                        (fn-was-put :slot slot (fn-was-put :vs (1+ at)
                          (fn-was-put :skipping t (fn-was-put :colon t x)))))
                    (let ((name (fn-was-get :name x)))
                      (if (< (len name) 17)
                          (fn-was-put :name (append name (list (fn-ot-downcase-octet o))) x) x))) x))
           (x (if (and (equal phase :headers) (fn-was-get :skipping x)
                       (fn-was-get :vs x) (>= at (fn-was-get :vs x)))
                  (if (member o '(32 9)) (fn-was-put :vs (1+ at) x)
                    (fn-was-put :skipping nil x)) x))
           (x (if (and (equal phase :headers) (equal (fn-was-get :slot x) 1)
                       (not (fn-wrq-nth 1 (fn-was-get :fields x)))
                       (fn-was-get :vs x))
                  (let* ((pat (fn-was-get :pattern x))
                         (tail (append (fn-was-get :tail x) (list o)))
                         (tail (if (> (len tail) (len pat)) (cdr tail) tail)))
                    (fn-was-put :tail tail (fn-was-put :own
                      (or (fn-was-get :own x) (equal tail pat)) x))) x)))
      (if (and (equal o 10) (equal (fn-was-get :last x) 13))
          (let* ((prefix (fn-was-get :prefix x)) (ce (max ls (1- at)))
                 (x (case phase
                      (:group (fn-was-put :status-end ce (fn-was-put :phase
                                 (if (equal (fn-was-code prefix) 211) :article :refused) x)))
                      (:article (fn-was-put :phase
                                   (if (equal (fn-was-code prefix) 220) :headers :refused) x))
                      (:headers (if (equal (+ ls 1) at)
                                    (fn-was-put :body (1+ at) (fn-was-put :phase :body (fn-was-commit x)))
                                  (fn-was-put :fe ce x)))
                      (:body (if (equal prefix '(46 13 10))
                                 (fn-was-put :be ls (fn-was-put :phase :done x)) x))
                      (otherwise x))))
            (fn-was-put :ls (1+ at) (fn-was-put :prefix nil (fn-was-put :last o x))))
        (fn-was-put :last o x)))))
(defthm fn-was-commit-statep
  (implies (fn-was-statep x) (fn-was-statep (fn-was-commit x)))
  :hints (("Goal" :in-theory (disable fn-was-get fn-was-put fn-was-statep
                                      (:executable-counterpart tau-system))
                  :expand ((fn-was-commit x)))))

(defthm fn-was-octet-statep
  (implies (fn-was-statep x) (fn-was-statep (fn-was-octet o x)))
  :hints (("Goal" :in-theory (disable fn-was-get fn-was-put fn-was-statep
                                      (:executable-counterpart tau-system)))))

(defun fn-was-scan (i end x fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp i) (natp end) (<= end (fn-octets-len fn-web-in))
                              (fn-was-statep x))
                  :guard-hints (("Goal" :in-theory (disable fn-was-octet)))
                  :measure (nfix (- (nfix end) (nfix i)))))
  (if (>= (nfix i) (nfix end)) x
    (fn-was-scan (1+ (nfix i)) end (fn-was-octet (fn-octets-get i fn-web-in) x) fn-web-in)))

;; The :v-list rows' segments are plan segments (a kind, then a list).
(local
 (defthm fn-was-octets-only-listp
   (or (consp (fn-wr-octets-only xs)) (equal (fn-wr-octets-only xs) nil))
   :hints (("Goal" :in-theory (enable fn-wr-octets-only)))
   :rule-classes :type-prescription))

(local
 (defthm fn-was-cdr-txt
   (equal (cdr (fn-wr-txt xs)) (fn-wr-octets-only xs))
   :hints (("Goal" :in-theory (enable fn-wr-txt)))))

(defthm fn-wgl-segs-wsegsp
  (implies (fn-wgl-rowp row) (fn-wpc-wsegsp (fn-wgl-segs row))))

;; A windowed cursor: the plain cursor's seven fields over segments whose
;; spans may lie anywhere in the virtual reply (only the window is in
;; fn-web-in), a :v-list span carrying its row parser and nothing pending.
(defun fn-wpc-wcursorp (cursor)
  (declare (xargs :guard t))
  (and (true-listp cursor) (equal (len cursor) 7)
       (fn-wpc-wsegsp (fn-wrq-nth 0 cursor))
       (member (fn-wrq-nth 1 cursor) (cons nil (remove :w *fn-wpc-kinds*)))
       (implies (null (fn-wrq-nth 1 cursor)) (null (fn-wrq-nth 6 cursor)))
       (implies (equal (fn-wrq-nth 1 cursor) :v-list)
                (and (null (fn-wrq-nth 6 cursor))
                     (or (null (fn-wrq-nth 2 cursor))
                         (fn-wgl-statep (fn-wrq-nth 2 cursor)))))))

;; What the window functions read off a windowed cursor (stated over nth and
;; car: the rewriter has already turned fn-wrq-nth into them where these fire).
(defthm fn-wpc-wcursorp-facts
  (implies (fn-wpc-wcursorp cursor)
           (and (true-listp cursor) (equal (len cursor) 7) (consp cursor)
                (fn-wpc-wsegsp (car cursor))
                (member (nth 1 cursor) (cons nil (remove :w *fn-wpc-kinds*)))))
  :hints (("Goal" :in-theory (enable fn-wpc-wcursorp fn-wrq-nth-is-nth)))
  :rule-classes :forward-chaining)

(defthm fn-wpc-wcursorp-pending
  (implies (and (fn-wpc-wcursorp cursor) (null (nth 1 cursor)))
           (null (nth 6 cursor)))
  :hints (("Goal" :in-theory (enable fn-wpc-wcursorp fn-wrq-nth-is-nth)))
  :rule-classes :forward-chaining)

(defthm fn-wpc-wcursorp-v-list
  (implies (and (fn-wpc-wcursorp cursor) (equal (nth 1 cursor) :v-list))
           (and (null (nth 6 cursor))
                (or (null (nth 2 cursor)) (fn-wgl-statep (nth 2 cursor)))))
  :hints (("Goal" :in-theory (enable fn-wpc-wcursorp fn-wrq-nth-is-nth)))
  :rule-classes :forward-chaining)

(defthm fn-wpc-wsegsp-head
  (implies (fn-wpc-wsegsp segs)
           (if (consp segs)
               (and (consp (car segs))
                    (member (car (car segs)) *fn-wpc-kinds*)
                    (or (consp (cdr (car segs))) (null (cdr (car segs))))
                    (fn-wpc-wsegsp (cdr segs)))
             (null segs)))
  :hints (("Goal" :in-theory (enable fn-wpc-wsegsp)))
  :rule-classes nil)

; The window cursor returns a fifth value NEED=(START . END). It never
; advances a virtual source without those exact source octets being present.
(defun fn-wpc-window-next (cursor base fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp base) (fn-wpc-wcursorp cursor))
                  :guard-hints (("Goal" :do-not-induct t
                                 :use ((:instance fn-wpc-wcursorp-facts (cursor cursor))
                                       (:instance fn-wpc-wcursorp-v-list (cursor cursor))
                                       (:instance fn-wpc-wcursorp-pending (cursor cursor))
                                       (:instance fn-wpc-wsegsp-head (segs (car cursor))))
                                 :in-theory (disable fn-wpc-next fn-wpc-wcursorp)))))
  (let* ((kind (fn-wrq-nth 1 cursor)) (s (nfix (fn-wrq-nth 3 cursor)))
         (e (nfix (fn-wrq-nth 4 cursor))) (seg (car (fn-wrq-nth 0 cursor)))
         (wk (and (not kind) (consp seg) (equal (car seg) :w)))
         (s (if wk (nfix (cadr seg)) s)) (e (if wk (nfix (cddr seg)) e))
         (spanp (or wk (member kind '(:s :d :v-u :v-list))))
         (need-end (if (and wk (<= (- e s) *fn-w47-max*)) e
                     (min e (+ s 4096))))
         (required-end (if (and wk (<= (- e s) *fn-w47-max*)) e
                         (min e (+ s (if (and (equal kind :d) (fn-wrq-nth 5 cursor)) 2 1)))))
         (limit (+ (nfix base) (fn-octets-len fn-web-in))))
    (if (and spanp (< s e) (not (consp (fn-wrq-nth 6 cursor)))
             (or (< s (nfix base)) (< limit required-end)))
        (mv nil nil cursor nil (cons s need-end))
      (if (equal kind :v-list)
          (if (< s e)
              (mv-let (row parser) (fn-wgl-feed (fn-octets-get (- s base) fn-web-in) s
                                              (or (fn-wrq-nth 2 cursor) (fn-wgl-start s)))
                (mv nil nil
                    (if row
                        (fn-wpc-cursor (append (fn-wgl-segs row)
                          (cons (cons :v-list (cons (1+ s) e)) (car cursor))))
                      (list (car cursor) kind parser (1+ s) e t nil)) nil nil))
            (mv nil nil (fn-wpc-cursor (car cursor)) nil nil))
      (if (and (equal kind :v-u) (consp (fn-wrq-nth 6 cursor)))
          (mv t (car (fn-wrq-nth 6 cursor))
              (list (car cursor) kind nil s e t (cdr (fn-wrq-nth 6 cursor))) nil nil)
      (if (equal kind :v-u)
          (if (< s e)
              (mv nil nil (list (car cursor) kind nil (1+ s) e t
                               (fn-wr-escape (fn-wr-pct-encode
                                              (list (fn-octets-get (- s base) fn-web-in))))) nil nil)
            (mv nil nil (fn-wpc-cursor (car cursor)) nil nil))
        (let* ((local (if (member kind '(:s :d))
                          (list (car cursor) kind nil (- s base) (- e base)
                                (fn-wrq-nth 5 cursor) (fn-wrq-nth 6 cursor))
                        (if (and wk (<= (- e s) *fn-w47-max*))
                            (list (cons (cons :w (cons (- s base) (- e base))) (cdr (car cursor)))
                                  nil nil 0 0 t nil) cursor))))
          (if (and (not kind) (consp seg) (member (car seg) '(:s :d :v-u :v-list)))
              (mv nil nil (list (cdr (car cursor)) (car seg) nil (cadr seg) (cddr seg) t nil) nil nil)
            (if (and wk (> (- e s) *fn-w47-max*))
                (mv nil nil (list (cdr (car cursor)) :s nil s e t nil) nil nil)
              (mv-let (present octet next done) (fn-wpc-next local fn-web-in)
                (mv present octet
                    (if (member (fn-wrq-nth 1 next) '(:s :d))
                        (list (car next) (cadr next) nil (+ base (fn-wrq-nth 3 next))
                              (+ base (fn-wrq-nth 4 next)) (fn-wrq-nth 5 next) (fn-wrq-nth 6 next)) next)
                    done nil)))))))))))
;; A window step keeps the windowed cursor in its vocabulary.  One lemma per
;; kind of cursor (the step is a different path in each), then their union.
(defthm fn-wpc-wsegsp-append
  (implies (and (fn-wpc-wsegsp a) (fn-wpc-wsegsp b))
           (fn-wpc-wsegsp (append a b)))
  :hints (("Goal" :in-theory (enable fn-wpc-wsegsp))))

(defthm fn-wgl-feed-segs-wsegsp
  (implies (and (natp at) (fn-wgl-statep x) (car (fn-wgl-feed o at x)))
           (fn-wpc-wsegsp (fn-wgl-segs (car (fn-wgl-feed o at x)))))
  :hints (("Goal" :use ((:instance fn-wgl-feed-rowp) (:instance fn-wgl-segs-wsegsp (row (car (fn-wgl-feed o at x)))))
                  :in-theory (disable fn-wgl-feed fn-wgl-segs fn-wgl-rowp fn-wgl-feed-rowp fn-wgl-segs-wsegsp))))

(defthm fn-wpc-wcursorp-of-list
  (equal (fn-wpc-wcursorp (list segs kind xs s e bol pending))
         (and (fn-wpc-wsegsp segs)
              (member kind (cons nil (remove :w *fn-wpc-kinds*)))
              (implies (null kind) (null pending))
              (implies (equal kind :v-list)
                       (and (null pending) (or (null xs) (fn-wgl-statep xs))))))
  :hints (("Goal" :in-theory (enable fn-wpc-wcursorp))))

(defthm fn-wpc-wcursorp-of-facts
  ; a cursor of the vocabulary that is not a :v-list span
  (implies (and (true-listp c) (equal (len c) 7)
                (fn-wpc-wsegsp (car c))
                (member (nth 1 c) (cons nil (remove :w *fn-wpc-kinds*)))
                (implies (null (nth 1 c)) (null (nth 6 c)))
                (not (equal (nth 1 c) :v-list)))
           (fn-wpc-wcursorp c))
  :hints (("Goal" :in-theory (enable fn-wpc-wcursorp))))

(defthm wn-vlist
  (implies (and (natp base) (fn-wpc-wcursorp cursor) (equal (nth 1 cursor) :v-list))
           (fn-wpc-wcursorp (mv-nth 2 (fn-wpc-window-next cursor base fn-web-in))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-wpc-wcursorp-facts (cursor cursor))
                        (:instance fn-wpc-wcursorp-v-list (cursor cursor))
                        (:instance fn-wpc-wsegsp-head (segs (car cursor))))
                  :in-theory (disable fn-wpc-next fn-wpc-wcursorp fn-wgl-feed fn-wgl-start fn-wgl-segs))))

(defthm wn-vu
  (implies (and (natp base) (fn-wpc-wcursorp cursor) (equal (nth 1 cursor) :v-u))
           (fn-wpc-wcursorp (mv-nth 2 (fn-wpc-window-next cursor base fn-web-in))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-wpc-wcursorp-facts (cursor cursor))
                        (:instance fn-wpc-wsegsp-head (segs (car cursor))))
                  :in-theory (disable fn-wpc-next fn-wpc-wcursorp fn-wgl-feed fn-wgl-start fn-wgl-segs))))

(defthm wn-span
  (implies (and (natp base) (fn-wpc-wcursorp cursor) (member (nth 1 cursor) '(:s :d)))
           (fn-wpc-wcursorp (mv-nth 2 (fn-wpc-window-next cursor base fn-web-in))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-wpc-wcursorp-facts (cursor cursor))
                        (:instance fn-wpc-wcursorp-pending (cursor cursor))
                        (:instance fn-wpc-next-shape
                                   (cursor (list (car cursor) (nth 1 cursor) nil
                                                 (+ (nfix (nth 3 cursor)) (- base))
                                                 (+ (nfix (nth 4 cursor)) (- base))
                                                 (nth 5 cursor) (nth 6 cursor))))
                        (:instance fn-wpc-next-not-v-list
                                   (cursor (list (car cursor) (nth 1 cursor) nil
                                                 (+ (nfix (nth 3 cursor)) (- base))
                                                 (+ (nfix (nth 4 cursor)) (- base))
                                                 (nth 5 cursor) (nth 6 cursor)))))
                  :in-theory (disable fn-wpc-next fn-wpc-wcursorp fn-wgl-feed fn-wgl-start fn-wgl-segs))))

(defthm wn-text
  (implies (and (natp base) (fn-wpc-wcursorp cursor) (member (nth 1 cursor) '(:m :t :u)))
           (fn-wpc-wcursorp (mv-nth 2 (fn-wpc-window-next cursor base fn-web-in))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-wpc-wcursorp-facts (cursor cursor))
                        (:instance fn-wpc-wcursorp-pending (cursor cursor))
                        (:instance fn-wpc-next-shape (cursor cursor))
                        (:instance fn-wpc-next-not-v-list (cursor cursor)))
                  :in-theory (disable fn-wpc-next fn-wpc-wcursorp fn-wgl-feed fn-wgl-start fn-wgl-segs))))

(defthm wn-none
  (implies (and (natp base) (fn-wpc-wcursorp cursor) (null (nth 1 cursor)))
           (fn-wpc-wcursorp (mv-nth 2 (fn-wpc-window-next cursor base fn-web-in))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-wpc-wcursorp-facts (cursor cursor))
                        (:instance fn-wpc-wcursorp-pending (cursor cursor))
                        (:instance fn-wpc-wsegsp-head (segs (car cursor)))
                        (:instance fn-wpc-next-shape (cursor cursor))
                        (:instance fn-wpc-next-not-v-list (cursor cursor))
                        (:instance fn-wpc-next-shape
                                   (cursor (list (cons (cons :w (cons (+ (nfix (cadr (car (car cursor)))) (- base))
                                                                      (+ (nfix (cddr (car (car cursor)))) (- base))))
                                                       (cdr (car cursor)))
                                                 nil nil 0 0 t nil)))
                        (:instance fn-wpc-next-not-v-list
                                   (cursor (list (cons (cons :w (cons (+ (nfix (cadr (car (car cursor)))) (- base))
                                                                      (+ (nfix (cddr (car (car cursor)))) (- base))))
                                                       (cdr (car cursor)))
                                                 nil nil 0 0 t nil))))
                  :in-theory (disable fn-wpc-next fn-wpc-wcursorp fn-wgl-feed fn-wgl-start fn-wgl-segs))))

(defthm fn-wpc-window-next-wcursorp
  (implies (and (natp base) (fn-wpc-wcursorp cursor))
           (fn-wpc-wcursorp (mv-nth 2 (fn-wpc-window-next cursor base fn-web-in))))
  :hints (("Goal" :use (wn-vlist wn-vu wn-span wn-text wn-none)
                  :in-theory (disable fn-wpc-window-next))))

(defun fn-wpc-window-drive (fuel cursor base count emitp rev fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp fuel) (natp base) (natp count)
                              (fn-wpc-wcursorp cursor) (true-listp rev))
                  :guard-hints (("Goal" :in-theory (disable fn-wpc-window-next)))))
  (if (zp fuel) (mv (reverse rev) cursor count nil nil)
    (mv-let (present octet next done need) (fn-wpc-window-next cursor base fn-web-in)
      (if (or done need) (mv (reverse rev) next count done need)
        (fn-wpc-window-drive (1- fuel) next base (if present (1+ count) count)
                             emitp (if (and present emitp) (cons octet rev) rev) fn-web-in)))))

(defun fn-was-page (config flow scan)
  (declare (xargs :guard (alistp scan)))
  (let* ((ctx (fn-wss-f-ctx flow)) (session (fn-wss-c-session ctx))
         (group (fn-wrq-nth 0 (fn-wss-f-data flow)))
         (ok (equal (fn-was-get :phase scan) :done))
         (fields (fn-was-get :fields scan))
         (title (if ok group (fn-wrq-oct "Not here")))
         (main (if ok
                   (fn-wr-article-main-segments group fields
                     (cons (fn-was-get :body scan) (fn-was-get :be scan))
                     (fn-was-get :own scan)
                     (let ((id (fn-wrq-nth 4 fields))) (and id (list (cons :v-u id)))))
                 (fn-wr-outcome-main-segments :no title
                   (fn-wrq-oct "That post isn't here: it may have been removed.")
                   (and (fn-was-get :status-end scan)
                        (list (cons :s (cons 0 (fn-was-get :status-end scan))))) nil)))
         (segs (fn-wr-frame title (fn-wss-cfg-site config) (fn-wss-c-theme ctx)
                            (and session (fn-wss-s-login session))
                            (and session (fn-wss-s-csrf session)) main)))
    (list :respond (if ok 200 404) *fn-wss-html-fields* (fn-wss-bodyp ctx) :page-plan segs)))

; The windowed cursor's quantum: at most FUEL octets per call (4096 from
; fn-web-host-page-window), and it never advances past a span whose source
; octets are absent (it returns NEED instead).
(defthm fn-wpc-window-drive-emits-at-most-fuel
  (<= (len (mv-nth 0 (fn-wpc-window-drive fuel cursor base count emitp rev fn-web-in)))
      (+ (len rev) (nfix fuel)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-wpc-window-next))))
