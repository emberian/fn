; Authored POST body windows over the retained HTTP request, PRF-1293.
; Logic-mode definitions, guards verified; the byte agreement with
; fn-wss-post-head/fn-wss-write-post is established by the tests
; (tests/acl2/web-post-stream-tests.lisp), not by a refinement theorem --
; both are proof-owed.  The keystones at the end state what IS proved: a
; POST is accepted only with its session's CSRF token, a valid group, a
; non-empty subject and body, and to that session's own connection, and
; every other request takes exactly the existing gate's refusal.
(in-package "ACL2")
(include-book "web-session-keystones")

; HEAD REST, encoded offset/end, BOL, pending CR, pending fragment, phase.
(defun fn-wps-cursor (head bs be)
  (declare (xargs :guard t))
  (list head bs be t nil nil :head))

(defun fn-wps-subject-prefix (fuel xs)
  (declare (xargs :guard (natp fuel)))
  (if (or (zp fuel) (atom xs)) nil
    (cons (if (member (car xs) '(13 10 9 0)) 32 (car xs))
          (fn-wps-subject-prefix (1- fuel) (cdr xs)))))
(defun fn-wps-header-cursor (login domain group subject ascii bs be)
  (declare (xargs :guard (true-listp group)))
  (list (append (fn-wss-from-field login domain) (fn-wrq-oct "Newsgroups: ") group
                '(13 10) (fn-wrq-oct "Subject: "))
        bs be t nil nil :head subject ascii
        (append '(13 10) (fn-wrq-oct "MIME-Version: 1.0") '(13 10)
                (fn-wrq-oct "Content-Type: text/plain; charset=utf-8") '(13 10)
                (fn-wrq-oct "Content-Transfer-Encoding: 8bit") '(13 10 13 10))))

;; The base64 and From octets the header cursor is made of.
(defthm fn-wps-b64-char-octet
  (fn-cbor-octetp (fn-wss-b64-char v urlp)))

(defthm fn-wps-b64-octets
  (fn-cbor-octet-listp (fn-wss-b64 xs urlp padp))
  :hints (("Goal" :in-theory (disable fn-wss-b64-char)
                  :induct (fn-wss-b64 xs urlp padp))))

(defthm fn-wps-from-field-octets
  (fn-cbor-octet-listp (fn-wss-from-field login domain)))

(defthm fn-wps-octets-of-nthcdr
  (implies (fn-cbor-octet-listp x) (fn-cbor-octet-listp (nthcdr k x))))

;; What fn-wps-next reads of a cursor over the N octets of fn-web-in: the
;; head, the pending fragment, the subject and the tail are octet lists, the
;; encoded body [I, E) lies inside the buffer, and the phase is one of four.
(defun fn-wps-cursorp (cursor n)
  (declare (xargs :guard (natp n)))
  (and (true-listp cursor)
       (fn-cbor-octet-listp (nth 0 cursor))
       (natp (nth 1 cursor)) (natp (nth 2 cursor)) (<= (nth 2 cursor) n)
       (fn-cbor-octet-listp (nth 5 cursor))
       (member (nth 6 cursor) '(:head :subject :body :tail))
       (fn-cbor-octet-listp (nth 7 cursor))
       (fn-cbor-octet-listp (nth 9 cursor))))

;; nth over update-nth, so a cursor's fields are read off a nest of updates one
;; at a time; and what each update of a field needs of its value.
(local
 (defthm fn-wps-nth-of-update-nth
   (implies (and (natp i) (natp j))
            (equal (nth i (update-nth j v l)) (if (equal i j) v (nth i l))))
   :hints (("Goal" :induct (nth i l)))))

(local
 (defthm fn-wps-true-listp-of-update-nth
   (implies (true-listp l) (true-listp (update-nth j v l)))))

(defthm fn-wps-cursorp-of-update-0
  (implies (and (fn-wps-cursorp c n) (fn-cbor-octet-listp v))
           (fn-wps-cursorp (update-nth 0 v c) n))
  :hints (("Goal" :in-theory (e/d (fn-wps-cursorp) (nth update-nth)))))
(defthm fn-wps-cursorp-of-update-3
  (implies (fn-wps-cursorp c n)
           (fn-wps-cursorp (update-nth 3 v c) n))
  :hints (("Goal" :in-theory (e/d (fn-wps-cursorp) (nth update-nth)))))
(defthm fn-wps-cursorp-of-update-4
  (implies (fn-wps-cursorp c n)
           (fn-wps-cursorp (update-nth 4 v c) n))
  :hints (("Goal" :in-theory (e/d (fn-wps-cursorp) (nth update-nth)))))
(defthm fn-wps-cursorp-of-update-5
  (implies (and (fn-wps-cursorp c n) (fn-cbor-octet-listp v))
           (fn-wps-cursorp (update-nth 5 v c) n))
  :hints (("Goal" :in-theory (e/d (fn-wps-cursorp) (nth update-nth)))))
(defthm fn-wps-cursorp-of-update-6
  (implies (and (fn-wps-cursorp c n) (member v '(:head :subject :body :tail)))
           (fn-wps-cursorp (update-nth 6 v c) n))
  :hints (("Goal" :in-theory (e/d (fn-wps-cursorp) (nth update-nth)))))
(defthm fn-wps-cursorp-of-update-7
  (implies (and (fn-wps-cursorp c n) (fn-cbor-octet-listp v))
           (fn-wps-cursorp (update-nth 7 v c) n))
  :hints (("Goal" :in-theory (e/d (fn-wps-cursorp) (nth update-nth)))))
(defthm fn-wps-cursorp-of-update-9
  (implies (and (fn-wps-cursorp c n) (fn-cbor-octet-listp v))
           (fn-wps-cursorp (update-nth 9 v c) n))
  :hints (("Goal" :in-theory (e/d (fn-wps-cursorp) (nth update-nth)))))

(defthm fn-wps-cursorp-of-seven
  (implies (and (fn-cbor-octet-listp head) (natp i) (natp e) (<= e n)
                (fn-cbor-octet-listp pending)
                (member phase '(:head :subject :body :tail)))
           (fn-wps-cursorp (list head i e bol pcr pending phase) n))
  :hints (("Goal" :in-theory (e/d (fn-wps-cursorp) (nth update-nth)))))

(defthm fn-wps-header-cursor-cursorp
  ; The cursor a form's finish makes is one fn-wps-next can read.
  (implies (and (fn-cbor-octet-listp group) (fn-cbor-octet-listp subject)
                (natp bs) (natp be) (<= be n))
           (fn-wps-cursorp (fn-wps-header-cursor login domain group subject ascii bs be) n))
  :hints (("Goal" :in-theory (e/d (fn-wps-cursorp fn-wps-header-cursor) (nth update-nth)))))

(defun fn-wps-next (cursor fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (fn-wps-cursorp cursor (fn-octets-len fn-web-in))))
  (let ((head (nth 0 cursor)) (i (nth 1 cursor)) (e (nth 2 cursor))
        (bol (nth 3 cursor)) (pcr (nth 4 cursor)) (pending (nth 5 cursor))
        (phase (nth 6 cursor)))
    (cond
     ((consp pending)
      (mv (car pending) (update-nth 5 (cdr pending) cursor) nil))
     ((equal phase :head)
      (if (consp head)
          (mv (car head) (update-nth 0 (cdr head) cursor) nil)
        (mv nil (update-nth 6 (if (consp (nth 7 cursor)) :subject :body) cursor) nil)))
     ((equal phase :subject)
      (let ((subject (nth 7 cursor)))
        (if (atom subject)
            (mv nil (update-nth 0 (nth 9 cursor) (update-nth 9 nil
                      (update-nth 6 :head cursor))) nil)
          (if (nth 8 cursor)
              (mv (if (member (car subject) '(13 10 9 0)) 32 (car subject))
                  (update-nth 7 (cdr subject) cursor) nil)
            (let* ((cut (fn-wss-utf8-take (fn-wps-subject-prefix 46 subject) 45 nil))
                   (rest (nthcdr (len (car cut)) subject))
                   (word (append (fn-wrq-oct "=?UTF-8?B?")
                                 (fn-wss-b64 (car cut) nil t) (fn-wrq-oct "?=")
                                 (if (consp rest) '(13 10 32) nil))))
              (mv nil (update-nth 5 word (update-nth 7 rest cursor)) nil))))))
     ((equal phase :body)
      (if (>= i e)
          (mv nil (update-nth 5 (append (if (or pcr (not bol)) '(13 10) nil) '(46 13 10))
                   (update-nth 6 :tail cursor)) nil)
        (let* ((d (fn-wss-decode-at i e fn-web-in)) (o (car d)))
          (if (and pcr (not (equal o 10)))
              ; Flush the pending CR without consuming this decoded octet.
              (mv nil (update-nth 5 '(13 10)
                       (update-nth 3 t (update-nth 4 nil cursor))) nil)
            (let* ((b (if pcr t bol))
                   (bytes (if pcr '(13 10) (fn-wss-step-octets o b))))
              (mv nil (list head (cdr d) e (fn-wss-step-bol o b)
                            (fn-wss-step-pcr o) bytes phase) nil))))))
     (t (mv nil cursor t)))))

(local
 (defthm fn-wps-decode-at-octet
   ; A decoded octet of a span inside the buffer.
   (implies (and (fn-cbor-octet-listp fn-web-in) (natp i) (< i e) (<= e (len fn-web-in)))
            (fn-cbor-octetp (car (fn-wss-decode-at i e fn-web-in))))
   :hints (("Goal" :use (fn-wss-decode-at-octet)))))

(defthm fn-wps-next-cursorp
  ; A step keeps the cursor inside the buffer it reads.
  (implies (and (fn-wps-cursorp cursor n) (equal n (fn-octets-len fn-web-in))
                (fn-cbor-octet-listp fn-web-in))
           (fn-wps-cursorp (mv-nth 1 (fn-wps-next cursor fn-web-in)) n))
  :hints (("Goal" :in-theory (disable nth update-nth fn-wps-cursorp fn-wss-utf8-take
                                      fn-wps-subject-prefix fn-wss-b64 fn-wss-decode-at)
                  :use ((:instance fn-wps-cursorp (cursor cursor))))))

(defun fn-wps-octet-or-nil-p (o)
  (declare (xargs :guard t))
  (or (null o) (fn-cbor-octetp o)))

(defthm fn-wps-next-octet
  ; ... and what it emits is an octet or nothing.
  (implies (and (fn-wps-cursorp cursor n) (equal n (fn-octets-len fn-web-in))
                (fn-cbor-octet-listp fn-web-in))
           (fn-wps-octet-or-nil-p (mv-nth 0 (fn-wps-next cursor fn-web-in))))
  :hints (("Goal" :in-theory (disable nth update-nth fn-wps-cursorp fn-wss-utf8-take
                                      fn-wps-subject-prefix fn-wss-b64 fn-wss-decode-at)
                  :use ((:instance fn-wps-cursorp (cursor cursor))))))

(defun fn-wps-window (fuel cursor acc fn-web-in)
  ; One transition per work unit; zero-output CR/phase transitions also pay.
  ; At most FUEL octets and one <=75-byte RFC2047 fragment, including quantum one.
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp fuel)
                              (fn-wps-cursorp cursor (fn-octets-len fn-web-in))
                              (fn-cbor-octet-listp acc))
                  :guard-hints (("Goal" :do-not-induct t
                                        :in-theory (disable fn-wps-next fn-wps-cursorp)
                                        :use ((:instance fn-wps-next-octet
                                                         (n (fn-octets-len fn-web-in))))))))
  (if (zp fuel) (mv (reverse acc) cursor nil)
    (mv-let (o next done) (fn-wps-next cursor fn-web-in)
      (if done (mv (reverse acc) next t)
        (fn-wps-window (1- fuel) next (if o (cons o acc) acc) fn-web-in)))))

; The step's own facts, stated for the buffer in hand, and what a window of
; them emits.
(defthm fn-wps-next-keeps-cursorp
  (implies (and (fn-cbor-octet-listp fn-web-in)
                (fn-wps-cursorp cursor (fn-octets-len fn-web-in)))
           (fn-wps-cursorp (mv-nth 1 (fn-wps-next cursor fn-web-in)) (fn-octets-len fn-web-in)))
  :hints (("Goal" :use ((:instance fn-wps-next-cursorp (n (fn-octets-len fn-web-in))))
                  :in-theory (disable fn-wps-next fn-wps-cursorp fn-wps-next-cursorp))))

(defthm fn-wps-next-emits-octet
  ; What a step emits, when it emits, is an octet.
  (implies (and (fn-cbor-octet-listp fn-web-in)
                (fn-wps-cursorp cursor (fn-octets-len fn-web-in))
                (car (fn-wps-next cursor fn-web-in)))
           (fn-cbor-octetp (car (fn-wps-next cursor fn-web-in))))
  :hints (("Goal" :use ((:instance fn-wps-next-octet (n (fn-octets-len fn-web-in))))
                  :in-theory (e/d (fn-wps-octet-or-nil-p)
                                  (fn-wps-next fn-wps-cursorp fn-wps-next-octet)))))

(defthm fn-wps-octets-of-revappend
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
           (fn-cbor-octet-listp (revappend a b))))

(defthm fn-wps-window-octets
  ; What a window emits is octets.
  (implies (and (fn-cbor-octet-listp fn-web-in)
                (fn-wps-cursorp cursor (fn-octets-len fn-web-in))
                (fn-cbor-octet-listp acc))
           (fn-cbor-octet-listp (mv-nth 0 (fn-wps-window fuel cursor acc fn-web-in))))
  :hints (("Goal" :induct (fn-wps-window fuel cursor acc fn-web-in)
                  :in-theory (disable fn-wps-next fn-wps-cursorp fn-cbor-octetp))))

(local (defthm fn-wps-len-revappend
  (equal (len (revappend a b)) (+ (len a) (len b)))))

(defthm fn-wps-window-emits-at-most-fuel
  ; One host call (fuel 4096) emits at most FUEL octets; the at most one
  ; pending RFC 2047 fragment rides in the cursor, not the window.
  (<= (len (mv-nth 0 (fn-wps-window fuel cursor acc fn-web-in)))
      (+ (len acc) (nfix fuel)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-wps-next))))

(defun fn-wps-private-reply (config flow event cursor fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (if (and cursor (equal (fn-wss-f-route flow) :post)
           (equal (fn-wss-f-stage flow) :posting)
           (equal (fn-wss-reply-code (fn-wss-reply 0 fn-web-in)) 340))
      (mv (list :post-stream (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx flow)))
                (fn-wss-flow :post :article (fn-wss-f-ctx flow) (fn-wss-f-data flow))) fn-web-out)
    (fn-web-private-reply-step config flow event fn-web-in fn-web-out)))

; One form traversal. Raw names are at most seven octets; values remain spans.
;
; The traversal state P is (ACTION AT END NAME START SPANS PHASE INDEX POS REV
; VALS ACC): the private-begin action, the position and end of the form
; [AT, END) in fn-web-in, the name read so far (reversed) and where its value
; starts, the four (START . END) value spans, the phase, the span being
; decoded and where, the value being reversed, the decoded values and the
; value being collected (ACC; the subject check leaves its verdict there).  It reads fn-web-in only inside [AT, END), and END
; lies in the buffer.
(defun fn-wpf-spansp (spans n)
  (declare (xargs :guard (natp n)))
  (if (consp spans)
      (and (or (null (car spans))
               (and (consp (car spans)) (natp (car (car spans)))
                    (natp (cdr (car spans))) (<= (cdr (car spans)) n)))
           (fn-wpf-spansp (cdr spans) n))
    (null spans)))

(defun fn-wpf-valsp (vals)
  (declare (xargs :guard t))
  (if (consp vals)
      (and (fn-cbor-octet-listp (car vals)) (fn-wpf-valsp (cdr vals)))
    (null vals)))

(defun fn-wpf-statep (p n)
  (declare (xargs :guard (natp n)))
  (and (true-listp p)
       (true-listp (nth 0 p))
       (natp (nth 1 p)) (natp (nth 2 p)) (<= (nth 1 p) (nth 2 p)) (<= (nth 2 p) n)
       (true-listp (nth 3 p))
       (or (null (nth 4 p)) (natp (nth 4 p)))
       (fn-wpf-spansp (nth 5 p) n) (equal (len (nth 5 p)) 4)
       (member (nth 6 p) '(:scan :decode :reverse :subject-check))
       (natp (nth 7 p))
       (implies (equal (nth 6 p) :decode) (or (null (nth 8 p)) (natp (nth 8 p))))
       (implies (equal (nth 6 p) :subject-check) (fn-cbor-octet-listp (nth 8 p)))
       (fn-cbor-octet-listp (nth 9 p))
       (fn-wpf-valsp (nth 10 p))
       ; the value being collected, until the subject's check turns it
       ; into the verdict
       (if (equal (nth 6 p) :subject-check)
           (booleanp (nth 11 p))
         (fn-cbor-octet-listp (nth 11 p)))))

(defthm fn-wpf-valsp-true-listp
  (implies (fn-wpf-valsp vals) (true-listp vals))
  :rule-classes :forward-chaining)

(defthm fn-wpf-spansp-true-listp
  (implies (fn-wpf-spansp spans n) (true-listp spans))
  :rule-classes :forward-chaining)

(defthm fn-wpf-spansp-nth
  ; Every span stored is a pair of naturals, its end inside the buffer.
  (implies (and (fn-wpf-spansp spans n) (nth k spans))
           (and (consp (nth k spans))
                (integerp (car (nth k spans))) (<= 0 (car (nth k spans)))
                (integerp (cdr (nth k spans))) (<= 0 (cdr (nth k spans)))
                (<= (cdr (nth k spans)) n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth k spans)))))

(defthm fn-wpf-spansp-update
  ; A span stored is a span in the buffer.
  (implies (and (fn-wpf-spansp spans n) (natp start) (natp end) (<= end n)
                (natp k) (< k (len spans)))
           (fn-wpf-spansp (update-nth k (cons start end) spans) n))
  :hints (("Goal" :induct (update-nth k (cons start end) spans))))

(defthm fn-wpf-valsp-nth
  (implies (fn-wpf-valsp vals) (fn-cbor-octet-listp (nth k vals))))

(defthm fn-wpf-valsp-append
  (implies (and (fn-wpf-valsp a) (fn-cbor-octet-listp x))
           (fn-wpf-valsp (append a (list x)))))

(defthm fn-wpf-spansp-start
  (fn-wpf-spansp (list nil nil nil nil) n))

(defun fn-wpf-start (action)
  (declare (xargs :guard (true-listp action)))
  (let ((ctx (nth 3 action)))
    (list action (fn-wss-c-bs ctx) (fn-wss-c-be ctx) nil nil
          (list nil nil nil nil) :scan 0 nil nil nil)))
(defthm fn-wpf-start-statep
  ; The form traversal begins inside the buffer: private-begin starts it only
  ; for a body span within the request in fn-web-in.
  (implies (and (true-listp action)
                (<= (fn-wss-c-bs (nth 3 action)) (fn-wss-c-be (nth 3 action)))
                (<= (fn-wss-c-be (nth 3 action)) n))
           (fn-wpf-statep (fn-wpf-start action) n))
  :hints (("Goal" :in-theory (e/d (fn-wpf-statep fn-wpf-start) (nth update-nth)))))
(defun fn-wpf-store (name start end spans)
  (declare (xargs :guard (true-listp spans)))
  (let ((index (cond ((equal name (fn-wrq-oct "csrf")) 0)
                     ((equal name (fn-wrq-oct "g")) 1)
                     ((equal name (fn-wrq-oct "subject")) 2)
                     ((equal name (fn-wrq-oct "body")) 3)
                     (t nil))))
    (if (and index start (not (nth index spans)))
        (update-nth index (cons start end) spans) spans)))
(defthm fn-wpf-statep-of-eleven
  (implies (and (true-listp a) (natp at) (natp end) (<= at end) (<= end n)
                (true-listp name) (or (null start) (natp start))
                (fn-wpf-spansp spans n) (equal (len spans) 4)
                (member phase '(:scan :decode :reverse :subject-check))
                (natp index)
                (implies (equal phase :decode) (or (null pos) (natp pos)))
                (implies (equal phase :subject-check) (fn-cbor-octet-listp pos))
                (fn-cbor-octet-listp rev) (fn-wpf-valsp vals))
           (fn-wpf-statep (list a at end name start spans phase index pos rev vals) n))
  :hints (("Goal" :in-theory (e/d (fn-wpf-statep) (nth update-nth)))))

(defthm fn-wpf-store-spansp
  (implies (and (fn-wpf-spansp spans n) (equal (len spans) 4)
                (or (null start) (natp start)) (natp end) (<= end n))
           (and (fn-wpf-spansp (fn-wpf-store name start end spans) n)
                (equal (len (fn-wpf-store name start end spans)) 4)))
  :hints (("Goal" :in-theory (enable fn-wpf-store))))

(defun fn-wpf-step (p fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (fn-wpf-statep p (fn-octets-len fn-web-in))
                  :guard-hints (("Goal" :do-not-induct t))))
  (let* ((at (nth 1 p)) (end (nth 2 p)) (name (nth 3 p)) (start (nth 4 p))
         (spans (nth 5 p)) (phase (nth 6 p)) (index (nth 7 p))
         (pos (nth 8 p)) (rev (nth 9 p)) (vals (nth 10 p)))
    (cond
     ((equal phase :scan)
      (if (>= at end)
          (let ((spans (fn-wpf-store (reverse name) start at spans)))
            (mv (list (nth 0 p) at end nil nil spans :decode 0 nil nil nil) nil))
        (let ((o (fn-octets-get at fn-web-in)))
          (cond ((equal o 38)
                 (mv (list (nth 0 p) (1+ at) end nil nil
                           (fn-wpf-store (reverse name) start at spans) phase index pos rev vals) nil))
                ((and (not start) (equal o 61))
                 (mv (update-nth 4 (1+ at) (update-nth 1 (1+ at) p)) nil))
                (t (mv (update-nth 3 (if start name
                                        (if (< (len name) 8) (cons o name) name))
                                  (update-nth 1 (1+ at) p)) nil))))))
     ((equal phase :decode)
      (if (>= index 3)
          (mv (update-nth 6 :subject-check
                (update-nth 8 (nth 2 vals) (update-nth 11 t p))) nil)
        (let* ((span (nth index spans)) (i (if pos pos (car span))) (e (cdr span)))
          (if (or (not span) (>= i e))
              (mv (update-nth 6 :reverse (update-nth 11 nil p)) nil)
            (let ((d (fn-wss-decode-at i e fn-web-in)))
              (mv (update-nth 8 (cdr d) (update-nth 9 (cons (car d) rev) p)) nil))))))
     ((equal phase :reverse)
      (if (consp rev)
          (mv (update-nth 9 (cdr rev)
                (update-nth 11 (cons (car rev) (nth 11 p)) p)) nil)
        (mv (update-nth 6 :decode (update-nth 7 (1+ index)
              (update-nth 8 nil (update-nth 10 (append vals (list (nth 11 p))) p)))) nil)))
     ((equal phase :subject-check)
      (if (atom pos) (mv p t)
        (let ((o (if (member (car pos) '(13 10 9 0)) 32 (car pos))))
          (mv (update-nth 8 (cdr pos) (update-nth 11
                (and (nth 11 p) (<= 32 o) (<= o 126)) p)) nil))))
     (t (mv p t)))))
(defthm fn-wpf-step-statep
  ; A step keeps the traversal inside the buffer it reads.
  (implies (and (fn-wpf-statep p n) (equal n (fn-octets-len fn-web-in))
                (fn-cbor-octet-listp fn-web-in))
           (fn-wpf-statep (mv-nth 0 (fn-wpf-step p fn-web-in)) n))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable nth update-nth fn-wss-decode-at fn-wpf-store))))

(defun fn-wpf-drive (fuel p fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp fuel) (fn-wpf-statep p (fn-octets-len fn-web-in)))
                  :guard-hints (("Goal" :in-theory (disable fn-wpf-step fn-wpf-statep mv-nth)))))
  (if (zp fuel) (mv p nil)
    (mv-let (next done) (fn-wpf-step p fn-web-in)
      (if done (mv next t) (fn-wpf-drive (1- fuel) next fn-web-in)))))
(defthm fn-wpf-drive-statep
  (implies (and (fn-wpf-statep p n) (equal n (fn-octets-len fn-web-in))
                (fn-cbor-octet-listp fn-web-in))
           (fn-wpf-statep (mv-nth 0 (fn-wpf-drive fuel p fn-web-in)) n))
  :hints (("Goal" :in-theory (disable fn-wpf-step fn-wpf-statep mv-nth))))

(defun fn-wpf-finish (config p fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out)
                  :guard (fn-wpf-statep p (fn-octets-len fn-web-in))))
  (let* ((action (nth 0 p)) (session (nth 2 action)) (ctx (nth 3 action))
         (vals (nth 10 p)) (csrf (nth 0 vals)) (group (nth 1 vals))
         (subject (nth 2 vals)) (span (nth 3 (nth 5 p))))
    (if (and (equal csrf (fn-wss-s-csrf session)) (fn-wss-groupp group)
             (consp subject) (consp span) (< (car span) (cdr span)))
        (let* ((cursor (fn-wps-header-cursor (fn-wss-s-login session)
                                             (fn-wss-cfg-domain config) group subject
                                             (nth 11 p) (car span) (cdr span)))
               (fn-web-out (fn-octets-clear fn-web-out))
               (fn-web-out (fn-octets-append-list '(80 79 83 84 13 10) fn-web-out)))
          (mv (list :post-command (fn-wss-s-cid session)
                    cursor
                    (fn-wss-flow :post :posting ctx (list group nil))) fn-web-out))
      ; Preserve the exact existing refusal/page behavior, currently full.
      (fn-web-private-begin-step config action fn-web-in fn-web-out))))
(defun fn-wpf-private-begin (config action fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard (true-listp action)))
  (let* ((row (nth 1 action)) (session (nth 2 action)) (ctx (nth 3 action)))
    (if (and (fn-web-private-begin-p action) (equal (fn-web-row-name row) :post)
             session (fn-wss-same-site (fn-wss-c-request ctx))
             (<= (fn-wss-c-bs ctx) (fn-wss-c-be ctx))
             (<= (fn-wss-c-be ctx) (fn-octets-len fn-web-in)))
        (mv (list :post-form (fn-wpf-start action)) fn-web-out)
      (fn-web-private-begin-step config action fn-web-in fn-web-out))))

; ---------------------------------------------------------------------------
; Accepted and refused stay distinct.

(defthm fn-wpf-finish-refusal-is-the-existing-gate
  ; A form whose CSRF token is not its session's, or whose group, subject or
  ; body is unusable, is answered exactly as the full gate answers it.
  (implies (not (and (equal (nth 0 (nth 10 p)) (fn-wss-s-csrf (nth 2 (nth 0 p))))
                     (fn-wss-groupp (nth 1 (nth 10 p)))
                     (consp (nth 2 (nth 10 p)))
                     (consp (nth 3 (nth 5 p)))
                     (< (car (nth 3 (nth 5 p))) (cdr (nth 3 (nth 5 p))))))
           (equal (fn-wpf-finish config p fn-web-in fn-web-out)
                  (fn-web-private-begin-step config (nth 0 p) fn-web-in fn-web-out)))
  :hints (("Goal" :in-theory (union-theories '(fn-wpf-finish) (theory 'minimal-theory)))))


(defthm fn-wpf-finish-accepts-to-its-session
  ; Accepted: the POST command goes to the session's own connection, with
  ; the posting flow, and the outgoing buffer holds exactly "POST" CR LF.
  (implies (and (equal (nth 0 (nth 10 p)) (fn-wss-s-csrf (nth 2 (nth 0 p))))
                (fn-wss-groupp (nth 1 (nth 10 p)))
                (consp (nth 2 (nth 10 p)))
                (consp (nth 3 (nth 5 p)))
                (< (car (nth 3 (nth 5 p))) (cdr (nth 3 (nth 5 p)))))
           (let ((action (mv-nth 0 (fn-wpf-finish config p fn-web-in fn-web-out))))
             (and (equal (car action) :post-command)
                  (equal (cadr action) (fn-wss-s-cid (nth 2 (nth 0 p))))
                  (equal (fn-octets-list (mv-nth 1 (fn-wpf-finish config p fn-web-in fn-web-out)))
                         '(80 79 83 84 13 10)))))
  :hints (("Goal" :in-theory (e/d (fn-wpf-finish)
                                  (fn-web-private-begin-step fn-wps-header-cursor fn-wss-groupp
                                   fn-wss-s-csrf fn-wss-s-cid fn-wss-flow)))))


(defthm fn-wpf-private-begin-refusal-is-the-existing-gate
  ; Not a captured POST gate, no session, cross-site, or a body span outside
  ; the request: the full gate's answer, unchanged.
  (implies (not (and (fn-web-private-begin-p action)
                     (equal (fn-web-row-name (nth 1 action)) :post)
                     (nth 2 action)
                     (fn-wss-same-site (fn-wss-c-request (nth 3 action)))
                     (<= (fn-wss-c-bs (nth 3 action)) (fn-wss-c-be (nth 3 action)))
                     (<= (fn-wss-c-be (nth 3 action)) (fn-octets-len fn-web-in))))
           (equal (fn-wpf-private-begin config action fn-web-in fn-web-out)
                  (fn-web-private-begin-step config action fn-web-in fn-web-out)))
  :hints (("Goal" :in-theory (union-theories '(fn-wpf-private-begin) (theory 'minimal-theory)))))


(defthm fn-wps-private-reply-streams-only-after-340
  ; The body is streamed only after the server's 340 to this flow's POST;
  ; any other reply is the existing private reply step's.
  (implies (not (and cursor (equal (fn-wss-f-route flow) :post)
                     (equal (fn-wss-f-stage flow) :posting)
                     (equal (fn-wss-reply-code (fn-wss-reply 0 fn-web-in)) 340)))
           (equal (fn-wps-private-reply config flow event cursor fn-web-in fn-web-out)
                  (fn-web-private-reply-step config flow event fn-web-in fn-web-out)))
  :hints (("Goal" :in-theory (union-theories '(fn-wps-private-reply) (theory 'minimal-theory)))))
