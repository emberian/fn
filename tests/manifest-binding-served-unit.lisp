; Actual POST -> published article -> disk-read -> BODY substitution control.
; Two real articles, each requiring a manifest, are committed. Replace the
; first manifest's entries with the second's entries, preserving the first
; header's source identity/length/block size. The replacement references
; valid live blocks with matching block hashes/CVs. The first read must
; refuse before 222; the independently committed second article still reads.
; This finite control does not prove cryptographic collision resistance.
(in-package "ACL2")
(include-book "../books/owed-txn")
(defconst *fn2-mbs-profile*
 (put-assoc-equal :pool-classes '((8 . 1024) (128 . 16384) (64 . 65536))
  (put-assoc-equal :reading t (put-assoc-equal :x 2 *fn2-txn-posting-profile*))))
(defconst *fn2-mbs-a-line* "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
(defconst *fn2-mbs-b-line* "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
(defconst *fn2-mbs-a*
 (append '("From: a@example.invalid" "Subject: manifest" "Newsgroups: local.test"
           "Message-ID: <a@example.invalid>" "") (make-list 220 :initial-element *fn2-mbs-a-line*)))
(defconst *fn2-mbs-b*
 (append '("From: a@example.invalid" "Subject: manifest" "Newsgroups: local.test"
           "Message-ID: <b@example.invalid>" "") (make-list 220 :initial-element *fn2-mbs-b-line*)))
;; Independent LEB128 header oracle, used only to locate fixture writes.
(defun fn2-mbs-varint (n)
 (declare (xargs :verify-guards nil :measure (nfix n)))
 (if (< (nfix n) 128) (list (nfix n))
  (cons (+ 128 (mod (nfix n) 128)) (fn2-mbs-varint (floor (nfix n) 128)))))
(defun fn2-mbs-header (lines)
 (declare (xargs :verify-guards nil))
 (let ((bytes (fn2-cw-crlf-octets lines)))
  (append (fn2-mbs-varint (len bytes)) '(128 32) (fn-blake3 bytes))))
(defun fn2-mbs-find (header store)
 (declare (xargs :verify-guards nil))
 (cond ((atom store) nil)
       ((and (equal (len (cdar store)) 4096)
             (equal (take (len header) (cdar store)) header)) (car store))
       (t (fn2-mbs-find header (cdr store)))))
(defun fn2-mbs-pending-accept (left i fn2-ops)
 (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix left)))
 (cond ((or (zp left) (>= (nfix i) (fn2-ops-rows fn2-ops))) nil)
       ((and (equal (fn2-ops-kind (nfix i) fn2-ops) *fn2-action-accept*)
             (equal (fn2-ops-phase (nfix i) fn2-ops) *fn2-op-phase-submitted*))
        (list (nfix i) (fn2-ops-gen (nfix i) fn2-ops)))
       (t (fn2-mbs-pending-accept (- left 1) (+ 1 (nfix i)) fn2-ops))))
(defun fn2-mbs-check (substitute fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor *fn2-mbs-profile* :echo nil fn2-core))
      ((mv ec fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
        (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
      (post (fn2-cw-crlf-octets (append '("POST") *fn2-mbs-a* '("." "POST") *fn2-mbs-b* '("." "QUIT"))))
      ((mv status clients store fn2-core)
       (fn2-cw-loop 20000 0 0 (fn2-cw-clients (list (list post (list (len post))))) nil fn2-core))
      (posted (fn2-cw-crlf-octets '("200 fn-nntp experimental server ready"
                  "340 send article to be posted" "240 article received OK"
                  "340 send article to be posted" "240 article received OK" "205 closing connection")))
      (head (fn2-mbs-header *fn2-mbs-a*))
      (a (fn2-mbs-find head store))
      (b (fn2-mbs-find (fn2-mbs-header *fn2-mbs-b*) store))
      ((unless (and (eq ec :ok) (eq status :quiet)
                    (equal (fn2-cw-results clients) (list (list posted t)))
                    a b (not (equal (car a) (car b)))
                    (not (equal (cdr a) (cdr b)))
                    (< 12288 (len (fn2-cw-crlf-octets *fn2-mbs-a*)))))
       (mv (list :setup ec status (fn2-cw-results clients) (and a t) (and b t)) fn2-core))
      ;; Preserve target header, replace entries and padding with the other
      ;; genuinely committed manifest's. Neither article row is changed.
      (replacement (append head (nthcdr (len head) (cdr b))))
      (store (if substitute (cons (cons (car a) replacement) store) store))
      (read (fn2-cw-crlf-octets '("BODY <a@example.invalid>" "BODY <b@example.invalid>" "QUIT")))
      (clients (fn2-cw-clients (list (list read (list (len read))))))
      (acc (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (acc)
             (fn2-mbs-pending-accept (fn2-ops-rows fn2-ops) 0 fn2-ops) acc))
      ((unless acc) (mv '(:no-accept) fn2-core))
      (fn2-core (fn2-cw-post-accept (car acc) (cadr acc) 0 77 nil fn2-core))
      ((mv status clients & fn2-core) (fn2-cw-loop 20000 0 1 clients store fn2-core))
      (expected (fn2-cw-crlf-octets
                 (append '("200 fn-nntp experimental server ready")
                  (if substitute '("503 archive projection unavailable")
                    (append '("222 0 <a@example.invalid> body follows")
                     (make-list 220 :initial-element *fn2-mbs-a-line*) '(".")))
                  '("222 0 <b@example.invalid> body follows")
                  (make-list 220 :initial-element *fn2-mbs-b-line*) '("." "205 closing connection")))))
  (mv (if (and (eq status :quiet) (equal (fn2-core-stop-reason fn2-core) 0)
               (equal (fn2-cw-results clients) (list (list expected t)))) t
        (list :read status (fn2-core-stop-reason fn2-core) (fn2-cw-results clients))) fn2-core)))
(defun fn2-mbs-run (substitute)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-mbs-check substitute fn2-core) r)))
(assert-event (equal (fn2-mbs-run nil) t))
(assert-event (equal (fn2-mbs-run t) t))
