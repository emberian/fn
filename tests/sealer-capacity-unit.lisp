; C5 evidence (docs/c-ordered-runs.md section 5, "Capacity"): the node keeps
; accepting POSTs. One connection posts 32 articles at the reading unit
; profile (*fn2-cursor-profile*: 64 slots of 64 KiB, its store sized below), every reply 240, then
; GROUP, OVER over all of them and ARTICLE of each read every one back. One
; batch seals into 10 runs (one per schema it writes; 11 pages with the
; identity summary's filter), so without the sealer's merge the 64 KiB class
; is exhausted by the sixth POST and the core stops :sealer-full; with it
; every schema stays at a few runs and the pages of the runs it replaces
; return to the pool. The expected wire is written here from the
; catalogue's texts, as tests/cursor-unit.lisp's POST round trip is.
; Run: sh tools/certify.sh tests/sealer-capacity-unit.lisp
(in-package "ACL2")
(include-book "../books/owed-cursor")

(defconst *fn2-scu-n* 72)
;; The reading unit profile with a device that stores 72 articles (720 overlay
;; seals across 10 schemas on 64 :identity-runs rows and 64 slots of 64 KiB):
;; B's extents (:extent-slots, 16 by default) hold each article's source and
;; each batch's commit record, so 256 holds two per POST with headroom.
(defconst *fn2-scu-profile* (put-assoc-equal :extent-slots 256 *fn2-cursor-profile*))
(defun fn2-scu-digits (n acc)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (or (zp n) (< n 10)) (cons (code-char (+ 48 (nfix n))) acc)
    (fn2-scu-digits (floor n 10) (cons (code-char (+ 48 (mod n 10))) acc))))
(defun fn2-scu-dec (n) (declare (xargs :verify-guards nil)) (coerce (fn2-scu-digits (nfix n) nil) 'string))
(defun fn2-scu-chars (octets)
  (declare (xargs :verify-guards nil))
  (if (atom octets) nil (cons (code-char (nfix (car octets))) (fn2-scu-chars (cdr octets)))))
(defun fn2-scu-tab () (declare (xargs :verify-guards nil)) (coerce (list (code-char 9)) 'string))
(defun fn2-scu-mid (i) (declare (xargs :verify-guards nil)) (fn2-csp-cat (list "<c" (fn2-scu-dec i) "@example.invalid>")))
(defun fn2-scu-subject (i) (declare (xargs :verify-guards nil)) (fn2-csp-cat (list "capacity " (fn2-scu-dec i))))
;; Article I as posted (unstuffed): its header, an empty line, two body lines.
(defun fn2-scu-header (i)
  (declare (xargs :verify-guards nil))
  (list "From: c@example.invalid" (fn2-csp-cat (list "Subject: " (fn2-scu-subject i))) "Newsgroups: local.test"
        (fn2-csp-cat (list "Message-ID: " (fn2-scu-mid i)))))
(defun fn2-scu-body (i) (declare (xargs :verify-guards nil)) (list (fn2-csp-cat (list "body " (fn2-scu-dec i))) "end"))
(defun fn2-scu-article (i) (declare (xargs :verify-guards nil)) (append (fn2-scu-header i) (list "") (fn2-scu-body i)))
;; :bytes is the article's octets, every line ending CR LF (RFC 3977 8.4.2).
(defun fn2-scu-octets (lines)
  (declare (xargs :verify-guards nil))
  (if (atom lines) 0 (+ (length (car lines)) 2 (fn2-scu-octets (cdr lines)))))
(defun fn2-scu-posts (i n)
  (declare (xargs :verify-guards nil :measure (nfix (- (+ 1 (nfix n)) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (> i n)) nil
    (append (list "POST") (fn2-scu-article i) (list ".") (fn2-scu-posts (+ 1 i) n))))
(defun fn2-scu-articles-cmds (i n)
  (declare (xargs :verify-guards nil :measure (nfix (- (+ 1 (nfix n)) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (> i n)) nil
    (cons (fn2-csp-cat (list "ARTICLE " (fn2-scu-dec i))) (fn2-scu-articles-cmds (+ 1 i) n))))
(defun fn2-scu-lines (n)
  (declare (xargs :verify-guards nil))
  (append (fn2-scu-posts 1 n)
          (list "GROUP local.test" (fn2-csp-cat (list "OVER 1-" (fn2-scu-dec n))))
          (fn2-scu-articles-cmds 1 n) (list "QUIT")))

;; The expected replies.
(defun fn2-scu-accepts (i n)
  (declare (xargs :verify-guards nil :measure (nfix (- (+ 1 (nfix n)) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (> i n)) nil
    (list* "340 send article to be posted" "240 article received OK" (fn2-scu-accepts (+ 1 i) n))))
;; The Xref field the transaction files (the profile's path identity, the
;; article's number): the overview line's last field and the article's
;; first header line.
(defun fn2-scu-xref (i)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list "Xref: fn2.invalid local.test:" (fn2-scu-dec i))))
(defun fn2-scu-ov (i)
  (declare (xargs :verify-guards nil))
  (let ((tab (fn2-scu-tab)))
    (fn2-csp-cat (list (fn2-scu-dec i) tab (fn2-scu-subject i) tab "c@example.invalid" tab tab (fn2-scu-mid i)
                       tab tab (fn2-scu-dec (fn2-scu-octets (fn2-scu-article i))) tab
                       (fn2-scu-dec (len (fn2-scu-body i))) tab (fn2-scu-xref i)))))
(defun fn2-scu-ovs (i n)
  (declare (xargs :verify-guards nil :measure (nfix (- (+ 1 (nfix n)) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (> i n)) nil (cons (fn2-scu-ov i) (fn2-scu-ovs (+ 1 i) n))))
(defun fn2-scu-article-replies (i n)
  (declare (xargs :verify-guards nil :measure (nfix (- (+ 1 (nfix n)) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (> i n)) nil
    (append (list (fn2-csp-cat (list "220 " (fn2-scu-dec i) " " (fn2-scu-mid i) " article follows")))
            (list (fn2-scu-xref i)) (fn2-scu-article i) (list ".") (fn2-scu-article-replies (+ 1 i) n))))
(defun fn2-scu-expected (n)
  (declare (xargs :verify-guards nil))
  (fn2-cw-crlf-octets
   (append (list "200 fn-nntp experimental server ready") (fn2-scu-accepts 1 n)
           (list (fn2-csp-cat (list "211 " (fn2-scu-dec n) " 1 " (fn2-scu-dec n) " local.test"))
                 "224 overview information follows")
           (fn2-scu-ovs 1 n) (list ".") (fn2-scu-article-replies 1 n) (list "205 closing connection"))))

;; The served run, with fuel for N posts (each a batch: its seals, merges and
;; releases are the sealer's turns between the connection's).
(defun fn2-scu-live-runs (k r fn2-run-installed)
  (declare (xargs :stobjs fn2-run-installed :verify-guards nil :measure (nfix k)))
  (if (or (zp k) (>= (nfix r) (fn2-run-installed-rows fn2-run-installed))) 0
    (+ (if (equal (fn2-run-installed-state (nfix r) fn2-run-installed) *fn2-run-installed-state-live*) 1 0)
       (fn2-scu-live-runs (- k 1) (+ 1 (nfix r)) fn2-run-installed))))

(defun fn2-scu-run-profile (profile n)
  (declare (xargs :verify-guards nil))
  (let ((transcripts (list (list (fn2-cw-crlf-octets (fn2-scu-lines n)) nil))))
    (with-local-stobj fn2-core
      (mv-let (result fn2-core)
        (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
             ((mv & fn2-core)
              (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
                (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
             ((mv status clients & & fn2-core)
              (fn2-cs-loop (* 20000 (+ 1 n)) 0 0 (fn2-cw-clients transcripts) nil nil nil 0 :ok fn2-core))
             (live-runs (stobj-let ((fn2-run-installed (fn2-core-run-installed fn2-core))) (cnt)
                          (fn2-scu-live-runs (fn2-run-installed-rows fn2-run-installed) 0 fn2-run-installed) cnt))
             (free-pages (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (fp)
                           (fn2-seal-free-pages fn2-pool) fp)))
          (mv (list status (car (fn2-cw-results clients)) (fn2-core-stop-reason fn2-core) live-runs free-pages) fn2-core))
        result))))

(defun fn2-scu-run (n)
  (declare (xargs :verify-guards nil))
  (fn2-scu-run-profile *fn2-scu-profile* n))

(defun fn2-scu-check (n)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-scu-run n)) (want (list (fn2-scu-expected n) t)))
    (or (and (equal (car r) :quiet) (equal (nth 2 r) 0) (equal (nth 1 r) want)
             (<= (nth 3 r) 42) (<= 20 (nth 4 r)))
        (cw "capacity ~x0 stop ~x1 live-runs ~x2 free-pages ~x3~%got ~s4~%"
            (car r) (nth 2 r) (nth 3 r) (nth 4 r)
            (coerce (fn2-scu-chars (car (nth 1 r))) 'string)))))

;; Negative tooth: 8 installed-run rows cannot hold 10 distinct schemas' live
;; runs even at 1 run per schema, proving :sealer-full fires when row demand
;; exceeds the table and that 72 POSTs (720 overlay seals) only succeed on 64
;; rows because C5 merges and reclaims superseded runs and 64 KiB page slots.
(defun fn2-scu-negative-tooth ()
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-scu-run-profile (put-assoc-equal :identity-runs 8 *fn2-scu-profile*) 2)))
    (equal (nth 2 r) *fn2-stop-reason-sealer-full*)))

(assert-event (and (fn2-scu-check *fn2-scu-n*) (fn2-scu-negative-tooth)))
