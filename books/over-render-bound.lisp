; over-render-bound.lisp -- the NOV line bound OVER's quantum reads (Builder O, row O1,
; landing 1, KO8).  A served NOV line is within its article's own header plus fixed terms
; (KO8a, M's fn-ovw-nov-line-within-the-bound with the Xref term C's max(31, 12(HDR + 1)) of
; fn-o1-xref-within-the-header); every probe of a window is within that bound plus CRLF when
; every catalog row is a tombstone or filed within its header (KO8).
;
;   KO8a fn-ovw-nov-line-within-the-header-bound
;   KO8  fn-ovr-probes-within-the-header-bound
;
; KO8's row hypothesis is the defun-sk fn-ovr-rows-within-header: C's K1c
; (fn-o1-served-catalog-rows-are-reclaimed-or-within-header, packet 5) discharges its
; tombstone-or-filed half for the owner's catalog; the parse and length halves are the stored
; article's (HDR the sealed header limits, A the retained payload bound, carried separately:
; A is live-changeable).  With KO7 and CAP >= 2 + this bound + the framing, no quantum stalls.

(in-package "ACL2")
(include-book "over-render-quantum")
(include-book "filed-groups")

(defun fn-ovr-nov-line-header-bound (hdr a server)
  (declare (xargs :guard t))
  (+ (nfix hdr)
     *fn-nntp-max-decimal-octets* 7
     (* 2 (len (fn-nntp-decimal (nfix a))))
     1 (len *fn-xref-name*) (len (true-list-fix server))
     (max 31 (* 12 (+ 1 (nfix hdr))))))

(local
 (defthm fn-ovrb-len-append-pieces
   (equal (len (fn-nntp-append-pieces pieces))
          (if (consp pieces)
              (+ (len (car pieces)) (len (fn-nntp-append-pieces (cdr pieces))))
            0))
   :hints (("Goal" :in-theory (enable fn-nntp-append-pieces)))))

(local
 (defthm fn-ovrb-nov-line-len
   (equal (len (fn-nov-line number over))
          (+ (len (fn-nntp-decimal-field number))
             (len (fn-nov-subject over)) (len (fn-nov-from over)) (len (fn-nov-date over))
             (len (fn-nov-msgid over)) (len (fn-nov-references over))
             (len (fn-nntp-decimal (fn-nov-bytes over)))
             (len (fn-nntp-decimal (fn-nov-lines over)))
             7))
   :hints (("Goal" :in-theory (enable fn-nov-line)))))

(local
 (defthm fn-ovrb-decimal-field-len
   (<= (len (fn-nntp-decimal-field number)) *fn-nntp-max-decimal-octets*)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-nntp-decimal-field)))))

(local
 (defthm fn-ovrb-xref-term
   (implies (and (natp lim) (natp hdr) (<= lim hdr) (<= x (max 31 (* 12 (+ 1 lim)))))
            (<= x (max 31 (* 12 (+ 1 hdr)))))
   :rule-classes nil))

; KO8a: a served NOV line of an article filed within its own header is within the bound.
(defthm fn-ovw-nov-line-within-the-header-bound
  (let ((payload (fn-nntp-article-bytes article fn-arena)))
    (implies (and (fn-article-result-okp (fn-article-parse-under payload limits))
                  (<= (nfix (fn-article-limit-octets limits)) (nfix hdr))
                  (<= (len payload) (nfix a))
                  (fn-o1-article-within-headerp article payload))
             (<= (len (fn-nov-served-line number (fn-nov-overview article fn-arena) server article))
                 (fn-ovr-nov-line-header-bound hdr a server))))
  :hints (("Goal"
           :use ((:instance fn-ovw-overview-text-within-header)
                 (:instance fn-ovw-overview-counts)
                 (:instance fn-o1-xref-within-the-header)
                 (:instance fn-ovrb-xref-term
                            (lim (nfix (fn-article-limit-octets limits))) (hdr (nfix hdr))
                            (x (len (fn-xref-locations (fn-xref-pairs article))))))
           :in-theory (e/d (fn-nov-served-line fn-xref-field fn-ovr-nov-line-header-bound)
                           (fn-nov-line fn-nov-overview fn-nntp-article-bytes fn-nov-subject fn-nov-from fn-nov-date
                            fn-nov-msgid fn-nov-references fn-nov-bytes fn-nov-lines fn-article-parse-under
                            fn-xref-locations fn-xref-pairs fn-article-limit-octets fn-o1-article-within-headerp
                            fn-nntp-decimal fn-nntp-decimal-field)))))

; Every catalog row below the count is a tombstone, or filed within its own header with its
; payload parsing under LIMITS and at most A octets long.
(defun-sk fn-ovr-rows-within-header (a limits fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)))
  (forall i
    (implies (and (natp i) (< i (fn-cat-count fn-cat)))
             (let* ((article (fn-cat-row-article i fn-arena fn-cat))
                    (payload (fn-nntp-article-bytes article fn-arena)))
               (or (fn-nntp-article-tombstonep article fn-arena)
                   (and (fn-o1-article-within-headerp article payload)
                        (fn-article-result-okp (fn-article-parse-under payload limits))
                        (<= (len payload) (nfix a))))))))

; ---------------------------------------------------------------------------
; KO8's proof.  Helpers local, prefix fn-ovrb-.

; The available article of a number is the catalog row its view sequence names.
(local
 (defthm fn-ovrb-available-is-row
   (implies (consp (fn-scat-available-article group n v fn-arena fn-cat))
            (and (natp (fn-cnx-view-seq group n v fn-cat))
                 (< (fn-cnx-view-seq group n v fn-cat) (fn-cat-count fn-cat))
                 (equal (fn-scat-available-article group n v fn-arena fn-cat)
                        (fn-cat-row-article (fn-cnx-view-seq group n v fn-cat) fn-arena fn-cat))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-scat-available-article fn-scat-number-article fn-cnx-view-seq)
                                   (fn-cat-row-article))))))

; A rendered row's served line is within the bound.
(local
 (defthm fn-ovrb-row-line
   (let ((article (fn-scat-available-article group n v fn-arena fn-cat)))
     (implies (and (fn-ovr-rows-within-header a limits fn-arena fn-cat)
                   (<= (nfix (fn-article-limit-octets limits)) (nfix hdr))
                   (consp article)
                   (not (fn-nntp-article-tombstonep article fn-arena)))
              (<= (len (fn-nov-served-line n (fn-nov-overview article fn-arena) server article))
                  (fn-ovr-nov-line-header-bound hdr a server))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-ovrb-available-is-row
                  (:instance fn-ovr-rows-within-header-necc (i (fn-cnx-view-seq group n v fn-cat)))
                  (:instance fn-ovw-nov-line-within-the-header-bound
                             (article (fn-scat-available-article group n v fn-arena fn-cat))
                             (number n)))
            :in-theory (disable fn-ovr-rows-within-header-necc fn-ovw-nov-line-within-the-header-bound
                                fn-scat-available-article fn-cat-row-article fn-nov-served-line
                                fn-nov-overview fn-nntp-article-bytes fn-nntp-article-tombstonep
                                fn-o1-article-within-headerp fn-article-parse-under fn-ovr-nov-line-header-bound
                                fn-ovr-rows-within-header fn-article-limit-octets)))))

; No NOV line begins with a dot: its first field is a decimal.
(local
 (defthm fn-ovrb-decimal-field-head
   (and (consp (fn-nntp-decimal-field n))
        (not (equal (car (fn-nntp-decimal-field n)) 46)))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal-field fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)))))

(local
 (defthm fn-ovrb-car-append-consp
   (implies (consp a) (equal (car (append a b)) (car a)))))

(local
 (defthm fn-ovrb-nov-line-head
   (not (equal (car (fn-nov-line n over)) 46))
   :hints (("Goal" :in-theory (e/d (fn-nov-line fn-nntp-append-pieces) (fn-nntp-decimal-field))))))

(local
 (defthm fn-ovrb-served-line-head
   (not (equal (car (fn-nov-served-line n over server article)) 46))
   :hints (("Goal" :in-theory (e/d (fn-nov-served-line) (fn-nov-line))
            :cases ((consp (fn-nov-line n over)))))))

(local
 (defthm fn-ovrb-len-stuff-not-dot
   (implies (not (equal (car line) 46))
            (equal (len (fn-nntp-crlf (fn-wire-stuff-line line))) (+ 2 (len line))))
   :hints (("Goal" :in-theory (enable fn-nntp-crlf fn-wire-stuff-line)))))

(local
 (defthm fn-ovrb-len-append
   (equal (len (append x y)) (+ (len x) (len y)))))

; Over a list of numbers, the stuffed served lines are at most (B + 2) a number.
(local
 (defthm fn-ovrb-served-lines-within
   (implies (and (fn-scol-okp fn-arena fn-cat)
                 (fn-ovr-rows-within-header a limits fn-arena fn-cat)
                 (<= (nfix (fn-article-limit-octets limits)) (nfix hdr)))
            (<= (len (fn-nntp-stuff-lines
                      (fn-nov-served-lines-for-numbers-cat group numbers server v fn-arena fn-cat)))
                (* (len numbers) (+ 2 (fn-ovr-nov-line-header-bound hdr a server)))))
   :hints (("Goal" :induct (len numbers)
            :in-theory (e/d (fn-nntp-stuff-lines)
                            (fn-scat-available-article fn-nov-served-line fn-nov-overview fn-scol-overview-of
                             fn-scol-tombstonep fn-nntp-article-tombstonep fn-ovr-nov-line-header-bound
                             fn-ovr-rows-within-header fn-nntp-crlf fn-wire-stuff-line fn-scol-okp)))
           ("Subgoal *1/1" :expand ((fn-nov-served-lines-for-numbers-cat group numbers server v fn-arena fn-cat))
            :use ((:instance fn-ovrb-row-line (n (car numbers))))))))

(local
 (defthm fn-ovrb-lines-within
   (implies (and (fn-ovr-rows-within-header a limits fn-arena fn-cat)
                 (<= (nfix (fn-article-limit-octets limits)) (nfix hdr)))
            (<= (len (fn-nntp-stuff-lines
                      (fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat)))
                (* (len numbers) (+ 2 (fn-ovr-nov-line-header-bound hdr a nil)))))
   :hints (("Goal" :induct (len numbers)
            :in-theory (e/d (fn-nntp-stuff-lines)
                            (fn-scat-available-article fn-nov-line fn-nov-overview
                             fn-nntp-article-tombstonep fn-ovr-nov-line-header-bound
                             fn-ovr-rows-within-header fn-nntp-crlf fn-wire-stuff-line)))
           ("Subgoal *1/1" :expand ((fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat))
            :use ((:instance fn-ovrb-row-line (n (car numbers)) (server nil)))
            :in-theory (e/d (fn-nntp-stuff-lines fn-nov-served-line)
                            (fn-scat-available-article fn-nov-line fn-nov-overview
                             fn-nntp-article-tombstonep fn-ovr-nov-line-header-bound
                             fn-ovr-rows-within-header fn-nntp-crlf fn-wire-stuff-line))))))

(local
 (defthm fn-ovrb-range-keep-len
   (<= (len (fn-scat-range-keep group seqs fn-cat)) (len seqs))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-scat-range-keep)))))

(local
 (defthm fn-ovrb-range-aux-one
   (<= (len (fn-cnx-range-aux group j j v fn-cat)) 1)
   :rule-classes :linear
   :hints (("Goal" :expand ((fn-cnx-range-aux group j j v fn-cat)
                            (fn-cnx-range-aux group (+ 1 j) j v fn-cat))))))

(local
 (defthm fn-ovrb-at-most-one
   (implies (and (natp m) (<= m 1) (natp b) (<= l (* m (+ 2 b))))
            (<= l (+ 2 b)))
   :rule-classes nil
   :hints (("Goal" :cases ((equal m 0))))))

(local
 (defthm fn-ovrb-probe-within
   (implies (and (fn-scol-okp fn-arena fn-cat)
                 (fn-ovr-rows-within-header a limits fn-arena fn-cat)
                 (<= (nfix (fn-article-limit-octets limits)) (nfix hdr))
                 (natp v))
            (<= (fn-ovr-probe-len group j server v fn-arena fn-cat)
                (+ 2 (fn-ovr-nov-line-header-bound hdr a server))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ovrb-served-lines-within
                             (numbers (fn-scat-range-keep group (fn-cnx-range-aux group j j v fn-cat) fn-cat)))
                  (:instance fn-ovrb-lines-within
                             (numbers (fn-scat-range-keep group (fn-cnx-range-aux group j j v fn-cat) fn-cat)))
                  (:instance fn-ovrb-at-most-one
                             (m (len (fn-scat-range-keep group (fn-cnx-range-aux group j j v fn-cat) fn-cat)))
                             (b (fn-ovr-nov-line-header-bound hdr a server))
                             (l (fn-ovr-probe-len group j server v fn-arena fn-cat))))
            :in-theory (e/d (fn-ovr-probe-octets fn-ovw-lines)
                            (fn-ovrb-served-lines-within fn-ovrb-lines-within fn-scat-range-keep fn-cnx-range-aux
                             fn-nov-served-lines-for-numbers-cat fn-nov-lines-for-numbers-cat
                             fn-nntp-stuff-lines fn-ovr-nov-line-header-bound fn-ovr-rows-within-header
                             fn-scol-okp fn-article-limit-octets))))))


; KO8: every probe of GROUP's numbers K..TOP is within the bound plus CRLF.
(defthm fn-ovr-probes-within-the-header-bound
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-ovr-rows-within-header a limits fn-arena fn-cat)
                (<= (nfix (fn-article-limit-octets limits)) (nfix hdr))
                (natp v))
           (fn-ovr-probes-within group k top server v
                                 (+ 2 (fn-ovr-nov-line-header-bound hdr a server))
                                 fn-arena fn-cat))
  :hints (("Goal" :induct (fn-ovr-probes-within group k top server v
                                                (+ 2 (fn-ovr-nov-line-header-bound hdr a server))
                                                fn-arena fn-cat)
           :in-theory (disable fn-ovr-probe-len fn-ovr-nov-line-header-bound fn-ovr-rows-within-header
                               fn-scol-okp fn-ovr-probe-len-is-the-length fn-article-limit-octets))
          ("Subgoal *1/2" :use ((:instance fn-ovrb-probe-within (j k))))))

; The snapshot domain does not affect the per-row length bound.
(local
 (defthm fn-ovrb-any-stuff-one
   (implies (not (equal (car line) 46))
            (equal (fn-nntp-stuff-lines (list line)) (fn-nntp-crlf line)))
   :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines fn-wire-stuff-line)))))

(local
 (defthm fn-ovrb-any-scol-overview-of-facts
   (implies (fn-scol-facts article fn-cat)
            (equal (fn-scol-overview-of article fn-arena fn-cat)
                   (let ((facts (fn-scol-facts article fn-cat)))
                     (if (fn-hnov-ok (fn-hf-nov facts))
                         (fn-ovr-column-over (fn-hf-nov facts) (fn-nntp-article-length article fn-arena)
                                             (fn-hf-body-lines facts))
                       (list :error)))))
   :hints (("Goal" :in-theory (enable fn-scol-overview-of fn-scol-nov-overview fn-ovr-column-over)))))

(local
 (defthm fn-ovrb-any-scol-overview-of-no-facts
   (implies (not (fn-scol-facts article fn-cat))
            (equal (fn-scol-overview-of article fn-arena fn-cat)
                   (fn-nov-overview article fn-arena)))
   :hints (("Goal" :in-theory (enable fn-scol-overview-of)))))

(local
 (defthm fn-ovrb-any-column-over-okp
   (fn-nov-okp (fn-ovr-column-over nov octets body))
   :hints (("Goal" :in-theory (enable fn-nov-okp fn-ovr-column-over)))))

(local (defthm fn-ovrb-any-served-lines-nil
  (equal (fn-nov-served-lines-for-numbers-cat group nil server v fn-arena fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-nov-served-lines-for-numbers-cat)))))

(local (defthm fn-ovrb-any-lines-nil
  (equal (fn-nov-lines-for-numbers-cat group nil v fn-arena fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-nov-lines-for-numbers-cat)))))

(local (defthm fn-ovrb-any-stuff-nil
  (equal (fn-nntp-stuff-lines nil) nil)
  :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines)))))

(local (defthm fn-ovrb-any-append-nil-tl (implies (true-listp x) (equal (append x nil) x))))

(local (defthm fn-ovrb-any-len-append (equal (len (append a b)) (+ (len a) (len b)))))

(local (defthm fn-ovrb-any-number-len-is-len
  (equal (fn-ovr-number-len group n server v fn-arena fn-cat)
                  (len (fn-nntp-stuff-lines
                        (if server
                            (fn-nov-served-lines-for-numbers-cat group (list n) server v fn-arena fn-cat)
                          (fn-nov-lines-for-numbers-cat group (list n) v fn-arena fn-cat)))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-number-len fn-nov-served-lines-for-numbers-cat
                                   fn-nov-lines-for-numbers-cat fn-scol-tombstonep)
                                  (fn-ovr-column-line-len fn-nov-served-line fn-nov-line fn-nov-overview
                                   fn-hf-nov fn-scol-facts fn-scat-available-article fn-ovr-available-article
                                   fn-nntp-article-tombstonep fn-nntp-stuff-lines fn-nntp-crlf
                                   fn-scol-overview-of fn-ovr-column-over fn-nntp-article-length
                                   fn-ovr-msgid-okp))))))
(local (defthm fn-ovrb-any-probe-len-is-length
  (equal (fn-ovr-probe-len group j server v fn-arena fn-cat)
                  (len (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-ovr-probe-len fn-ovr-probe-octets fn-ovw-lines fn-scat-range-keep
                                   fn-ovr-msgid-okp-is-idp)
                                  (fn-ovr-number-len fn-nov-served-lines-for-numbers-cat
                                   fn-nov-lines-for-numbers-cat fn-cnx-view-seq fn-held-number-in
                                   fn-scat-msgid-idp fn-ovr-msgid-okp fn-nntp-stuff-lines))
           :expand ((fn-cnx-range-aux group j j v fn-cat)
                    (fn-cnx-range-aux group (+ 1 j) j v fn-cat))))))
(local
 (defthm fn-ovrb-any-probe-within
   (implies (and (fn-scol-okp fn-arena fn-cat)
                 (fn-ovr-rows-within-header a limits fn-arena fn-cat)
                 (<= (nfix (fn-article-limit-octets limits)) (nfix hdr))
                 )
            (<= (fn-ovr-probe-len group j server v fn-arena fn-cat)
                (+ 2 (fn-ovr-nov-line-header-bound hdr a server))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ovrb-served-lines-within
                             (numbers (fn-scat-range-keep group (fn-cnx-range-aux group j j v fn-cat) fn-cat)))
                  (:instance fn-ovrb-lines-within
                             (numbers (fn-scat-range-keep group (fn-cnx-range-aux group j j v fn-cat) fn-cat)))
                  (:instance fn-ovrb-at-most-one
                             (m (len (fn-scat-range-keep group (fn-cnx-range-aux group j j v fn-cat) fn-cat)))
                             (b (fn-ovr-nov-line-header-bound hdr a server))
                             (l (fn-ovr-probe-len group j server v fn-arena fn-cat))))
            :in-theory (e/d (fn-ovr-probe-octets fn-ovw-lines)
                            (fn-ovrb-served-lines-within fn-ovrb-lines-within fn-scat-range-keep fn-cnx-range-aux
                             fn-nov-served-lines-for-numbers-cat fn-nov-lines-for-numbers-cat
                             fn-nntp-stuff-lines fn-ovr-nov-line-header-bound fn-ovr-rows-within-header
                             fn-scol-okp fn-article-limit-octets))))))


; KO8: every probe of GROUP's numbers K..TOP is within the bound plus CRLF.
(defthm fn-ovr-probes-within-the-header-bound-any-view
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-ovr-rows-within-header a limits fn-arena fn-cat)
                (<= (nfix (fn-article-limit-octets limits)) (nfix hdr))
                )
           (fn-ovr-probes-within group k top server v
                                 (+ 2 (fn-ovr-nov-line-header-bound hdr a server))
                                 fn-arena fn-cat))
  :hints (("Goal" :induct (fn-ovr-probes-within group k top server v
                                                (+ 2 (fn-ovr-nov-line-header-bound hdr a server))
                                                fn-arena fn-cat)
           :in-theory (disable fn-ovr-probe-len fn-ovr-nov-line-header-bound fn-ovr-rows-within-header
                               fn-scol-okp fn-ovr-probe-len-is-the-length fn-article-limit-octets))
          ("Subgoal *1/2" :use ((:instance fn-ovrb-any-probe-within (j k))))))
