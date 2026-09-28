; fn: the running owner's `status' reclaim line read from the catalog's
; columns (lane scale-reads, 2026-09-28; PRF-368).  Prefix `fn-nsc-'.
;
; The reclaim line (books/native-live-status.lisp fn-nls-reclaim-words)
; walks every article four times (fn-rcl-store-counts: the summary and the
; held count; fn-rcl-store-classes: signed and kept), and each walk asks
; whether the article is a reclaim tombstone by reading its payload's first
; octets through the arena (fn-rcl-payload-tombstonep).  On the served owner
; the arena realizes a payload from its extent and checks the extent's
; digest before any octet is read, so every `status' read and hashed the
; whole store four times under the owner mutex: syn100k-2k, 7 s per walk in
; a raw Lisp over the production core (the reference BLAKE3; sb-sprof: 98%
; of the walk under fn-durable-realize-octet -> fn-frame-digest-buffer).  At
; 1,000,000 articles `status' passed the control client's 10 s and the owner,
; still rendering, took over 600 s to stop (lane serve-depth, native-sd5).
;
; The intern decided each row's tombstone flag once (books/served-columns.lisp
; fn-scol-tombstonep, KEYSTONE fn-scol-tombstonep-is-bytes under the column
; relation F = fn-scol-okp).  This book reads it there, and makes ONE walk
; that tallies all seven figures (fn-nsc-tally-loop, a guard-verified loop).
;
; KEYSTONES (the subject is fn-nsc-answer-report, which
; host/native-live-status-host.lisp fn-native-live-status-host-answer calls):
;   fn-nsc-store-tally-is-counts-and-classes   the one walk's seven figures
;       are fn-rcl-store-counts followed by fn-rcl-store-classes, under F;
;   fn-nsc-answer-report-is-answer-report     the owner's report of every
;       kind is fn-nh-answer-report's (books/native-health.lisp), under F.
; F is the relation the served OVER/HDR/XPAT column readers assume
; (books/served-columns.lisp); its owner-level establishment at the opens is
; the same open obligation (sca-join-4).  An article whose row the lookup
; does not find is read through the arena, as before.

(in-package "ACL2")
(include-book "native-health")
(include-book "served-columns")

; -----------------------------------------------------------------------------
; One article's verdict, its tombstone flag from the column.

(defun fn-nsc-verdict (rule now h verdicts a fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (if (fn-scol-tombstonep a fn-arena fn-cat)
      :already-reclaimed
    (fn-rcl-standing-verdict rule now h verdicts a)))

(defthm fn-nsc-verdict-is-verdict-in
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nsc-verdict rule now h verdicts a fn-arena fn-cat)
                  (fn-rcl-verdict-in rule now h verdicts a fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nsc-verdict fn-rcl-verdict-in
                                   fn-rcl-payload-tombstonep fn-nntp-article-tombstonep
                                   fn-nntp-article-bytes fn-nntp-payload-bytes
                                   fn-rcl-payload-bytes)
                                  (fn-scol-okp fn-scol-tombstonep
                                   fn-rcl-standing-verdict fn-rcl-tombstonep)))))

(in-theory (disable fn-nsc-verdict))

; -----------------------------------------------------------------------------
; The one walk: (reclaimable reclaimable-octets reclaimed freed-octets held
; signed kept).

(defun fn-nsc-tally-loop (rule now h verdicts articles c0 c1 c2 c3 held signed kept
                               fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp c0) (natp c1) (natp c2) (natp c3)
                              (natp held) (natp signed) (natp kept))))
  (if (consp articles)
      (let* ((a (car articles))
             (p (fn-article-payload a))
             (v (fn-nsc-verdict rule now h verdicts a fn-arena fn-cat))
             (gone (equal v :already-reclaimed))
             (free (equal v :reclaimable))
             (sig (fn-rcl-verdict-heldp (fn-article-msgid a) verdicts)))
        (fn-nsc-tally-loop
         rule now h verdicts (cdr articles)
         (if free (+ 1 c0) c0)
         (if free (+ (fn-rcl-payload-len p fn-arena) c1) c1)
         (if gone (+ 1 c2) c2)
         (if gone
             (+ (nfix (- (fn-rcl-payload-tomb-length p fn-arena)
                         (fn-rcl-payload-len p fn-arena)))
                c3)
           c3)
         (if (fn-rcl-heldp v) (+ 1 held) held)
         (if (and (not gone) sig) (+ 1 signed) signed)
         (if (and (not gone) (not sig) (not free) (not (fn-rcl-heldp v))) (+ 1 kept) kept)
         fn-arena fn-cat))
    (list c0 c1 c2 c3 held signed kept)))

(local
 (defthm fn-nsc-payload-len-natp
   (natp (fn-rcl-payload-len p fn-arena))
   :rule-classes :type-prescription))

(local
 (defthm fn-nsc-summary-in-shape
   (and (true-listp (fn-rcl-summary-in rule now h verdicts articles fn-arena))
        (equal (len (fn-rcl-summary-in rule now h verdicts articles fn-arena)) 4)
        (natp (nth 0 (fn-rcl-summary-in rule now h verdicts articles fn-arena)))
        (natp (nth 1 (fn-rcl-summary-in rule now h verdicts articles fn-arena)))
        (natp (nth 2 (fn-rcl-summary-in rule now h verdicts articles fn-arena)))
        (natp (nth 3 (fn-rcl-summary-in rule now h verdicts articles fn-arena))))
   :hints (("Goal" :induct (fn-rcl-summary-in rule now h verdicts articles fn-arena)
            :in-theory (e/d (fn-rcl-summary-in) (fn-rcl-verdict-in
                                                 fn-rcl-payload-len
                                                 fn-rcl-payload-tomb-length))))))

; The one walk is the three loops the counts execute by
; (fn-rcl-summary-loop, fn-rcl-held-count-loop, fn-rcl-class-count-loop),
; each proved equal to its count in books/store-reclaim-holders.lisp.
(local
 (defthm fn-nsc-tally-loop-is-the-loops
   (implies (fn-scol-okp fn-arena fn-cat)
            (equal (fn-nsc-tally-loop rule now h verdicts articles
                                      c0 c1 c2 c3 held signed kept fn-arena fn-cat)
                   (append (fn-rcl-summary-loop rule now h verdicts articles
                                                c0 c1 c2 c3 fn-arena)
                           (list (fn-rcl-held-count-loop rule now h verdicts articles
                                                         held fn-arena)
                                 (fn-rcl-class-count-loop :signed rule now h verdicts
                                                          articles signed fn-arena)
                                 (fn-rcl-class-count-loop :kept rule now h verdicts
                                                          articles kept fn-arena)))))
   :hints (("Goal" :induct (fn-nsc-tally-loop rule now h verdicts articles
                                              c0 c1 c2 c3 held signed kept fn-arena fn-cat)
            :in-theory (e/d (fn-rcl-class-in)
                            (fn-rcl-verdict-in fn-rcl-payload-len fn-rcl-payload-tomb-length
                             fn-scol-okp fn-rcl-verdict-heldp fn-rcl-heldp))))))

(local
 (defthm fn-nsc-append-assoc
   (equal (append (append x y) z) (append x y z))))

(defun fn-nsc-store-tally (rule now s fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (let ((h (fn-rcl-store-holders s))
        (verdicts (fn-rcl-held-verdicts (fn-sn-verdicts s)))
        (articles (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
    (fn-nsc-tally-loop rule now h verdicts articles 0 0 0 0 0 0 0 fn-arena fn-cat)))

; KEYSTONE (the one walk is the four).  Under F, the seven figures the
; owner's reclaim line reads are fn-rcl-store-counts (reclaimable,
; reclaimable-octets, reclaimed, freed-octets, held) followed by
; fn-rcl-store-classes (signed, kept) -- the figures
; fn-rcl-store-counts-is-the-model-over-alpha and
; fn-rcl-store-classes-over-every-verdict (books/store-reclaim-holders.lisp)
; speak of.
(defthm fn-nsc-store-tally-is-counts-and-classes
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nsc-store-tally rule now s fn-arena fn-cat)
                  (append (fn-rcl-store-counts rule now s fn-arena)
                          (fn-rcl-store-classes rule now s fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-nsc-store-tally fn-rcl-store-counts
                                                      fn-rcl-store-classes
                                                      fn-rcl-summary-loop-is-the-summary
                                                      fn-rcl-held-count-loop-is-the-count
                                                      fn-rcl-class-count-loop-is-the-count)
                                  (fn-nsc-tally-loop fn-scol-okp fn-rcl-summary-in
                                                     fn-rcl-held-count-in fn-rcl-class-count-in
                                                     fn-rcl-summary-loop fn-rcl-held-count-loop
                                                     fn-rcl-class-count-loop)))))

(in-theory (disable fn-nsc-store-tally))

; -----------------------------------------------------------------------------
; The reclaim line, then the report, from the one walk.

(defun fn-nsc-reclaim-words (s cfg obs fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (let* ((rule (fn-rcl-config-rule (fn-cfg-value cfg)))
         (stamp (fn-record-stamp-of-observation (fn-nls-obs-clock obs)))
         (now (if (natp stamp) stamp nil))
         (tally (fn-nsc-store-tally rule now s fn-arena fn-cat)))
    (append (fn-nls-text "reclaim rule=") (fn-nls-rule-words rule)
            (fn-nls-field "reclaimable" (nth 0 tally))
            (fn-nls-field "reclaimable-octets" (nth 1 tally))
            (fn-nls-field "held" (nth 4 tally))
            (fn-nls-field "reclaimed" (nth 2 tally))
            (fn-nls-field "freed-octets" (nth 3 tally))
            (fn-nls-field "signed" (nth 5 tally))
            (fn-nls-field "kept" (nth 6 tally)))))

(local
 (defthm fn-nsc-counts-shape
   (and (true-listp (fn-rcl-store-counts rule now s fn-arena))
        (equal (len (fn-rcl-store-counts rule now s fn-arena)) 5))
   :hints (("Goal" :in-theory (enable fn-rcl-store-counts)
            :use ((:instance fn-nsc-summary-in-shape
                             (h (fn-rcl-store-holders s))
                             (verdicts (fn-rcl-held-verdicts (fn-sn-verdicts s)))
                             (articles (fn-state-articles
                                        (fn-node-acceptance (fn-sn-node s))))))))))

(local
 (defthm fn-nsc-nth-of-append-five
   (implies (and (true-listp x) (equal (len x) 5))
            (and (equal (nth 0 (append x y)) (nth 0 x))
                 (equal (nth 1 (append x y)) (nth 1 x))
                 (equal (nth 2 (append x y)) (nth 2 x))
                 (equal (nth 3 (append x y)) (nth 3 x))
                 (equal (nth 4 (append x y)) (nth 4 x))
                 (equal (nth 5 (append x y)) (nth 0 y))
                 (equal (nth 6 (append x y)) (nth 1 y))))
   :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
                            (len (cddddr x)) (len (cdr (cddddr x))))))))

(defthm fn-nsc-reclaim-words-is-reclaim-words
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nsc-reclaim-words s cfg obs fn-arena fn-cat)
                  (fn-nls-reclaim-words s cfg obs fn-arena)))
  :hints (("Goal" :in-theory '(fn-nsc-reclaim-words fn-nls-reclaim-words
                               fn-nsc-store-tally-is-counts-and-classes
                               fn-nsc-nth-of-append-five fn-nsc-counts-shape
                               fn-rcl-store-classes car-cons cdr-cons (:e zp) nth))))

(in-theory (disable fn-nsc-reclaim-words))

; The status branch of fn-nls-report, its reclaim line from the one walk.
; Every other kind is fn-nls-report's.
(defun fn-nsc-report (kind profile s bytes cfg pins obs fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (if (member-equal kind '(:peers :control :accounts :pins :obligations))
      (fn-nls-report kind profile s bytes cfg pins obs fn-arena)
    (append (fn-nls-text "transactions=") (fn-nls-nat (fn-sbud-used s))
            (fn-nls-field "articles"
                          (len (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
            (fn-nls-text " ") (fn-nls-orphan-words obs)
            (fn-nls-text " unsigned-legacy-experiment") *fn-nls-lf*
            (fn-nls-text "profile")
            (fn-nls-profile-words (fn-bs-profile-report profile)) *fn-nls-lf*
            (fn-nls-open-cost-words profile) *fn-nls-lf*
            (fn-nls-headroom-words (fn-sbud-headroom-at profile s bytes)) *fn-nls-lf*
            (fn-nls-capacity-words (fn-sbud-headroom-at profile s bytes)) *fn-nls-lf*
            (fn-nls-reserve-words
             (fn-cvec-report profile (fn-sbud-used s) bytes
                             (fn-cvec-record-debt (fn-sf-records (fn-sn-files s)))))
            *fn-nls-lf*
            (fn-nls-open-words obs) *fn-nls-lf*
            (fn-nsc-reclaim-words s cfg obs fn-arena fn-cat) *fn-nls-lf*
            (fn-nls-checkpoint-file-words obs) *fn-nls-lf*
            (fn-nls-pins-line s pins))))

(defthm fn-nsc-report-is-report
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nsc-report kind profile s bytes cfg pins obs fn-arena fn-cat)
                  (fn-nls-report kind profile s bytes cfg pins obs fn-arena)))
  :hints (("Goal" :in-theory '(fn-nsc-report fn-nls-report member-equal
                               fn-nsc-reclaim-words-is-reclaim-words))))

(defun fn-nsc-live-report (kind profile oc cache obs fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (let ((s (fn-own-store (fn-ocfg-owner oc))))
    (fn-nsc-report kind profile s
                   (fn-sbud-bytes-extend cache (fn-sf-records (fn-sn-files s)))
                   (fn-ocfg-config oc) (fn-ocfg-pins oc) obs fn-arena fn-cat)))

(defun fn-nsc-answer-report (kind profile oc cache obs min fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (if (equal kind :health)
      (fn-nh-live-report profile oc cache min)
    (fn-nsc-live-report kind profile oc cache obs fn-arena fn-cat)))

; KEYSTONE (the owner's report is the report).  The subject is
; fn-nsc-answer-report, which host/native-live-status-host.lisp
; fn-native-live-status-host-answer calls for every FNLS kind the running
; owner renders; under F it is fn-nh-answer-report, so every theorem about
; that report (fn-nls-live-report-is-the-offline-report,
; fn-nls-obligations-figures-are-the-retention-figures, the health verdict's)
; is about the words the owner sends.
(defthm fn-nsc-answer-report-is-answer-report
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nsc-answer-report kind profile oc cache obs min fn-arena fn-cat)
                  (fn-nh-answer-report kind profile oc cache obs min fn-arena)))
  :hints (("Goal" :in-theory '(fn-nsc-answer-report fn-nh-answer-report
                               fn-nsc-live-report fn-nls-live-report
                               fn-nsc-report-is-report))))
