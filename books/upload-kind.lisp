;; Schema, core child, and partition registration for fn2-upload (layer D, quest D4).
;; Arm bodies and helper operations live in books/upload.lisp (a leaf book).
(in-package "ACL2")
(include-book "machines-a")
(include-book "machines-b")
(include-book "conn-kind")
(include-book "profile")
(include-book "upload-scan")
(include-book "upload-feed")
(include-book "blake3")
(include-book "machine-arms") ; defmachine-registry (MACHINE-FORM 6.5 P4)
(fn2-book-layer :d)

;; The run quantum, split statically: at most *fn2-upload-hash-bytes* hashed
;; and *fn2-upload-scan-bytes* of header scanned per run.
(defconst *fn2-upload-hash-bytes* 2048)
(defconst *fn2-upload-scan-bytes* 2048)
(defconst *fn2-upload-run-bytes* (+ *fn2-upload-hash-bytes* *fn2-upload-scan-bytes*))
;; The pool class of a chunk (the profile's second class: 64 KiB in the
;; concrete profile) and the article bound when the profile names none
;; (fn1's source bound, specs/article-parser.md).
(defconst *fn2-upload-chunk-class* 1)
;; Large-upload windows (ROUND2 B.1): an upload holds one while it streams.
(defconst *fn2-upload-windows* 16)
(defconst *fn2-upload-article-max* 32768)
;; The source's content identity (BLAKE3, 32 octets) is appended to the
;; window right after the source at the verdict, for C's offer and the
;; article row (a pool workspace is written at its fill): in chunk 0 when it
;; fits there, else in chunk 1. The bound leaves its room in chunk 1.
(defconst *fn2-upload-digest-octets* 32)
;; Where it goes for a source of FILLED octets: (mv in1 off), IN1 true for
;; chunk 1.
(defun fn2-upload-digest-at (filled cap0)
  (declare (xargs :guard (and (natp filled) (natp cap0))))
  (cond ((<= (+ filled *fn2-upload-digest-octets*) cap0) (mv nil filled))
        ((<= filled cap0) (mv t 0))
        (t (mv t (- filled cap0)))))
(defthm fn2-upload-digest-at-natp
  (implies (and (natp filled) (natp cap0)) (natp (mv-nth 1 (fn2-upload-digest-at filled cap0))))
  :rule-classes :type-prescription)
;; Words an upload or a transaction posts to its connection (section 14.5),
;; by name; 0 is none.
(defconst *fn2-upload-words*
  '(:none :accepted :uncertain :duplicate :conflict :too-large :malformed :framing :line-length
    :header-fields :header-lines :header-octets :missing :duplicate-field :path :message-id :mismatch
    :injected :no-clock :group :unaffordable :control-malformed :refused :not-stored
    ;; the verdict's :missing, :duplicate-field and :injected by field (the catalogue's rows)
    :from-missing :subject-missing :newsgroups-missing :from-duplicate :subject-duplicate
    :newsgroups-duplicate :message-id-duplicate :date-duplicate :path-duplicate :xref :injection-info
    :injection-date))
;; The verdict's word refined by field, in the order the model checks them.
(defun fn2-upload-word-by-field (word seen)
  (declare (xargs :guard (natp seen)))
  (cond ((eq word :missing)
           (cond ((not (fn2-upload-bit seen *fn2-upload-field-from*)) :from-missing)
                 ((not (fn2-upload-bit seen *fn2-upload-field-subject*)) :subject-missing)
                 ((not (fn2-upload-bit seen *fn2-upload-field-ng*)) :newsgroups-missing)
                 (t :missing)))
          ((eq word :duplicate-field)
           (cond ((fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-from*)) :from-duplicate)
                 ((fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-subject*)) :subject-duplicate)
                 ((fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-ng*)) :newsgroups-duplicate)
                 ((fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-mid*)) :message-id-duplicate)
                 ((fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-date*)) :date-duplicate)
                 (t :path-duplicate)))
          ((eq word :injected)
           (cond ((fn2-upload-bit seen *fn2-upload-field-xref*) :xref)
                 ((fn2-upload-bit seen *fn2-upload-field-injection-info*) :injection-info)
                 (t :injection-date)))
          (t word)))
(defun fn2-upload-word-code (word)
  (declare (xargs :guard t))
  (let ((tail (member-eq word *fn2-upload-words*)))
    (if tail (- (len *fn2-upload-words*) (len tail)) 0)))
(defun fn2-upload-word-of (code)
  (declare (xargs :guard (natp code)))
  (if (< code (len *fn2-upload-words*)) (nth code *fn2-upload-words*) :none))

;; The input configuration (a D core child, one row): whether posting is
;; served under the interim (section 14.5: the public capability stays off
;; until a POST can succeed; tests set :posting-interim) and the article
;; bound.
(defcolumns fn2-input-config ((posting :bool) (article-max :u32)))
(defun fn2-input-config-profilep (profile)
  (declare (xargs :guard t))
  (and (booleanp (fn2-profile-get :posting-interim profile))
       ;; article input needs the chunk class and a hasher row per window
       (or (not (fn2-profile-get :posting-interim profile))
           (and (true-listp (fn2-profile-get :pool-classes profile))
                (< *fn2-upload-chunk-class* (len (fn2-profile-get :pool-classes profile)))
                (< 0 (fn2-b-upload-windows profile))))
       (or (null (fn2-profile-get :article-max profile))
           (unsigned-byte-p 32 (fn2-profile-get :article-max profile)))))
(defun fn2-input-config-from (profile fn2-input-config)
  (declare (xargs :stobjs fn2-input-config :guard (fn2-input-config-profilep profile)))
  (let* ((fn2-input-config (fn2-input-config-init 1 fn2-input-config))
         (max (fn2-profile-get :article-max profile)))
    (fn2-input-config-put 0 (posting (if (fn2-profile-get :posting-interim profile) 1 0))
                          (article-max (if (unsigned-byte-p 32 max) max *fn2-upload-article-max*)))))
(defthm fn2-input-config-from-type
  (implies (fn2-input-configp fn2-input-config)
           (fn2-input-configp (fn2-input-config-from profile fn2-input-config))))
(defthm fn2-input-config-from-wfp
  (fn2-input-config-wfp (fn2-input-config-from profile fn2-input-config)))
(in-theory (disable fn2-input-config-from fn2-input-config-profilep))
(defcorechild fn2-core-input-config fn2-input-config
 :init (fn2-input-config-from profile fn2-input-config) :profilep (fn2-input-config-profilep profile)
 :why "The node's article-input settings: the posting switch and the article bound, read by the connection and the upload.")

;; One row per window, and none unless the profile serves article input
;; (B-S1: hasher rows 3 .. 2+w of fn2-b3 are the windows', B's row map). Opaque to the
;; directory's proofs (a capacity is a natural).
(defun fn2-upload-capacity (profile)
  (declare (xargs :guard t))
  (if (fn2-profile-get :posting-interim profile)
      (min (min (nfix (fn2-profile-u profile)) *fn2-upload-windows*)
           (fn2-b-upload-windows profile))
    0))
(defthm fn2-upload-capacity-natp (natp (fn2-upload-capacity profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-upload-capacity))

(defmachine fn2-upload
 :states (:free :head :identity :receiving :validating :discard :sealed :aborting :draining :retired)
 :fields ((conn :link) (conn-gen :u60) (request :u32)
          (rule (:enum fn2-upload-rule (:post :ihave :takethis)))
          (c0-slot :link) (c0-gen :u60) (c1-slot :link) (c1-gen :u60)
          (filled :u60) (hashed :u60)
          (scan-off :u32) (ofield :u8) (visible :bool) (nfields :u16) (nlines :u16) (seen :u32)
          (mo :u32) (ml :u32) (no :u32) (nl :u32) (po :u32) (pl :u32)
          (head-status (:enum fn2-upload-head (:scanning :done :malformed :line-length :header-fields
                                                :header-lines :header-octets)))
          (word :u8) (inj :u8) (txn :link) (txn-gen :u60) (stopped :bool) (next-free :link))
 :links ((conn :kind fn2-conn :slot conn :gen conn-gen :back (upload upload-gen)
               :reads (fed feed-mode feed-discard))
         (child-txn :kind fn2-txn :slot txn :gen txn-gen :back (upload upload-gen)))
 :holds ((:head :upload-row :chunk-window) (:identity :upload-row :chunk-window)
         (:receiving :upload-row :chunk-window) (:validating :upload-row :chunk-window)
         (:discard :upload-row :chunk-window) (:sealed :upload-row :chunk-window)
         (:aborting :upload-row :chunk-window) (:draining :upload-row :chunk-window))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-upload-capacity profile)
 ;; A connection takes the row with its two chunks (A-S7).
 :taken (:phase :head :rows :upload-row
         :ranges ((:chunk-window :slot c0-slot :gen c0-gen :class 1)
                  (:chunk-window :slot c1-slot :gen c1-gen :class 1))
         :copy (conn conn-gen request rule principal-slot)
         :clear (filled hashed scan-off visible nfields nlines seen mo ml no nl po pl
                 head-status word inj txn-gen stopped))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (c0-slot *fn2-none*) (c1-slot *fn2-none*) (conn *fn2-none*) (txn *fn2-none*) (account-ref *fn2-none*)
           (ofield 12) (next-free fn2-machine-initial-next-free))
 :arms ((:free) (:head) (:identity) (:receiving) (:validating) (:discard) (:sealed) (:aborting) (:draining) (:retired))
 :observes ())

; MACHINE-FORM 6.5 P4: the kind's take in child form, proved here;
; the admission section (assembly-callbacks-a) makes its core face.
(defmachine-registry fn2-upload)
