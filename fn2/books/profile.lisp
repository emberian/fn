; Init-time resident execution profiles.  These values size arrays; they do
; not bound durable namespaces.  All post-init capacities are read from state.
(in-package "ACL2")

(defun fn2-profile-get (key profile)
  (declare (xargs :guard t))
  (if (alistp profile) (cdr (assoc-equal key profile)) nil))

(defmacro fn2-def-profile-reader (name key)
  `(defun ,name (profile)
     (declare (xargs :guard t))
     (fn2-profile-get ,key profile)))

(fn2-def-profile-reader fn2-profile-c :c)
(fn2-def-profile-reader fn2-profile-p :p)
(fn2-def-profile-reader fn2-profile-u :u)
(fn2-def-profile-reader fn2-profile-t :t)
(fn2-def-profile-reader fn2-profile-x :x)
(fn2-def-profile-reader fn2-profile-w :w)
(fn2-def-profile-reader fn2-profile-o :o)
(fn2-def-profile-reader fn2-profile-qa :qa)
(fn2-def-profile-reader fn2-profile-h :h)
(fn2-def-profile-reader fn2-profile-k :k)
(fn2-def-profile-reader fn2-profile-aturn :aturn)
(fn2-def-profile-reader fn2-profile-run-bytes :run-bytes)
(fn2-def-profile-reader fn2-profile-run-steps :run-steps)
(fn2-def-profile-reader fn2-profile-run-descriptors :run-descriptors)
(fn2-def-profile-reader fn2-profile-ncancel :ncancel)
(fn2-def-profile-reader fn2-profile-jread :jread)
(fn2-def-profile-reader fn2-profile-jwrite :jwrite)
(fn2-def-profile-reader fn2-profile-accept-credits :accept-credits)
(fn2-def-profile-reader fn2-profile-pool-classes :pool-classes)
(fn2-def-profile-reader fn2-profile-generation-start :generation-start)
(fn2-def-profile-reader fn2-profile-generation-limit :generation-limit)
(fn2-def-profile-reader fn2-profile-trace :trace)
(fn2-def-profile-reader fn2-profile-calendar-length :calendar-length)

(defun fn2-profile-positive-u32p (x)
  (declare (xargs :guard t))
  (and (posp x) (unsigned-byte-p 32 x)))

(defun fn2-profile-positive-fields-p (keys profile)
  (declare (xargs :guard t))
  (if (atom keys)
      (null keys)
    (and (fn2-profile-positive-u32p (fn2-profile-get (car keys) profile))
         (fn2-profile-positive-fields-p (cdr keys) profile))))

(defun fn2-profile-classes-p (classes)
  (declare (xargs :guard t))
  (if (atom classes)
      (null classes)
    (and (consp (car classes))
         (unsigned-byte-p 32 (caar classes))
         (fn2-profile-positive-u32p (cdar classes))
         (fn2-profile-classes-p (cdr classes)))))

(defun fn2-profile-pool-slots (classes)
  (declare (xargs :guard (fn2-profile-classes-p classes)))
  (if (consp classes)
      (+ (caar classes) (fn2-profile-pool-slots (cdr classes)))
    0))

(defun fn2-profile-pool-bytes (classes)
  (declare (xargs :guard (fn2-profile-classes-p classes)))
  (if (consp classes)
      (+ (* (caar classes) (cdar classes))
         (fn2-profile-pool-bytes (cdr classes)))
    0))

(defun fn2-profilep (profile)
  (declare (xargs :guard t))
  (and
   (alistp profile)
   (no-duplicatesp-equal (strip-cars profile))
   (fn2-profile-positive-fields-p
    '(:c :p :u :t :x :w :o :qa :h :k :aturn
      :run-bytes :run-steps :run-descriptors
      :ncancel :jread :jwrite :accept-credits :calendar-length) profile)
   ; Principal references use u16; the other table references use u32.
   (<= (fn2-profile-p profile) 65536)
   (consp (fn2-profile-pool-classes profile))
   (fn2-profile-classes-p (fn2-profile-pool-classes profile))
   (unsigned-byte-p 32
                    (fn2-profile-pool-slots (fn2-profile-pool-classes profile)))
   (unsigned-byte-p 60
                    (fn2-profile-pool-bytes (fn2-profile-pool-classes profile)))
   (unsigned-byte-p 60 (fn2-profile-generation-start profile))
   (unsigned-byte-p 60 (fn2-profile-generation-limit profile))
   (<= (fn2-profile-generation-start profile)
       (fn2-profile-generation-limit profile))
   (consp (assoc-equal :trace profile))
   (booleanp (fn2-profile-trace profile))))

; Init callers use these field facts without opening the full profile schema.
(defthm fn2-profile-o-bounds
  (implies (fn2-profilep profile)
           (and (posp (fn2-profile-o profile))
                (unsigned-byte-p 32 (fn2-profile-o profile))))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn2-profile-qa-bounds
  (implies (fn2-profilep profile)
           (and (posp (fn2-profile-qa profile))
                (unsigned-byte-p 32 (fn2-profile-qa profile))))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn2-profile-generation-bounds
  (implies (fn2-profilep profile)
           (and (unsigned-byte-p 60 (fn2-profile-generation-start profile))
                (unsigned-byte-p 60 (fn2-profile-generation-limit profile))
                (<= (fn2-profile-generation-start profile)
                    (fn2-profile-generation-limit profile))))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable fn2-profilep))

; 512 4-KiB slots: separate RX and TX for every one of 256 connections.
; 80 64-KiB slots: one storage window for each of 64 read and 16 write jobs.
; Total: 592 slots and 7,340,032 bytes (7 MiB).
(defconst *fn2-profile-concrete*
  '((:c . 256) (:p . 64) (:u . 128) (:t . 128) (:x . 256) (:w . 256)
    (:o . 1024) (:qa . 1024) (:h . 128) (:k . 64) (:aturn . 256)
    (:run-bytes . 4096) (:run-steps . 32) (:run-descriptors . 4)
    (:ncancel . 32) (:jread . 64) (:jwrite . 16) (:accept-credits . 8)
    (:pool-classes . ((512 . 4096) (80 . 65536)))
    (:generation-start . 1) (:generation-limit . 1152921504606846975)
    (:trace . nil) (:calendar-length . 80)))

; Tiny calendar: principal slots 0..3, commit, timer/grant, wake, maintenance.
; The run quanta remain the declared per-run caps; resident capacities shrink.
(defconst *fn2-profile-tiny*
  '((:c . 4) (:p . 4) (:u . 2) (:t . 2) (:x . 4) (:w . 4)
    (:o . 8) (:qa . 4) (:h . 4) (:k . 8) (:aturn . 8)
    (:run-bytes . 4096) (:run-steps . 32) (:run-descriptors . 4)
    (:ncancel . 2) (:jread . 2) (:jwrite . 2) (:accept-credits . 2)
    (:pool-classes . ((8 . 64) (4 . 256)))
    (:generation-start . 1) (:generation-limit . 1152921504606846975)
    (:trace . t) (:calendar-length . 8)))

(defconst *fn2-profile-tiny-near-limit*
  (put-assoc-equal :generation-start 1152921504606846972 *fn2-profile-tiny*))

(assert-event
 (and (fn2-profilep *fn2-profile-concrete*)
      (fn2-profilep *fn2-profile-tiny*)
      (fn2-profilep *fn2-profile-tiny-near-limit*)
      (equal (fn2-profile-pool-slots
              (fn2-profile-pool-classes *fn2-profile-concrete*)) 592)
      (equal (fn2-profile-pool-bytes
              (fn2-profile-pool-classes *fn2-profile-concrete*)) 7340032)
      (equal (- (fn2-profile-generation-limit *fn2-profile-tiny-near-limit*)
                (fn2-profile-generation-start *fn2-profile-tiny-near-limit*)) 3)
      (not (fn2-profilep nil))
      (not (fn2-profilep (put-assoc-equal :qa 0 *fn2-profile-tiny*)))
      (not (fn2-profilep
            (put-assoc-equal :generation-start 1152921504606846976
                             *fn2-profile-tiny*)))))

(defun fn2-profile-exports-compliant-p (names world)
  (declare (xargs :guard (and (symbol-listp names) (plist-worldp world))))
  (if (endp names) t
    (and (eq (symbol-class (car names) world) :common-lisp-compliant)
         (fn2-profile-exports-compliant-p (cdr names) world))))

(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-profile-get fn2-profilep fn2-profile-c fn2-profile-p fn2-profile-u
    fn2-profile-t fn2-profile-x fn2-profile-w fn2-profile-o fn2-profile-qa
    fn2-profile-h fn2-profile-k fn2-profile-aturn fn2-profile-run-bytes
    fn2-profile-run-steps fn2-profile-run-descriptors fn2-profile-ncancel
    fn2-profile-jread fn2-profile-jwrite fn2-profile-accept-credits
    fn2-profile-pool-classes fn2-profile-generation-start
    fn2-profile-generation-limit fn2-profile-trace fn2-profile-calendar-length
    fn2-profile-positive-u32p fn2-profile-positive-fields-p
    fn2-profile-classes-p fn2-profile-pool-slots fn2-profile-pool-bytes)
  (w state)))
