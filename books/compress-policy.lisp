; ACL2-owned admission, bounded codec requests and expansion accounting.
; The shared codec ledger owns spans/incarnations; this policy never owns a
; second copy of its cursors. Credit is a supported-profile admission limit,
; not a bound on an article or on the lifetime of a compressed connection.
(in-package "ACL2")
(include-book "profile")
(include-book "owed-discharge")
(fn2-book-layer :a)

(defconst *fn2-compress-min-output-window* 7)

(defun fn2-compress-profilep (profile)
 (declare (xargs :guard t))
 (and (booleanp (fn2-profile-get :compress-enabled profile))
  (or (not (fn2-profile-get :compress-enabled profile))
   (and (fn2-profile-positive-u32p (fn2-profile-get :compress-input-quantum profile))
        (fn2-profile-positive-u32p (fn2-profile-get :compress-output-quantum profile))
        ;; The encoder always supplies a full private output window. zlib
        ;; requires avail_out >6 for resumable Z_SYNC_FLUSH completion.
        (<= *fn2-compress-min-output-window* (fn2-profile-get :compress-output-quantum profile))
        (fn2-profile-positive-u32p (fn2-profile-get :compress-expansion-ratio profile))
        (fn2-profile-positive-u32p (fn2-profile-get :compress-expansion-burst profile))
        (<= (fn2-profile-get :compress-output-quantum profile)
            (fn2-profile-get :compress-expansion-burst profile))))))

(defun fn2-compress-admission (authenticated active deflate enabled)
 (declare (xargs :guard t))
 (cond ((not authenticated) :auth-required)
       (active :running)
       ((or (not deflate) (not enabled)) :algorithm)
       (t :started)))
(defun fn2-compress-admit (authenticated active deflate profile)
 (declare (xargs :guard t))
 (fn2-compress-admission authenticated active deflate
  (and (fn2-compress-profilep profile) (fn2-profile-get :compress-enabled profile))))

; Output credit begins at BURST. Each successfully observed compressed input
; octet earns RATIO credit; produced application octets spend it. Saturation
; at BURST bounds resident accounting and prevents saving unlimited credit.
; Requests spend only existing credit; an unobserved input never grants any.
(defun fn2-compress-plan (input-room output-room input-quantum output-quantum credit)
 (declare (xargs :guard t))
 (if (not (and (natp input-room) (natp output-room)
               (posp input-quantum) (posp output-quantum) (natp credit)))
     (mv :bounds 0 0)
  (cond ((zp credit) (mv :limit 0 0))
        ((zp output-room) (mv :need-output 0 0))
        (t (mv :transform (min input-room input-quantum)
                   (min output-room (min output-quantum credit)))))))

(defun fn2-compress-observe (raw used made requested-input requested-output credit ratio burst)
 (declare (xargs :guard t))
 (if (not (and (integerp raw) (natp used) (natp made)
               (natp requested-input) (natp requested-output)
               (<= used requested-input) (<= made requested-output)
               (natp credit) (posp ratio) (posp burst)
               (<= credit burst) (<= requested-output credit)))
     (mv :bounds credit)
  (let ((next (min burst (- (+ credit (* ratio used)) made))))
   (mv (cond ((equal raw 1) :final)
             ((not (equal raw 0)) :failed)
             ((and (equal used 0) (equal made 0)) :need-input)
             ((equal made requested-output) :need-output)
             (t :progress)) next))))

(defthm-owed fn2-compress-plan-bounded (ir oroom iq oq credit)
 (implies (equal (mv-nth 0 (fn2-compress-plan ir oroom iq oq credit)) :transform)
  (and (natp (mv-nth 1 (fn2-compress-plan ir oroom iq oq credit)))
       (natp (mv-nth 2 (fn2-compress-plan ir oroom iq oq credit)))
       (<= (mv-nth 1 (fn2-compress-plan ir oroom iq oq credit)) ir)
       (<= (mv-nth 1 (fn2-compress-plan ir oroom iq oq credit)) iq)
       (<= (mv-nth 2 (fn2-compress-plan ir oroom iq oq credit)) oroom)
       (<= (mv-nth 2 (fn2-compress-plan ir oroom iq oq credit)) oq)
       (<= (mv-nth 2 (fn2-compress-plan ir oroom iq oq credit)) credit)))
 :teeth (fn2-compress-plan-positive fn2-compress-plan-negative)
 :doc "Admitted DEFLATE requests bound both shared-ledger spans and pre-observation expansion credit.")
(defthm fn2-compress-plan-bounded
 (implies (equal (mv-nth 0 (fn2-compress-plan ir oroom iq oq credit)) :transform)
  (and (natp (mv-nth 1 (fn2-compress-plan ir oroom iq oq credit)))
       (natp (mv-nth 2 (fn2-compress-plan ir oroom iq oq credit)))
       (<= (mv-nth 1 (fn2-compress-plan ir oroom iq oq credit)) ir)
       (<= (mv-nth 1 (fn2-compress-plan ir oroom iq oq credit)) iq)
       (<= (mv-nth 2 (fn2-compress-plan ir oroom iq oq credit)) oroom)
       (<= (mv-nth 2 (fn2-compress-plan ir oroom iq oq credit)) oq)
       (<= (mv-nth 2 (fn2-compress-plan ir oroom iq oq credit)) credit))))

(defthm-owed fn2-compress-observe-credit-bounded (raw used made ri ro credit ratio burst)
 (implies (not (equal (mv-nth 0 (fn2-compress-observe raw used made ri ro credit ratio burst)) :bounds))
  (let ((next (mv-nth 1 (fn2-compress-observe raw used made ri ro credit ratio burst))))
   (and (natp next) (<= next burst)
        (<= (+ next made) (+ credit (* ratio used))))))
 :teeth (fn2-compress-credit-positive fn2-compress-credit-negative)
 :doc "Validated DEFLATE observations conserve expansion credit; saturation is the profile burst policy, not a lifetime article bound.")
(defthm fn2-compress-observe-credit-bounded
 (implies (not (equal (mv-nth 0 (fn2-compress-observe raw used made ri ro credit ratio burst)) :bounds))
  (let ((next (mv-nth 1 (fn2-compress-observe raw used made ri ro credit ratio burst))))
   (and (natp next) (<= next burst)
        (<= (+ next made) (+ credit (* ratio used)))))))

(defthm fn2-compress-observe-refusal-frame-by-definition
 (implies (equal (mv-nth 0 (fn2-compress-observe raw used made ri ro credit ratio burst)) :bounds)
  (equal (mv-nth 1 (fn2-compress-observe raw used made ri ro credit ratio burst)) credit)))


; Guard clients keep the policy opaque. Refusals return the original credit;
; accepted observations return a natural bounded by the admitted burst.
(defthm fn2-compress-observe-credit-natural
 (implies (natp credit)
  (natp (mv-nth 1 (fn2-compress-observe raw used made ri ro credit ratio burst))))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (disable fn2-compress-observe
                             fn2-compress-observe-credit-bounded
                             fn2-compress-observe-refusal-frame-by-definition)
          :cases ((equal (mv-nth 0 (fn2-compress-observe raw used made ri ro credit ratio burst)) :bounds))
          :use (fn2-compress-observe-credit-bounded
                fn2-compress-observe-refusal-frame-by-definition))))

(defthm fn2-compress-observe-credit-u32
 (implies (and (unsigned-byte-p 32 credit) (unsigned-byte-p 32 burst))
  (unsigned-byte-p 32 (mv-nth 1 (fn2-compress-observe raw used made ri ro credit ratio burst))))
 :hints (("Goal" :in-theory (disable fn2-compress-observe
                             fn2-compress-observe-credit-bounded
                             fn2-compress-observe-refusal-frame-by-definition)
          :cases ((equal (mv-nth 0 (fn2-compress-observe raw used made ri ro credit ratio burst)) :bounds))
          :use (fn2-compress-observe-credit-bounded
                fn2-compress-observe-refusal-frame-by-definition))))

(fn2-owed-discharge fn2-compress-plan-bounded fn2-compress-plan-bounded)
(fn2-owed-discharge fn2-compress-observe-credit-bounded fn2-compress-observe-credit-bounded)
