; Every field of a configuration record (books/config.lisp) at its maximum
; allowed value round-trips through the record codec, and one past each
; maximum is refused by name.  Lane clock-units-2 (2026-09-28): a
; millisecond stamp past 2^32 was admitted by fn-cfg-stampp but written with
; the narrow CBOR uint, so every native `init' faulted at open; nothing
; encoded a field at its maximum.  This book is that check.
;
; THE MAXIMA, each the recognizer that states it:
;   sequence, txid, generation   fn-record-uint32p        2^32 - 1
;   stamp monotonic/wall/error   fn-clock-timep           2^64 - 1 (ms)
;   stamp has-wall               booleanp                 t (item 1)
;   delta count                  *fn-cfg-max-deltas*      64
;   delta kind                   *fn-cfg-delta-kinds*     code 27
;   delta a, b; row a, b, c      fn-cfg-labelp            256 octets
;   delta n, row n               fn-record-uint32p        2^32 - 1
;   rows per delta               *fn-cfg-max-rows*        1024
;   items per record             *fn-cfg-max-items*       65535
;   octets per record            *fn-cfg-max-octets*      65538
; The last two are the decoder's whole-record ceilings.  They are NOT part
; of fn-cfg-recordp: a record every field of which is within its maximum can
; encode past 65,538 octets (below, the GAP witness), and the decoder then
; refuses it :limit.  Stated here; its enforcement at admission is open
; (LANEDUMP clock-units-2).
(in-package "ACL2")
(include-book "../../books/config")

(defconst *cfm-u32* *fn-cbor-max-uint*)
(defconst *cfm-u64* *fn-clock-max*)
(defconst *cfm-label* (coerce (make-list *fn-cfg-max-label* :initial-element #\z)
                              'string))
(defconst *cfm-label+1* (coerce (make-list (+ 1 *fn-cfg-max-label*)
                                           :initial-element #\z)
                                'string))
(defconst *cfm-stamp* (fn-clock-observation *cfm-u64* *cfm-u64* *cfm-u64* t))
(defconst *cfm-row* (fn-cfg-row-make *cfm-label* *cfm-label* *cfm-label* *cfm-u32*))
(defconst *cfm-delta*
  (fn-cfg-delta-make :account-delete *cfm-label* *cfm-label* *cfm-u32*
                     (list *cfm-row*)))

(defmacro cfm-round-trips (r)
  `(and (fn-cfg-recordp ,r)
        (equal (fn-cfg-decode-exact (fn-cfg-encode ,r))
               (fn-record-parse-ok ,r nil))))

; Every scalar and every label at its maximum, the last kind code.
(defconst *cfm-max*
  (fn-cfg-record-make *cfm-u32* *cfm-u32* *cfm-u32* (list *cfm-delta*) *cfm-stamp*))
(assert-event (equal (fn-cfg-kind-code :account-delete) 27))
(assert-event (cfm-round-trips *cfm-max*))

; The stamp at its maximum without a wall claim.
(assert-event
 (cfm-round-trips
  (fn-cfg-record-make 0 0 1 (list *cfm-delta*)
                      (fn-clock-observation *cfm-u64* *cfm-u64* *cfm-u64* nil))))

; The delta count at its maximum.
(defconst *cfm-64*
  (fn-cfg-record-make 1 1 2 (make-list *fn-cfg-max-deltas*
                                       :initial-element (fn-cfg-remove-group "g"))
                      *cfm-stamp*))
(assert-event (cfm-round-trips *cfm-64*))

; The rows of one delta at their maximum (short labels: at 256 octets each,
; 1,024 rows are far past the record's octet ceiling).
(defconst *cfm-1024*
  (fn-cfg-record-make 1 1 2
                      (list (fn-cfg-delta-make
                             :set-peers "" "" *cfm-u32*
                             (make-list *fn-cfg-max-rows*
                                        :initial-element
                                        (fn-cfg-row-make "a" "b" "c" *cfm-u32*))))
                      *cfm-stamp*))
(assert-event (cfm-round-trips *cfm-1024*))

; One past each maximum: never a record, and the codec refuses it by name.
(defmacro cfm-refused (r)
  `(and (not (fn-cfg-recordp ,r))
        (not (fn-record-parse-okp (fn-cfg-decode-exact (fn-cfg-encode ,r))))))
(assert-event (cfm-refused (fn-cfg-record-make (+ 1 *cfm-u32*) 0 1 (list *cfm-delta*)
                                               *cfm-stamp*)))
(assert-event (cfm-refused (fn-cfg-record-make 0 (+ 1 *cfm-u32*) 1 (list *cfm-delta*)
                                               *cfm-stamp*)))
(assert-event (cfm-refused (fn-cfg-record-make 0 0 (+ 1 *cfm-u32*) (list *cfm-delta*)
                                               *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make 0 0 1 (list (fn-cfg-delta-make
                                               :account-delete *cfm-label+1* "" 0 nil))
                                  *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make 0 0 1 (list (fn-cfg-delta-make
                                               :account-delete "" "" (+ 1 *cfm-u32*) nil))
                                  *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make
               0 0 1 (list (fn-cfg-delta-make
                            :set-peers "" "" 0
                            (list (fn-cfg-row-make "" "" *cfm-label+1* 0))))
               *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make
               0 0 1 (list (fn-cfg-delta-make
                            :set-peers "" "" 0
                            (list (fn-cfg-row-make "" "" "" (+ 1 *cfm-u32*)))))
               *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make 1 1 2 (make-list (+ 1 *fn-cfg-max-deltas*)
                                                   :initial-element
                                                   (fn-cfg-remove-group "g"))
                                  *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make
               1 1 2 (list (fn-cfg-delta-make
                            :set-peers "" "" 0
                            (make-list (+ 1 *fn-cfg-max-rows*)
                                       :initial-element (fn-cfg-row-make "a" "b" "c" 0))))
               *cfm-stamp*)))
; A stamp time past 2^64 - 1 is no clock time, so no record stamp.
(assert-event
 (not (fn-cfg-recordp (fn-cfg-record-make 0 0 1 (list *cfm-delta*)
                                          (fn-clock-observation (+ 1 *cfm-u64*) 0 0 t)))))
(assert-event (not (fn-cfg-deltap (fn-cfg-delta-make :no-such-kind "" "" 0 nil))))

; GAP witness (labelled; the open item above): a record whose every field is
; within its maximum encodes past *fn-cfg-max-octets* and does not decode.
; When admission bounds the encoding, this record stops being acceptable;
; until then it is a recognized record the codec cannot carry.
(defconst *cfm-gap*
  (fn-cfg-record-make 1 1 2
                      (list (fn-cfg-delta-make :set-peers "" "" 0
                                               (make-list 100 :initial-element
                                                          *cfm-row*)))
                      *cfm-stamp*))
(assert-event
 (and (fn-cfg-recordp *cfm-gap*)
      (< *fn-cfg-max-octets* (len (fn-cfg-encode *cfm-gap*)))
      (equal (fn-cfg-decode-exact (fn-cfg-encode *cfm-gap*))
             (fn-record-parse-error :limit))))
