;;; tools/extract/hostio.scm -- the host primitives of an extracted program
;;; (lane extract-2): host/store-open-host.lisp's `fn-hx-' stubs and the
;;; durable-extent realizers (A-DURABLE-EXTENT), in the trust boundary beside
;;; runtime.scm.  Filesystem syscalls that decide nothing: every answer goes
;;; back to ACL2 as a value, and every refusal text is ACL2's or io.lisp's.
;;; A HANDLE is an index into one table of read-only descriptors held for the
;;; process's life (never closed, never reused: an unlinked segment stays
;;; readable); it is also the realizer's durable FILE id.
(foreign-declare "
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/file.h>
#ifdef __linux__
#include <sys/vfs.h>
#else
#include <sys/param.h>
#include <sys/mount.h>
#endif
static long fnx_lstat(const char *p, int want_size) {
  struct stat st;
  if (lstat(p, &st) != 0) return errno == ENOENT ? -1 : -2;
  if (want_size) return (long) st.st_size;
  if (S_ISREG(st.st_mode)) return 1;
  if (S_ISDIR(st.st_mode)) return 2;
  if (S_ISLNK(st.st_mode)) return 3;
  return 4;
}
static long fnx_open(const char *p) {
  int fd = open(p, O_RDONLY | O_NOFOLLOW);
  return fd < 0 ? -(long) errno : fd;
}
static long fnx_fsize(int fd) {
  struct stat st;
  if (fstat(fd, &st) != 0) return -1;
  return S_ISREG(st.st_mode) ? (long) st.st_size : -2;
}
static long fnx_pread(int fd, unsigned char *buf, size_t n, long off) {
  size_t done = 0;
  while (done < n) {
    ssize_t r = pread(fd, buf + done, n - done, off + (long) done);
    if (r > 0) done += (size_t) r;
    else if (r == 0) break;
    else if (errno == EINTR) continue;
    else return -1;
  }
  return (long) done;
}
static long fnx_pwrite(int fd, unsigned char *buf, size_t n, long off) {
  size_t done = 0;
  while (done < n) {
    ssize_t r = pwrite(fd, buf + done, n - done, off + (long) done);
    if (r > 0) done += (size_t) r;
    else if (r < 0 && errno == EINTR) continue;
    else return -1;
  }
  return (long) done;
}
static long fnx_lock_shared(const char *p) {
  int fd = open(p, O_RDONLY | O_NOFOLLOW);
  struct stat st;
  if (fd < 0) return -(long) errno;
  if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) { close(fd); return 1000000; }
  if (flock(fd, LOCK_SH | LOCK_NB) != 0) { close(fd); return 1000001; }
  return fd;
}
static long fnx_fsync_dir(const char *p) {
  int fd = open(p, O_RDONLY | O_DIRECTORY);
  if (fd < 0) return -(long) errno;
  if (fsync(fd) != 0) { int e = errno; close(fd); return -(long) e; }
  close(fd);
  return 0;
}
static int fnx_statfs(const char *p, unsigned char *buf) {
  memset(buf, 0, 4096);
  return statfs(p, (void *) buf) == 0 ? 0 : -1;
}
")

(define %lstat (foreign-lambda long "fnx_lstat" c-string int))
(define %open (foreign-lambda long "fnx_open" c-string))
(define %fsize (foreign-lambda long "fnx_fsize" int))
(define %pread (foreign-lambda* long ((int fd) (u8vector buf) (size_t n) (long off))
                 "C_return(fnx_pread(fd, buf, n, off));"))
(define %pwrite (foreign-lambda* long ((int fd) (u8vector buf) (size_t start) (size_t n) (long off))
                  "C_return(fnx_pwrite(fd, buf + start, n, off));"))
(define %lock-shared (foreign-lambda long "fnx_lock_shared" c-string))
(define %fsync-dir (foreign-lambda long "fnx_fsync_dir" c-string))
(define %statfs (foreign-lambda int "fnx_statfs" c-string u8vector))
(define %realpath (foreign-lambda* c-string* ((c-string p)) "C_return(realpath(p, NULL));"))
(define %opendir (foreign-lambda c-pointer "opendir" c-string))
(define %readdir-name
  (foreign-lambda* c-string ((c-pointer d))
    "struct dirent *e = readdir((DIR *) d); C_return(e ? e->d_name : NULL);"))
(define %closedir (foreign-lambda int "closedir" c-pointer))

(define kw-ok '|KEYWORD::OK|)
(define kw-error '|KEYWORD::ERROR|)

;; the handle table: handle -> (fd . path)
(define hx-handles (make-vector 16 #f))
(define hx-next 1)
(define (hx-register fd path)
  (when (fx>= hx-next (vector-length hx-handles))
    (set! hx-handles (vector-resize hx-handles (fx* 2 (vector-length hx-handles)) #f)))
  (vector-set! hx-handles hx-next (cons fd path))
  (set! hx-next (fx+ hx-next 1))
  (fx- hx-next 1))
(define (hx-fd h)
  (let ((e (and (fixnum? h) (fx> h 0) (fx< h hx-next) (vector-ref hx-handles h))))
    (if e (car e) (error (sprintf "arena-extent-read: no durable file ~a is registered" h)))))
(define (hx-path h) (let ((e (vector-ref hx-handles h))) (if e (cdr e) "?")))

(define (a-hx-lstat path)
  (let ((k (%lstat path 0)))
    (case k
      ((-1) (list '|KEYWORD::ABSENT|))
      ((1) (list '|KEYWORD::REGULAR| (%lstat path 1)))
      ((2) (list '|KEYWORD::DIRECTORY|))
      ((3) (list '|KEYWORD::SYMLINK|))
      (else (list '|KEYWORD::OTHER|)))))

(define (a-hx-list-dir path limit)
  (let ((d (%opendir path)))
    (if (not d)
        (list kw-error "opendir")
        (let loop ((names '()) (count 0))
          (let ((name (%readdir-name d)))
            (cond ((not name) (%closedir d) (list kw-ok (reverse names) '()))
                  ((or (string=? name ".") (string=? name "..")) (loop names count))
                  ((>= count limit) (%closedir d) (list kw-ok (reverse names) '|COMMON-LISP::T|))
                  (else (loop (cons name names) (fx+ count 1)))))))))

(define (a-hx-open path)
  (let ((fd (%open path)))
    (if (< fd 0)
        (list kw-error (- fd) "open")
        (let ((size (%fsize fd)))
          (cond ((= size -1) (list kw-error 0 "fstat"))
                ((= size -2) (list kw-ok (hx-register fd path) 0 '()))
                (else (list kw-ok (hx-register fd path) size '|COMMON-LISP::T|)))))))

(define (hx-pread-u8 h off n)
  (let* ((buf (make-u8vector n 0))
         (got (%pread (hx-fd h) buf n off)))
    (cond ((< got 0) #f)
          ((= got n) buf)
          (else (subu8vector buf 0 got)))))

(define (a-hx-pread h off n)
  (let ((buf (hx-pread-u8 h off n)))
    (if buf (list kw-ok (u8vector->list buf)) (list kw-error "pread"))))

;; the log walk's buffer (fn-octets-lg, foundation fn-octets$c: slot 0 the
;; array, slot 1 the fill) holds exactly the entry, as io.lisp sets it
(define (a-hx-fill h off n buf)
  (let ((v (if (eqv? n 0) (make-u8vector 0 0) (hx-pread-u8 h off n))))
    (if v
        (begin (vector-set! buf 0 v) (vector-set! buf 1 (u8vector-length v))
               (values (u8vector-length v) buf))
        (values -1 buf))))

(define (a-hx-lock-shared path)
  (let ((r (%lock-shared path)))
    (cond ((= r 1000000) '|KEYWORD::NOT-REGULAR|)
          ((= r 1000001) '|KEYWORD::LOCKED|)
          ;; the text is the image's fnn-os-error report (fnn-open names the path)
          ((< r 0) (list kw-error (- r) (hx-os-text (- r) path)))
          (else kw-ok))))

(define (a-hx-fsync-dir path)
  (if (= (%fsync-dir path) 0) kw-ok (list kw-error "fsync")))

(define (a-hx-statfs path)
  (let ((buf (make-u8vector 4096 0)))
    (if (= (%statfs path buf) 0) (u8vector->list buf) '())))

(define (a-hx-realpath path)
  (let ((r (%realpath path)))
    (if r (map char->integer (string->list r)) '())))

(define (a-hx-os)
  (cond-expand (linux '|KEYWORD::LINUX|) (openbsd '|KEYWORD::OPENBSD|)
               (macosx '|KEYWORD::DARWIN|) (else '|KEYWORD::OTHER|)))

(define (a-hx-warn text)
  (let ((port (current-error-port))) (display text port) (newline port) '()))

;; The page store's two byte primitives (host/native/proto-pagestore-io.lisp
;; fnps-fill-from-file / fnps-write-to-file): a u8vector range from or to a
;; file at a byte offset; a short read is end of file, refused by name.
(define %pread-at (foreign-lambda* long ((int fd) (u8vector buf) (size_t start) (size_t n) (long off))
                    "C_return(fnx_pread(fd, buf + start, n, off));"))
(define (a-hx-fill-from-file h byte-offset vec start count)
  (let ((got (%pread-at (hx-fd h) vec start count byte-offset)))
    (unless (= got count)
      (error (sprintf "pread: end of file at byte ~a" (+ byte-offset (max got 0)))))
    count))
(define (a-hx-write-to-file h byte-offset vec start count)
  (unless (= (%pwrite (hx-fd h) vec start count byte-offset) count)
    (error "pwrite failed"))
  count)

(define (remove-eq x l) (cond ((null? l) '()) ((eq? x (car l)) (cdr l)) (else (cons (car l) (remove-eq x (cdr l))))))

;; --- the durable-extent realizers (host/native/extent.lisp) -------------------
;; An entry's protected prefix and trailer read once (one pread), checked by
;; ACL2 (fn-arx-entry-ok-buffer over the realizer's buffer fn-octets-rd, its
;; array the octets read and its fill the prefix's length), kept in a cache
;; of ACL2's size (fn-arx-read-cache-entries), most recent first.  The two
;; ACL2 calls are the raw procedures: the image makes them through fnn-call
;; inside the outer entry's call, and both guards are T.
(define extent-cache '())
(define extent-rd #f)
(define (extent-entry file eoff elen)
  (let ((hit (let find ((c extent-cache))
               (cond ((null? c) #f)
                     ((and (eqv? (car (car c)) file) (eqv? (cadr (car c)) eoff)) (car c))
                     (else (find (cdr c)))))))
    (if hit
        (begin (unless (eq? hit (car extent-cache))
                 (set! extent-cache (cons hit (remove-eq hit extent-cache))))
               (cddr hit))
        (let* ((fd (hx-fd file))
               (octets (make-u8vector (+ elen 32) 0))
               (got (%pread fd octets (+ elen 32) eoff)))
          (unless (= got (+ elen 32))
            (error (sprintf "arena-extent-read: ~a at ~a holds fewer than ~a octets"
                            (hx-path file) eoff (+ elen 32))))
          (unless extent-rd (set! extent-rd (|f:ACL2::CREATE-FN-OCTETS$C|)))
          (vector-set! extent-rd 0 octets)
          (vector-set! extent-rd 1 elen)
          (let ((ok (call-with-values
                        (lambda () (|f:ACL2::FN-ARX-ENTRY-OK-BUFFER|
                                    (u8vector->list (subu8vector octets elen (+ elen 32))) extent-rd))
                      (lambda vs (car vs)))))
            (vector-set! extent-rd 1 0)
            (vector-set! extent-rd 0 (make-u8vector 0 0))
            (unless (eq? ok '|COMMON-LISP::T|)
              (error (sprintf "arena-extent-digest: the entry at ~a of ~a does not match its trailer"
                              eoff (hx-path file)))))
          (let ((limit (|f:ACL2::FN-ARX-READ-CACHE-ENTRIES|)))
            (when (> limit 0)
              (set! extent-cache (cons (cons file (cons eoff octets)) extent-cache))
              (when (> (length extent-cache) limit)
                (set! extent-cache (list-head extent-cache limit)))))
          octets))))
(define (a-durable-realize-octet file eoff elen poff plen trailer i)
  (u8vector-ref (extent-entry file eoff elen) (+ (- poff eoff) i)))
(define (a-durable-realize-octets file eoff elen poff plen trailer)
  (let ((entry (extent-entry file eoff elen)) (start (- poff eoff)))
    (let loop ((i (+ start plen -1)) (acc '()))
      (if (< i start) acc (loop (- i 1) (cons (u8vector-ref entry i) acc))))))

;; A-PGS-HOST-IO's page fill (host/native/extent.lisp fn-pgs-fill-realize):
;; the 2048 little-endian u64 words page ADDR of the page file FILE holds
;; (FILE a handle), one pread; a short read refused by name.  ACL2's digest
;; check decides whether they are the page the committed table names.
(define (a-pgs-fill-realize file addr)
  (let* ((buf (make-u8vector 16384 0))
         (got (%pread (hx-fd file) buf 16384 (* addr 16384))))
    (unless (= got 16384)
      (error (sprintf "history-page-read: page ~a of ~a: ~a of 16384 octets" addr (hx-path file) got)))
    (let loop ((k 2047) (acc '()))
      (if (< k 0)
          acc
          (loop (- k 1)
                (cons (let wl ((b 7) (w 0))
                        (if (< b 0) w (wl (- b 1) (+ (* w 256) (u8vector-ref buf (+ (* 8 k) b))))))
                      acc))))))

;; A-PGS-HOST-IO's frame fill (host/native/extent.lisp fn-pgs-fill-frame;
;; books/assumptions-pgs-host-io.lisp): the same page put IN PLACE into words
;; BASE.. of the pgs-mem array SEL selects (slot 0 pgs-w, 1 pgs-m, 2 pgs-t;
;; the u64 arrays are Scheme vectors here).  The oracle does what the
;; constraint says, the put of the page's words; the native host preads into
;; the array's storage.  Lane page-word-boundary, 2026-10-01.
(define (a-pgs-fill-frame file addr sel base pgs-mem)
  (let ((arr (vector-ref pgs-mem sel)))
    (unless (<= (+ base 2048) (vector-length arr))
      (error (sprintf "history-page-fill: selector ~a at word ~a is outside the page store (page ~a)" sel base addr)))
    (let loop ((k 0) (ws (a-pgs-fill-realize file addr)))
      (if (< k 2048)
          (begin (vector-set! arr (+ base k) (car ws)) (loop (+ k 1) (cdr ws)))
          pgs-mem))))

;; A-DURABLE-LZ's realizer (host/native/extent.lisp fn-durable-realize-lz):
;; the block read through the extent realizer (trailer checked), ACL2's
;; decoder fn-lzr-lz-read over it (called as the host calls it, through the
;; boundary), its octets answered; a failed decode refused by name.  The last
;; decoded payload is kept (key: file, entry, block, length; the dictionary by
;; identity), so an octet-by-octet reader decodes once.
(define extent-lz-last #f)
(define (a-durable-realize-lz file eoff elen poff plen trailer n dict)
  (let ((key (list file eoff poff plen n)))
    (if (and extent-lz-last (equal? (car extent-lz-last) key) (eq? (cadr extent-lz-last) dict))
        (cddr extent-lz-last)
        (let* ((c (a-durable-realize-octets file eoff elen poff plen trailer))
               (saved a-current-entry)
               (r (|b:ACL2::FN-LZR-LZ-READ| dict c n)))
          (set! a-current-entry saved)
          (unless (and (pair? r) (eq? (car r) '|KEYWORD::OK|))
            (error (sprintf "arena-extent-lz-decode: the block at ~a of ~a does not decode to its ~a octets"
                            poff (hx-path file) n)))
          (set! extent-lz-last (cons key (cons dict (cadr r))))
          (cadr r)))))

;;; --- the writable verbs' primitives (host/store-write-host.lisp; lane
;;; extract-writable) ---------------------------------------------------------
;;; A syscall's failure answers (:error ERRNO TEXT), TEXT exactly what io.lisp's
;;; fnn-os-error reports: "[Errno N] STRERROR", then ": 'PATH'" where io.lisp's
;;; fnn-posix names the path (open, lstat, unlink, mkdir, link and rename name
;;; it; a write, a barrier, a close and an allocation do not).  Read-write
;;; handles live in the handle table beside the read-only ones and are closed.
(import (chicken process-context) (chicken process-context posix) (chicken process signal)
        (chicken process) (chicken time))
(foreign-declare "
#include <stdio.h>
#include <time.h>
#include <sys/time.h>
static long fnx_open_flags(const char *p, int flags, int mode) {
  int fd = open(p, flags, mode);
  return fd < 0 ? -(long) errno : fd;
}
static long fnx_lock_ex(const char *p) {
  int fd = open(p, O_RDWR | O_CREAT | O_NOFOLLOW, 0600);
  struct stat st;
  if (fd < 0) return -(long) errno;
  if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) { close(fd); return 1000000; }
  if (flock(fd, LOCK_EX | LOCK_NB) != 0) { close(fd); return 1000001; }
  return fd;
}
static long fnx_lstat_full(const char *p, long *out) {
  struct stat st;
  if (lstat(p, &st) != 0) return errno == ENOENT ? -1 : -(long) errno - 10;
  out[0] = S_ISREG(st.st_mode) ? 1 : S_ISDIR(st.st_mode) ? 2 : S_ISLNK(st.st_mode) ? 3 : 4;
  out[1] = (long) st.st_size;
  out[2] = (long) st.st_mode;
  return 0;
}
static long fnx_write_at(int fd, unsigned char *buf, size_t n, long off, int positioned) {
  size_t done = 0;
  if (positioned && lseek(fd, off, SEEK_SET) < 0) return -(long) errno;
  while (done < n) {
    ssize_t r = write(fd, buf + done, n - done);
    if (r > 0) done += (size_t) r;
    else if (r < 0 && errno == EINTR) continue;
    else return r < 0 ? -(long) errno : -(long) EIO;
  }
  return 0;
}
static long fnx_read_at(int fd, unsigned char *buf, size_t n, long off) {
  size_t done = 0;
  if (lseek(fd, off, SEEK_SET) < 0) return -(long) errno;
  while (done < n) {
    ssize_t r = read(fd, buf + done, n - done);
    if (r > 0) done += (size_t) r;
    else if (r == 0) break;
    else if (errno == EINTR) continue;
    else return -(long) errno;
  }
  return (long) done;
}
static long fnx_datasync(int fd) {
#ifdef __linux__
  return fdatasync(fd) == 0 ? 0 : (long) errno;
#else
  return fsync(fd) == 0 ? 0 : (long) errno;
#endif
}
static long fnx_fsync(int fd) { return fsync(fd) == 0 ? 0 : (long) errno; }
static long fnx_prealloc(int fd, long from, long extent) {
#ifdef __linux__
  return (long) posix_fallocate(fd, from, extent - from);
#else
  static unsigned char zeros[65536];
  long at = from;
  if (lseek(fd, from, SEEK_SET) < 0) return (long) errno;
  while (at < extent) {
    long n = extent - at < 65536 ? extent - at : 65536;
    long r = fnx_write_at(fd, zeros, (size_t) n, 0, 0);
    if (r != 0) return -r;
    at += n;
  }
  return 0;
#endif
}
static long fnx_sync_dir(const char *p) {
  int fd = open(p, O_RDONLY | O_DIRECTORY);
  if (fd < 0) return -(long) errno;
  if (fsync(fd) != 0) { int e = errno; close(fd); return (long) e; }
  close(fd);
  return 0;
}
static long fnx_mono_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (long) ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}
static long fnx_tod(long *out) {
  struct timeval tv;
  gettimeofday(&tv, NULL);
  out[0] = (long) tv.tv_sec; out[1] = (long) tv.tv_usec;
  return 0;
}
int fn_lz4_compress_hc(const unsigned char *dict, int dict_len, const unsigned char *src, int src_len,
                       unsigned char *dst, int dst_cap, int level);
")

(define %open-flags (foreign-lambda long "fnx_open_flags" c-string int int))
(define %lock-ex (foreign-lambda long "fnx_lock_ex" c-string))
(define %lstat-full (foreign-lambda long "fnx_lstat_full" c-string s64vector))
(define %write-at (foreign-lambda* long ((int fd) (u8vector buf) (size_t n) (long off) (int pos))
                    "C_return(fnx_write_at(fd, buf, n, off, pos));"))
(define %read-at (foreign-lambda* long ((int fd) (u8vector buf) (size_t n) (long off))
                   "C_return(fnx_read_at(fd, buf, n, off));"))
(define %datasync (foreign-lambda long "fnx_datasync" int))
(define %fsync-fd (foreign-lambda long "fnx_fsync" int))
(define %prealloc (foreign-lambda long "fnx_prealloc" int long long))
(define %sync-dir (foreign-lambda long "fnx_sync_dir" c-string))
(define %close-fd (foreign-lambda* int ((int fd)) "C_return(close(fd) == 0 ? 0 : errno);"))
(define %unlock-close (foreign-lambda* int ((int fd)) "flock(fd, LOCK_UN); C_return(close(fd));"))
(define %strerror (foreign-lambda c-string "strerror" int))
(define %unlink (foreign-lambda* int ((c-string p)) "C_return(unlink(p) == 0 ? 0 : errno);"))
(define %mkdir (foreign-lambda* int ((c-string p)) "C_return(mkdir(p, 0700) == 0 ? 0 : errno);"))
(define %link (foreign-lambda* int ((c-string a) (c-string b)) "C_return(link(a, b) == 0 ? 0 : errno);"))
(define %rename (foreign-lambda* int ((c-string a) (c-string b)) "C_return(rename(a, b) == 0 ? 0 : errno);"))
(define %mono-ms (foreign-lambda long "fnx_mono_ms"))
(define %tod (foreign-lambda long "fnx_tod" s64vector))
(define %getcwd (foreign-lambda* c-string* () "C_return(getcwd(NULL, 0));"))
(define %lz4-hc
  (foreign-lambda* int ((u8vector src) (int start) (int n) (u8vector dst) (int cap))
    "C_return(fn_lz4_compress_hc((const unsigned char *) \"\", 0, src + start, n, dst, cap, 9));"))
(define o-rdonly (foreign-value "O_RDONLY" int))
(define o-rdwr (foreign-value "O_RDWR" int))
(define o-wronly (foreign-value "O_WRONLY" int))
(define o-creat (foreign-value "O_CREAT" int))
(define o-excl (foreign-value "O_EXCL" int))
(define o-nofollow (foreign-value "O_NOFOLLOW" int))

(define kw-absent '|KEYWORD::ABSENT|)
(define (hx-os-text errno path)
  (string-append "[Errno " (number->string errno) "] " (%strerror errno)
                 (if path (string-append ": '" path "'") "")))
(define (hx-err errno path) (list kw-error errno (hx-os-text errno path)))
(define (hx-bool x) (if x '|COMMON-LISP::T| '()))
(define (hx-status code path) (if (eqv? code 0) kw-ok (hx-err code path)))

(define (a-hx-getenv name) (or (get-environment-variable name) '()))
(define (a-hx-strerror errno) (%strerror errno))
(define (a-hx-kill-self) (process-signal (current-process-id) signal/kill) '())
(define (a-hx-out text)
  (let ((port (current-output-port))) (display text port) (newline port) (flush-output port) '()))
(define (a-hx-getpid) (current-process-id))
(define (a-hx-getcwd) (or (%getcwd) "."))

(define (a-hx-lock-exclusive path)
  (let ((r (%lock-ex path)))
    (cond ((= r 1000000) '|KEYWORD::NOT-REGULAR|)
          ((= r 1000001) '|KEYWORD::LOCKED|)
          ((< r 0) (hx-err (- r) path))
          (else (list kw-ok (hx-register r path))))))
(define (a-hx-unlock h) (%unlock-close (hx-fd h)) (vector-set! hx-handles h #f) kw-ok)

(define (hx-open-with path flags mode)
  (let ((fd (%open-flags path flags mode)))
    (if (< fd 0)
        (hx-err (- fd) path)
        (let ((size (%fsize fd)))
          (list kw-ok (hx-register fd path) (if (< size 0) 0 size))))))
(define (a-hx-open-rw path) (hx-open-with path (bitwise-ior o-rdwr o-nofollow) 0))
(define (a-hx-open-ro path) (hx-open-with path (bitwise-ior o-rdonly o-nofollow) 0))
(define (a-hx-create-excl path nofollow)
  (let ((fd (%open-flags path (bitwise-ior o-wronly o-creat o-excl (if (null? nofollow) 0 o-nofollow)) #o600)))
    (if (< fd 0) (hx-err (- fd) path) (list kw-ok (hx-register fd path)))))
(define (a-hx-close h)
  (let ((e (%close-fd (hx-fd h))))
    (vector-set! hx-handles h #f)
    (hx-status e #f)))

(define (hx-list->u8 l)
  (let ((v (make-u8vector (length l) 0)))
    (let loop ((l l) (i 0)) (if (null? l) v (begin (u8vector-set! v i (car l)) (loop (cdr l) (fx+ i 1)))))))
(define (a-hx-pwrite h off octets)
  (let ((v (hx-list->u8 octets)))
    (let ((r (%write-at (hx-fd h) v (u8vector-length v) off 1))) (if (= r 0) kw-ok (hx-err (- r) #f)))))
(define (a-hx-pwrite-zeros h off n)
  (let ((r (%write-at (hx-fd h) (make-u8vector n 0) n off 1))) (if (= r 0) kw-ok (hx-err (- r) #f))))
(define (a-hx-write-all h octets)
  (let* ((v (hx-list->u8 octets)) (r (%write-at (hx-fd h) v (u8vector-length v) 0 0)))
    (if (= r 0) kw-ok (hx-err (- r) #f))))
(define (a-hx-read-at h off n)
  (let* ((buf (make-u8vector n 0)) (r (%read-at (hx-fd h) buf n off)))
    (cond ((< r 0) (hx-err (- r) #f))
          (else (list kw-ok (u8vector->list (if (= r n) buf (subu8vector buf 0 r))))))))
(define (a-hx-fdatasync h) (hx-status (%datasync (hx-fd h)) #f))
(define (a-hx-fsync h) (hx-status (%fsync-fd (hx-fd h)) #f))
(define (a-hx-preallocate h from extent) (hx-status (%prealloc (hx-fd h) from extent) #f))
(define (a-hx-sync-dir path)
  (let ((r (%sync-dir path))) (cond ((= r 0) kw-ok) ((< r 0) (hx-err (- r) path)) (else (hx-err r #f)))))
(define (a-hx-unlink path) (hx-status (%unlink path) path))
(define (a-hx-mkdir path) (hx-status (%mkdir path) path))
(define (a-hx-link old new) (hx-status (%link old new) new))
(define (a-hx-rename old new) (hx-status (%rename old new) new))

(define (a-hx-lstat-full path)
  (let* ((out (make-s64vector 3 0)) (r (%lstat-full path out)))
    (cond ((= r -1) (list kw-absent))
          ((< r -1) (hx-err (- (+ r 10)) path))
          (else (list kw-ok
                      (case (s64vector-ref out 0)
                        ((1) '|KEYWORD::REGULAR|) ((2) '|KEYWORD::DIRECTORY|)
                        ((3) '|KEYWORD::SYMLINK|) (else '|KEYWORD::OTHER|))
                      (s64vector-ref out 1) (s64vector-ref out 2))))))

(define (hx-readdir path limit window)
  ;; (:ok NAMES MORE) in directory order; bounded: (:over) past LIMIT
  (let ((d (%opendir path)))
    (if (not d)
        (hx-err (foreign-value "errno" int) path)
        (let loop ((names '()) (count 0))
          (let ((name (%readdir-name d)))
            (cond ((not name) (%closedir d) (list kw-ok (reverse names) '()))
                  ((or (string=? name ".") (string=? name "..")) (loop names count))
                  ((>= count limit) (%closedir d)
                   (if window (list kw-ok (reverse names) '|COMMON-LISP::T|) (list '|KEYWORD::OVER|)))
                  (else (loop (cons name names) (fx+ count 1)))))))))
(define (a-hx-list-window path limit) (hx-readdir path limit #t))
(define (a-hx-list-bounded path limit) (hx-readdir path limit #f))

(define (a-hx-read-file path maximum)
  ;; fnn-read-regular-bounded
  (let ((fd (%open-flags path (bitwise-ior o-rdonly o-nofollow) 0)))
    (if (< fd 0)
        (hx-err (- fd) path)
        (let ((size (%fsize fd)))
          (cond ((= size -2) (%close-fd fd) (list '|KEYWORD::NON-REGULAR|))
                ((= size -1) (%close-fd fd) (hx-err 5 #f))
                ((> size maximum) (%close-fd fd) (list '|KEYWORD::OVERBOUND|))
                (else
                 (let* ((buf (make-u8vector (+ maximum 1) 0))
                        (r (%read-at fd buf (+ maximum 1) 0)))
                   (%close-fd fd)
                   (cond ((< r 0) (hx-err (- r) #f))
                         ((> r maximum) (list '|KEYWORD::GREW|))
                         (else (list kw-ok (u8vector->list (subu8vector buf 0 r))))))))))))

;; The environment readings, recorded when the developer selectors say so (as
;; the image's fnn-test-clock-readings and fnn-test-entropy read them).
(define (hx-digits? s) (and (> (string-length s) 0) (<= (string-length s) 18)
                            (let loop ((i 0)) (or (= i (string-length s))
                                                  (and (char-numeric? (string-ref s i)) (loop (+ i 1)))))))
(define (a-hx-clock)
  (let ((raw (get-environment-variable "FN_NATIVE_TEST_CLOCK")))
    (if raw
        (let ((words (string-split raw ":" #t)))
          (if (and (= (length words) 3) (hx-digits? (car words)) (hx-digits? (cadr words))
                   (hx-digits? (caddr words)))
              (map string->number words)
              (error "invalid FN_NATIVE_TEST_CLOCK (expected MONO-MS:SECONDS:MICROSECONDS)")))
        (let ((tod (make-s64vector 2 0)))
          (%tod tod)
          (list (%mono-ms) (s64vector-ref tod 0) (s64vector-ref tod 1))))))
(define hx-entropy-draws 0)
(define (a-hx-random-octets n)
  (let ((raw (get-environment-variable "FN_NATIVE_TEST_ENTROPY")))
    (if raw
        (let ((b (string->number raw)))
          (unless (and (hx-digits? raw) (<= (string-length raw) 3) b (< b 256))
            (error "invalid FN_NATIVE_TEST_ENTROPY (expected 0 to 255)"))
          (let ((k hx-entropy-draws))
            (set! hx-entropy-draws (+ k 1))
            (list kw-ok (let loop ((i (- n 1)) (acc '()))
                          (if (< i 0) acc (loop (- i 1) (cons (modulo (+ b (* 7 k) i) 256) acc)))))))
        (let ((fd (%open-flags "/dev/urandom" o-rdonly 0)))
          (if (< fd 0) (hx-err (- fd) "/dev/urandom")
              (let* ((buf (make-u8vector n 0)) (r (%read-at fd buf n 0)))
                (%close-fd fd)
                (if (= r n) (list kw-ok (u8vector->list buf))
                    (hx-err 5 #f))))))))
(define (a-hx-random-hex n)
  (let ((fd (%open-flags "/dev/urandom" o-rdonly 0)) (buf (make-u8vector n 0)))
    (when (>= fd 0) (%read-at fd buf n 0) (%close-fd fd))
    (apply string-append
           (map (lambda (b) (let ((s (number->string b 16))) (if (< b 16) (string-append "0" s) s)))
                (u8vector->list buf)))))

;; host/native/lz4.lisp fnn-lz4-candidate over the image's lib/libfn-lz4, the
;; empty dictionary (ID 0, ACL2's only one) at level 9 (+fnn-lz4-level+)
(define (a-hx-lz4-candidate src k n cap)
  (let* ((v (hx-list->u8 src)) (dst (make-u8vector cap 0)) (got (%lz4-hc v k n dst cap)))
    (cond ((> got 0) (u8vector->list (subu8vector dst 0 got)))
          ((= got 0) '|KEYWORD::NONE|)
          (else (list '|KEYWORD::CODE| got)))))
