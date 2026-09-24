/* Bounded ION sender with an observed, real BP bundle ID.
 *
 * Built against the pinned ION bpP.h: the public bp_send API returns a
 * bundle object only for a detained source SAP. The object is read while
 * detained, then released. stdout is emitted only after both operations.
 * ION transport submission is not fn application acceptance or a receipt.
 */
#include "bpP.h"
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#define FN_MAX_ADU 65538
#define FN_MAX_EID 255

/* ION's file ZCO stores a pathname and inode, not the ADU bytes. Freeze a
 * private source before bp_send; ION unlinks it only after its final file-ref
 * user is gone. The caller retains its original durable ADU for retry. */
static int stage_source(const char *input, const char *observation,
                        char *source, size_t source_size, off_t *length)
{
    char directory[PATH_MAX], buffer[8192];
    char *slash;
    struct stat st;
    int in = -1, out = -1, dirfd = -1, ok = -1;
    ssize_t n;
    off_t copied = 0;

    if (snprintf(source, source_size, "%s.source", observation) >= (int) source_size ||
        strlen(source) > 255 ||
        snprintf(directory, sizeof directory, "%s", source) >= (int) sizeof directory)
        return -1;
    slash = strrchr(directory, '/');
    if (!slash) return -1;
    if (slash == directory) slash[1] = '\0'; else *slash = '\0';
    dirfd = open(directory, O_RDONLY | O_DIRECTORY | O_NOFOLLOW);
    if (dirfd < 0 || fstat(dirfd, &st) < 0 || !S_ISDIR(st.st_mode) ||
        st.st_uid != geteuid() || (st.st_mode & 077) != 0)
        goto done;
    in = open(input, O_RDONLY | O_NOFOLLOW);
    if (in < 0 || fstat(in, &st) < 0 || !S_ISREG(st.st_mode) ||
        st.st_size < 1 || st.st_size > FN_MAX_ADU)
        goto done;
    *length = st.st_size;
    out = open(source, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW, 0600);
    if (out < 0) goto done;
    while (copied < *length) {
        size_t want = (size_t) (*length - copied);
        if (want > sizeof buffer) want = sizeof buffer;
        n = read(in, buffer, want);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) goto done;
        for (ssize_t offset = 0; offset < n;) {
            ssize_t written = write(out, buffer + offset, (size_t) (n - offset));
            if (written < 0 && errno == EINTR) continue;
            if (written <= 0) goto done;
            offset += written;
        }
        copied += n;
    }
    if (fsync(out) < 0 || fsync(dirfd) < 0) goto done;
    ok = 0;
done:
    if (out >= 0) close(out);
    if (in >= 0) close(in);
    if (dirfd >= 0) close(dirfd);
    if (ok < 0 && out >= 0) unlink(source);
    return ok;
}

static int decimal_ttl(const char *text, int *ttl)
{
    char *end = NULL;
    long value;
    errno = 0;
    value = strtol(text, &end, 10);
    if (errno || end == text || *end || value < 1 || value > INT_MAX / 1000)
        return -1;
    *ttl = (int) value;
    return 0;
}

/* Publish a complete observation without overwriting any prior attempt.
 * ION itself writes to stdout, so stdout cannot be a framed machine API. */
static int publish_observation(const char *path, const char *line)
{
    char tmp[PATH_MAX], dir[PATH_MAX];
    char *slash;
    size_t left = strlen(line);
    const char *cursor = line;
    int fd = -1, dirfd = -1, ok = -1;
    if (strlen(path) > PATH_MAX - 48 ||
        snprintf(tmp, sizeof tmp, "%s.tmp.%ld", path, (long) getpid()) >= (int) sizeof tmp)
        return -1;
    if (snprintf(dir, sizeof dir, "%s", path) >= (int) sizeof dir) return -1;
    slash = strrchr(dir, '/');
    if (!slash) return -1;
    if (slash == dir) slash[1] = '\0'; else *slash = '\0';
    fd = open(tmp, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW, 0600);
    if (fd < 0) return -1;
    while (left) {
        ssize_t n = write(fd, cursor, left);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) goto done;
        cursor += n; left -= (size_t) n;
    }
    if (fsync(fd) < 0) goto done;
    if (close(fd) < 0) { fd = -1; goto done; }
    fd = -1;
    if (link(tmp, path) < 0) goto done;
    dirfd = open(dir, O_RDONLY | O_DIRECTORY);
    if (dirfd < 0 || fsync(dirfd) < 0) goto done;
    ok = 0;
done:
    if (dirfd >= 0) close(dirfd);
    if (fd >= 0) close(fd);
    unlink(tmp);
    return ok;
}

int main(int argc, char **argv)
{
    const char *own, *destination, *application_peer, *path, *observation_path;
    char source_path[PATH_MAX];
    off_t source_length = 0;
    BpSAP sap = NULL;
    Sdr sdr;
    SdrObject file_ref = 0, adu = 0, bundle_obj = 0;
    Bundle bundle;
    char *source = NULL;
    char line[1024];
    int ttl, entered_send = 0, send_returned_success = 0, result = 1;

    if (argc != 7 || decimal_ttl(argv[5], &ttl) < 0) {
        fprintf(stderr, "usage: fn_ltp_send OWN_EID BP_DEST_EID APP_PEER_EID ADU_FILE TTL_SECONDS OBSERVATION_OUT\n");
        return 5;
    }
    own = argv[1]; destination = argv[2]; application_peer = argv[3];
    path = argv[4]; observation_path = argv[6];
    if (!*own || !*destination || !*application_peer ||
        strlen(own) > FN_MAX_EID || strlen(destination) > FN_MAX_EID ||
        strlen(application_peer) > FN_MAX_EID ||
        strchr(own, '\n') || strchr(destination, '\n') ||
        strchr(application_peer, '\n') || strchr(own, '|') ||
        strchr(destination, '|') || strchr(application_peer, '|') ||
        access(observation_path, F_OK) == 0) {
        fprintf(stderr, "refused bounded LTP send inputs\n");
        return 1;
    }
    if (stage_source(path, observation_path, source_path,
                     sizeof source_path, &source_length) < 0) {
        fprintf(stderr, "refused durable ION source staging\n");
        return 1;
    }
    if (bp_attach() < 0) {
        fprintf(stderr, "ION source endpoint unavailable\n");
        unlink(source_path);
        return 1;
    }
    if (bp_open_source((char *) own, &sap, 1) < 0) {
        fprintf(stderr, "ION source endpoint unavailable\n");
        bp_detach();
        unlink(source_path);
        return 1;
    }
    sdr = bp_get_sdr();
    if (sdr_begin_xn(sdr) < 0) goto done;
    file_ref = zco_create_file_ref(sdr, source_path, "", ZcoOutbound);
    if (sdr_end_xn(sdr) < 0 || !file_ref) goto done;
    adu = ionCreateZco(ZcoFileSource, file_ref, 0, source_length,
                       BP_STD_PRIORITY, 0, ZcoOutbound, NULL);
    if (!adu || adu == (SdrObject) ERROR) goto done;
    /* Once bp_send is called, even an error return cannot prove that no
     * transport work was committed. The fn attempt remains recoverable. */
    result = 3;
    entered_send = 1;
    if (bp_send(sap, (char *) destination, NULL, ttl, BP_STD_PRIORITY,
                NoCustodyRequested, 0, 0, NULL, adu, &bundle_obj) <= 0)
        goto done;
    send_returned_success = 1;
    if (!bundle_obj || sdr_begin_xn(sdr) < 0) goto done;
    memset(&bundle, 0, sizeof bundle);
    sdr_read(sdr, (char *) &bundle, bundle_obj, sizeof bundle);
    readEid(&bundle.id.source, &source);
    if (sdr_end_xn(sdr) < 0 || !source || !*source ||
        strlen(source) > FN_MAX_EID || strchr(source, '|') ||
        strchr(source, '\n') || bundle.id.fragmentOffset != 0)
        goto done;
    /* Release detention only after the RFC 9171 ID fields are copied. */
    if (bp_release(bundle_obj) < 0) goto done;
    bundle_obj = 0;
    int line_len = snprintf(line, sizeof line,
                 "observed-v1|%s|%s|%s|" UVAST_FIELDSPEC "|%u\n",
                 application_peer, destination, source,
                 bundle.id.creationTime.msec,
                 bundle.id.creationTime.count);
    if (line_len < 0 || line_len >= (int) sizeof line)
        goto done;
    if (publish_observation(observation_path, line) < 0) goto done;
    result = 0;

done:
    if (result != 0)
        fprintf(stderr, "%s ION send%s\n",
                result == 3 ? "uncertain" : "refused",
                result == 3 ? "; fn attempt requires recovery" : "");
    if (send_returned_success && bundle_obj) bp_release(bundle_obj);
    /* bpSend may fail at its final SDR commit after the bundle was inserted.
     * No return value after entry proves this ZCO is still caller-owned. */
    if (!entered_send && adu && adu != (SdrObject) ERROR && sdr_begin_xn(sdr) >= 0) {
        zco_destroy(sdr, adu);
        sdr_end_xn(sdr);
    }
    if (file_ref && sdr_begin_xn(sdr) >= 0) {
        zco_destroy_file_ref(sdr, file_ref);
        sdr_end_xn(sdr);
    }
    if (!entered_send && !file_ref) unlink(source_path);
    if (source) MRELEASE(source);
    if (sap) bp_close(sap);
    bp_detach();
    return result;
}
