/* Physical TLS primitive. No socket, NNTP, identity, admission or time policy.
 * Callers supply profile-sized BIO capacity and bounded byte spans. */
#include <limits.h>
#include <stddef.h>
#include <stdlib.h>
#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/ssl.h>

#if OPENSSL_VERSION_NUMBER < 0x30000000L
#error "fn2 TLS primitive requires OpenSSL 3"
#endif

/* ABI outcomes: progress, needs input, needs output, peer closed, failed. */
enum { FN2_TLS_OK, FN2_TLS_READ, FN2_TLS_WRITE, FN2_TLS_CLOSED, FN2_TLS_FAILED };
struct fn2_tls { SSL *ssl; BIO *wire; };

void *fn2_tls_config(const char *certificate, const char *key, int minimum_version)
{
    SSL_CTX *ctx;
    ERR_clear_error();
    ctx = SSL_CTX_new(TLS_server_method());
    if (!ctx) return NULL;
    if (!SSL_CTX_set_min_proto_version(ctx, minimum_version) ||
        SSL_CTX_use_certificate_chain_file(ctx, certificate) != 1 ||
        SSL_CTX_use_PrivateKey_file(ctx, key, SSL_FILETYPE_PEM) != 1 ||
        SSL_CTX_check_private_key(ctx) != 1) {
        SSL_CTX_free(ctx);
        return NULL;
    }
    /* This primitive provides server transport, not client-certificate login.
     * Renegotiation and early application data have no admitted machine state. */
    SSL_CTX_set_options(ctx, SSL_OP_NO_RENEGOTIATION);
    SSL_CTX_set_max_early_data(ctx, 0);
    SSL_CTX_set_session_cache_mode(ctx, SSL_SESS_CACHE_OFF);
    return ctx;
}

void fn2_tls_config_free(void *ctx) { SSL_CTX_free(ctx); }

void *fn2_tls_new(void *config, size_t capacity)
{
    struct fn2_tls *tls;
    BIO *inner = NULL, *wire = NULL;
    if (!config || !capacity || capacity > INT_MAX) return NULL;
    tls = calloc(1, sizeof(*tls));
    if (!tls) return NULL;
    ERR_clear_error();
    tls->ssl = SSL_new(config);
    if (!tls->ssl || BIO_new_bio_pair(&inner, capacity, &wire, capacity) != 1) {
        SSL_free(tls->ssl);
        free(tls);
        return NULL;
    }
    SSL_set_bio(tls->ssl, inner, inner); /* SSL owns inner; tls owns wire. */
    SSL_set_accept_state(tls->ssl);
    tls->wire = wire;
    return tls;
}

void fn2_tls_free(void *state)
{
    struct fn2_tls *tls = state;
    if (!tls) return;
    SSL_free(tls->ssl);
    BIO_free(tls->wire);
    free(tls);
}

static int fn2_tls_outcome(struct fn2_tls *tls, int result)
{
    switch (SSL_get_error(tls->ssl, result)) {
    case SSL_ERROR_WANT_READ: return FN2_TLS_READ;
    case SSL_ERROR_WANT_WRITE: return FN2_TLS_WRITE;
    case SSL_ERROR_ZERO_RETURN: return FN2_TLS_CLOSED;
    default: return FN2_TLS_FAILED;
    }
}

int fn2_tls_handshake(void *state)
{
    struct fn2_tls *tls = state;
    int result;
    if (!tls) return FN2_TLS_FAILED;
    ERR_clear_error();
    result = SSL_do_handshake(tls->ssl);
    return result == 1 ? FN2_TLS_OK : fn2_tls_outcome(tls, result);
}

/* Feed/drain never consume or produce more than the passed span; zero means
 * blocked. Negative means invalid input or a physical BIO failure. */
int fn2_tls_feed(void *state, const void *bytes, size_t length)
{
    struct fn2_tls *tls = state;
    int n;
    if (!tls || length > INT_MAX || (length && !bytes)) return -1;
    if (!length) return 0;
    n = BIO_write(tls->wire, bytes, (int)length);
    return n > 0 ? n : (BIO_should_retry(tls->wire) ? 0 : -1);
}
int fn2_tls_drain(void *state, void *bytes, size_t length)
{
    struct fn2_tls *tls = state;
    int n;
    if (!tls || length > INT_MAX || (length && !bytes)) return -1;
    if (!length) return 0;
    n = BIO_read(tls->wire, bytes, (int)length);
    return n > 0 ? n : (BIO_should_retry(tls->wire) ? 0 : -1);
}
size_t fn2_tls_output_pending(void *state)
{
    struct fn2_tls *tls = state;
    return tls ? BIO_ctrl_pending(tls->wire) : 0;
}
size_t fn2_tls_input_room(void *state)
{
    struct fn2_tls *tls = state;
    return tls ? BIO_ctrl_get_write_guarantee(tls->wire) : 0;
}

int fn2_tls_read(void *state, void *bytes, size_t length, size_t *count)
{
    struct fn2_tls *tls = state;
    int n;
    if (!count) return FN2_TLS_FAILED;
    *count = 0;
    if (!tls || !bytes || !length || length > INT_MAX) return FN2_TLS_FAILED;
    ERR_clear_error();
    n = SSL_read(tls->ssl, bytes, (int)length);
    if (n <= 0) return fn2_tls_outcome(tls, n);
    *count = (size_t)n;
    return FN2_TLS_OK;
}
int fn2_tls_write(void *state, const void *bytes, size_t length, size_t *count)
{
    struct fn2_tls *tls = state;
    int n;
    if (!count) return FN2_TLS_FAILED;
    *count = 0;
    if (!tls || !bytes || !length || length > INT_MAX) return FN2_TLS_FAILED;
    ERR_clear_error();
    n = SSL_write(tls->ssl, bytes, (int)length);
    if (n <= 0) return fn2_tls_outcome(tls, n);
    *count = (size_t)n;
    return FN2_TLS_OK;
}
