/*
*  SQLCIPHER_SPECK
*
*  Author: vertigo (github.com/vertigo6622)
*  License: BSD-3-Clause license 
*
*  * SQLCipher SPECK 128/256 CTR Provider
*  * Self-contained crypto provider using SPECK 128/256 in CTR mode 
*  * SHA-256 based HMAC and PBKDF2
*
*/
#ifdef SQLITE_HAS_CODEC
#ifdef SQLCIPHER_CRYPTO_CUSTOM

#include "sqliteInt.h"
#include "sqlcipher.h"
#include <string.h>
#include <stdlib.h>
#include <stdint.h>

/* ========================================================================
 * SPECK 128/256 CORE
 * Block size: 128 bits, Key size: 256 bits, Rounds: 34
 * ======================================================================== */

#define SPECK128_256_ROUNDS 34
#define SPECK128_BLOCK_SZ   16
#define SPECK128_KEY_SZ     32
#define SPECK128_IV_SZ      16

static uint64_t rol64(uint64_t x, int r) {
    return (x << r) | (x >> (64 - r));
}

static uint64_t ror64(uint64_t x, int r) {
    return (x >> r) | (x << (64 - r));
}

static void speck128_256_key_schedule(const uint64_t key[4], uint64_t rk[SPECK128_256_ROUNDS]) {
    uint64_t b[3];
    rk[0] = key[0];
    b[0] = key[1];
    b[1] = key[2];
    b[2] = key[3];
    for (int i = 0; i < SPECK128_256_ROUNDS - 1; i++) {
        int idx = i % 3;
        b[idx] = ror64(b[idx], 8) + rk[i];
        b[idx] ^= (uint64_t)i;
        rk[i + 1] = rol64(rk[i], 3) ^ b[idx];
    }
}

static void speck128_encrypt_block(uint64_t *x, uint64_t *y, const uint64_t rk[SPECK128_256_ROUNDS]) {
    for (int i = 0; i < SPECK128_256_ROUNDS; i++) {
        *x = ror64(*x, 8) + *y;
        *x ^= rk[i];
        *y = rol64(*y, 3) ^ *x;
    }
}

static void speck128_ctr(const uint64_t rk[SPECK128_256_ROUNDS],
                         const unsigned char *iv,
                         const unsigned char *in, int in_sz,
                         unsigned char *out) {
    uint64_t counter = 0;
    unsigned char keystream[SPECK128_BLOCK_SZ];

    for (int i = 0; i < in_sz; i += SPECK128_BLOCK_SZ) {
        uint64_t b0, b1;
        memcpy(&b0, iv, 8);
        memcpy(&b1, iv + 8, 8);
        b1 ^= counter;
        counter++;

        speck128_encrypt_block(&b0, &b1, rk);

        memcpy(keystream, &b0, 8);
        memcpy(keystream + 8, &b1, 8);

        int remaining = in_sz - i;
        int chunk = remaining < SPECK128_BLOCK_SZ ? remaining : SPECK128_BLOCK_SZ;
        for (int j = 0; j < chunk; j++) {
            out[i + j] = in[i + j] ^ keystream[j];
        }
    }
}

/* ========================================================================
 * SHA-256 (self-contained implementation)
 * ======================================================================== */

static const uint32_t sha256_k[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

typedef struct {
    uint32_t state[8];
    uint64_t bitcount;
    unsigned char buffer[64];
    uint32_t buflen;
} sha256_ctx;

static void sha256_init(sha256_ctx *ctx) {
    ctx->state[0] = 0x6a09e667;
    ctx->state[1] = 0xbb67ae85;
    ctx->state[2] = 0x3c6ef372;
    ctx->state[3] = 0xa54ff53a;
    ctx->state[4] = 0x510e527f;
    ctx->state[5] = 0x9b05688c;
    ctx->state[6] = 0x1f83d9ab;
    ctx->state[7] = 0x5be0cd19;
    ctx->bitcount = 0;
    ctx->buflen = 0;
}

#define SHA256_ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))
#define SHA256_CH(x, y, z) (((x) & (y)) ^ (~(x) & (z)))
#define SHA256_MAJ(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define SHA256_SIGMA0(x) (SHA256_ROTR(x, 2) ^ SHA256_ROTR(x, 13) ^ SHA256_ROTR(x, 22))
#define SHA256_SIGMA1(x) (SHA256_ROTR(x, 6) ^ SHA256_ROTR(x, 11) ^ SHA256_ROTR(x, 25))
#define SHA256_sigma0(x) (SHA256_ROTR(x, 7) ^ SHA256_ROTR(x, 18) ^ ((x) >> 3))
#define SHA256_sigma1(x) (SHA256_ROTR(x, 17) ^ SHA256_ROTR(x, 19) ^ ((x) >> 10))

static void sha256_transform(sha256_ctx *ctx, const unsigned char block[64]) {
    uint32_t w[64];
    uint32_t a, b, c, d, e, f, g, h, t1, t2;

    for (int i = 0; i < 16; i++) {
        w[i] = ((uint32_t)block[i * 4] << 24) |
               ((uint32_t)block[i * 4 + 1] << 16) |
               ((uint32_t)block[i * 4 + 2] << 8) |
               ((uint32_t)block[i * 4 + 3]);
    }
    for (int i = 16; i < 64; i++) {
        w[i] = SHA256_sigma1(w[i - 2]) + w[i - 7] + SHA256_sigma0(w[i - 15]) + w[i - 16];
    }

    a = ctx->state[0]; b = ctx->state[1]; c = ctx->state[2]; d = ctx->state[3];
    e = ctx->state[4]; f = ctx->state[5]; g = ctx->state[6]; h = ctx->state[7];

    for (int i = 0; i < 64; i++) {
        t1 = h + SHA256_SIGMA1(e) + SHA256_CH(e, f, g) + sha256_k[i] + w[i];
        t2 = SHA256_SIGMA0(a) + SHA256_MAJ(a, b, c);
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }

    ctx->state[0] += a; ctx->state[1] += b; ctx->state[2] += c; ctx->state[3] += d;
    ctx->state[4] += e; ctx->state[5] += f; ctx->state[6] += g; ctx->state[7] += h;
}

static void sha256_update(sha256_ctx *ctx, const unsigned char *data, uint32_t len) {
    uint32_t i = 0;
    ctx->bitcount += (uint64_t)len * 8;

    if (ctx->buflen > 0) {
        uint32_t needed = 64 - ctx->buflen;
        if (len < needed) {
            memcpy(ctx->buffer + ctx->buflen, data, len);
            ctx->buflen += len;
            return;
        }
        memcpy(ctx->buffer + ctx->buflen, data, needed);
        sha256_transform(ctx, ctx->buffer);
        i = needed;
        ctx->buflen = 0;
    }

    for (; i + 64 <= len; i += 64) {
        sha256_transform(ctx, data + i);
    }

    if (i < len) {
        ctx->buflen = len - i;
        memcpy(ctx->buffer, data + i, ctx->buflen);
    }
}

static void sha256_final(sha256_ctx *ctx, unsigned char hash[32]) {
    ctx->buffer[ctx->buflen] = 0x80;
    ctx->buflen++;

    if (ctx->buflen > 56) {
        memset(ctx->buffer + ctx->buflen, 0, 64 - ctx->buflen);
        sha256_transform(ctx, ctx->buffer);
        memset(ctx->buffer, 0, 56);
    } else {
        memset(ctx->buffer + ctx->buflen, 0, 56 - ctx->buflen);
    }

    uint64_t bits = ctx->bitcount;
    ctx->buffer[56] = (unsigned char)(bits >> 56);
    ctx->buffer[57] = (unsigned char)(bits >> 48);
    ctx->buffer[58] = (unsigned char)(bits >> 40);
    ctx->buffer[59] = (unsigned char)(bits >> 32);
    ctx->buffer[60] = (unsigned char)(bits >> 24);
    ctx->buffer[61] = (unsigned char)(bits >> 16);
    ctx->buffer[62] = (unsigned char)(bits >> 8);
    ctx->buffer[63] = (unsigned char)(bits);
    sha256_transform(ctx, ctx->buffer);

    for (int i = 0; i < 8; i++) {
        hash[i * 4]     = (unsigned char)(ctx->state[i] >> 24);
        hash[i * 4 + 1] = (unsigned char)(ctx->state[i] >> 16);
        hash[i * 4 + 2] = (unsigned char)(ctx->state[i] >> 8);
        hash[i * 4 + 3] = (unsigned char)(ctx->state[i]);
    }
}

static void sha256_hash(const unsigned char *data, uint32_t len, unsigned char hash[32]) {
    sha256_ctx ctx;
    sha256_init(&ctx);
    sha256_update(&ctx, data, len);
    sha256_final(&ctx, hash);
}

/* ========================================================================
 * HMAC-SHA-256
 * ======================================================================== */

#define HMAC_BLOCK_SZ 64

static void hmac_sha256(const unsigned char *key, int key_sz,
                        const unsigned char *in, int in_sz,
                        const unsigned char *in2, int in2_sz,
                        unsigned char out[32]) {
    unsigned char k_pad[HMAC_BLOCK_SZ];
    unsigned char tk[32];
    sha256_ctx ctx;

    if ((unsigned int)key_sz > HMAC_BLOCK_SZ) {
        sha256_hash(key, key_sz, tk);
        key = tk;
        key_sz = 32;
    }

    memset(k_pad, 0x36, HMAC_BLOCK_SZ);
    for (int i = 0; i < key_sz; i++) k_pad[i] ^= key[i];

    sha256_init(&ctx);
    sha256_update(&ctx, k_pad, HMAC_BLOCK_SZ);
    sha256_update(&ctx, in, in_sz);
    if (in2 != NULL && in2_sz > 0) sha256_update(&ctx, in2, in2_sz);
    sha256_final(&ctx, out);

    memset(k_pad, 0x5c, HMAC_BLOCK_SZ);
    for (int i = 0; i < key_sz; i++) k_pad[i] ^= key[i];

    sha256_init(&ctx);
    sha256_update(&ctx, k_pad, HMAC_BLOCK_SZ);
    sha256_update(&ctx, out, 32);
    sha256_final(&ctx, out);
}

/* ========================================================================
 * PBKDF2-HMAC-SHA-256
 * ======================================================================== */

static void pbkdf2_hmac_sha256(const unsigned char *pass, int pass_sz,
                               const unsigned char *salt, int salt_sz,
                               int iterations, int key_sz,
                               unsigned char *key) {
    int block_count = (key_sz + 31) / 32;
    unsigned char *salt_i = (unsigned char *)sqlcipher_malloc(salt_sz + 4);
    if (salt_i == NULL) return;
    memcpy(salt_i, salt, salt_sz);

    for (int i = 1; i <= block_count; i++) {
        unsigned char u[32], t[32];
        salt_i[salt_sz]     = (unsigned char)(i >> 24);
        salt_i[salt_sz + 1] = (unsigned char)(i >> 16);
        salt_i[salt_sz + 2] = (unsigned char)(i >> 8);
        salt_i[salt_sz + 3] = (unsigned char)(i);

        hmac_sha256(pass, pass_sz, salt_i, salt_sz + 4, NULL, 0, u);
        memcpy(t, u, 32);

        for (int j = 1; j < iterations; j++) {
            hmac_sha256(pass, pass_sz, u, 32, NULL, 0, u);
            for (int k = 0; k < 32; k++) t[k] ^= u[k];
        }

        int offset = (i - 1) * 32;
        int to_copy = key_sz - offset;
        if (to_copy > 32) to_copy = 32;
        memcpy(key + offset, t, to_copy);
    }

    sqlcipher_free(salt_i, salt_sz + 4);
}

/* ========================================================================
 * CSPRNG (platform random source)
 * ======================================================================== */

static int speck_random(void *ctx, void *buffer, int length) {
    unsigned char *buf = (unsigned char *)buffer;
#if defined(__APPLE__) && defined(__MACH__)
    arc4random_buf(buf, length);
    return SQLITE_OK;
#elif defined(__linux__)
    FILE *f = fopen("/dev/urandom", "rb");
    if (!f) return SQLITE_ERROR;
    if (fread(buf, 1, length, f) != (size_t)length) {
        fclose(f);
        return SQLITE_ERROR;
    }
    fclose(f);
    return SQLITE_OK;
#else
    arc4random_buf(buf, length);
    return SQLITE_OK;
#endif
}

static int speck_add_random(void *ctx, const void *buffer, int length) {
    return SQLITE_OK;
}

/* ========================================================================
 * PROVIDER CONTEXT
 * ======================================================================== */

typedef struct {
    uint64_t round_keys[SPECK128_256_ROUNDS];
} speck_prov_ctx;

static int speck_ctx_init(void **ctx) {
    speck_prov_ctx *c = (speck_prov_ctx *)sqlcipher_malloc(sizeof(speck_prov_ctx));
    if (c == NULL) return SQLITE_NOMEM;
    memset(c, 0, sizeof(speck_prov_ctx));
    *ctx = c;
    return SQLITE_OK;
}

static int speck_ctx_free(void **ctx) {
    if (*ctx) {
        speck_prov_ctx *c = (speck_prov_ctx *)*ctx;
        sqlcipher_memset(c, 0, sizeof(speck_prov_ctx));
        sqlcipher_free(*ctx, sizeof(speck_prov_ctx));
        *ctx = NULL;
    }
    return SQLITE_OK;
}

/* ========================================================================
 * SQLCIPHER PROVIDER CALLBACKS
 * ======================================================================== */

static const char *speck_get_provider_name(void *ctx) {
    return "speck";
}

static const char *speck_get_provider_version(void *ctx) {
    return "1.0.0";
}

static const char *speck_get_cipher(void *ctx) {
    return "speck-128-256-ctr";
}

static int speck_get_key_sz(void *ctx) {
    return SPECK128_KEY_SZ;
}

static int speck_get_iv_sz(void *ctx) {
    return SPECK128_IV_SZ;
}

static int speck_get_block_sz(void *ctx) {
    return SPECK128_BLOCK_SZ;
}

static int speck_get_hmac_sz(void *ctx, int algorithm) {
    switch (algorithm) {
        case SQLCIPHER_HMAC_SHA1:   return 20;
        case SQLCIPHER_HMAC_SHA256: return 32;
        case SQLCIPHER_HMAC_SHA512: return 64;
        default: return 0;
    }
}

static int speck_fips_status(void *ctx) {
    return 0;
}

static int speck_hmac(void *ctx, int algorithm,
                      const unsigned char *hmac_key, int key_sz,
                      const unsigned char *in, int in_sz,
                      const unsigned char *in2, int in2_sz,
                      unsigned char *out) {
    if (algorithm == SQLCIPHER_HMAC_SHA256) {
        hmac_sha256(hmac_key, key_sz, in, in_sz, in2, in2_sz, out);
        return SQLITE_OK;
    }
    sqlcipher_log(SQLCIPHER_LOG_ERROR, SQLCIPHER_LOG_PROVIDER,
                  "speck_hmac: unsupported algorithm %d", algorithm);
    return SQLITE_ERROR;
}

static int speck_kdf(void *ctx, int algorithm,
                     const unsigned char *pass, int pass_sz,
                     const unsigned char *salt, int salt_sz,
                     int workfactor,
                     int key_sz, unsigned char *key) {
    if (algorithm == SQLCIPHER_PBKDF2_HMAC_SHA256) {
        pbkdf2_hmac_sha256(pass, pass_sz, salt, salt_sz, workfactor, key_sz, key);
        return SQLITE_OK;
    }
    sqlcipher_log(SQLCIPHER_LOG_ERROR, SQLCIPHER_LOG_PROVIDER,
                  "speck_kdf: unsupported algorithm %d", algorithm);
    return SQLITE_ERROR;
}

static int speck_cipher(void *ctx, int mode,
                        const unsigned char *key, int key_sz,
                        const unsigned char *iv,
                        const unsigned char *in, int in_sz,
                        unsigned char *out) {
    speck_prov_ctx *c = (speck_prov_ctx *)ctx;
    uint64_t k[4];

    if (key_sz != SPECK128_KEY_SZ) {
        sqlcipher_log(SQLCIPHER_LOG_ERROR, SQLCIPHER_LOG_PROVIDER,
                      "speck_cipher: invalid key size %d, expected %d", key_sz, SPECK128_KEY_SZ);
        return SQLITE_ERROR;
    }

    memcpy(k, key, SPECK128_KEY_SZ);
    speck128_256_key_schedule(k, c->round_keys);
    sqlcipher_memset(k, 0, sizeof(k));

    speck128_ctr(c->round_keys, iv, in, in_sz, out);
    return SQLITE_OK;
}

/* ========================================================================
 * PROVIDER REGISTRATION
 * ======================================================================== */

int speck_register_provider(sqlcipher_provider *p) {
    p->init = NULL;
    p->shutdown = NULL;
    p->get_provider_name = speck_get_provider_name;
    p->get_provider_version = speck_get_provider_version;
    p->add_random = speck_add_random;
    p->random = speck_random;
    p->hmac = speck_hmac;
    p->kdf = speck_kdf;
    p->cipher = speck_cipher;
    p->get_cipher = speck_get_cipher;
    p->get_key_sz = speck_get_key_sz;
    p->get_iv_sz = speck_get_iv_sz;
    p->get_block_sz = speck_get_block_sz;
    p->get_hmac_sz = speck_get_hmac_sz;
    p->ctx_init = speck_ctx_init;
    p->ctx_free = speck_ctx_free;
    p->fips_status = speck_fips_status;
    return SQLITE_OK;
}

#endif
#endif
