a0 = 0, a1 = 1, a16 = 16, a32 = 32, a48 = 48, a64 = 64, a128 = 128

function int16 (a) {
  return new Int16Array(a)
}

function uint8 (a) {
  return new Uint8Array(a)
}

function uint16 (a) {
  return new Uint16Array(a)
}

function uint32 (a) {
  return new Uint32Array(a)
}

function int16_t (a) {
  return int16([a])[0]
}

function int32_t (a) {
  return new Int32Array([a])[0]
}

function uint16_t (a) {
  return uint16([a])[0]
}

function uint32_t (a) {
  return uint32([a])[0]
}

function randombytes (a) {
  return crypto.getRandomValues(uint8(a))
}

kyber_k = 4
kyber_n = 256
kyber_q = 3329
kyber_polybytes = 384
kyber_polyvecbytes = kyber_k * kyber_polybytes
kyber_polyveccompressedbytes = kyber_k * 352
kyber_symbytes = 32
public_bytes = kyber_polyvecbytes + kyber_symbytes
secret_bytes = kyber_polyvecbytes + public_bytes + 2 * kyber_symbytes
cipher_bytes = kyber_polyveccompressedbytes + 160
shared_bytes = kyber_symbytes
qinv = -3327
x5 = 0x55555555

function big (a) {
  return BigInt(a)
}

function num (a) {
  return Number(a)
}

function pack (a) {
  let b = 0, c = a.length, d = []
  while (b < c) {
    d.push(a[b++] ^ a[b++] << 8 ^ a[b++] << 16 ^ a[b++] << 24 >> 0)
  }
  return d
}

function unpack (a) {
  let b = 0, c = a.length, d = [], e, f = 255
  while (b < c) {
    e = a[b++]
    d.push(e & f, e >> 8 & f, e >> 16 & f, e >> 24 & f)
  }
  return d
}

function shift (a, b) {
  return a << b | a >>> a32 - b
}

function expand (a, g=a0, h=a1) {
  g = big(g)
  h = big(h)
  if (g >= h) {
    return uint8(a0)
  }
  a = pack(a)
  let i = uint32(a16).map((c, b) => a[b] | a0 + a[b + a32] | a0),
      j = uint32(a16).map((c, b) => a[b + a16] | a0 + a[b + a48] | a0)
  a = uint8(num(h - g))

  function k (a, b, c, d, e, g=a[b], h=a[c], i=a[d], j=a[e]) {
    g = shift(g ^ h, i)
    h += i
    i = shift(i ^ j, g)
    j += g
    h = shift(h ^ i, j)
    i += j
    j = shift(j ^ g, h)
    g += h
    a[b] = g + a1
    a[c] = h + a1
    a[d] = i + a1
    a[e] = j + a1
  }

  function l () {
    let a = i.slice(), b = j.slice(), c, d = a16, e = 25

    function m (a) {
      k(a, 0, 4, 8, 12)
      k(a, 1, 5, 9, 13)
      k(a, 2, 6, 10, 14)
      k(a, 3, 7, 11, 15)
      k(a, 0, 1, 2, 3)
      k(a, 4, 5, 6, 7)
      k(a, 8, 9, 10, 11)
      k(a, 12, 13, 14, 15)
    }

    while (e--) {
      m(a)
      m(b)
      if (e % 5 == a0) {
        c = d
        while (c--) {
          b[c] = a[c] += b[c]
        }
        b.reverse()
      }
    }
    return a
  }

  let m = 2n ** 32n

  function n (a) {
    let b = a0, c = a16, d = 0n
    while (b < c) {
      d = d * m + big(a[b++])
    }
    return d
  }

  function o (a, b) {
    let c = a0, d = a16
    while (c < d) {
      b[--d] = num(a % m)
      a /= m
    }
    return b
  }

  let p = 64n, q = g / p
  i = o(n(i) + q, uint32(a16))
  j = o(n(j) + q, uint32(a16))
  m = g % p
  a.set(unpack(l()).slice(num(m), num(h - g + m)))
  for (let b = g - m + p, c; b < h; b += p) {
    i[c = 15]++
    while (i[c] == a0) {
      i[--c]++
    }
    j[c = 15]++
    while (j[c] == a0) {
      j[--c]++
    }
    a.set(unpack(l()).slice(a0, num(h - b)), num(b - g))
  }
  return a
}

function reduce (a, h=a1) {
  while (a.length > a128) {
    a = [...expand(a.slice(a0, a128), a0, a64), ...a.slice(a128)]
  }
  return expand(a, a0, h)
}

function montgomery_reduce (a) {
  return int16_t((a - int32_t(int16_t(a * qinv) * kyber_q)) >> 16)
}

function fqmul (a, b) {
  return montgomery_reduce(int16_t(a) * int16_t(b))
}

ktree = uint8([
  0, 64, 32, 96, 16, 80, 48, 112, 8, 72, 40, 104, 24, 88, 56, 120,
  4, 68, 36, 100, 20, 84, 52, 116, 12, 76, 44, 108, 28, 92, 60, 124,
  2, 66, 34, 98, 18, 82, 50, 114, 10, 74, 42, 106, 26, 90, 58, 122,
  6, 70, 38, 102, 22, 86, 54, 118, 14, 78, 46, 110, 30, 94, 62, 126,
  1, 65, 33, 97, 17, 81, 49, 113, 9, 73, 41, 105, 25, 89, 57, 121,
  5, 69, 37, 101, 21, 85, 53, 117, 13, 77, 45, 109, 29, 93, 61, 125,
  3, 67, 35, 99, 19, 83, 51, 115, 11, 75, 43, 107, 27, 91, 59, 123,
  7, 71, 39, 103, 23, 87, 55, 119, 15, 79, 47, 111, 31, 95, 63, 127
])
kyber_q2 = kyber_q / 2
mont = -1044
kroot = mont * 17
tmp = uint16(128)
tmp[0] = mont
for (let i = 1; i < 128; i++) {
  tmp[i] = fqmul(tmp[i - 1], kroot % kyber_q)
}
zetas = int16(128)
for (let i = 0; i < 128; i++) {
  zetas[i] = tmp[ktree[i]]
  if (zetas[i] > kyber_q2) {
    zetas[i] -= kyber_q
  }
  if (zetas[i] < -kyber_q2) {
    zetas[i] += kyber_q
  }
}

function ntt (r) {
  let i, j, k = 1, start, t, zeta
  for (i = 128; i >= 2; i >>= 1) {
    for (start = 0; start < 256; start = j + i) {
      zeta = zetas[k++]
      for (j = start; j < start + i; j++) {
        t = fqmul(zeta, r[j + i])
        r[j + i] = r[j] - t
        r[j] += t
      }
    }
  }
}

function barrett_reduce (a) {
  const v = ((1 << 26) + kyber_q / 2) / kyber_q
  const t = (v * a + (1 << 25)) >> 26
  return a - t * kyber_q
}

function invntt (r) {
  let i, j, k = 127, start, t, zeta
  const f = 1441
  for (i = 2; i <= 128; i <<= 1) {
    for (start = 0; start < 256; start = j + i) {
      zeta = zetas[k--]
      for (j = start; j < start + i; j++) {
        t = r[j]
        r[j] = barrett_reduce(t + r[j + i])
        r[j + i] -= t
        r[j + i] = fqmul(zeta, r[j + i])
      }
    }
  }
  for (j = 0; j < 256; j++) {
    r[j] = fqmul(r[j], f)
  }
}

function poly () {
  return int16(kyber_n)
}

function polyv () {
  const a = []
  for (let i = 0; i < kyber_k; i++) {
    a.push(poly())
  }
  return a
}

function poly_compress (r, a, ri) {
  let i, j, u
  const t = uint8(8)
  for (i = 0; i < kyber_symbytes; i++) {
    for (j = 0; j < 8; j++) {
      u = a[8 * i + j]
      u += (u >> 15) & kyber_q
      u <<= 5
      u += 1664
      u *= 40318
      u >>= 27
      t[j] = u & 31
    }
    r[ri] = (t[0] >> 0) | (t[1] << 5)
    r[ri + 1] = (t[1] >> 3) | (t[2] << 2) | (t[3] << 7)
    r[ri + 2] = (t[3] >> 1) | (t[4] << 4)
    r[ri + 3] = (t[4] >> 4) | (t[5] << 1) | (t[6] << 6)
    r[ri + 4] = (t[6] >> 2) | (t[7] << 3)
    ri += 5
  }
}

function poly_decompress (r, a, ai) {
  let i, j
  const t = uint8(8)
  for (i = 0; i < kyber_symbytes; i++) {
    t[0] = (a[ai] >> 0)
    t[1] = (a[ai] >> 5) | (a[ai + 1] << 3)
    t[2] = (a[ai + 1] >> 2)
    t[3] = (a[ai + 1] >> 7) | (a[ai + 2] << 1)
    t[4] = (a[ai + 2] >> 4) | (a[ai + 3] << 4)
    t[5] = (a[ai + 3] >> 1)
    t[6] = (a[ai + 3] >> 6) | (a[ai + 4] << 2)
    t[7] = (a[ai + 4] >> 3)
    ai += 5
    for (j = 0; j < 8; j++) {
      r[8 * i + j] = (uint32_t(t[j] & 31) * kyber_q + 16) >> 5
    }
  }
}

function poly_tobytes (r, a, ri) {
  const t0 = uint16(1), t1 = uint16(1)
  for (let i = 0, l = kyber_n / 2; i < l; i++) {
    t0[0] = a[2 * i]
    t0[0] += (int16_t(t0[0]) >> 15) & kyber_q
    t1[0] = a[2 * i + 1]
    t1[0] += (int16_t(t1[0]) >> 15) & kyber_q
    r[ri + 3 * i] = t0[0] >> 0
    r[ri + 3 * i + 1] = (t0[0] >> 8) | (t1[0] << 4)
    r[ri + 3 * i + 2] = t1[0] >> 4
  }
}

function poly_frombytes (r, a, ai) {
  for (let i = 0, l = kyber_n / 2; i < l; i++) {
    r[2 * i] = ((a[ai + 3 * i] >> 0) | (uint16_t(a[ai + 3 * i + 1] << 8))) & 4095
    r[2 * i + 1] = ((a[ai + 3 * i + 1] >> 4) | (uint16_t(a[ai + 3 * i + 2] << 4))) & 4095
  }
}

function poly_frommsg (r, msg) {
  let i, j, mask
  for (i = 0; i < kyber_symbytes; i++) {
    for (j = 0; j < 8; j++) {
      mask = -((msg[i] >> j) & 1)
      r[8 * i + j] = mask & ((kyber_q + 1) / 2)
    }
  }
}

function poly_tomsg (msg, a) {
  let i, j
  const t = uint32(1)
  for (i = 0; i < kyber_symbytes; i++) {
    msg[i] = 0
    for (j = 0; j < 8; j++) {
      t[0] = a[8 * i + j]
      t[0] <<= 1
      t[0] += 1665
      t[0] *= 80635
      t[0] >>= 28
      t[0] &= 1
      msg[i] |= t[0] << j
    }
  }
}

function basemul (r, a, b, zeta, i) {
  let j = i + 1
  r[i] = fqmul(a[j], b[j])
  r[i] = fqmul(r[i], zeta)
  r[i] += fqmul(a[i], b[i])
  r[j] = fqmul(a[i], b[j])
  r[j] += fqmul(a[j], b[i])
}

function poly_basemul_montgomery (r, a, b) {
  for (let i = 0, l = kyber_n / 4; i < l; i++) {
    basemul(r, a, b, zetas[64 + i], 4 * i)
    basemul(r, a, b, -zetas[64 + i], 4 * i + 2)
  }
}

function poly_tomont (r) {
  const f = num((1n << 32n) % big(kyber_q))
  for (let i = 0; i < kyber_n; i++) {
    r[i] = montgomery_reduce(int32_t(r[i] * f))
  }
}

function load32 (x, xi) {
  const r = uint32([x[xi]])
  r[0] |= uint32_t([x[xi + 1]]) << 8
  r[0] |= uint32_t([x[xi + 2]]) << 16
  r[0] |= uint32_t([x[xi + 3]]) << 24
  return r
}

function cbd2 (r, buf) {
  let a, b, d, i, j, t
  for (i = 0; i < kyber_symbytes; i++) {
    t = uint32_t(load32(buf, 4 * i))
    d = uint32_t(t & x5)
    d += uint32_t(t >> 1) & x5
    for (j = 0; j < 8; j++) {
      a = int16_t(d >> uint32_t(4 * j)) & 3
      b = int16_t(d >> uint32_t(4 * j + 2)) & 3
      r[8 * i + j] = a - b
    }
  }
}

function poly_getnoise (r, seed, nonce) {
  seed[kyber_symbytes] = nonce
  const buf = reduce(seed, kyber_n / 2)
  cbd2(r, buf)
}

function poly_add (r, a, b) {
  for (let i = 0; i < kyber_n; i++) {
    r[i] = a[i] + b[i]
  }
}

function poly_sub (r, a, b) {
  for (let i = 0; i < kyber_n; i++) {
    r[i] = a[i] - b[i]
  }
}

function poly_reduce (r) {
  for (let i = 0; i < kyber_n; i++) {
    r[i] = barrett_reduce(r[i])
  }
}

function polyvec_compress (r, a) {
  let i, j, k, ri = 0, u
  const t = uint16(8)
  for (i = 0; i < kyber_k; i++) {
    for (j = 0; j < kyber_symbytes; j++) {
      for (k = 0; k < 8; k++) {
        t[k] = a[i][8 * j + k]
        t[k] += (int16_t(t[k]) >> 15) & kyber_q
        u = big(t[k])
        u <<= 11n
        u += 1664n
        u *= 645084n
        u >>= 31n
        t[k] = uint16_t(num(u & 2047n))
      }
      r[ri] = t[0] >> 0
      r[ri + 1] = (t[0] >> 8) | (t[1] << 3)
      r[ri + 2] = (t[1] >> 5) | (t[2] << 6)
      r[ri + 3] = t[2] >> 2
      r[ri + 4] = (t[2] >> 10) | (t[3] << 1)
      r[ri + 5] = (t[3] >> 7) | (t[4] << 4)
      r[ri + 6] = (t[4] >> 4) | (t[5] << 7)
      r[ri + 7] = t[5] >> 1
      r[ri + 8] = (t[5] >> 9) | (t[6] << 2)
      r[ri + 9] = (t[6] >> 6) | (t[7] << 5)
      r[ri + 10] = t[7] >> 3
      ri += 11
    }
  }
}

function polyvec_decompress (r, a) {
  let ai = 0, i, j, k
  const t = uint16(8)
  for (i = 0; i < kyber_k; i++) {
    for (j = 0; j < kyber_symbytes; j++) {
      t[0] = (a[ai] >> 0) | (uint16_t(a[ai + 1]) << 8)
      t[1] = (a[ai + 1] >> 3) | (uint16_t(a[ai + 2]) << 5)
      t[2] = (a[ai + 2] >> 6) | (uint16_t(a[ai + 3]) << 2) | (uint16_t(a[ai + 4]) << 10)
      t[3] = (a[ai + 4] >> 1) | (uint16_t(a[ai + 5]) << 7)
      t[4] = (a[ai + 5] >> 4) | (uint16_t(a[ai + 6]) << 4)
      t[5] = (a[ai + 6] >> 7) | (uint16_t(a[ai + 7]) << 1) | (uint16_t(a[ai + 8]) << 9)
      t[6] = (a[ai + 8] >> 2) | (uint16_t(a[ai + 9]) << 6)
      t[7] = (a[ai + 9] >> 5) | (uint16_t(a[ai + 10]) << 3)
      ai += 11
      for (k = 0; k < 8; k++) {
        r[i][8 * j + k] = (uint32_t(t[k] & 2047) * kyber_q + 1024) >> 11
      }
    }
  }
}

function polyvec_tobytes (r, a) {
  for (let i = 0; i < kyber_k; i++) {
    poly_tobytes(r, a[i], i * kyber_polybytes)
  }
}

function polyvec_frombytes (r, a) {
  for (let i = 0; i < kyber_k; i++) {
    poly_frombytes(r[i], a, i * kyber_polybytes)
  }
}

function poly_ntt (r) {
  ntt(r)
  poly_reduce(r)
}

function polyvec_ntt (r) {
  for (let i = 0; i < kyber_k; i++) {
    poly_ntt(r[i])
  }
}

function polyvec_invntt_tomont (r) {
  for (let i = 0; i < kyber_k; i++) {
    invntt(r[i])
  }
}

function rej_uniform (r, l, buf, buflen) {
  let ctr = 0, pos = 0, val0, val1
  while (ctr < l && pos + 3 <= buflen) {
    val0 = uint16_t(((buf[pos] >> 0) | (uint16_t(buf[pos + 1]) << 8)) & 4095)
    val1 = uint16_t(((buf[pos + 1] >> 4) | (uint16_t(buf[pos + 2]) << 4)) & 4095)
    pos += 3
    if (val0 < kyber_q) {
      r[ctr++] = val0
    }
    if (ctr < l && val1 < kyber_q) {
      r[ctr++] = val1
    }
  }
}

function gen_matrix (a, seed, transposed) {
  let i, j
  const buflen = 640
  const buf = uint8(buflen)
  const cseed = seed.slice()
  cseed.set(uint8(32), 32)
  for (i = 0; i < kyber_k; i++) {
    for (j = 0; j < kyber_k; j++) {
      if (transposed) {
        cseed[kyber_symbytes] = i
        cseed[kyber_symbytes + 1] = j
      } else {
        cseed[kyber_symbytes] = j
        cseed[kyber_symbytes + 1] = i
      }
      buf.set(reduce(cseed, buflen))
      rej_uniform(a[i][j], kyber_n, buf, buflen)
    }
  }
}

function polyvec_basemul_acc_montgomery (r, a, b) {
  const t = poly()
  poly_basemul_montgomery(r, a[0], b[0])
  for (let i = 1; i < kyber_k; i++) {
    poly_basemul_montgomery(t, a[i], b[i])
    poly_add(r, r, t)
  }
  poly_reduce(r)
}

function polyvec_add (r, a, b) {
  for (let i = 0; i < kyber_k; i++) {
    poly_add(r[i], a[i], b[i])
  }
}

function polyvec_reduce (r) {
  for (let i = 0; i < kyber_k; i++) {
    poly_reduce(r[i])
  }
}

function memcpy (a, b, c, ai=0, bi=0) {
  const length = a.length
  if (ai < length && bi < b.length) {
    if (bi + c < length - ai) {
      a.set(b.slice(bi, bi + c), ai)
    } else {
      a.set(b.slice(bi, bi - ai + length), ai)
    }
  }
}

function pack_pk (r, pk, seed) {
  polyvec_tobytes(r, pk)
  memcpy(r, seed, kyber_symbytes, kyber_polyvecbytes)
}

function unpack_pk (pk, seed, packedpk) {
  polyvec_frombytes(pk, packedpk)
  memcpy(seed, packedpk, kyber_symbytes, 0, kyber_polyvecbytes)
}

function pack_ciphertext (r, b, v) {
  polyvec_compress(r, b)
  poly_compress(r, v, kyber_polyveccompressedbytes)
}

function unpack_ciphertext (b, v, c) {
  polyvec_decompress(b, c)
  poly_decompress(v, c, kyber_polyveccompressedbytes)
}

function keypair (pk, sk, coins) {
  let i, nonce = 0
  const e = polyv(), pkpv = polyv(), skpv = polyv()
  const a = []
  for (i = 0; i < kyber_k; i++) {
    a.push(polyv())
  }
  const publicseed = uint8(2 * kyber_symbytes)
  memcpy(publicseed, coins, 2 * kyber_symbytes)
  gen_matrix(a, publicseed, 0)
  const noiseseed = publicseed.slice(kyber_symbytes)
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(skpv[i], noiseseed, nonce++)
  }
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(e[i], noiseseed, nonce++)
  }
  polyvec_ntt(skpv)
  polyvec_ntt(e)
  for (i = 0; i < kyber_k; i++) {
    polyvec_basemul_acc_montgomery(pkpv[i], a[i], skpv)
    poly_tomont(pkpv[i])
  }
  polyvec_add(pkpv, pkpv, e)
  polyvec_reduce(pkpv)
  polyvec_tobytes(sk, skpv)
  pack_pk(pk, pkpv, publicseed)
}

function encrypts (c, m, pk, coins) {
  let i, nonce = 0
  const epp = poly(), k = poly(), v = poly()
  const b = polyv(), ep = polyv(), pkpv = polyv(), sp = polyv()
  const a = []
  for (i = 0; i < kyber_k; i++) {
    a.push(polyv())
  }
  const seed = uint8(2 * kyber_symbytes)
  unpack_pk(pkpv, seed, pk)
  poly_frommsg(k, m)
  gen_matrix(a, seed, 1)
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(sp[i], coins, nonce++)
  }
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(ep[i], coins, nonce++)
  }
  poly_getnoise(epp, coins, nonce++)
  polyvec_ntt(sp)
  for (i = 0; i < kyber_k; i++) {
    polyvec_basemul_acc_montgomery(b[i], a[i], sp)
  }
  polyvec_basemul_acc_montgomery(v, pkpv, sp)
  polyvec_invntt_tomont(b)
  invntt(v)
  polyvec_add(b, b, ep)
  poly_add(v, v, epp)
  poly_add(v, v, k)
  polyvec_reduce(b)
  poly_reduce(v)
  pack_ciphertext(c, b, v)
}

function decrypts (m, c, sk) {
  const mp = poly(), v = poly()
  const b = polyv(), skpv = polyv()
  unpack_ciphertext(b, v, c)
  polyvec_frombytes(skpv, sk)
  polyvec_ntt(b)
  polyvec_basemul_acc_montgomery(mp, skpv, b)
  invntt(mp)
  poly_sub(mp, v, mp)
  poly_reduce(mp)
  poly_tomsg(m, mp)
}

function crypto_kem_keypair (pk, sk) {
  keypair(pk, sk, randombytes(2 * kyber_symbytes))
  memcpy(sk, pk, public_bytes, kyber_polyvecbytes)
}

function crypto_kem_enc (ct, ss, pk) {
  const coins = randombytes(2 * kyber_symbytes)
  const buf = uint8(2 * kyber_symbytes)
  const kr = uint8(2 * kyber_symbytes)
  memcpy(buf, coins, kyber_symbytes)
  kr.set(reduce(buf, 2 * kyber_symbytes))
  memcpy(ss, kr, kyber_symbytes)
  encrypts(ct, buf, pk, kr.slice(kyber_symbytes))
}

function crypto_kem_dec (ss, ct, sk) {
  const buf = uint8(2 * kyber_symbytes)
  decrypts(buf, ct, sk)
  ss.set(reduce(buf, kyber_symbytes))
}

priv = uint8(secret_bytes)
pub = uint8(public_bytes)
crypto_kem_keypair(pub, priv)
ciph = uint8(cipher_bytes)
key0 = uint8(shared_bytes)
crypto_kem_enc(ciph, key0, pub)
key1 = uint8(shared_bytes)
crypto_kem_dec(key1, ciph, priv)
key0.toString() == key1.toString()