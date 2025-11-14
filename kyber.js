a0 = 0, a1 = 1, a16 = 16, a32 = 32, a48 = 48, a64 = 64, a128 = 128

function big (a) {
  return BigInt(a)
}

function num (a) {
  return Number(a)
}

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
kyber_poly = 384
kyber_polyvec = kyber_k * kyber_poly
kyber_vec = kyber_k * 352
kyber_sym = 32
kyber_sym2 = 2 * kyber_sym
public_bytes = kyber_polyvec + kyber_sym
secret_bytes = kyber_polyvec + public_bytes + kyber_sym2
cipher_bytes = kyber_vec + 160
shared_bytes = kyber_sym
qinv = -3327
x5 = 0x55555555

function pack (a) {
  let b = 0, c = a.length, d = []
  while (b < c) {
    d.push(a[b++] ^ a[b++] << 8 ^ a[b++] << 16 ^ a[b++] << 24)
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

  const p = 64n, q = g / p
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

function br7 (a) {
  a = [0, a >> 5 & 1, a >> 4 & 1, a >> 3 & 1, a >> 2 & 1, a >> 1 & 1, a & 1]
  let b = 0
  return a[b++] ^ a[b++] << 1 ^ a[b++] << 2 ^ a[b++] << 3 ^ a[b++] << 4 ^ a[b++] << 5 ^ a[b++] << 6
}

function get_zetas () {
  const ktree = uint8(128)
  let i = 0
  while (i < 64) {
    ktree[i] = br7(i++)
  }
  while (i < 128) {
    ktree[i] = br7(i++) + 1
  }
  const kyber_q2 = kyber_q / 2
  const mont = -1044
  const kroot = 17 * mont % kyber_q
  const tmp = uint16(128)
  tmp[0] = mont
  for (i = 1; i < 128; i++) {
    tmp[i] = fqmul(tmp[i - 1], kroot)
  }
  const zetas = int16(128)
  for (i = 0; i < 128; i++) {
    zetas[i] = tmp[ktree[i]]
    if (zetas[i] > kyber_q2) {
      zetas[i] -= kyber_q
    }
    if (zetas[i] < -kyber_q2) {
      zetas[i] += kyber_q
    }
  }
  return zetas
}

zetas = get_zetas()

function ntt (r) {
  let i, j, k = 1, l, s, t, z
  for (i = 128; i >= 2; i >>= 1) {
    for (s = 0; s < 256; s = j + i) {
      z = zetas[k++]
      for (j = s; j < s + i; j++) {
        t = fqmul(z, r[l = i + j])
        r[l] = r[j] - t
        r[j] += t
      }
    }
  }
}

function barrett_reduce (a) {
  let t = ((1 << 26) + kyber_q / 2) / kyber_q
  t = (t * a + (1 << 25)) >> 26
  return a - t * kyber_q
}

function invntt (r) {
  let i, j, k = 127, l, s, t, z
  for (i = 2; i <= 128; i <<= 1) {
    for (s = 0; s < 256; s = j + i) {
      z = zetas[k--]
      for (j = s, l; j < s + i; j++) {
        t = r[j]
        r[j] = barrett_reduce(t + r[l = i + j])
        r[l] -= t
        r[l] = fqmul(z, r[l])
      }
    }
  }
  for (j = 0; j < 256; j++) {
    r[j] = fqmul(r[j], 1441)
  }
}

function poly () {
  return int16(kyber_n)
}

function polyvec () {
  const a = []
  for (let i = 0; i < kyber_k; i++) {
    a.push(poly())
  }
  return a
}

function poly_compress (r, a, ri) {
  const t = uint8(8)
  for (let h, i = 0, j, u; i < kyber_sym; i++) {
    for (h = 8 * i, j = 0; j < 8; j++) {
      u = a[h + j]
      u += (u >> 15) & kyber_q
      u <<= 5
      u += 1664
      u *= 40318
      u >>= 27
      t[j] = u & 31
    }
    r[ri++] = (t[0] >> 0) | (t[1] << 5)
    r[ri++] = (t[1] >> 3) | (t[2] << 2) | (t[3] << 7)
    r[ri++] = (t[3] >> 1) | (t[4] << 4)
    r[ri++] = (t[4] >> 4) | (t[5] << 1) | (t[6] << 6)
    r[ri++] = (t[6] >> 2) | (t[7] << 3)
  }
}

function poly_decompress (r, a, ai) {
  const t = uint8(8)
  for (let h, i = 0, j; i < kyber_sym; i++) {
    t[0] = (a[ai] >> 0)
    t[1] = (a[ai++] >> 5) | (a[ai] << 3)
    t[2] = (a[ai] >> 2)
    t[3] = (a[ai++] >> 7) | (a[ai] << 1)
    t[4] = (a[ai++] >> 4) | (a[ai] << 4)
    t[5] = (a[ai] >> 1)
    t[6] = (a[ai++] >> 6) | (a[ai] << 2)
    t[7] = (a[ai++] >> 3)
    for (h = 8 * i, j = 0; j < 8; j++) {
      r[h + j] = (uint32_t(t[j] & 31) * kyber_q + 16) >> 5
    }
  }
}

function poly_tobytes (r, a, ri) {
  const t = uint16(1), u = uint16(1)
  for (let i = 0, j, l = kyber_n / 2; i < l; i++) {
    j = i + i
    t[0] = a[j]
    t[0] += (int16_t(t[0]) >> 15) & kyber_q
    u[0] = a[j + 1]
    u[0] += (int16_t(u[0]) >> 15) & kyber_q
    j += i
    r[ri + j] = t[0] >> 0
    r[ri + j + 1] = (t[0] >> 8) | (u[0] << 4)
    r[ri + j + 2] = u[0] >> 4
  }
}

function poly_frombytes (r, a, ai) {
  for (let i = 0, j, k, l = kyber_n / 2; i < l; i++) {
    j = i + i
    k = i + j
    r[j] = ((a[ai + k++] >> 0) | (uint16_t(a[ai + k] << 8))) & 4095
    r[j + 1] = ((a[ai + k++] >> 4) | (uint16_t(a[ai + k] << 4))) & 4095
  }
}

function poly_frommsg (r, m) {
  for (let h, i = 0, j, k; i < kyber_sym; i++) {
    for (h = 8 * i, j = 0; j < 8; j++) {
      k = -((m[i] >> j) & 1)
      r[h + j] = k & ((kyber_q + 1) / 2)
    }
  }
}

function poly_tomsg (m, a) {
  const t = uint32(1)
  for (let h, i = 0, j; i < kyber_sym; i++) {
    m[i] = 0
    for (h = 8 * i, j = 0; j < 8; j++) {
      t[0] = a[h + j]
      t[0] <<= 1
      t[0] += 1665
      t[0] *= 80635
      t[0] >>= 28
      t[0] &= 1
      m[i] |= t[0] << j
    }
  }
}

function basemul (r, a, b, z, i) {
  const j = i + 1
  r[i] = fqmul(a[j], b[j])
  r[i] = fqmul(r[i], z)
  r[i] += fqmul(a[i], b[i])
  r[j] = fqmul(a[i], b[j])
  r[j] += fqmul(a[j], b[i])
}

function poly_basemul_montgomery (r, a, b) {
  for (let i = 0, j, k, l = kyber_n / 4; i < l; i++) {
    basemul(r, a, b, zetas[j = 64 + i], k = 4 * i)
    basemul(r, a, b, -zetas[j], k + 2)
  }
}

function poly_tomont (r) {
  const f = num(1n << 32n) % kyber_q
  for (let i = 0; i < kyber_n; i++) {
    r[i] = montgomery_reduce(int32_t(r[i] * f))
  }
}

function load32 (x, xi) {
  const r = uint32([x[xi]])
  r[0] |= x[xi + 1] << 8
  r[0] |= x[xi + 2] << 16
  r[0] |= x[xi + 3] << 24
  return r[0]
}

function cbd2 (r, f) {
  for (let a, b, d, h, i = 0, j, t; i < kyber_sym; i++) {
    t = load32(f, 4 * i)
    d = uint32_t(t & x5)
    d += uint32_t(t >> 1) & x5
    for (h = 8 * i, j = 0; j < 8; j++) {
      a = int16_t(d >> uint32_t(4 * j)) & 3
      b = int16_t(d >> uint32_t(4 * j + 2)) & 3
      r[h + j] = a - b
    }
  }
}

function poly_getnoise (r, s, t) {
  s[kyber_sym] = t
  cbd2(r, reduce(s, kyber_n / 2))
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
  const t = uint16(8)
  for (let h, i = 0, j, k, ri = 0, u; i < kyber_k; i++) {
    for (j = 0; j < kyber_sym; j++) {
      for (h = 8 * j, k = 0; k < 8; k++) {
        t[k] = a[i][h + k]
        t[k] += (int16_t(t[k]) >> 15) & kyber_q
        u = big(t[k])
        u <<= 11n
        u += 1664n
        u *= 645084n
        u >>= 31n
        t[k] = uint16_t(num(u & 2047n))
      }
      r[ri++] = t[0] >> 0
      r[ri++] = (t[0] >> 8) | (t[1] << 3)
      r[ri++] = (t[1] >> 5) | (t[2] << 6)
      r[ri++] = t[2] >> 2
      r[ri++] = (t[2] >> 10) | (t[3] << 1)
      r[ri++] = (t[3] >> 7) | (t[4] << 4)
      r[ri++] = (t[4] >> 4) | (t[5] << 7)
      r[ri++] = t[5] >> 1
      r[ri++] = (t[5] >> 9) | (t[6] << 2)
      r[ri++] = (t[6] >> 6) | (t[7] << 5)
      r[ri++] = t[7] >> 3
    }
  }
}

function polyvec_decompress (r, a) {
  const t = uint16(8)
  for (let ai = 0, h, i = 0, j, k; i < kyber_k; i++) {
    for (j = 0; j < kyber_sym; j++) {
      t[0] = (a[ai++] >> 0) | (uint16_t(a[ai]) << 8)
      t[1] = (a[ai++] >> 3) | (uint16_t(a[ai]) << 5)
      t[2] = (a[ai++] >> 6) | (uint16_t(a[ai++]) << 2) | (uint16_t(a[ai]) << 10)
      t[3] = (a[ai++] >> 1) | (uint16_t(a[ai]) << 7)
      t[4] = (a[ai++] >> 4) | (uint16_t(a[ai]) << 4)
      t[5] = (a[ai++] >> 7) | (uint16_t(a[ai++]) << 1) | (uint16_t(a[ai]) << 9)
      t[6] = (a[ai++] >> 2) | (uint16_t(a[ai]) << 6)
      t[7] = (a[ai++] >> 5) | (uint16_t(a[ai++]) << 3)
      for (h = 8 * j, k = 0; k < 8; k++) {
        r[i][h + k] = (uint32_t(t[k] & 2047) * kyber_q + 1024) >> 11
      }
    }
  }
}

function polyvec_tobytes (r, a) {
  for (let i = 0; i < kyber_k; i++) {
    poly_tobytes(r, a[i], i * kyber_poly)
  }
}

function polyvec_frombytes (r, a) {
  for (let i = 0; i < kyber_k; i++) {
    poly_frombytes(r[i], a, i * kyber_poly)
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

function rej_uniform (r, l, f, g) {
  let a, b, i = 0, j = 0
  while (i < l && j + 3 <= g) {
    a = uint16_t(((f[j] >> 0) | (uint16_t(f[j + 1]) << 8)) & 4095)
    b = uint16_t(((f[j + 1] >> 4) | (uint16_t(f[j + 2]) << 4)) & 4095)
    j += 3
    if (a < kyber_q) {
      r[i++] = a
    }
    if (i < l && b < kyber_q) {
      r[i++] = b
    }
  }
}

function gen_matrix (a, s, t) {
  const g = 640
  const c = s.slice()
  c.set(uint8(32), 32)
  for (let f, i = 0, j; i < kyber_k; i++) {
    for (j = 0; j < kyber_k; j++) {
      if (t) {
        c[kyber_sym] = i
        c[kyber_sym + 1] = j
      } else {
        c[kyber_sym] = j
        c[kyber_sym + 1] = i
      }
      f = reduce(c, g)
      rej_uniform(a[i][j], kyber_n, f, g)
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
  const l = a.length
  if (ai < l && bi < b.length) {
    if (bi + c < l - ai) {
      for (let i = 0; i < c; i++) {
        a[ai + i] = b[bi + i]
      }
    } else {
      for (let i = 0, c = l - ai; i < c; i++) {
        a[ai + i] = b[bi + i]
      }
    }
  }
}

function pack_pk (r, p, s) {
  polyvec_tobytes(r, p)
  memcpy(r, s, kyber_sym, kyber_polyvec)
}

function unpack_pk (p, s, r) {
  polyvec_frombytes(p, r)
  memcpy(s, r, kyber_sym, 0, kyber_polyvec)
}

function pack_ciphertext (r, b, v) {
  polyvec_compress(r, b)
  poly_compress(r, v, kyber_vec)
}

function unpack_ciphertext (b, v, c) {
  polyvec_decompress(b, c)
  poly_decompress(v, c, kyber_vec)
}

function polyvecs () {
  const a = []
  for (let i = 0; i < kyber_k; i++) {
    a.push(polyvec())
  }
  return a
}

function keypair (p, s, t) {
  let i, u = 0
  const e = polyvec(), o = polyvec(), r = polyvec()
  const a = polyvecs()
  const f = uint8(kyber_sym2)
  memcpy(f, t, kyber_sym2)
  f[kyber_sym] = kyber_k
  f.set(reduce(f.slice(0, kyber_sym + 1), kyber_sym))
  gen_matrix(a, f, 0)
  const g = f.slice(kyber_sym)
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(r[i], g, u++)
  }
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(e[i], g, u++)
  }
  polyvec_ntt(r)
  polyvec_ntt(e)
  for (i = 0; i < kyber_k; i++) {
    polyvec_basemul_acc_montgomery(o[i], a[i], r)
    poly_tomont(o[i])
  }
  polyvec_add(o, o, e)
  polyvec_reduce(o)
  polyvec_tobytes(s, r)
  pack_pk(p, o, f)
}

function encrypts (c, m, p, t) {
  let i, u = 0
  const j = poly(), k = poly(), v = poly()
  const b = polyvec(), e = polyvec(), o = polyvec(), r = polyvec()
  const a = polyvecs()
  const s = uint8(kyber_sym2)
  unpack_pk(o, s, p)
  poly_frommsg(k, m)
  gen_matrix(a, s, 1)
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(r[i], t, u++)
  }
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(e[i], t, u++)
  }
  poly_getnoise(j, t, u++)
  polyvec_ntt(r)
  for (i = 0; i < kyber_k; i++) {
    polyvec_basemul_acc_montgomery(b[i], a[i], r)
  }
  polyvec_basemul_acc_montgomery(v, o, r)
  polyvec_invntt_tomont(b)
  invntt(v)
  polyvec_add(b, b, e)
  poly_add(v, v, j)
  poly_add(v, v, k)
  polyvec_reduce(b)
  poly_reduce(v)
  pack_ciphertext(c, b, v)
}

function decrypts (m, c, s) {
  const p = poly(), v = poly()
  const b = polyvec(), a = polyvec()
  unpack_ciphertext(b, v, c)
  polyvec_frombytes(a, s)
  polyvec_ntt(b)
  polyvec_basemul_acc_montgomery(p, a, b)
  invntt(p)
  poly_sub(p, v, p)
  poly_reduce(p)
  poly_tomsg(m, p)
}

function crypto_kem_keypair (p, s) {
  const c = randombytes(kyber_sym2)
  keypair(p, s, c)
  memcpy(s, p, public_bytes, kyber_polyvec)
  s.set(reduce(p, kyber_sym), secret_bytes - kyber_sym2)
  memcpy(s, c, kyber_sym, secret_bytes - kyber_sym, kyber_sym)
}

function crypto_kem_enc (c, k, p) {
  const f = uint8(kyber_sym2)
  const t = randombytes(kyber_sym2)
  memcpy(f, t, kyber_sym)
  const r = uint8(kyber_sym2)
  f.set(reduce(p, kyber_sym))
  r.set(reduce(f, kyber_sym2))
  memcpy(k, r, kyber_sym)
  encrypts(c, f, p, r.slice(kyber_sym))
}

function crypto_kem_dec (k, c, s) {
  const f = uint8(kyber_sym2)
  decrypts(f, c, s)
  k.set(reduce(f, kyber_sym))
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