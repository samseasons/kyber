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

function uint16_t (a) {
  return uint16([a])[0]
}

function randombytes (a) {
  return crypto.getRandomValues(uint8(a))
}

kyber_k = 4
kyber_n = 256
kyber_poly = 384
kyber_polyvec = kyber_k * kyber_poly
kyber_q = 3329
kyber_qinv = -3327
kyber_sym = 32
kyber_sym2 = kyber_sym * 2
kyber_vec = kyber_k * 352
kyber_x5 = 0x55555555
public_bytes = kyber_polyvec + kyber_sym
secret_bytes = kyber_polyvec + public_bytes + kyber_sym2
cipher_bytes = kyber_vec + 160
shared_bytes = kyber_sym

function montgomery_reduce (a) {
  return (a - int16_t(a * kyber_qinv) * kyber_q) >> 16
}

function fqmul (a, b) {
  return montgomery_reduce(int16_t(a) * int16_t(b))
}

function br7 (a) {
  a = [a >> 5 & 1, a >> 4 & 1, a >> 3 & 1, a >> 2 & 1, a >> 1 & 1, a & 1]
  let b = 0
  return a[b++] << 1 ^ a[b++] << 2 ^ a[b++] << 3 ^ a[b++] << 4 ^ a[b++] << 5 ^ a[b++] << 6
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
  const mont = -1044
  const kroot = mont * 17 % kyber_q
  const tmp = uint16(128)
  tmp[0] = mont
  for (i = 1; i < 128; i++) {
    tmp[i] = fqmul(tmp[i - 1], kroot)
  }
  const kyber_q2 = kyber_q / 2
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

function polyvecs () {
  const a = []
  for (let i = 0; i < kyber_k; i++) {
    a.push(polyvec())
  }
  return a
}

function poly_compress (r, a, ri) {
  const t = uint8(8)
  for (let h = 0, i = 0, j, k; i < kyber_sym; h += 8, i++) {
    for (j = 0; j < 8; j++) {
      k = a[h + j]
      k += (k >> 15) & kyber_q
      k <<= 5
      k += 1664
      k *= 40318
      k >>= 27
      t[j] = k & 31
    }
    j = 0
    r[ri++] = t[j++] | (t[j] << 5)
    r[ri++] = (t[j++] >> 3) | (t[j++] << 2) | (t[j] << 7)
    r[ri++] = (t[j++] >> 1) | (t[j] << 4)
    r[ri++] = (t[j++] >> 4) | (t[j++] << 1) | (t[j] << 6)
    r[ri++] = (t[j++] >> 2) | (t[j] << 3)
  }
}

function poly_decompress (r, a, ai) {
  const t = uint8(8)
  for (let h = 0, i = 0, j; i < kyber_sym; h += 8, i++) {
    t[0] = a[ai]
    t[1] = (a[ai++] >> 5) | (a[ai] << 3)
    t[2] = (a[ai] >> 2)
    t[3] = (a[ai++] >> 7) | (a[ai] << 1)
    t[4] = (a[ai++] >> 4) | (a[ai] << 4)
    t[5] = (a[ai] >> 1)
    t[6] = (a[ai++] >> 6) | (a[ai] << 2)
    t[7] = (a[ai++] >> 3)
    for (j = 0; j < 8; j++) {
      r[h + j] = ((t[j] & 31) * kyber_q + 16) >> 5
    }
  }
}

function poly_tobytes (r, a, ri) {
  const t = uint16(1), u = uint16(1)
  for (let i = 0, j, l = kyber_n / 2; i < l; i++) {
    j = i * 2
    t[0] = a[j]
    t[0] += (int16_t(t[0]) >> 15) & kyber_q
    u[0] = a[j + 1]
    u[0] += (int16_t(u[0]) >> 15) & kyber_q
    j += i
    r[ri + j] = t[0]
    r[ri + j + 1] = (t[0] >> 8) | (u[0] << 4)
    r[ri + j + 2] = u[0] >> 4
  }
}

function poly_frombytes (r, a, ai) {
  for (let i = 0, j, k, l = kyber_n / 2; i < l; i++) {
    j = i * 2
    k = i + j
    r[j] = (a[ai + k++] | (uint16_t(a[ai + k] << 8))) & 4095
    r[j + 1] = ((a[ai + k++] >> 4) | (uint16_t(a[ai + k] << 4))) & 4095
  }
}

function poly_frommsg (r, m) {
  for (let h = 0, i = 0, j; i < kyber_sym; h += 8, i++) {
    for (j = 0; j < 8; j++) {
      r[h + j] = -((m[i] >> j) & 1) & ((kyber_q + 1) / 2)
    }
  }
}

function poly_tomsg (m, a) {
  for (let h = 0, i = 0, j, t = 1; i < kyber_sym; h += 8, i++) {
    m[i] = 0
    for (j = 0; j < 8; j++) {
      t = a[h + j] << 1
      t += 1665
      t *= 80635
      t >>= 28
      t &= 1
      m[i] |= t << j
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
    j = i + 64
    k = i * 4
    basemul(r, a, b, zetas[j], k)
    basemul(r, a, b, -zetas[j], k + 2)
  }
}

function poly_tomont (r) {
  const f = num(1n << 32n) % kyber_q
  for (let i = 0; i < kyber_n; i++) {
    r[i] = montgomery_reduce(r[i] * f)
  }
}

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

function reduces (a, h=a1) {
  while (a.length > a128) {
    a = [...expand(a.slice(a0, a128), a0, a64), ...a.slice(a128)]
  }
  return expand(a, a0, h)
}

function load32 (x, xi) {
  let r = x[xi]
  r |= x[xi + 1] << 8
  r |= x[xi + 2] << 16
  r |= x[xi + 3] << 24
  return r
}

function cbd2 (r, f) {
  for (let a, b, d, h = 0, i = 0, j, k, t; i < kyber_sym; h += 8, i++) {
    t = load32(f, i * 4)
    d = t & kyber_x5 + (t >> 1) & kyber_x5
    for (j = 0; j < 8; j++) {
      k = j * 4
      a = int16_t(d >> k) & 3
      b = int16_t(d >> (k + 2)) & 3
      r[h + j] = a - b
    }
  }
}

function poly_getnoise (r, s, t) {
  s[kyber_sym] = t
  cbd2(r, reduces(s, kyber_n / 2))
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

function ntt (r) {
  let i, j, k = 1, l, m, s, t, z
  for (i = 128; i >= 2; i >>= 1) {
    for (s = 0; s < 256; s = i + j) {
      z = zetas[k++]
      for (j = s, l = i + s; j < l; j++) {
        m = i + j
        t = fqmul(z, r[m])
        r[m] = r[j] - t
        r[j] += t
      }
    }
  }
}

function barrett_reduce (a) {
  let t = (1 << 26) / kyber_q + 0.5
  t = (a * t + (1 << 25)) >> 26
  return a - kyber_q * t
}

function invntt (r) {
  let i, j, k = 127, l, m, s, t, z
  for (i = 2; i <= 128; i <<= 1) {
    for (s = 0; s < 256; s = i + j) {
      z = zetas[k--]
      for (j = s, l = i + s; j < l; j++) {
        m = i + j
        t = r[j]
        r[j] = barrett_reduce(r[m] + t)
        r[m] -= t
        r[m] = fqmul(z, r[m])
      }
    }
  }
  for (j = 0; j < 256; j++) {
    r[j] = fqmul(r[j], 1441)
  }
}

function poly_reduce (r) {
  for (let i = 0; i < kyber_n; i++) {
    r[i] = barrett_reduce(r[i])
  }
}

function polyvec_compress (r, a) {
  const t = uint16(8)
  for (let h, i = 0, j, k, l = 0, m; i < kyber_k; i++) {
    for (h = 0, j = 0; j < kyber_sym; h += 8, j++) {
      for (k = 0; k < 8; k++) {
        t[k] = a[i][h + k]
        t[k] += (int16_t(t[k]) >> 15) & kyber_q
        m = big(t[k]) << 11n
        m += 1664n
        m *= 645084n
        m >>= 31n
        t[k] = num(m & 2047n)
      }
      k = 0
      r[l++] = t[k]
      r[l++] = (t[k++] >> 8) | (t[k] << 3)
      r[l++] = (t[k++] >> 5) | (t[k] << 6)
      r[l++] = t[k] >> 2
      r[l++] = (t[k++] >> 10) | (t[k] << 1)
      r[l++] = (t[k++] >> 7) | (t[k] << 4)
      r[l++] = (t[k++] >> 4) | (t[k] << 7)
      r[l++] = t[k] >> 1
      r[l++] = (t[k++] >> 9) | (t[k] << 2)
      r[l++] = (t[k++] >> 6) | (t[k] << 5)
      r[l++] = t[k] >> 3
    }
  }
}

function polyvec_decompress (r, a) {
  const t = uint16(8)
  for (let g = 0, h, i = 0, j, k; i < kyber_k; i++) {
    for (h = 0, j = 0; j < kyber_sym; h += 8, j++) {
      t[0] = a[g++] | (a[g] << 8)
      t[1] = (a[g++] >> 3) | (a[g] << 5)
      t[2] = (a[g++] >> 6) | (a[g++] << 2) | (a[g] << 10)
      t[3] = (a[g++] >> 1) | (a[g] << 7)
      t[4] = (a[g++] >> 4) | (a[g] << 4)
      t[5] = (a[g++] >> 7) | (a[g++] << 1) | (a[g] << 9)
      t[6] = (a[g++] >> 2) | (a[g] << 6)
      t[7] = (a[g++] >> 5) | (a[g++] << 3)
      for (k = 0; k < 8; k++) {
        r[i][h + k] = ((t[k] & 2047) * kyber_q + 1024) >> 11
      }
    }
  }
}

function polyvec_frombytes (r, a) {
  for (let i = 0; i < kyber_k; i++) {
    poly_frombytes(r[i], a, i * kyber_poly)
  }
}

function polyvec_tobytes (r, a) {
  for (let i = 0; i < kyber_k; i++) {
    poly_tobytes(r, a[i], i * kyber_poly)
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
    a = uint16_t((f[j++] | (f[j] << 8)) & 4095)
    b = uint16_t(((f[j++] >> 4) | (f[j++] << 4)) & 4095)
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
  const c = uint8(64)
  c.set(s.slice(0, 32))
  for (let f, i = 0, j; i < kyber_k; i++) {
    for (j = 0; j < kyber_k; j++) {
      if (t) {
        c[kyber_sym] = i
        c[kyber_sym + 1] = j
      } else {
        c[kyber_sym] = j
        c[kyber_sym + 1] = i
      }
      f = reduces(c, g)
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

function keypair (p, s, t) {
  let i, m = 0
  const e = polyvec(), o = polyvec(), r = polyvec()
  const a = polyvecs()
  const f = uint8(kyber_sym2)
  memcpy(f, t, kyber_sym2)
  f[kyber_sym] = kyber_k
  f.set(reduces(f.slice(0, kyber_sym + 1), kyber_sym))
  gen_matrix(a, f, 0)
  const g = f.slice(kyber_sym)
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(e[i], g, m++)
  }
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(r[i], g, m++)
  }
  polyvec_ntt(e)
  polyvec_ntt(r)
  for (i = 0; i < kyber_k; i++) {
    polyvec_basemul_acc_montgomery(o[i], a[i], r)
    poly_tomont(o[i])
  }
  polyvec_add(o, o, e)
  polyvec_reduce(o)
  polyvec_tobytes(s, r)
  pack_pk(p, o, f)
}

function encrypts (c, f, p, t) {
  let i, m = 0
  const j = poly(), k = poly(), v = poly()
  const b = polyvec(), e = polyvec(), o = polyvec(), r = polyvec()
  const a = polyvecs()
  const s = uint8(kyber_sym2)
  unpack_pk(o, s, p)
  poly_frommsg(k, f)
  gen_matrix(a, s, 1)
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(r[i], t, m++)
  }
  for (i = 0; i < kyber_k; i++) {
    poly_getnoise(e[i], t, m++)
  }
  poly_getnoise(j, t, m++)
  polyvec_ntt(r)
  for (i = 0; i < kyber_k; i++) {
    polyvec_basemul_acc_montgomery(b[i], a[i], r)
  }
  polyvec_invntt_tomont(b)
  polyvec_add(b, b, e)
  polyvec_reduce(b)
  polyvec_basemul_acc_montgomery(v, o, r)
  invntt(v)
  poly_add(v, v, j)
  poly_add(v, v, k)
  poly_reduce(v)
  pack_ciphertext(c, b, v)
}

function decrypts (f, c, s) {
  const p = poly(), v = poly()
  const b = polyvec(), e = polyvec()
  unpack_ciphertext(b, v, c)
  polyvec_ntt(b)
  polyvec_frombytes(e, s)
  polyvec_basemul_acc_montgomery(p, e, b)
  invntt(p)
  poly_sub(p, v, p)
  poly_reduce(p)
  poly_tomsg(f, p)
}

function crypto_kem_keypair (p, s) {
  const c = randombytes(kyber_sym2)
  keypair(p, s, c)
  memcpy(s, p, public_bytes, kyber_polyvec)
  s.set(reduces(p, kyber_sym), secret_bytes - kyber_sym2)
  memcpy(s, c, kyber_sym, secret_bytes - kyber_sym, kyber_sym)
}

function crypto_kem_enc (c, k, p) {
  const f = uint8(kyber_sym2)
  const t = randombytes(kyber_sym2)
  memcpy(f, t, kyber_sym)
  const r = uint8(kyber_sym2)
  f.set(reduces(p, kyber_sym))
  r.set(reduces(f, kyber_sym2))
  memcpy(k, r, kyber_sym)
  encrypts(c, f, p, r.slice(kyber_sym))
}

function crypto_kem_dec (k, c, s) {
  const f = uint8(kyber_sym2)
  decrypts(f, c, s)
  k.set(reduces(f, shared_bytes))
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