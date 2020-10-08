package com.raugfer.crypto;

import java.math.BigInteger;

public class secp256k1_1 {

    private static BigInteger p = new BigInteger("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16);
    private static BigInteger a = new BigInteger("0000000000000000000000000000000000000000000000000000000000000000", 16);
    private static BigInteger b = new BigInteger("0000000000000000000000000000000000000000000000000000000000000007", 16);
    public static BigInteger[] G = new BigInteger[]{
            new BigInteger("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798", 16),
            new BigInteger("483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8", 16),
    };
    public static final BigInteger n = new BigInteger("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16);

    private static BigInteger[][] precomputes;
    private static BigInteger[][] precomputesJ;

    public static boolean rng(BigInteger e) {
        return e.compareTo(BigInteger.ZERO) > 0 && e.compareTo(n) < 0;
    }

    public static boolean has(BigInteger[] P) {
        if (P == null) return false;
        BigInteger x = P[0], y = P[1];
        return y.pow(2).subtract(x.pow(3).add(x.multiply(a)).add(b)).mod(p).equals(BigInteger.ZERO);
    }

    private static BigInteger[] add1(BigInteger[] P1, BigInteger[] P2) {
        if (P1 == null) return P2;
        if (P2 == null) return P1;
        BigInteger x1 = P1[0], y1 = P1[1];
        BigInteger x2 = P2[0], y2 = P2[1];
        BigInteger l;
        if (x1.equals(x2)) {
            if (!y1.equals(y2)) return null;
            if (y1.equals(BigInteger.ZERO)) return null;
            l = x1.pow(2).multiply(BigInteger.valueOf(3)).add(a).multiply(y1.shiftLeft(1).modInverse(p));
        } else {
            l = y2.subtract(y1).multiply(x2.subtract(x1).modInverse(p));
        }
        BigInteger x3 = l.pow(2).subtract(x1).subtract(x2);
        BigInteger y3 = l.multiply(x1.subtract(x3)).subtract(y1);
        BigInteger[] P3 = new BigInteger[]{x3.mod(p), y3.mod(p)};
        return P3;
    }

    private static BigInteger[] double_add(BigInteger[] P) {
        BigInteger X1 = P[0];
        BigInteger Y1 = P[1];
        BigInteger lam = BigInteger.valueOf(3).multiply(X1.pow(2)).multiply(BigInteger.valueOf(2).multiply(Y1).modInverse(p)).mod(p);
        BigInteger X3 = lam.multiply(lam).subtract(BigInteger.valueOf(2).multiply(X1)).mod(p);
        BigInteger Y3 = lam.multiply(X1.subtract(X3)).subtract(Y1).mod(p);
        return new BigInteger[]{X3, Y3};
    }

    private static BigInteger[] double_add_j(BigInteger[] P) {
        BigInteger X1 = P[0];
        BigInteger Y1 = P[1];
        BigInteger Z1 = P[2];
        BigInteger A = X1.pow(2);
        BigInteger B = Y1.pow(2);
        BigInteger C = B.pow(2);
        BigInteger D = BigInteger.valueOf(2).multiply((X1.add(B)).pow(2).subtract(A).subtract(C));
        BigInteger E = BigInteger.valueOf(3).multiply(A);
        BigInteger F = E.pow(2);
        BigInteger X3 = F.subtract(BigInteger.valueOf(2).multiply(D)).mod(p);
        BigInteger Y3 = E.multiply(D.subtract(X3)).subtract(BigInteger.valueOf(8).multiply(C)).mod(p);
        BigInteger Z3 = BigInteger.valueOf(2).multiply(Y1).multiply(Z1).mod(p);
        return new BigInteger[]{X3, Y3, Z3};
    }

    private static BigInteger[] add(BigInteger[] P1, BigInteger[] P2) {
        if (P1 == null) return P2;
        if (P2 == null) return P1;
        BigInteger X1 = P1[0], Y1 = P1[1];
        BigInteger X2 = P2[0], Y2 = P2[1];
        if (X1.compareTo(BigInteger.ZERO) == 0 || Y1.compareTo(BigInteger.ZERO) == 0) {
            return P2;
        }
        if (X2.compareTo(BigInteger.ZERO) == 0 || Y2.compareTo(BigInteger.ZERO) == 0) {
            return P1;
        }
        if (X1.compareTo(X2) == 0 && Y1.compareTo(Y2) == 0) {
            return double_add(P1);
        }
        if (X1.compareTo(X2) == 0 && Y1.compareTo(Y2.negate()) == 0) {
            return new BigInteger[]{BigInteger.ZERO, BigInteger.ZERO};
        }
        BigInteger lam = Y2.subtract(Y1).multiply((X2.subtract(X1)).modInverse(p)).mod(p);
        BigInteger X3 = lam.multiply(lam).subtract(X1).subtract(X2).mod(p);
        BigInteger Y3 = lam.multiply(X1.subtract(X3)).subtract(Y1).mod(p);
        return new BigInteger[]{X3, Y3};
    }

    private static BigInteger[] add_j(BigInteger[] P1, BigInteger[] P2) {
        if (P1 == null) return P2;
        if (P2 == null) return P1;
        BigInteger X1 = P1[0], Y1 = P1[1], Z1 = P1[2];
        BigInteger X2 = P2[0], Y2 = P2[1], Z2 = P2[2];
        if (X1.compareTo(BigInteger.ZERO) == 0 || Y1.compareTo(BigInteger.ZERO) == 0) {
            return P2;
        }
        if (X2.compareTo(BigInteger.ZERO) == 0 || Y2.compareTo(BigInteger.ZERO) == 0) {
            return P1;
        }
        BigInteger Z1Z1 = Z1.pow(2);
        BigInteger Z2Z2 = Z2.pow(2);
        BigInteger U1 = X1.multiply(Z2Z2);
        BigInteger U2 = X2.multiply(Z1Z1);
        BigInteger S1 = Y1.multiply(Z2).multiply(Z2Z2);
        BigInteger S2 = Y2.multiply(Z1).multiply(Z1Z1);
        BigInteger H = U2.subtract(U1).mod(p);
        BigInteger r = S2.subtract(S1).mod(p);
        if (H.compareTo(BigInteger.ZERO) == 0) {
            if (r.compareTo(BigInteger.ZERO) == 0) {
                return double_add_j(P1);
            } else {
                return new BigInteger[]{BigInteger.ZERO, BigInteger.ONE, BigInteger.ZERO};
            }
        }
        BigInteger HH = H.pow(2).mod(p);
        BigInteger HHH = H.multiply(HH).mod(p);
        BigInteger V = U1.multiply(HH);
        BigInteger X3 = r.pow(2).subtract(HHH).subtract(BigInteger.valueOf(2).multiply(V)).mod(p);
        BigInteger Y3 = r.multiply(V.subtract(X3)).subtract(S1.multiply(HHH)).mod(p);
        BigInteger Z3 = Z1.multiply(Z2).multiply(H).mod(p);
        return new BigInteger[]{X3, Y3, Z3};
    }

    private static BigInteger[] mul(BigInteger[] P, BigInteger e) {
        if (e.equals(BigInteger.ZERO)) return null;
        BigInteger[] Q = mul(add(P, P), e.shiftRight(1));
        if (!e.and(BigInteger.ONE).equals(BigInteger.ZERO)) Q = add(Q, P);
        return Q;
    }

    public static BigInteger[][] get_precomputes() {
        if (precomputes != null) {
            return precomputes;
        }
        precomputes = new BigInteger[256][];
        BigInteger[] dbl = G;
        for (int i = 0; i < 256; i++) {
            precomputes[i] = dbl;
            dbl = double_add(dbl);
        }
        return precomputes;
    }

    public static BigInteger[][] get_precomputes_j() {
        if (precomputesJ != null) {
            return precomputesJ;
        }
        precomputesJ = new BigInteger[256][];
        BigInteger[] dbl = from_affine(G);
        for (int i = 0; i < 256; i++) {
            precomputesJ[i] = dbl;
            dbl = double_add_j(dbl);
        }
        return precomputesJ;
    }

    public static BigInteger[] mul_ct(BigInteger[] P, BigInteger e) {
        BigInteger[] dbl;
        BigInteger[] p = new BigInteger[]{BigInteger.ZERO, BigInteger.ZERO};
        BigInteger[] f = new BigInteger[]{BigInteger.ZERO, BigInteger.ZERO};
        BigInteger[][] dbls = get_precomputes();
        for (int i = 0; i < 256; i++) {
            dbl = dbls[i];
            if (e.and(BigInteger.ONE).compareTo(BigInteger.ONE) == 0) {
                p = add(p, dbl);
            } else {
                f = add(f, dbl);
            }
            e = e.shiftRight(1);
        }
        return p;
    }

    public static BigInteger[] mul_ct_j(BigInteger[] P, BigInteger e) {
        BigInteger[] dbl;
        BigInteger[] p = new BigInteger[]{BigInteger.ZERO, BigInteger.ONE, BigInteger.ZERO};
        BigInteger[] f = new BigInteger[]{BigInteger.ZERO, BigInteger.ONE, BigInteger.ZERO};
        BigInteger[][] dbls = get_precomputes_j();
        for (int i = 0; i < 256; i++) {
            dbl = dbls[i];
            if (e.and(BigInteger.ONE).compareTo(BigInteger.ONE) == 0) {
                p = add_j(p, dbl);
            } else {
                f = add_j(f, dbl);
            }
            e = e.shiftRight(1);
        }
        return to_affine(p);
    }

    private static BigInteger[] from_affine(BigInteger[] P) {
        return new BigInteger[]{P[0], P[1], BigInteger.ONE};
    }

    private static BigInteger[] to_affine(BigInteger[] P) {
        BigInteger invZ = P[2].modInverse(p);
        BigInteger invZ2 = invZ.pow(2);
        BigInteger x = P[0].multiply(invZ2).mod(p);
        BigInteger y = P[1].multiply(invZ2).multiply(invZ).mod(p);
        return new BigInteger[]{x, y};
    }

    public static BigInteger aex(BigInteger e1, BigInteger e2) {
        if (!rng(e1)) throw new IllegalArgumentException("Out of range");
        if (!rng(e2)) throw new IllegalArgumentException("Out of range");
        BigInteger e3 = e1.add(e2).mod(n);
        if (!rng(e3)) throw new IllegalArgumentException("Out of range");
        return e3;
    }

    public static BigInteger[] apt(BigInteger[] P1, BigInteger[] P2) {
        if (!has(P1)) throw new IllegalArgumentException("Invalid point");
        if (!has(P2)) throw new IllegalArgumentException("Invalid point");
        BigInteger[] P3 = add(P1, P2);
        assert has(P3);
        return P3;
    }

    public static BigInteger fnd(BigInteger x, boolean odd) {
        BigInteger y = x.pow(3).add(x.multiply(a)).add(b).modPow(p.add(BigInteger.ONE).shiftRight(2), p);
        if (odd == y.and(BigInteger.ONE).equals(BigInteger.ZERO)) y = p.subtract(y);
        BigInteger[] P = new BigInteger[]{x, y};
        assert has(P) && mul(P, n) == null;
        return y;
    }

    public static BigInteger[] gen(BigInteger e) {
        assert has(G);
        if (!rng(e)) throw new IllegalArgumentException("Out of range");
        BigInteger[] P = mul(G, e);
        if (P == null) throw new IllegalArgumentException("Point at infinity");
        BigInteger x = P[0], y = P[1];
        assert has(P) && mul(P, n) == null;
        return P;
    }

    public static pair<BigInteger, Boolean> enc(BigInteger[] P) {
        BigInteger x = P[0], y = P[1];
        if (!has(P)) throw new IllegalArgumentException("Invalid point");
        boolean odd = y.and(BigInteger.ONE).equals(BigInteger.ONE);
        return new pair<>(x, odd);
    }

    public static BigInteger[] dec(BigInteger p, boolean odd) {
        BigInteger x = p;
        BigInteger y = fnd(x, odd);
        BigInteger[] P = new BigInteger[]{x, y};
        if (!has(P)) throw new IllegalArgumentException("Invalid point");
        return P;
    }

    public static Object[] sgn(BigInteger e, BigInteger h, BigInteger k) {
        if (!rng(e)) throw new IllegalArgumentException("Out of range");
        if (!rng(h)) throw new IllegalArgumentException("Out of range");
        BigInteger[] P = gen(k);
        BigInteger r = P[0], y = P[1];
        BigInteger s = ((k.modPow(n.subtract(BigInteger.valueOf(2)), n)).multiply(h.add(r.multiply(e)))).mod(n);
        boolean odd = y.and(BigInteger.ONE).equals(BigInteger.ONE);
        if (s.compareTo(n.shiftRight(1)) > 0) {
            s = n.subtract(s);
            odd = !odd;
        }
        if (!rng(s)) throw new IllegalArgumentException("Out of range");
        return new Object[]{r, s, odd};
    }

    public static boolean ver(BigInteger[] P, BigInteger h, Object[] S) {
        if (!(has(P) && mul(P, n) == null)) throw new IllegalArgumentException("Invalid point");
        if (!rng(h)) throw new IllegalArgumentException("Out of range");
        BigInteger r = (BigInteger) S[0];
        BigInteger s = (BigInteger) S[1];
        if (!rng(r)) throw new IllegalArgumentException("Out of range");
        if (!rng(s)) throw new IllegalArgumentException("Out of range");
        if (s.compareTo(n.shiftRight(1)) > 0) throw new IllegalArgumentException("Out of range");
        BigInteger w = s.modPow(n.subtract(BigInteger.valueOf(2)), n);
        BigInteger u = h.multiply(w).mod(n), v = r.multiply(w).mod(n);
        BigInteger[] Q = add(mul(G, u), mul(P, v));
        if (Q == null) throw new IllegalArgumentException("Point at infinity");
        BigInteger x = Q[0];
        return r.equals(x);
    }

    public static BigInteger[] rec(BigInteger h, Object[] S) {
        if (!rng(h)) throw new IllegalArgumentException("Out of range");
        BigInteger r = (BigInteger) S[0];
        BigInteger s = (BigInteger) S[1];
        boolean odd = (boolean) S[2];
        if (!rng(r)) throw new IllegalArgumentException("Out of range");
        if (!rng(s)) throw new IllegalArgumentException("Out of range");
        if (s.compareTo(n.shiftRight(1)) > 0) throw new IllegalArgumentException("Out of range");
        BigInteger[] R = {r, fnd(r, odd)};
        BigInteger z = h.negate().mod(n);
        BigInteger invr = r.modPow(n.subtract(BigInteger.valueOf(2)), n);
        BigInteger[] P = mul(add(mul(R, s), mul(G, z)), invr);
        if (!(has(P) && mul(P, n) == null)) throw new IllegalArgumentException("Invalid point");
        return P;
    }

    public static BigInteger[] egcd(BigInteger a, BigInteger b) {
        BigInteger x = BigInteger.ZERO;
        BigInteger y = BigInteger.ONE;
        BigInteger u = BigInteger.ONE;
        BigInteger v = BigInteger.ZERO;
        while (a.compareTo(BigInteger.ZERO) != 0) {
            BigInteger q = b.divide(a);
            BigInteger r = b.remainder(a);
            BigInteger m = x.subtract(u.multiply(q));
            BigInteger n = y.subtract(v.multiply(q));
            b = a;
            a = r;
            x = u;
            y = v;
            u = m;
            v = n;
        }
        return new BigInteger[]{b, x, y};
    }

    public static BigInteger invert(BigInteger number, BigInteger modulo) {
        if (number.compareTo(BigInteger.ZERO) == 0 || modulo.compareTo(BigInteger.ZERO) <= 0) {
            throw new IllegalArgumentException("invert: expected positive integers");
        }
        BigInteger[] result = egcd(number.mod(modulo), modulo);
        if (result[0].compareTo(BigInteger.ONE) != 0) {
            throw new IllegalArgumentException("invert: does not exist");
        }
        return result[1].mod(modulo);
    }

}
