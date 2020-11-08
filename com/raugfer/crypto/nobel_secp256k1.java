package com.raugfer.crypto;

import java.math.BigInteger;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

// https://www.secg.org/sec2-v2.pdf
// Curve fomula is y^2 = x^3 + ax + b
public class nobel_secp256k1 {
    // Params: a, b
    private static final BigInteger a = BigInteger.ZERO;
    private static final BigInteger b = BigInteger.valueOf(7L);
    // Field over which we'll do calculations
    private static final BigInteger P = new BigInteger("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16);
    // Subgroup order aka prime_order
    private static final BigInteger n = new BigInteger("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16);
    // Cofactor
    private static final BigInteger h = BigInteger.ONE;
    // Base point (x, y) aka generator point
    private static final BigInteger Gx = new BigInteger("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798", 16);
    private static final BigInteger Gy = new BigInteger("483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8", 16);

    // For endomorphism, see below.
    private static final BigInteger beta = new BigInteger("7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee", 16);

    /**
     * Note: cannot be reused for other curves when a != 0.
     * If we're using Koblitz curve, we can improve efficiency by using endomorphism.
     * Uses 2x less RAM, speeds up precomputation by 2x and ECDH / sign key recovery by 20%.
     * Should always be used for Jacobian's double-and-add multiplication.
     * For affines cached multiplication, it trades off 1/2 init time & 1/3 ram for 20% perf hit.
     * https://gist.github.com/paulmillr/eb670806793e84df628a7c434a873066
     */
    private static final boolean USE_ENDOMORPHISM = a.signum() == 0;

    /**
     * Default Point works in 2d / affine coordinates: (x, y)
     * Jacobian Point works in 3d / jacobi coordinates: (x, y, z) ∋ (x=x/z^2, y=y/z^3)
     * We're doing calculations in jacobi, because its operations don't require costly inversion.
     */
    static class JacobianPoint {
        private final BigInteger x;
        private final BigInteger y;
        private final BigInteger z;

        public JacobianPoint(BigInteger x, BigInteger y, BigInteger z) {
            this.x = x;
            this.y = y;
            this.z = z;
        }

        static final JacobianPoint BASE = new JacobianPoint(Gx, Gy, BigInteger.ONE);
        static final JacobianPoint ZERO = new JacobianPoint(BigInteger.ZERO, BigInteger.ONE, BigInteger.ZERO);
        static JacobianPoint fromAffine(Point p) {
            return new JacobianPoint(p.x, p.y, BigInteger.ONE);
        }

        // Takes a bunch of Jacobian Points but executes only one
        // invert on all of them. invert is very slow operation,
        // so this improves performance massively.
        static List<Point> toAffineBatch(List<JacobianPoint> points) {
            BigInteger[] toInv = invertBatch(points.stream().map(p -> p.z).toArray(BigInteger[]::new));
            return IntStream.range(0, points.size()).mapToObj(i -> points.get(i).toAffine(toInv[i])).collect(Collectors.toList());
        }

        boolean equals(JacobianPoint other) {
            JacobianPoint a = this;
            JacobianPoint b = other;
            BigInteger az2 = mod(a.z.multiply(a.z));
            BigInteger az3 = mod(a.z.multiply(az2));
            BigInteger bz2 = mod(b.z.multiply(b.z));
            BigInteger bz3 = mod(b.z.multiply(bz2));
            return mod(a.x.multiply(bz2)).compareTo(mod(az2.multiply(b.x))) == 0 && mod(a.y.multiply(bz3)).compareTo(mod(az3.multiply(b.y))) == 0;
        }

        JacobianPoint negate() {
            return new JacobianPoint(this.x, mod(this.y.negate()), this.z);
        }

        JacobianPoint doubleAdd() {
            BigInteger X1 = this.x;
            BigInteger Y1 = this.y;
            BigInteger Z1 = this.z;
            BigInteger A = X1.pow(2);
            BigInteger B = Y1.pow(2);
            BigInteger C = B.pow(2);
            BigInteger D = BigInteger.valueOf(2L).multiply((X1.add(B)).pow(2).subtract(A).subtract(C));
            BigInteger E = BigInteger.valueOf(3L).multiply(A);
            BigInteger F = E.pow(2);
            BigInteger X3 = mod(F.subtract(BigInteger.valueOf(2L).multiply(D)));
            BigInteger Y3 = mod(E.multiply(D.subtract(X3)).subtract(BigInteger.valueOf(8L).multiply(C)));
            BigInteger Z3 = mod(BigInteger.valueOf(2L).multiply(Y1).multiply(Z1));
            return new JacobianPoint(X3, Y3, Z3);
        }

        JacobianPoint add(JacobianPoint other) {
            if (other == null) {
                throw new IllegalArgumentException("JacobianPoint#add: expected JacobianPoint");
            }
            BigInteger X1 = this.x;
            BigInteger Y1 = this.y;
            BigInteger Z1 = this.z;
            BigInteger X2 = other.x;
            BigInteger Y2 = other.y;
            BigInteger Z2 = other.z;
            if (X2.signum() == 0 || Y2.signum() == 0) return this;
            if (X1.signum() == 0 || Y1.signum() == 0) return other;
            BigInteger Z1Z1 = Z1.pow(2);
            BigInteger Z2Z2 = Z2.pow(2);
            BigInteger U1 = X1.multiply(Z2Z2);
            BigInteger U2 = X2.multiply(Z1Z1);
            BigInteger S1 = Y1.multiply(Z2).multiply(Z2Z2);
            BigInteger S2 = Y2.multiply(Z1).multiply(Z1Z1);
            BigInteger H = mod(U2.subtract(U1));
            BigInteger r = mod(S2.subtract(S1));
            if (H.signum() == 0) {
                if (r.signum() == 0) {
                    return this.doubleAdd();
                } else {
                    return JacobianPoint.ZERO;
                }
            }
            BigInteger HH = mod(H.pow(2));
            BigInteger HHH = mod(H.multiply(HH));
            BigInteger V = U1.multiply(HH);
            BigInteger X3 = mod(r.pow(2).subtract(HHH).subtract(BigInteger.valueOf(2L).multiply(V)));
            BigInteger Y3 = mod(r.multiply(V.subtract(X3)).subtract(S1.multiply(HHH)));
            BigInteger Z3 = mod(Z1.multiply(Z2).multiply(H));
            return new JacobianPoint(X3, Y3, Z3);
        }

        JacobianPoint multiplyUnsafe(BigInteger scalar) {
            BigInteger n = mod(scalar, nobel_secp256k1.n);
            if (n.signum() <= 0) {
                throw new IllegalArgumentException("Point#multiply: invalid scalar, expected positive integer");
            }
            if (!USE_ENDOMORPHISM) {
                JacobianPoint p = JacobianPoint.ZERO;
                JacobianPoint d = this;
                while (n.signum() > 0) {
                    if (n.and(BigInteger.ONE).signum() == 1) p = p.add(d);
                    d = d.doubleAdd();
                    n = n.shiftRight(1);
                }
                return p;
            }
            BigInteger[] k = splitScalarEndo(n);
            boolean k1neg = k[0].signum() < 0;
            boolean k2neg = k[1].signum() < 0;
            BigInteger k1 = k1neg ? k[0].negate() : k[0];
            BigInteger k2 = k2neg ? k[1].negate() : k[1];
            JacobianPoint k1p = JacobianPoint.ZERO;
            JacobianPoint k2p = JacobianPoint.ZERO;
            JacobianPoint d = this;
            while (k1.signum() > 0 || k2.signum() > 0) {
                if (k1.and(BigInteger.ONE).signum() == 1) k1p = k1p.add(d);
                if (k2.and(BigInteger.ONE).signum() == 1) k2p = k2p.add(d);
                d = d.doubleAdd();
                k1 = k1.shiftRight(1);
                k2 = k2.shiftRight(1);
            }
            if (k1neg) k1p = k1p.negate();
            if (k2neg) k2p = k2p.negate();
            k2p = new JacobianPoint(mod(k2p.x.multiply(beta)), k2p.y, k2p.z);
            return k1p.add(k2p);
        }

        Point toAffine() {
            return toAffine(this.z.modInverse(P));
        }

        // Converts Jacobian point to default (x, y) coordinates.
        // Can accept precomputed Z^-1 - for example, from invertBatch.
        Point toAffine(BigInteger invZ) {
            BigInteger invZ2 = invZ.pow(2);
            BigInteger x = mod(this.x.multiply(invZ2));
            BigInteger y = mod(this.y.multiply(invZ2).multiply(invZ));
            return new Point(x, y);
        }
    }

    /**
     * Default Point works in default aka affine coordinates: (x, y)
     */
    static class Point {
        // Base point aka generator
        // public_key = Point.BASE * private_key
        static final Point BASE = new Point(Gx, Gy);
        // Identity point aka point at infinity
        // point = point + zero_point
        static final Point ZERO = new Point(BigInteger.ZERO, BigInteger.ZERO);

        private final BigInteger x;
        private final BigInteger y;

        public Point(BigInteger x, BigInteger y) {
            this.x = x;
            this.y = y;
        }
    }

    // -------------------------

    private static BigInteger mod(BigInteger a) {
        return mod(a, P);
    }

    private static BigInteger mod(BigInteger a, BigInteger b) {
        BigInteger result = a.remainder(b);
        return result.signum() >= 0 ? result : b.add(result);
    }

    // Eucledian GCD
    // https://brilliant.org/wiki/extended-euclidean-algorithm/
    private static BigInteger[] egcd(BigInteger a, BigInteger b) {
        BigInteger x = BigInteger.ZERO, y = BigInteger.ONE, u = BigInteger.ONE, v = BigInteger.ZERO;
        while (a.signum() != 0) {
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
        BigInteger gcd = b;
        return new BigInteger[]{gcd, x, y};
    }

    private static BigInteger invert(BigInteger number) {
        return invert(number, P);
    }

    private static BigInteger invert(BigInteger number, BigInteger modulo) {
        if (number.signum() == 0 || modulo.signum() <= 0) {
            throw new IllegalArgumentException("invert: expected positive integers");
        }
        BigInteger[] result = egcd(mod(number, modulo), modulo);
        if (result[0].compareTo(BigInteger.ONE) != 0) {
            throw new IllegalArgumentException("invert: does not exist");
        }
        return mod(result[1], modulo);
    }

    private static BigInteger[] invertBatch(BigInteger[] nums) {
        return invertBatch(nums, P);
    }

    private static BigInteger[] invertBatch(BigInteger[] nums, BigInteger n) {
        int len = nums.length;
        BigInteger[] scratch = new BigInteger[len];
        BigInteger acc = BigInteger.ONE;
        for (int i = 0; i < len; i++) {
            if (nums[i].signum() == 0) continue;
            scratch[i] = acc;
            acc = mod(acc.multiply(nums[i]), n);
        }
        acc = invert(acc, n);
        for (int i = len - 1; i >= 0 ; i--) {
            if (nums[i].signum() == 0) continue;
            BigInteger tmp = mod(acc.multiply(nums[i]), n);
            nums[i] = mod(acc.multiply(scratch[i]), n);
            acc = tmp;
        }
        return nums;
    }

    // Split 256-bit K into 2 128-bit (k1, k2) for which k1 + k2 * lambda = K.
    // Used for endomorphism.
    // https://gist.github.com/paulmillr/eb670806793e84df628a7c434a873066
    private static BigInteger[] splitScalarEndo(BigInteger k) {
        BigInteger a1 = new BigInteger("3086d221a7d46bcde86c90e49284eb15", 16);
        BigInteger b1 = new BigInteger("-e4437ed6010e88286f547fa90abfe4c3", 16);
        BigInteger a2 = new BigInteger("114ca50f7a8e2f3f657c1108d9d44cfd8", 16);
        BigInteger b2 = a1;
        BigInteger c1 = b2.multiply(k).divide(n);
        BigInteger c2 = b1.negate().multiply(k).divide(n);
        BigInteger k1 = k.subtract(c1.multiply(a1)).subtract(c2.multiply(a2));
        BigInteger k2 = c1.negate().multiply(b1).subtract(c2.multiply(b2));
        return new BigInteger[]{k1, k2};
    }
}
