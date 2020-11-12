package com.raugfer.crypto;

import java.math.BigInteger;
import java.util.*;
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
            final BigInteger[] toInv = invertBatch(points.stream().map(p -> p.z).toArray(BigInteger[]::new));
            return IntStream.range(0, points.size()).mapToObj(i -> points.get(i).toAffine(toInv[i])).collect(Collectors.toList());
        }

        static List<JacobianPoint> normalizeZ(List<JacobianPoint> points) {
            return JacobianPoint.toAffineBatch(points).stream().map(JacobianPoint::fromAffine).collect(Collectors.toList());
        }

        // Compare one point to another.
        boolean equals(JacobianPoint other) {
            final JacobianPoint a = this;
            final JacobianPoint b = other;
            final BigInteger az2 = mod(a.z.multiply(a.z));
            final BigInteger az3 = mod(a.z.multiply(az2));
            final BigInteger bz2 = mod(b.z.multiply(b.z));
            final BigInteger bz3 = mod(b.z.multiply(bz2));
            return mod(a.x.multiply(bz2)).compareTo(mod(az2.multiply(b.x))) == 0 && mod(a.y.multiply(bz3)).compareTo(mod(az3.multiply(b.y))) == 0;
        }

        // Flips point to one corresponding to (x, -y) in Affine coordinates.
        JacobianPoint negate() {
            return new JacobianPoint(this.x, mod(this.y.negate()), this.z);
        }

        // Fast algo for doubling 2 Jacobian Points when curve's a=0.
        // Note: cannot be reused for other curves when a != 0.
        // From: http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
        // Cost: 2M + 5S + 6add + 3*2 + 1*3 + 1*8.
        JacobianPoint doubleAdd() {
            final BigInteger X1 = this.x;
            final BigInteger Y1 = this.y;
            final BigInteger Z1 = this.z;
            final BigInteger A = X1.pow(2);
            final BigInteger B = Y1.pow(2);
            final BigInteger C = B.pow(2);
            final BigInteger D = BigInteger.valueOf(2L).multiply((X1.add(B)).pow(2).subtract(A).subtract(C));
            final BigInteger E = BigInteger.valueOf(3L).multiply(A);
            final BigInteger F = E.pow(2);
            final BigInteger X3 = mod(F.subtract(BigInteger.valueOf(2L).multiply(D)));
            final BigInteger Y3 = mod(E.multiply(D.subtract(X3)).subtract(BigInteger.valueOf(8L).multiply(C)));
            final BigInteger Z3 = mod(BigInteger.valueOf(2L).multiply(Y1).multiply(Z1));
            return new JacobianPoint(X3, Y3, Z3);
        }

        // Fast algo for adding 2 Jacobian Points when curve's a=0.
        // Note: cannot be reused for other curves when a != 0.
        // http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-1998-cmo-2
        // Cost: 12M + 4S + 6add + 1*2.
        // Note: 2007 Bernstein-Lange (11M + 5S + 9add + 4*2) is actually *slower*. No idea why.
        JacobianPoint add(JacobianPoint other) {
            final BigInteger X1 = this.x;
            final BigInteger Y1 = this.y;
            final BigInteger Z1 = this.z;
            final BigInteger X2 = other.x;
            final BigInteger Y2 = other.y;
            final BigInteger Z2 = other.z;
            if (X2.signum() == 0 || Y2.signum() == 0) return this;
            if (X1.signum() == 0 || Y1.signum() == 0) return other;
            final BigInteger Z1Z1 = Z1.pow(2);
            final BigInteger Z2Z2 = Z2.pow(2);
            final BigInteger U1 = X1.multiply(Z2Z2);
            final BigInteger U2 = X2.multiply(Z1Z1);
            final BigInteger S1 = Y1.multiply(Z2).multiply(Z2Z2);
            final BigInteger S2 = Y2.multiply(Z1).multiply(Z1Z1);
            final BigInteger H = mod(U2.subtract(U1));
            final BigInteger r = mod(S2.subtract(S1));
            if (H.signum() == 0) {
                if (r.signum() == 0) {
                    return this.doubleAdd();
                } else {
                    return JacobianPoint.ZERO;
                }
            }
            final BigInteger HH = mod(H.pow(2));
            final BigInteger HHH = mod(H.multiply(HH));
            final BigInteger V = U1.multiply(HH);
            final BigInteger X3 = mod(r.pow(2).subtract(HHH).subtract(BigInteger.valueOf(2L).multiply(V)));
            final BigInteger Y3 = mod(r.multiply(V.subtract(X3)).subtract(S1.multiply(HHH)));
            final BigInteger Z3 = mod(Z1.multiply(Z2).multiply(H));
            return new JacobianPoint(X3, Y3, Z3);
        }

        // Non-constant-time multiplication. Uses double-and-add algorithm.
        // It's faster, but should only be used when you don't care about
        // an exposed private key e.g. sig verification, which works over *public* keys.
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

        private List<JacobianPoint> precomputeWindow(int W) {
            final int windows = USE_ENDOMORPHISM ? 128 / W + 2 : 256 / W + 1;
            List<JacobianPoint> points = new ArrayList<>();
            JacobianPoint p = this;
            JacobianPoint base;
            for (int window = 0; window < windows; window++) {
                base = p;
                points.add(base);
                for (int i = 1; i < Math.pow(2, W -1); i++) {
                    base = base.add(p);
                    points.add(base);
                }
                p = base.doubleAdd();
            }
            return points;
        }

        private JacobianPoint[] wNAF(BigInteger n, Point affinePoint) {
            if (affinePoint == null && this.equals(JacobianPoint.BASE)) affinePoint = Point.BASE;
            final int W = affinePoint != null && affinePoint._WINDOW_SIZE > 0 ? affinePoint._WINDOW_SIZE : 1;
            if (256 % W == 1) {
                throw new IllegalArgumentException("Point#wNAF: Invalid precomputation window, must be power of 2");
            }
            List<JacobianPoint> precomputes = affinePoint != null && pointPrecomputes.get(affinePoint) != null ? pointPrecomputes.get(affinePoint) : null;
            if (precomputes == null) {
                precomputes = this.precomputeWindow(W);
                if (affinePoint != null && W != 1) {
                    precomputes = JacobianPoint.normalizeZ(precomputes);
                    pointPrecomputes.put(affinePoint, precomputes);
                }
            }

            JacobianPoint p = JacobianPoint.ZERO;
            JacobianPoint f = JacobianPoint.ZERO;

            final int windows = USE_ENDOMORPHISM ? 128 / W + 2 : 256 / W + 1;
            final int windowSize = (int) Math.pow(2, W - 1);
            final BigInteger mask = BigInteger.valueOf((long) (Math.pow(2, W) - 1)); // Create mask with W ones: 0b1111 for W=4 etc.
            final int maxNumber = (int) Math.pow(2, W);

            for (int window = 0; window < windows; window++) {
                final int offset = window * windowSize;
                // Extract W bits.
                int wbits = n.and(mask).intValue();

                // Shift number by W bits.
                n = n.shiftRight(W);

                // If the bits are bigger than max size, we'll split those.
                // +224 => 256 - 32
                if (wbits > windowSize) {
                    wbits -= maxNumber;
                    n = n.add(BigInteger.ONE);
                }

                // Check if we're onto Zero point.
                // Add random point inside current window to f.
                if (wbits == 0) {
                    f = f.add(window % 2 == 1 ? precomputes.get(offset).negate() : precomputes.get(offset));
                } else {
                    final JacobianPoint cached = precomputes.get(offset + Math.abs(wbits) - 1);
                    p = p.add(wbits < 0 ? cached.negate() : cached);
                }
            }
            return new JacobianPoint[]{p, f};
        }

        // Constant time multiplication.
        // Uses wNAF method. Windowed method may be 10% faster,
        // but takes 2x longer to generate and consumes 2x memory.
        JacobianPoint multiply(BigInteger scalar, Point affinePoint) {
            BigInteger n = mod(scalar, nobel_secp256k1.n);
            if (n.signum() <= 0) {
                throw new IllegalArgumentException("Point#multiply: invalid scalar, expected positive integer");
            }
            // Real point.
            JacobianPoint point;
            // Fake point, we use it to achieve constant-time multiplication.
            JacobianPoint fake;
            if (USE_ENDOMORPHISM) {
                BigInteger[] k = splitScalarEndo(n);
                boolean k1neg = k[0].signum() < 0;
                boolean k2neg = k[1].signum() < 0;
                BigInteger k1 = k1neg ? k[0].negate() : k[0];
                BigInteger k2 = k2neg ? k[1].negate() : k[1];
                JacobianPoint[] result1 = this.wNAF(k1, affinePoint);
                JacobianPoint k1p = result1[0];
                JacobianPoint f1p = result1[1];
                JacobianPoint[] result2 = this.wNAF(k2, affinePoint);
                JacobianPoint k2p = result2[0];
                JacobianPoint f2p = result2[1];
                if (k1neg) k1p = k1p.negate();
                if (k2neg) k2p = k2p.negate();
                k2p = new JacobianPoint(mod(k2p.x.multiply(beta)), k2p.y, k2p.z);
                point = k1p.add(k2p);
                fake = f1p.add(f2p);
            } else {
                JacobianPoint[] result = this.wNAF(n, affinePoint);
                point = result[0];
                fake = result[1];
            }
            return JacobianPoint.normalizeZ(Arrays.asList(point, fake)).get(0);
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

    // Stores precomputed values for points.
    static HashMap<Point, List<JacobianPoint>> pointPrecomputes = new HashMap<>();

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
        // We calculate precomputes for elliptic curve point multiplication
        // using windowed method. This specifies window size and
        // stores precomputed values. Usually only base point would be precomputed.
        int _WINDOW_SIZE;

        private final BigInteger x;
        private final BigInteger y;

        public Point(BigInteger x, BigInteger y) {
            this.x = x;
            this.y = y;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            return equals((Point) o);
        }

        @Override
        public int hashCode() {
            return Objects.hash(x, y);
        }

        // "Private method", don't use it directly.
        void _setWindowSize(int windowSize) {
            this._WINDOW_SIZE = windowSize;
            pointPrecomputes.remove(this);
        }

        boolean equals(Point other) {
            return this.x.compareTo(other.x) == 0 && this.y.compareTo(other.y) == 0;
        }

        Point negate() {
            return new Point(this.x, mod(this.y.negate()));
        }

        Point doubleAdd() {
            return JacobianPoint.fromAffine(this).doubleAdd().toAffine();
        }

        Point add(Point other) {
            return JacobianPoint.fromAffine(this).add(JacobianPoint.fromAffine(other)).toAffine();
        }

        Point subtract(Point other) {
            return this.add(other.negate());
        }

        Point multiply(BigInteger scalar) {
            return JacobianPoint.fromAffine(this).multiply(scalar, this).toAffine();
        }

    }

    // -------------------------

    private static BigInteger mod(BigInteger a) {
        return mod(a, P);
    }

    private static BigInteger mod(BigInteger a, BigInteger b) {
        final BigInteger result = a.remainder(b);
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
        final BigInteger gcd = b;
        return new BigInteger[]{gcd, x, y};
    }

    private static BigInteger invert(BigInteger number) {
        return invert(number, P);
    }

    private static BigInteger invert(BigInteger number, BigInteger modulo) {
        if (number.signum() == 0 || modulo.signum() <= 0) {
            throw new IllegalArgumentException("invert: expected positive integers");
        }
        final BigInteger[] result = egcd(mod(number, modulo), modulo);
        if (result[0].compareTo(BigInteger.ONE) != 0) {
            throw new IllegalArgumentException("invert: does not exist");
        }
        return mod(result[1], modulo);
    }

    private static BigInteger[] invertBatch(BigInteger[] nums) {
        return invertBatch(nums, P);
    }

    private static BigInteger[] invertBatch(BigInteger[] nums, BigInteger n) {
        final int len = nums.length;
        final BigInteger[] scratch = new BigInteger[len];
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
        final BigInteger a1 = new BigInteger("3086d221a7d46bcde86c90e49284eb15", 16);
        final BigInteger b1 = new BigInteger("-e4437ed6010e88286f547fa90abfe4c3", 16);
        final BigInteger a2 = new BigInteger("114ca50f7a8e2f3f657c1108d9d44cfd8", 16);
        final BigInteger b2 = a1;
        final BigInteger c1 = b2.multiply(k).divide(n);
        final BigInteger c2 = b1.negate().multiply(k).divide(n);
        final BigInteger k1 = k.subtract(c1.multiply(a1)).subtract(c2.multiply(a2));
        final BigInteger k2 = c1.negate().multiply(b1).subtract(c2.multiply(b2));
        return new BigInteger[]{k1, k2};
    }

    // Enable precomputes. Slows down first publicKey computation by 20ms.
//    Point.BASE._setWindowSize(8);


    public static void main(String[] args) {
        Point.BASE._setWindowSize(8);
        BigInteger scalar = BigInteger.valueOf(2L).pow(255).subtract(BigInteger.valueOf(19L));
        BigInteger e = scalar.divide(BigInteger.valueOf(2L));
        Point.BASE.multiply(scalar);
        //101882464215605532259071152557064774604578577202762638099270085421610171632006
        //71930336516333869201847187295180427488149033125922296280127429751733155275509
        // 78732798984116430258613239589690684862379840002607688608364865156785237059007
        long a = System.nanoTime();
        for (int i = 0; i < 4017; i++) {
            Point.BASE.multiply(scalar);
//            secp256k1.sgn(e, scalar, scalar);
        }
        long b = System.nanoTime();
        System.out.println((b - a) / 1000000);
    }
}
