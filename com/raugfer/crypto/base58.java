package com.raugfer.crypto;

import java.math.BigInteger;

public class base58 {

    public static final String digits = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

    public static String encode(byte[] b) {
        StringBuilder sb = new StringBuilder();
        BigInteger n = binint.b2n(b);
        BigInteger base = BigInteger.valueOf(digits.length());
        while (n.compareTo(BigInteger.ZERO) > 0) {
            BigInteger r = n.mod(base);
            n = n.divide(base);
            sb.append(digits.charAt(r.intValue()));
        }
        for (byte c : b) {
            if (c != 0) break;
            sb.append(digits.charAt(0));
        }
        return sb.reverse().toString();
    }

    public static byte[] decode(String w) {
        BigInteger v = BigInteger.ZERO;
        BigInteger base = BigInteger.valueOf(digits.length());
        for (int i = 0; i < w.length(); i++) {
            char c = w.charAt(i);
            int index = digits.indexOf(c);
            if (index < 0) throw new IllegalArgumentException("Invalid input");
            v = v.multiply(base).add(BigInteger.valueOf(index));
        }
        byte[] b = binint.n2b(v);
        int zeros = 0;
        for (int i = 0; i < w.length(); i++) {
            char c = w.charAt(i);
            if (c != digits.charAt(0)) break;
            zeros++;
        }
        if (zeros > 0) {
            byte[] t = new byte[zeros + b.length];
            System.arraycopy(b, 0, t, zeros, b.length);
            b = t;
        }
        return b;
    }

    public static String check_encode(byte[] b, byte[] prefix) {
        return check_encode(b, prefix, null);
    }

    public static String check_encode(byte[] b, byte[] prefix, hashing.hashfun f) {
        if (f == null) f = base58::_sub_hash256_0_4;
        b = bytes.concat(prefix, b);
        byte[] h = f.hash(b);
        b = bytes.concat(b, h);
        return encode(b);
    }

    public static pair<byte[], byte[]> check_decode(String w) {
        return check_decode(w, 1);
    }

    public static pair<byte[], byte[]> check_decode(String w, int prefix_len) {
        return check_decode(w, prefix_len, 4, null);
    }

    public static pair<byte[], byte[]> check_decode(String w, int prefix_len, int hash_len, hashing.hashfun f) {
        if (f == null) f = base58::_sub_hash256_0_4;
        byte[] b = decode(w);
        if (b.length < prefix_len + hash_len) throw new IllegalArgumentException("Invalid length");
        byte[] h = bytes.sub(b, -hash_len);
        b = bytes.sub(b, 0, -hash_len);
        if (!bytes.equ(h, f.hash(b))) throw new IllegalArgumentException("Invalid hash");
        byte[] prefix = bytes.sub(b, 0, prefix_len);
        b = bytes.sub(b, prefix_len);
        return new pair<>(b, prefix);
    }

    public static String translate(String w, String from_digits, String to_digits) {
        if (from_digits == null) from_digits = digits;
        if (to_digits == null) to_digits = digits;
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < w.length(); i++) {
            char c = w.charAt(i);
            int index = from_digits.indexOf(c);
            if (index < 0) throw new IllegalArgumentException("Invalid input");
            sb.append(to_digits.charAt(index));
        }
        return sb.toString();
    }

    static byte[] _sub_hash256_0_4(byte[] b) {
        return bytes.sub(hashing.hash256(b), 0, 4);
    }

}