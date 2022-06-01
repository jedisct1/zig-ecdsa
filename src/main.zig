const std = @import("std");
const mem = std.mem;
const crypto = std.crypto;

const IdentityElementError = crypto.errors.IdentityElementError;
const NonCanonicalError = crypto.errors.NonCanonicalError;
const SignatureVerificationError = crypto.errors.SignatureVerificationError;

pub fn Ecdsa(comptime Curve: type, comptime Hash: type) type {
    const Hmac = crypto.auth.hmac.Hmac(Hash);

    return struct {
        /// Length (in bytes) of a compressed secret key.
        pub const secret_length = Curve.scalar.encoded_length;
        /// Length (in bytes) of a signature.
        pub const signature_length = Curve.scalar.encoded_length * 2;
        /// Length (in bytes) of optional random bytes, for non-deterministic signatures.
        pub const noise_length = Curve.scalar.encoded_length;
        /// Length (in bytes) of a seed required to create a key pair.
        pub const seed_length = noise_length;

        /// An ECDSA secret key.
        pub const SecretKey = Curve.scalar.CompressedScalar;
        /// An ECDSA public key.
        pub const PublicKey = Curve;

        /// An ECDSA key pair.
        pub const KeyPair = struct {
            /// Public part.
            public_key: PublicKey,
            /// Secret scalar.
            secret_key: SecretKey,

            pub fn create(seed: ?[seed_length]u8) IdentityElementError!KeyPair {
                const h = [_]u8{0x00} ** Hash.digest_length;
                const k0 = [_]u8{0x01} ** secret_length;
                const secret_key = deterministicScalar(h, k0, seed).toBytes(.Big);
                return fromSecretKey(secret_key);
            }

            pub fn fromSecretKey(secret_key: [secret_length]u8) IdentityElementError!KeyPair {
                const public_key = try Curve.basePoint.mul(secret_key, .Big);
                return KeyPair{ .secret_key = secret_key, .public_key = public_key };
            }
        };

        pub fn sign(msg: []const u8, secret_key: SecretKey, noise: ?[noise_length]u8) (IdentityElementError || NonCanonicalError)![signature_length]u8 {
            var h: [Hash.digest_length]u8 = undefined;
            Hash.hash(msg, &h, .{});

            const scalar_encoded_length = Curve.scalar.encoded_length;
            std.debug.assert(h.len >= scalar_encoded_length);
            const z = reduceToScalar(scalar_encoded_length, h[0..scalar_encoded_length].*);

            const k = deterministicScalar(h, secret_key, noise);

            const p = try Curve.basePoint.mul(k.toBytes(.Big), .Big);
            const xs = p.affineCoordinates().x.toBytes(.Big);
            const r = reduceToScalar(Curve.Fe.encoded_length, xs);
            if (r.isZero()) return error.IdentityElement;

            const k_inv = k.invert();
            const zrs = z.add(r.mul(try Curve.scalar.Scalar.fromBytes(secret_key, .Big)));
            const s = k_inv.mul(zrs);
            if (s.isZero()) return error.IdentityElement;

            var sig: [signature_length]u8 = undefined;
            mem.copy(u8, sig[0..Curve.scalar.encoded_length], &r.toBytes(.Big));
            mem.copy(u8, sig[Curve.scalar.encoded_length..], &s.toBytes(.Big));
            return sig;
        }

        pub fn verify(sig: [signature_length]u8, msg: []const u8, public_key: PublicKey) (IdentityElementError || NonCanonicalError || SignatureVerificationError)!void {
            const r = try Curve.scalar.Scalar.fromBytes(sig[0..Curve.scalar.encoded_length].*, .Big);
            const s = try Curve.scalar.Scalar.fromBytes(sig[Curve.scalar.encoded_length..].*, .Big);
            if (r.isZero() or s.isZero()) return error.IdentityElement;

            var h: [Hash.digest_length]u8 = undefined;
            Hash.hash(msg, &h, .{});

            const ht = Curve.scalar.encoded_length;
            const z = reduceToScalar(ht, h[0..ht].*);
            if (z.isZero()) {
                return error.SignatureVerificationFailed;
            }

            const s_inv = s.invert();
            const v1 = z.mul(s_inv).toBytes(.Little);
            const v2 = r.mul(s_inv).toBytes(.Little);
            const v1g = try Curve.basePoint.mulPublic(v1, .Little);
            const v2pk = try public_key.mulPublic(v2, .Little);
            const vxs = v1g.add(v2pk).affineCoordinates().x.toBytes(.Big);
            const vr = reduceToScalar(Curve.Fe.encoded_length, vxs);
            if (!r.equivalent(vr)) {
                return error.SignatureVerificationFailed;
            }
        }

        fn reduceToScalar(comptime unreduced_len: usize, s: [unreduced_len]u8) Curve.scalar.Scalar {
            if (unreduced_len >= 48) {
                var xs = [_]u8{0} ** 64;
                mem.copy(u8, xs[xs.len - s.len ..], s[0..]);
                return Curve.scalar.Scalar.fromBytes64(xs, .Big);
            }
            var xs = [_]u8{0} ** 48;
            mem.copy(u8, xs[xs.len - s.len ..], s[0..]);
            return Curve.scalar.Scalar.fromBytes48(xs, .Big);
        }

        fn deterministicScalar(h: [Hash.digest_length]u8, secret_key: SecretKey, noise: ?[noise_length]u8) Curve.scalar.Scalar {
            var k = [_]u8{0x00} ** h.len;
            var m = [_]u8{0x00} ** (h.len + 1 + noise_length + secret_key.len + h.len);
            const m_v = m[0..h.len];
            const m_i = &m[m_v.len];
            const m_z = m[m_v.len + 1 ..][0..noise_length];
            const m_x = m[m_v.len + 1 + noise_length ..][0..secret_key.len];
            const m_h = m[m.len - h.len ..];

            mem.set(u8, m_v, 0x01);
            m_i.* = 0x00;
            if (noise) |n| mem.copy(u8, m_z, &n);
            mem.copy(u8, m_x, &secret_key);
            mem.copy(u8, m_h, &h);
            Hmac.create(&k, &m, &k);
            Hmac.create(m_v, m_v, &k);
            mem.copy(u8, m_v, m_v);
            m_i.* = 0x01;
            Hmac.create(&k, &m, &k);
            Hmac.create(m_v, m_v, &k);
            while (true) {
                Hmac.create(m_v, m_v, &k);
                if (Curve.scalar.Scalar.fromBytes(m_v[0..Curve.scalar.encoded_length].*, .Big)) |s| return s else |_| {}
                mem.copy(u8, m_v, m_v);
                m_i.* = 0x00;
                Hmac.create(&k, m[0 .. m_v.len + 1], &k);
                Hmac.create(m_v, m_v, &k);
            }
        }
    };
}

pub fn main() anyerror!void {
    const Curve = crypto.ecc.P384;
    const Hash = crypto.hash.sha2.Sha384;

    const Scheme = Ecdsa(Curve, Hash);
    const kp = try Scheme.KeyPair.create(null);
    const msg = "test";

    var noise: [Scheme.noise_length]u8 = undefined;
    std.crypto.random.bytes(&noise);
    var sig = try Scheme.sign(msg, kp.secret_key, noise);

    std.debug.print("{s}\n", .{std.fmt.fmtSliceHexLower(&sig)});

    try Scheme.verify(sig, msg, kp.public_key);
}
