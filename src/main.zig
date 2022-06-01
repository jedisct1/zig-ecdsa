const std = @import("std");
const io = std.io;
const mem = std.mem;
const crypto = std.crypto;

const EncodingError = crypto.errors.EncodingError;
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
        /// Maximum length (in bytes) of a DER-encoded signature.
        pub const max_der_signature_length = signature_length + 2 + 2 * 3;
        /// Length (in bytes) of optional random bytes, for non-deterministic signatures.
        pub const noise_length = Curve.scalar.encoded_length;
        /// Length (in bytes) of a seed required to create a key pair.
        pub const seed_length = noise_length;

        /// An ECDSA secret key.
        pub const SecretKey = Curve.scalar.CompressedScalar;
        /// An ECDSA public key.
        pub const PublicKey = Curve;
        /// An ECDSA signature.
        pub const Signature = struct {
            /// The R component of an ECDSA signature.
            r: Curve.scalar.CompressedScalar,
            /// The S component of an ECDSA signature.
            s: Curve.scalar.CompressedScalar,

            pub fn to_compact(self: Signature) [signature_length]u8 {
                var bytes: [signature_length]u8 = undefined;
                mem.copy(u8, bytes[0 .. signature_length / 2], &self.r);
                mem.copy(u8, bytes[signature_length / 2 ..], &self.s);
                return bytes;
            }

            pub fn from_compact(bytes: [signature_length]u8) Signature {
                return Signature{
                    .r = bytes[0 .. signature_length / 2],
                    .s = bytes[signature_length / 2 ..],
                };
            }

            pub fn to_der(self: Signature, buf: *[max_der_signature_length]u8) []u8 {
                var w = io.fixedBufferStream(buf);
                const r_len = @intCast(u8, self.r.len + (self.r[0] >> 7));
                const s_len = @intCast(u8, self.s.len + (self.s[0] >> 7));
                const seq_len = @intCast(u8, 2 + r_len + 2 + s_len);
                _ = w.write(&[_]u8{ 0x30, seq_len }) catch unreachable;
                _ = w.write(&[_]u8{ 0x02, r_len }) catch unreachable;
                if (self.r[0] >> 7 != 0) {
                    _ = w.write(&[_]u8{0x00}) catch unreachable;
                }
                _ = w.write(&self.r) catch unreachable;
                _ = w.write(&[_]u8{ 0x02, s_len }) catch unreachable;
                if (self.s[0] >> 7 != 0) {
                    _ = w.write(&[_]u8{0x00}) catch unreachable;
                }
                _ = w.write(&self.s) catch unreachable;
                return w.getWritten();
            }

            pub fn from_der(der: []const u8) EncodingError!Signature {
                var sig: Signature = undefined;
                var r = io.fixedBufferStream(der);
                var buf: [2]u8 = undefined;
                _ = try r.read(&buf);
                if (buf[0] != 0x30 or @as(usize, buf[1]) + 2 != der.len) {
                    std.debug.print("{} vs {}\n", .{ buf[1], der.len });
                    return error.InvalidEncoding;
                }

                _ = try r.read(&buf);
                if (buf[0] != 0x02) {
                    return error.InvalidEncoding;
                }
                var r_len: usize = buf[1];
                if (r_len == sig.r.len + 1) {
                    _ = try r.read(buf[0..1]);
                    if (buf[0] != 0x00) {
                        return error.InvalidEncoding;
                    }
                    r_len -= 1;
                }
                if (r_len != sig.r.len) {
                    return error.InvalidEncoding;
                }
                _ = try r.read(&sig.r);

                _ = try r.read(&buf);
                var s_len: usize = buf[1];
                if (s_len == sig.s.len + 1) {
                    _ = try r.read(buf[0..1]);
                    if (buf[0] != 0x00) {
                        return error.InvalidEncoding;
                    }
                    s_len -= 1;
                }
                if (s_len != sig.s.len) {
                    return error.InvalidEncoding;
                }
                _ = try r.read(&sig.s);

                if (r.getPos() catch unreachable != der.len) {
                    return error.InvalidEncoding;
                }
                return sig;
            }
        };

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

        pub fn sign(msg: []const u8, secret_key: SecretKey, noise: ?[noise_length]u8) (IdentityElementError || NonCanonicalError)!Signature {
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

            return Signature{ .r = r.toBytes(.Big), .s = s.toBytes(.Big) };
        }

        pub fn verify(sig: Signature, msg: []const u8, public_key: PublicKey) (IdentityElementError || NonCanonicalError || SignatureVerificationError)!void {
            const r = try Curve.scalar.Scalar.fromBytes(sig.r, .Big);
            const s = try Curve.scalar.Scalar.fromBytes(sig.s, .Big);
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
    const Curve = crypto.ecc.P256;
    const Hash = crypto.hash.sha2.Sha256;

    const Scheme = Ecdsa(Curve, Hash);
    const kp = try Scheme.KeyPair.create(null);
    const msg = "test";

    var noise: [Scheme.noise_length]u8 = undefined;
    crypto.random.bytes(&noise);
    var sig = try Scheme.sign(msg, kp.secret_key, noise);

    std.debug.print("{s}\n", .{std.fmt.fmtSliceHexLower(&sig.to_compact())});

    var buf: [Scheme.max_der_signature_length]u8 = undefined;
    const der = sig.to_der(&buf);
    std.debug.print("{s}\n", .{std.fmt.fmtSliceHexLower(der)});
    const sig2 = try Scheme.Signature.from_der(der);
    std.debug.print("{s}\n", .{std.fmt.fmtSliceHexLower(&sig2.to_compact())});

    try Scheme.verify(sig, msg, kp.public_key);
}
