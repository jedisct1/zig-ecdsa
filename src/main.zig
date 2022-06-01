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
            /// Length (in bytes) of a raw signature.
            pub const raw_encoded_length = Curve.scalar.encoded_length * 2;
            /// Maximum length (in bytes) of a DER-encoded signature.
            pub const der_encoded_max_length = raw_encoded_length + 2 + 2 * 3;

            /// The R component of an ECDSA signature.
            r: Curve.scalar.CompressedScalar,
            /// The S component of an ECDSA signature.
            s: Curve.scalar.CompressedScalar,

            pub fn verify(self: Signature, msg: []const u8, public_key: PublicKey) (IdentityElementError || NonCanonicalError || SignatureVerificationError)!void {
                const r = try Curve.scalar.Scalar.fromBytes(self.r, .Big);
                const s = try Curve.scalar.Scalar.fromBytes(self.s, .Big);
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

            pub fn to_raw(self: Signature) [raw_encoded_length]u8 {
                var bytes: [raw_encoded_length]u8 = undefined;
                mem.copy(u8, bytes[0 .. raw_encoded_length / 2], &self.r);
                mem.copy(u8, bytes[raw_encoded_length / 2 ..], &self.s);
                return bytes;
            }

            pub fn from_raw(bytes: [raw_encoded_length]u8) Signature {
                return Signature{
                    .r = bytes[0 .. raw_encoded_length / 2].*,
                    .s = bytes[raw_encoded_length / 2 ..].*,
                };
            }

            pub fn to_der(self: Signature, buf: *[der_encoded_max_length]u8) []u8 {
                var fb = io.fixedBufferStream(buf);
                const w = fb.writer();
                const r_len = @intCast(u8, self.r.len + (self.r[0] >> 7));
                const s_len = @intCast(u8, self.s.len + (self.s[0] >> 7));
                const seq_len = @intCast(u8, 2 + r_len + 2 + s_len);
                w.writeAll(&[_]u8{ 0x30, seq_len }) catch unreachable;
                w.writeAll(&[_]u8{ 0x02, r_len }) catch unreachable;
                if (self.r[0] >> 7 != 0) {
                    w.writeByte(0x00) catch unreachable;
                }
                w.writeAll(&self.r) catch unreachable;
                w.writeAll(&[_]u8{ 0x02, s_len }) catch unreachable;
                if (self.s[0] >> 7 != 0) {
                    w.writeByte(0x00) catch unreachable;
                }
                w.writeAll(&self.s) catch unreachable;
                return fb.getWritten();
            }

            pub fn from_der(der: []const u8) EncodingError!Signature {
                var sig: Signature = undefined;
                var fb = io.fixedBufferStream(der);
                const r = fb.reader();
                var buf: [2]u8 = undefined;
                _ = r.readAll(&buf) catch return error.InvalidEncoding;
                if (buf[0] != 0x30 or @as(usize, buf[1]) + 2 != der.len) {
                    std.debug.print("{} vs {}\n", .{ buf[1], der.len });
                    return error.InvalidEncoding;
                }

                _ = r.readAll(&buf) catch return error.InvalidEncoding;
                if (buf[0] != 0x02) return error.InvalidEncoding;
                var r_len: usize = buf[1];
                if (r_len == sig.r.len + 1) {
                    if ((r.readByte() catch return error.InvalidEncoding) != 0x00) return error.InvalidEncoding;
                    r_len -= 1;
                }
                if (r_len != sig.r.len) return error.InvalidEncoding;
                _ = r.readAll(&sig.r) catch return error.InvalidEncoding;

                _ = r.readAll(&buf) catch return error.InvalidEncoding;
                var s_len: usize = buf[1];
                if (s_len == sig.s.len + 1) {
                    if ((r.readByte() catch return error.InvalidEncoding) != 0x00) return error.InvalidEncoding;
                    s_len -= 1;
                }
                if (s_len != sig.s.len) return error.InvalidEncoding;
                _ = r.read(&sig.s) catch return error.InvalidEncoding;

                if (fb.getPos() catch unreachable != der.len) return error.InvalidEncoding;

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

    std.debug.print("{s}\n", .{std.fmt.fmtSliceHexLower(&sig.to_raw())});

    var buf: [Scheme.Signature.der_encoded_max_length]u8 = undefined;
    const der = sig.to_der(&buf);
    std.debug.print("{s}\n", .{std.fmt.fmtSliceHexLower(der)});
    const sig2 = try Scheme.Signature.from_der(der);
    std.debug.print("{s}\n", .{std.fmt.fmtSliceHexLower(&sig2.to_raw())});

    try sig.verify(msg, kp.public_key);

    const Scheme2 = Ecdsa(crypto.ecc.P384, crypto.hash.sha2.Sha384);
    const raw_sk: [48]u8 = .{ 32, 52, 118, 9, 96, 116, 119, 172, 168, 251, 251, 197, 230, 33, 132, 85, 243, 25, 150, 105, 121, 46, 248, 180, 102, 250, 168, 123, 220, 103, 121, 129, 68, 200, 72, 221, 3, 102, 30, 237, 90, 198, 36, 97, 52, 12, 234, 150 };
    const sk = try Scheme2.KeyPair.fromSecretKey(raw_sk);
    const raw_sig: [96]u8 = .{ 192, 233, 12, 152, 202, 13, 215, 5, 221, 225, 105, 76, 100, 188, 6, 234, 26, 45, 213, 166, 72, 21, 167, 112, 121, 34, 50, 175, 194, 137, 21, 42, 253, 245, 34, 125, 21, 88, 71, 191, 18, 53, 136, 149, 28, 251, 115, 204, 181, 93, 139, 88, 188, 79, 5, 169, 71, 40, 9, 15, 148, 214, 188, 54, 94, 148, 115, 224, 42, 214, 54, 162, 177, 37, 23, 220, 59, 3, 182, 43, 157, 172, 8, 123, 107, 31, 74, 4, 91, 134, 24, 195, 95, 103, 241, 11 };
    const sig3 = Scheme2.Signature.from_raw(raw_sig);
    try sig3.verify("test", sk.public_key);
}
