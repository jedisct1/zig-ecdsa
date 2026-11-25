const std = @import("std");

pub fn build(b: *std.Build) void {
    const module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = b.standardTargetOptions(.{}),
        .optimize = b.standardOptimizeOption(.{}),
    });

    const lib = b.addLibrary(.{
        .name = "ecdsa",
        .linkage = .static,
        .root_module = module,
    });
    b.installArtifact(lib);

    const main_tests = b.addTest(.{ .root_module = module });
    const run_tests = b.addRunArtifact(main_tests);
    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&run_tests.step);
}
