// This defines the amd64 target for the Linux Kernel. See the linux-kernel-base module for
// generic Linux kernel options.

use crate::spec::{Cc, CodeModel, LinkerFlavor, Lld, Target};

pub fn target() -> Target {
    let mut base = super::linux_kernel_base::opts();
    base.cpu = "x86-64".into();
    base.max_atomic_width = Some(64);
    base.features =
        "-mmx,-sse,-sse2,-sse3,-ssse3,-sse4.1,-sse4.2,-3dnow,-3dnowa,-avx,-avx2,+soft-float".into();
    base.code_model = Some(CodeModel::Kernel);
    base.add_pre_link_args(LinkerFlavor::Gnu(Cc::Yes, Lld::No), &["-m64"]);

    Target {
        // FIXME: Some dispute, the linux-on-clang folks think this should use
        // "Linux". We disagree because running *on* Linux is nothing like
        // running *as" linux, and historically the "os" component as has always
        // been used to mean the "on" part.
        llvm_target: "x86_64-unknown-none-elf".into(),
        pointer_width: 64,
        data_layout: "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
            .into(),
        arch: "x86_64".into(),

        options: base,
    }
}
