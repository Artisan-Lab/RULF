use super::{RelocModel, Target, TargetOptions};

pub fn target() -> Target {
    let base = super::solid_base::opts("asp3");
    Target {
        llvm_target: "armv7a-none-eabi".into(),
        pointer_width: 32,
        data_layout: "e-m:e-p:32:32-Fi8-i64:64-v128:64:128-a:0:32-n32-S64".into(),
        arch: "arm".into(),
        options: TargetOptions {
            linker: Some("arm-kmc-eabi-gcc".into()),
            features: "+v7,+soft-float,+thumb2,-neon".into(),
            relocation_model: RelocModel::Static,
            disable_redzone: true,
            max_atomic_width: Some(64),
            ..base
        },
    }
}
