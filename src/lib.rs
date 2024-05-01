pub mod annotations;
pub mod termname;
use cranelift_codegen_meta::isa::Isa;
use std::path::PathBuf;

pub const REG_WIDTH: usize = 64;

pub const FLAGS_WIDTH: usize = 4;

pub fn build_clif_lower_isle() -> PathBuf {
    // Build the relevant ISLE prelude using the meta crate
    let out_dir = "veri-isle-clif-gen";
    let isle_dir = std::path::Path::new(&out_dir);

    if isle_dir.is_dir() {
        let clif_lower_isle = isle_dir.join("clif_lower.isle");
        if clif_lower_isle.is_file() {
            return clif_lower_isle;
        }
    }
    std::fs::create_dir_all(isle_dir)
        .expect("Could not create directory for CLIF ISLE meta-generated code");

    // For now, build ISLE files for x86 and aarch64
    let isas = vec![Isa::X86, Isa::Arm64];

    if let Err(err) = cranelift_codegen_meta::generate(&isas, &out_dir, isle_dir.to_str().unwrap())
    {
        panic!("Meta generate error: {}", err);
    }

    PathBuf::from(isle_dir.join("clif_lower.isle"))
}
